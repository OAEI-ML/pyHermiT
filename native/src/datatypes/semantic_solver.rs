//! Exact datatype-component solving over canonical dense semantic range IDs.
//!
//! The semantic compiler has already assigned every normalized data range a dense
//! `u32` ID and every fixed literal an exact [`DataIdentity`].  This bridge resolves
//! each referenced range once, collapses equality classes, intersects positive and
//! negative ranges exactly, and solves the remaining finite inequality core without
//! exposing the range module's private DNF representation.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};

use crate::model::DependencySet;

use super::range::Cardinality;
use super::range_wire::{
    NativeDataRange, NativeDataWitness, NativeDatatypeRangeModel, RangeWireLimits,
};
use super::solver::{ClashKind, DatatypeClash};
use super::value::{DataIdentity, DatatypeControl, DatatypeError};

/// A positive or negative assertion against one dense semantic-model range ID.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticRangeConstraint {
    pub variable: u32,
    pub data_range_id: u32,
    pub positive: bool,
    pub dependencies: DependencySet,
}

/// A fixed semantic data identity. Source-literal identity remains outside the solver.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticFixedValueConstraint {
    pub variable: u32,
    pub value: DataIdentity,
    pub dependencies: DependencySet,
}

/// Require two concrete variables to denote one exact data identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticEqualityConstraint {
    pub left: u32,
    pub right: u32,
    pub dependencies: DependencySet,
}

/// Require two concrete variables to denote distinct data identities.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticInequalityConstraint {
    pub left: u32,
    pub right: u32,
    pub dependencies: DependencySet,
}

/// Require a variable's exact allowed range to contain at least `minimum` identities.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticCardinalityConstraint {
    pub variable: u32,
    pub minimum: u64,
    pub dependencies: DependencySet,
}

/// One closed semantic datatype component independent of tableau node handles.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticDatatypeConstraintComponent {
    pub variables: Vec<u32>,
    pub ranges: Vec<SemanticRangeConstraint>,
    pub fixed_values: Vec<SemanticFixedValueConstraint>,
    pub equalities: Vec<SemanticEqualityConstraint>,
    pub inequalities: Vec<SemanticInequalityConstraint>,
    pub cardinalities: Vec<SemanticCardinalityConstraint>,
}

/// Per-call controls. No counter or cancellation state is retained in a component.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SemanticSolverLimits {
    pub max_variables: u32,
    pub max_constraints: u32,
    pub max_compiled_ranges: u32,
    pub max_compile_steps: u64,
    pub max_solver_steps: u64,
    pub cancellation_poll_stride: u64,
    pub range_wire: RangeWireLimits,
}

impl Default for SemanticSolverLimits {
    fn default() -> Self {
        Self {
            max_variables: 1_000_000,
            max_constraints: 5_000_000,
            max_compiled_ranges: 1_000_000,
            max_compile_steps: 5_000_000,
            max_solver_steps: 1_000_000,
            cancellation_poll_stride: 64,
            range_wire: RangeWireLimits::default(),
        }
    }
}

impl SemanticSolverLimits {
    fn validate(self) -> Result<Self, DatatypeError> {
        let positive = [
            ("max_variables", u64::from(self.max_variables)),
            ("max_constraints", u64::from(self.max_constraints)),
            ("max_compiled_ranges", u64::from(self.max_compiled_ranges)),
            ("max_compile_steps", self.max_compile_steps),
            ("max_solver_steps", self.max_solver_steps),
            ("cancellation_poll_stride", self.cancellation_poll_stride),
        ];
        if let Some((name, _value)) = positive.into_iter().find(|(_name, value)| *value == 0) {
            return Err(DatatypeError::invalid(format!(
                "native semantic solver limit must be positive: {name}"
            )));
        }
        Ok(self)
    }
}

/// A validated component with every distinct dense range ID compiled exactly once.
#[derive(Clone, Debug)]
pub struct CompiledSemanticDatatypeConstraintComponent {
    component: SemanticDatatypeConstraintComponent,
    compiled_ranges: BTreeMap<u32, NativeDataRange>,
}

impl CompiledSemanticDatatypeConstraintComponent {
    #[must_use]
    pub const fn component(&self) -> &SemanticDatatypeConstraintComponent {
        &self.component
    }

    #[must_use]
    pub fn compiled_range_count(&self) -> usize {
        self.compiled_ranges.len()
    }
}

/// An immutable SAT certificate or a sufficient semantic datatype clash.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticSolveResult {
    pub satisfiable: bool,
    pub assignments: Vec<(u32, NativeDataWitness)>,
    pub clash: Option<DatatypeClash>,
}

impl SemanticSolveResult {
    const fn satisfiable(assignments: Vec<(u32, NativeDataWitness)>) -> Self {
        Self {
            satisfiable: true,
            assignments,
            clash: None,
        }
    }

    const fn unsatisfiable(clash: DatatypeClash) -> Self {
        Self {
            satisfiable: false,
            assignments: Vec::new(),
            clash: Some(clash),
        }
    }
}

/// Resolve every referenced dense range once without mutating the semantic model.
pub fn compile_datatype_constraint_component(
    model: &NativeDatatypeRangeModel,
    component: &SemanticDatatypeConstraintComponent,
    limits: SemanticSolverLimits,
    control: &impl DatatypeControl,
) -> Result<CompiledSemanticDatatypeConstraintComponent, DatatypeError> {
    let limits = limits.validate()?;
    validate_component(component, limits)?;
    control.poll()?;
    control.observe_memory(estimated_component_bytes(component).saturating_mul(2))?;
    let mut work = OperationWork::new(
        limits.max_compile_steps,
        "max_semantic_compile_steps",
        limits.cancellation_poll_stride,
        control,
    );
    let mut compiled_ranges = BTreeMap::new();
    for constraint in &component.ranges {
        work.add(1)?;
        if compiled_ranges.contains_key(&constraint.data_range_id) {
            continue;
        }
        let observed = u64::try_from(compiled_ranges.len())
            .unwrap_or(u64::MAX)
            .saturating_add(1);
        if observed > u64::from(limits.max_compiled_ranges) {
            return Err(DatatypeError::resource(
                "max_compiled_ranges",
                observed,
                u64::from(limits.max_compiled_ranges),
            ));
        }
        let data_range = model.compile_range(constraint.data_range_id, control)?;
        compiled_ranges.insert(constraint.data_range_id, data_range);
    }
    control.poll()?;
    Ok(CompiledSemanticDatatypeConstraintComponent {
        component: component.clone(),
        compiled_ranges,
    })
}

/// Compile and solve one component, retaining large and infinite ranges symbolically.
pub fn solve_semantic_component(
    model: &NativeDatatypeRangeModel,
    component: &SemanticDatatypeConstraintComponent,
    limits: SemanticSolverLimits,
    control: &impl DatatypeControl,
) -> Result<SemanticSolveResult, DatatypeError> {
    let compiled = compile_datatype_constraint_component(model, component, limits, control)?;
    solve_compiled_semantic_component(&compiled, limits, control)
}

/// Solve an already compiled component with deterministic finite-core elimination.
pub fn solve_compiled_semantic_component(
    component: &CompiledSemanticDatatypeConstraintComponent,
    limits: SemanticSolverLimits,
    control: &impl DatatypeControl,
) -> Result<SemanticSolveResult, DatatypeError> {
    solve_compiled(component, limits, control, false)
}

/// Slow exact finite-domain oracle used by generated Python/Rust differential tests.
pub fn solve_compiled_semantic_component_exhaustive(
    component: &CompiledSemanticDatatypeConstraintComponent,
    limits: SemanticSolverLimits,
    control: &impl DatatypeControl,
) -> Result<SemanticSolveResult, DatatypeError> {
    solve_compiled(component, limits, control, true)
}

fn solve_compiled(
    compiled: &CompiledSemanticDatatypeConstraintComponent,
    limits: SemanticSolverLimits,
    control: &impl DatatypeControl,
    exhaustive: bool,
) -> Result<SemanticSolveResult, DatatypeError> {
    let limits = limits.validate()?;
    validate_component(&compiled.component, limits)?;
    control.poll()?;
    control.observe_memory(estimated_component_bytes(&compiled.component).saturating_mul(5))?;
    let mut work = OperationWork::new(
        limits.max_solver_steps,
        "max_semantic_solver_steps",
        limits.cancellation_poll_stride,
        control,
    );
    let result = match prepare(compiled, limits, &mut work)? {
        Ok(prepared) => colour(prepared, limits, &mut work, exhaustive)?,
        Err(result) => result,
    };
    control.poll()?;
    Ok(result)
}

fn validate_component(
    component: &SemanticDatatypeConstraintComponent,
    limits: SemanticSolverLimits,
) -> Result<(), DatatypeError> {
    if component.variables.is_empty() {
        return Err(DatatypeError::invalid(
            "semantic datatype components require at least one variable",
        ));
    }
    let variable_count = u64::try_from(component.variables.len()).unwrap_or(u64::MAX);
    if variable_count > u64::from(limits.max_variables) {
        return Err(DatatypeError::resource(
            "max_variables",
            variable_count,
            u64::from(limits.max_variables),
        ));
    }
    if component
        .variables
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(DatatypeError::invalid(
            "semantic datatype variables must be sorted and unique",
        ));
    }
    let constraint_count = component
        .ranges
        .len()
        .checked_add(component.fixed_values.len())
        .and_then(|value| value.checked_add(component.equalities.len()))
        .and_then(|value| value.checked_add(component.inequalities.len()))
        .and_then(|value| value.checked_add(component.cardinalities.len()))
        .ok_or_else(|| DatatypeError::invalid("semantic datatype constraint count overflow"))?;
    let constraint_count = u64::try_from(constraint_count).unwrap_or(u64::MAX);
    if constraint_count > u64::from(limits.max_constraints) {
        return Err(DatatypeError::resource(
            "max_constraints",
            constraint_count,
            u64::from(limits.max_constraints),
        ));
    }
    let known: BTreeSet<_> = component.variables.iter().copied().collect();
    let unary = component
        .ranges
        .iter()
        .map(|value| value.variable)
        .chain(component.fixed_values.iter().map(|value| value.variable))
        .chain(component.cardinalities.iter().map(|value| value.variable));
    let binary = component
        .equalities
        .iter()
        .flat_map(|value| [value.left, value.right])
        .chain(
            component
                .inequalities
                .iter()
                .flat_map(|value| [value.left, value.right]),
        );
    if unary.chain(binary).any(|value| !known.contains(&value)) {
        return Err(DatatypeError::invalid(
            "semantic datatype constraint references a variable outside its component",
        ));
    }
    Ok(())
}

#[derive(Debug)]
struct OperationWork<'a, C> {
    steps: u64,
    since_poll: u64,
    maximum: u64,
    limit_name: &'static str,
    poll_stride: u64,
    control: &'a C,
}

impl<'a, C: DatatypeControl> OperationWork<'a, C> {
    const fn new(maximum: u64, limit_name: &'static str, poll_stride: u64, control: &'a C) -> Self {
        Self {
            steps: 0,
            since_poll: 0,
            maximum,
            limit_name,
            poll_stride,
            control,
        }
    }

    fn add(&mut self, amount: u64) -> Result<(), DatatypeError> {
        self.steps = self
            .steps
            .checked_add(amount)
            .ok_or_else(|| DatatypeError::invalid("semantic solver step counter overflow"))?;
        if self.steps > self.maximum {
            return Err(DatatypeError::resource(
                self.limit_name,
                self.steps,
                self.maximum,
            ));
        }
        self.since_poll = self.since_poll.checked_add(amount).ok_or_else(|| {
            DatatypeError::invalid("semantic solver cancellation counter overflow")
        })?;
        if self.since_poll >= self.poll_stride {
            self.control.poll()?;
            self.since_poll %= self.poll_stride;
        }
        Ok(())
    }
}

#[derive(Debug)]
struct UnionFind {
    parent: BTreeMap<u32, u32>,
}

impl UnionFind {
    fn new(variables: &[u32]) -> Self {
        Self {
            parent: variables.iter().map(|value| (*value, *value)).collect(),
        }
    }

    fn find(&mut self, value: u32) -> Result<u32, DatatypeError> {
        let mut root = value;
        loop {
            let parent =
                self.parent.get(&root).copied().ok_or_else(|| {
                    DatatypeError::invalid("semantic union-find variable is absent")
                })?;
            if parent == root {
                break;
            }
            root = parent;
        }
        let mut current = value;
        while current != root {
            let parent = self
                .parent
                .get(&current)
                .copied()
                .ok_or_else(|| DatatypeError::invalid("semantic union-find path is absent"))?;
            self.parent.insert(current, root);
            current = parent;
        }
        Ok(root)
    }

    fn union(&mut self, left: u32, right: u32) -> Result<(), DatatypeError> {
        let first = self.find(left)?;
        let second = self.find(right)?;
        if first != second {
            let (root, child) = if first < second {
                (first, second)
            } else {
                (second, first)
            };
            self.parent.insert(child, root);
        }
        Ok(())
    }
}

#[derive(Debug)]
struct Prepared {
    variables: Vec<u32>,
    representatives: Vec<u32>,
    representative_by_variable: BTreeMap<u32, u32>,
    members: BTreeMap<u32, Vec<u32>>,
    equality_dependencies: BTreeMap<u32, BTreeSet<u32>>,
    domains: BTreeMap<u32, NativeDataRange>,
    domain_dependencies: BTreeMap<u32, BTreeSet<u32>>,
    fixed: BTreeMap<u32, (DataIdentity, BTreeSet<u32>)>,
    adjacency: BTreeMap<u32, BTreeSet<u32>>,
    edge_dependencies: BTreeMap<(u32, u32), BTreeSet<u32>>,
}

fn prepare<C: DatatypeControl>(
    compiled: &CompiledSemanticDatatypeConstraintComponent,
    limits: SemanticSolverLimits,
    work: &mut OperationWork<'_, C>,
) -> Result<Result<Prepared, SemanticSolveResult>, DatatypeError> {
    let component = &compiled.component;
    let mut union_find = UnionFind::new(&component.variables);
    for equality in &component.equalities {
        work.add(1)?;
        union_find.union(equality.left, equality.right)?;
    }
    let mut representative_by_variable = BTreeMap::new();
    let mut members: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    for variable in &component.variables {
        let representative = union_find.find(*variable)?;
        representative_by_variable.insert(*variable, representative);
        members.entry(representative).or_default().push(*variable);
    }
    let representatives: Vec<_> = members.keys().copied().collect();
    let mut equality_dependencies = representatives
        .iter()
        .map(|value| (*value, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    for equality in &component.equalities {
        let representative = representative_by_variable[&equality.left];
        extend_dependencies(
            &mut equality_dependencies,
            representative,
            &equality.dependencies,
        );
    }
    let mut domains = representatives
        .iter()
        .map(|value| (*value, NativeDataRange::all()))
        .collect::<BTreeMap<_, _>>();
    let mut domain_dependencies = representatives
        .iter()
        .map(|value| (*value, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    for constraint in &component.ranges {
        work.add(1)?;
        let representative = representative_by_variable[&constraint.variable];
        let base = compiled
            .compiled_ranges
            .get(&constraint.data_range_id)
            .ok_or_else(|| DatatypeError::invalid("compiled semantic range is absent"))?;
        let selected = if constraint.positive {
            base.clone()
        } else {
            base.complement(limits.range_wire, work.control)?
        };
        let current = domains
            .get(&representative)
            .ok_or_else(|| DatatypeError::invalid("semantic representative domain is absent"))?;
        let intersection = current.intersection(&selected, limits.range_wire, work.control)?;
        domains.insert(representative, intersection);
        extend_dependencies(
            &mut domain_dependencies,
            representative,
            &constraint.dependencies,
        );
    }
    let mut fixed: BTreeMap<u32, (DataIdentity, BTreeSet<u32>)> = BTreeMap::new();
    for constraint in &component.fixed_values {
        work.add(1)?;
        let representative = representative_by_variable[&constraint.variable];
        match fixed.get_mut(&representative) {
            None => {
                fixed.insert(
                    representative,
                    (
                        constraint.value.clone(),
                        dependency_levels(&constraint.dependencies),
                    ),
                );
            }
            Some((known, dependencies)) if known == &constraint.value => {
                dependencies.extend(constraint.dependencies.as_slice());
            }
            Some((_known, dependencies)) => {
                let levels = combined_levels([
                    &*dependencies,
                    &dependency_levels(&constraint.dependencies),
                    &equality_dependencies[&representative],
                ]);
                return Ok(Err(clash(
                    ClashKind::ConflictingFixedValues,
                    levels,
                    members[&representative].clone(),
                )?));
            }
        }
    }
    for representative in &representatives {
        work.add(1)?;
        let domain = &domains[representative];
        if domain.is_empty_exact(limits.range_wire, work.control)? {
            let levels = combined_levels([
                &domain_dependencies[representative],
                &equality_dependencies[representative],
            ]);
            return Ok(Err(clash(
                ClashKind::EmptyDomain,
                levels,
                members[representative].clone(),
            )?));
        }
        if let Some((value, fixed_dependencies)) = fixed.get(representative) {
            if !domain.contains(value, limits.range_wire, work.control)? {
                let levels = combined_levels([
                    fixed_dependencies,
                    &domain_dependencies[representative],
                    &equality_dependencies[representative],
                ]);
                return Ok(Err(clash(
                    ClashKind::FixedValueOutsideDomain,
                    levels,
                    members[representative].clone(),
                )?));
            }
        }
    }
    for constraint in &component.cardinalities {
        work.add(1)?;
        let representative = representative_by_variable[&constraint.variable];
        if !domains[&representative].cardinality_at_least(
            constraint.minimum,
            limits.range_wire,
            work.control,
        )? {
            let requirement = dependency_levels(&constraint.dependencies);
            let levels = combined_levels([
                &requirement,
                &domain_dependencies[&representative],
                &equality_dependencies[&representative],
            ]);
            return Ok(Err(clash(
                ClashKind::InsufficientCardinality,
                levels,
                members[&representative].clone(),
            )?));
        }
    }
    let mut adjacency = representatives
        .iter()
        .map(|value| (*value, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    let mut edge_dependencies: BTreeMap<(u32, u32), BTreeSet<u32>> = BTreeMap::new();
    for constraint in &component.inequalities {
        work.add(1)?;
        let left = representative_by_variable[&constraint.left];
        let right = representative_by_variable[&constraint.right];
        if left == right {
            let inequality = dependency_levels(&constraint.dependencies);
            let levels = combined_levels([&inequality, &equality_dependencies[&left]]);
            return Ok(Err(clash(
                ClashKind::EqualityInequality,
                levels,
                members[&left].clone(),
            )?));
        }
        adjacency
            .get_mut(&left)
            .ok_or_else(|| DatatypeError::invalid("left semantic adjacency is absent"))?
            .insert(right);
        adjacency
            .get_mut(&right)
            .ok_or_else(|| DatatypeError::invalid("right semantic adjacency is absent"))?
            .insert(left);
        let edge = if left < right {
            (left, right)
        } else {
            (right, left)
        };
        let levels = dependency_levels(&constraint.dependencies);
        match edge_dependencies.get_mut(&edge) {
            None => {
                edge_dependencies.insert(edge, levels);
            }
            Some(prior) if dependency_key(&levels) < dependency_key(prior) => *prior = levels,
            Some(_) => {}
        }
    }
    for ((left, right), edge_levels) in &edge_dependencies {
        if let (Some((first, first_levels)), Some((second, second_levels))) =
            (fixed.get(left), fixed.get(right))
        {
            if first == second {
                let levels = combined_levels([
                    edge_levels,
                    first_levels,
                    second_levels,
                    &equality_dependencies[left],
                    &equality_dependencies[right],
                ]);
                let mut variables = members[left].clone();
                variables.extend(&members[right]);
                return Ok(Err(clash(
                    ClashKind::UnsatisfiableInequalities,
                    levels,
                    variables,
                )?));
            }
        }
    }
    Ok(Ok(Prepared {
        variables: component.variables.clone(),
        representatives,
        representative_by_variable,
        members,
        equality_dependencies,
        domains,
        domain_dependencies,
        fixed,
        adjacency,
        edge_dependencies,
    }))
}

#[derive(Debug)]
struct SearchFrame {
    variable: u32,
    values: Vec<DataIdentity>,
    next_index: usize,
}

fn colour<C: DatatypeControl>(
    prepared: Prepared,
    limits: SemanticSolverLimits,
    work: &mut OperationWork<'_, C>,
    exhaustive: bool,
) -> Result<SemanticSolveResult, DatatypeError> {
    let fixed_values = prepared
        .fixed
        .iter()
        .map(|(variable, (value, _dependencies))| (*variable, value.clone()))
        .collect::<BTreeMap<_, _>>();
    let unfixed = prepared
        .representatives
        .iter()
        .filter(|representative| !fixed_values.contains_key(representative))
        .copied()
        .collect::<BTreeSet<_>>();
    let forbidden_by_fixed = unfixed
        .iter()
        .map(|variable| {
            let forbidden = prepared.adjacency[variable]
                .iter()
                .filter_map(|neighbour| fixed_values.get(neighbour))
                .cloned()
                .collect::<BTreeSet<_>>();
            (*variable, forbidden)
        })
        .collect::<BTreeMap<_, _>>();
    let mut active = unfixed;
    let mut eliminated = Vec::new();
    if !exhaustive {
        loop {
            let mut selected = None;
            for variable in &active {
                work.add(1)?;
                let degree = prepared.adjacency[variable]
                    .iter()
                    .filter(|neighbour| active.contains(neighbour))
                    .count();
                let required = u64::try_from(degree)
                    .unwrap_or(u64::MAX)
                    .checked_add(
                        u64::try_from(forbidden_by_fixed[variable].len()).unwrap_or(u64::MAX),
                    )
                    .and_then(|value| value.checked_add(1))
                    .ok_or_else(|| {
                        DatatypeError::invalid("semantic datatype elimination degree overflow")
                    })?;
                if prepared.domains[variable].cardinality_at_least(
                    required,
                    limits.range_wire,
                    work.control,
                )? {
                    selected = Some(*variable);
                    break;
                }
            }
            let Some(variable) = selected else {
                break;
            };
            active.remove(&variable);
            eliminated.push(variable);
        }
    }

    let mut candidates = BTreeMap::new();
    for variable in &active {
        work.add(1)?;
        if exhaustive
            && prepared.domains[variable].cardinality(limits.range_wire, work.control)?
                == Cardinality::Infinite
        {
            return Err(DatatypeError::invalid(
                "the exhaustive semantic datatype solver requires finite domains",
            ));
        }
        let available = prepared.domains[variable]
            .enumerate_identities(limits.range_wire, work.control)?
            .into_iter()
            .filter(|value| !forbidden_by_fixed[variable].contains(value))
            .collect::<Vec<_>>();
        if available.is_empty() {
            return search_clash(&prepared, &active);
        }
        candidates.insert(*variable, available);
    }
    let Some(colouring) = search_colouring(&candidates, &prepared.adjacency, work)? else {
        return search_clash(&prepared, &active);
    };
    let mut assignment = colouring
        .into_iter()
        .map(|(variable, value)| (variable, NativeDataWitness::Concrete(value)))
        .collect::<BTreeMap<_, _>>();
    assignment.extend(
        fixed_values
            .into_iter()
            .map(|(variable, value)| (variable, NativeDataWitness::Concrete(value))),
    );
    for variable in eliminated.into_iter().rev() {
        let forbidden = prepared.adjacency[&variable]
            .iter()
            .filter_map(|neighbour| assignment.get(neighbour))
            .cloned()
            .collect::<BTreeSet<_>>();
        let witness =
            prepared.domains[&variable].witness(&forbidden, limits.range_wire, work.control)?;
        work.add(1)?;
        assignment.insert(variable, witness);
    }
    let assignments = prepared
        .variables
        .iter()
        .map(|variable| {
            let representative = prepared.representative_by_variable[variable];
            assignment
                .get(&representative)
                .cloned()
                .map(|value| (*variable, value))
                .ok_or_else(|| DatatypeError::invalid("semantic solver assignment is incomplete"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SemanticSolveResult::satisfiable(assignments))
}

fn search_colouring<C: DatatypeControl>(
    candidates: &BTreeMap<u32, Vec<DataIdentity>>,
    adjacency: &BTreeMap<u32, BTreeSet<u32>>,
    work: &mut OperationWork<'_, C>,
) -> Result<Option<BTreeMap<u32, DataIdentity>>, DatatypeError> {
    let mut assignment: BTreeMap<u32, DataIdentity> = BTreeMap::new();
    let mut stack: Vec<SearchFrame> = Vec::new();
    while assignment.len() < candidates.len() {
        let unassigned = candidates
            .keys()
            .filter(|variable| !assignment.contains_key(variable))
            .copied()
            .collect::<BTreeSet<_>>();
        let available = unassigned
            .iter()
            .map(|variable| {
                let values = candidates[variable]
                    .iter()
                    .filter(|value| {
                        adjacency[variable]
                            .iter()
                            .all(|neighbour| assignment.get(neighbour) != Some(*value))
                    })
                    .cloned()
                    .collect::<Vec<_>>();
                (*variable, values)
            })
            .collect::<BTreeMap<_, _>>();
        let variable = unassigned
            .iter()
            .min_by_key(|variable| {
                (
                    available[variable].len(),
                    usize::MAX
                        - adjacency[variable]
                            .iter()
                            .filter(|neighbour| unassigned.contains(neighbour))
                            .count(),
                    **variable,
                )
            })
            .copied()
            .ok_or_else(|| DatatypeError::invalid("semantic solver lost an unassigned variable"))?;
        stack.push(SearchFrame {
            variable,
            values: available[&variable].clone(),
            next_index: 0,
        });
        if !advance_search(&mut stack, &mut assignment, adjacency, work)? {
            return Ok(None);
        }
    }
    Ok(Some(assignment))
}

fn advance_search<C: DatatypeControl>(
    stack: &mut Vec<SearchFrame>,
    assignment: &mut BTreeMap<u32, DataIdentity>,
    adjacency: &BTreeMap<u32, BTreeSet<u32>>,
    work: &mut OperationWork<'_, C>,
) -> Result<bool, DatatypeError> {
    while let Some(frame) = stack.last_mut() {
        assignment.remove(&frame.variable);
        while frame.next_index < frame.values.len() {
            let value = frame.values[frame.next_index].clone();
            frame.next_index = frame.next_index.saturating_add(1);
            work.add(1)?;
            if adjacency[&frame.variable]
                .iter()
                .all(|neighbour| assignment.get(neighbour) != Some(&value))
            {
                assignment.insert(frame.variable, value);
                return Ok(true);
            }
        }
        stack.pop();
    }
    Ok(false)
}

fn search_clash(
    prepared: &Prepared,
    active: &BTreeSet<u32>,
) -> Result<SemanticSolveResult, DatatypeError> {
    let mut levels = BTreeSet::new();
    let mut variables = Vec::new();
    for representative in active {
        variables.extend(&prepared.members[representative]);
        levels.extend(&prepared.domain_dependencies[representative]);
        levels.extend(&prepared.equality_dependencies[representative]);
        if let Some((_value, fixed_levels)) = prepared.fixed.get(representative) {
            levels.extend(fixed_levels);
        }
        for neighbour in &prepared.adjacency[representative] {
            if active.contains(neighbour) || prepared.fixed.contains_key(neighbour) {
                let edge = if representative < neighbour {
                    (*representative, *neighbour)
                } else {
                    (*neighbour, *representative)
                };
                levels.extend(&prepared.edge_dependencies[&edge]);
                if let Some((_value, fixed_levels)) = prepared.fixed.get(neighbour) {
                    levels.extend(fixed_levels);
                    levels.extend(&prepared.equality_dependencies[neighbour]);
                    variables.extend(&prepared.members[neighbour]);
                }
            }
        }
    }
    clash(ClashKind::UnsatisfiableInequalities, levels, variables)
}

fn clash(
    kind: ClashKind,
    levels: BTreeSet<u32>,
    mut variables: Vec<u32>,
) -> Result<SemanticSolveResult, DatatypeError> {
    variables.sort_unstable();
    variables.dedup();
    Ok(SemanticSolveResult::unsatisfiable(DatatypeClash {
        kind,
        dependencies: dependency_set(levels)?,
        variables,
    }))
}

fn dependency_levels(value: &DependencySet) -> BTreeSet<u32> {
    value.as_slice().iter().copied().collect()
}

fn dependency_set(levels: BTreeSet<u32>) -> Result<DependencySet, DatatypeError> {
    DependencySet::new(levels.into_iter().collect())
        .map_err(|error| DatatypeError::invalid(error.message))
}

fn extend_dependencies(
    values: &mut BTreeMap<u32, BTreeSet<u32>>,
    key: u32,
    dependencies: &DependencySet,
) {
    values
        .entry(key)
        .or_default()
        .extend(dependencies.as_slice());
}

fn combined_levels<'a>(values: impl IntoIterator<Item = &'a BTreeSet<u32>>) -> BTreeSet<u32> {
    values.into_iter().flatten().copied().collect()
}

fn dependency_key(value: &BTreeSet<u32>) -> (usize, Vec<u32>) {
    (value.len(), value.iter().copied().collect())
}

fn estimated_component_bytes(component: &SemanticDatatypeConstraintComponent) -> u64 {
    let fixed = u64::try_from(std::mem::size_of::<SemanticFixedValueConstraint>())
        .unwrap_or(u64::MAX)
        .saturating_mul(u64::try_from(component.fixed_values.len()).unwrap_or(u64::MAX));
    let ranges = u64::try_from(std::mem::size_of::<SemanticRangeConstraint>())
        .unwrap_or(u64::MAX)
        .saturating_mul(u64::try_from(component.ranges.len()).unwrap_or(u64::MAX));
    let equalities = u64::try_from(std::mem::size_of::<SemanticEqualityConstraint>())
        .unwrap_or(u64::MAX)
        .saturating_mul(u64::try_from(component.equalities.len()).unwrap_or(u64::MAX));
    let inequalities = u64::try_from(std::mem::size_of::<SemanticInequalityConstraint>())
        .unwrap_or(u64::MAX)
        .saturating_mul(u64::try_from(component.inequalities.len()).unwrap_or(u64::MAX));
    let cardinalities = u64::try_from(std::mem::size_of::<SemanticCardinalityConstraint>())
        .unwrap_or(u64::MAX)
        .saturating_mul(u64::try_from(component.cardinalities.len()).unwrap_or(u64::MAX));
    let variables = u64::try_from(component.variables.len())
        .unwrap_or(u64::MAX)
        .saturating_mul(u64::try_from(std::mem::size_of::<u32>()).unwrap_or(u64::MAX));
    let dependency_levels = component
        .ranges
        .iter()
        .map(|value| value.dependencies.as_slice().len())
        .chain(
            component
                .fixed_values
                .iter()
                .map(|value| value.dependencies.as_slice().len()),
        )
        .chain(
            component
                .equalities
                .iter()
                .map(|value| value.dependencies.as_slice().len()),
        )
        .chain(
            component
                .inequalities
                .iter()
                .map(|value| value.dependencies.as_slice().len()),
        )
        .chain(
            component
                .cardinalities
                .iter()
                .map(|value| value.dependencies.as_slice().len()),
        )
        .fold(0_u64, |total, value| {
            total.saturating_add(u64::try_from(value).unwrap_or(u64::MAX))
        })
        .saturating_mul(u64::try_from(std::mem::size_of::<u32>()).unwrap_or(u64::MAX));
    variables
        .saturating_add(ranges)
        .saturating_add(fixed)
        .saturating_add(equalities)
        .saturating_add(inequalities)
        .saturating_add(cardinalities)
        .saturating_add(dependency_levels)
}

#[cfg(test)]
#[path = "semantic_solver_tests.rs"]
mod tests;
