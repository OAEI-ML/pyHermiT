//! Exact finite/symbolic concrete-domain component solver.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};

use crate::model::DependencySet;

use super::{DataIdentity, DatatypeControl, DatatypeError};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DomainKind {
    /// The variable is restricted to exactly these concrete data identities.
    Finite(BTreeSet<DataIdentity>),
    /// These concrete identities are removed from the otherwise unbounded OWL data domain.
    ComplementFinite(BTreeSet<DataIdentity>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DomainConstraint {
    pub variable: u32,
    pub domain: DomainKind,
    pub dependencies: DependencySet,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FixedValueConstraint {
    pub variable: u32,
    pub value: DataIdentity,
    pub dependencies: DependencySet,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EqualityConstraint {
    pub left: u32,
    pub right: u32,
    pub dependencies: DependencySet,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InequalityConstraint {
    pub left: u32,
    pub right: u32,
    pub dependencies: DependencySet,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CardinalityConstraint {
    pub variable: u32,
    pub minimum: u32,
    pub dependencies: DependencySet,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConstraintComponent {
    pub variables: Vec<u32>,
    pub domains: Vec<DomainConstraint>,
    pub fixed_values: Vec<FixedValueConstraint>,
    pub equalities: Vec<EqualityConstraint>,
    pub inequalities: Vec<InequalityConstraint>,
    pub cardinalities: Vec<CardinalityConstraint>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SolverLimits {
    pub max_variables: u32,
    pub max_constraints: u32,
    pub max_steps: u64,
}

impl Default for SolverLimits {
    fn default() -> Self {
        Self {
            max_variables: 1_000_000,
            max_constraints: 5_000_000,
            max_steps: 1_000_000,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClashKind {
    EqualityInequality,
    ConflictingFixedValues,
    EmptyDomain,
    FixedValueOutsideDomain,
    InsufficientCardinality,
    UnsatisfiableInequalities,
}

impl ClashKind {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::EqualityInequality => "equality-inequality",
            Self::ConflictingFixedValues => "conflicting-fixed-values",
            Self::EmptyDomain => "empty-domain",
            Self::FixedValueOutsideDomain => "fixed-value-outside-domain",
            Self::InsufficientCardinality => "insufficient-cardinality",
            Self::UnsatisfiableInequalities => "unsatisfiable-inequalities",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DatatypeClash {
    pub kind: ClashKind,
    pub dependencies: DependencySet,
    pub variables: Vec<u32>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DatatypeWitness {
    Concrete(DataIdentity),
    /// A backend-private existential certificate. It is never converted to a public literal.
    Symbolic {
        representative: u32,
        ordinal: u32,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SolveResult {
    pub satisfiable: bool,
    pub assignments: Vec<(u32, DatatypeWitness)>,
    pub clash: Option<DatatypeClash>,
}

impl SolveResult {
    const fn satisfiable(assignments: Vec<(u32, DatatypeWitness)>) -> Self {
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

#[derive(Clone, Debug, Eq, PartialEq)]
enum Domain {
    Infinite { excluded: BTreeSet<DataIdentity> },
    Finite(BTreeSet<DataIdentity>),
}

impl Domain {
    const fn all() -> Self {
        Self::Infinite {
            excluded: BTreeSet::new(),
        }
    }

    fn intersect(&mut self, constraint: &DomainKind) {
        *self = match (&*self, constraint) {
            (Self::Infinite { excluded }, DomainKind::Finite(values)) => Self::Finite(
                values
                    .difference(excluded)
                    .cloned()
                    .collect::<BTreeSet<_>>(),
            ),
            (Self::Infinite { excluded }, DomainKind::ComplementFinite(values)) => {
                let mut result = excluded.clone();
                result.extend(values.iter().cloned());
                Self::Infinite { excluded: result }
            }
            (Self::Finite(current), DomainKind::Finite(values)) => Self::Finite(
                current
                    .intersection(values)
                    .cloned()
                    .collect::<BTreeSet<_>>(),
            ),
            (Self::Finite(current), DomainKind::ComplementFinite(values)) => {
                Self::Finite(current.difference(values).cloned().collect::<BTreeSet<_>>())
            }
        };
    }

    fn contains(&self, value: &DataIdentity) -> bool {
        match self {
            Self::Infinite { excluded } => !excluded.contains(value),
            Self::Finite(values) => values.contains(value),
        }
    }

    fn cardinality_at_least(&self, minimum: u64) -> bool {
        match self {
            Self::Infinite { .. } => true,
            Self::Finite(values) => u64::try_from(values.len()).unwrap_or(u64::MAX) >= minimum,
        }
    }

    fn is_empty(&self) -> bool {
        matches!(self, Self::Finite(values) if values.is_empty())
    }
}

#[derive(Debug)]
struct Work<'a, C> {
    steps: u64,
    limits: SolverLimits,
    control: &'a C,
}

impl<C: DatatypeControl> Work<'_, C> {
    fn add(&mut self, amount: u64) -> Result<(), DatatypeError> {
        self.steps = self
            .steps
            .checked_add(amount)
            .ok_or_else(|| DatatypeError::invalid("datatype solver step counter overflow"))?;
        if self.steps > self.limits.max_steps {
            return Err(DatatypeError::resource(
                "max_solver_steps",
                self.steps,
                self.limits.max_steps,
            ));
        }
        if self.steps == amount || self.steps % 64 == 0 {
            self.control.poll()?;
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
            let parent = self
                .parent
                .get(&root)
                .copied()
                .ok_or_else(|| DatatypeError::invalid("union-find variable is absent"))?;
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
                .ok_or_else(|| DatatypeError::invalid("union-find path is absent"))?;
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
    domains: BTreeMap<u32, Domain>,
    domain_dependencies: BTreeMap<u32, BTreeSet<u32>>,
    fixed: BTreeMap<u32, (DataIdentity, BTreeSet<u32>)>,
    adjacency: BTreeMap<u32, BTreeSet<u32>>,
    edge_dependencies: BTreeMap<(u32, u32), BTreeSet<u32>>,
}

pub fn solve_component(
    component: &ConstraintComponent,
    limits: SolverLimits,
    control: &impl DatatypeControl,
) -> Result<SolveResult, DatatypeError> {
    validate_component(component, limits)?;
    let mut work = Work {
        steps: 0,
        limits,
        control,
    };
    control.poll()?;
    match prepare(component, &mut work)? {
        Ok(prepared) => colour(prepared, &mut work),
        Err(result) => Ok(result),
    }
}

fn validate_component(
    component: &ConstraintComponent,
    limits: SolverLimits,
) -> Result<(), DatatypeError> {
    if component.variables.is_empty() {
        return Err(DatatypeError::invalid(
            "datatype components require at least one variable",
        ));
    }
    if component.variables.len() > usize::try_from(limits.max_variables).unwrap_or(usize::MAX) {
        return Err(DatatypeError::resource(
            "max_variables",
            u64::try_from(component.variables.len()).unwrap_or(u64::MAX),
            u64::from(limits.max_variables),
        ));
    }
    if component
        .variables
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(DatatypeError::invalid(
            "datatype component variables must be sorted and unique",
        ));
    }
    let constraint_count = component
        .domains
        .len()
        .checked_add(component.fixed_values.len())
        .and_then(|value| value.checked_add(component.equalities.len()))
        .and_then(|value| value.checked_add(component.inequalities.len()))
        .and_then(|value| value.checked_add(component.cardinalities.len()))
        .ok_or_else(|| DatatypeError::invalid("datatype constraint count overflow"))?;
    if constraint_count > usize::try_from(limits.max_constraints).unwrap_or(usize::MAX) {
        return Err(DatatypeError::resource(
            "max_constraints",
            u64::try_from(constraint_count).unwrap_or(u64::MAX),
            u64::from(limits.max_constraints),
        ));
    }
    let known: BTreeSet<_> = component.variables.iter().copied().collect();
    let unary = component
        .domains
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
            "datatype constraint references a variable outside its component",
        ));
    }
    Ok(())
}

fn prepare<C: DatatypeControl>(
    component: &ConstraintComponent,
    work: &mut Work<'_, C>,
) -> Result<Result<Prepared, SolveResult>, DatatypeError> {
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
        .map(|value| (*value, Domain::all()))
        .collect::<BTreeMap<_, _>>();
    let mut domain_dependencies = representatives
        .iter()
        .map(|value| (*value, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    for constraint in &component.domains {
        work.add(1)?;
        let representative = representative_by_variable[&constraint.variable];
        domains
            .get_mut(&representative)
            .ok_or_else(|| DatatypeError::invalid("representative domain is absent"))?
            .intersect(&constraint.domain);
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
                let mut levels = dependencies.clone();
                levels.extend(constraint.dependencies.as_slice());
                levels.extend(&equality_dependencies[&representative]);
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
        if domain.is_empty() {
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
            if !domain.contains(value) {
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
        if !domains[&representative].cardinality_at_least(u64::from(constraint.minimum)) {
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
            let levels = combined_levels([
                &dependency_levels(&constraint.dependencies),
                &equality_dependencies[&left],
            ]);
            return Ok(Err(clash(
                ClashKind::EqualityInequality,
                levels,
                members[&left].clone(),
            )?));
        }
        adjacency
            .get_mut(&left)
            .ok_or_else(|| DatatypeError::invalid("left adjacency is absent"))?
            .insert(right);
        adjacency
            .get_mut(&right)
            .ok_or_else(|| DatatypeError::invalid("right adjacency is absent"))?
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
                variables.sort_unstable();
                variables.dedup();
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
    work: &mut Work<'_, C>,
) -> Result<SolveResult, DatatypeError> {
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
                .checked_add(u64::try_from(forbidden_by_fixed[variable].len()).unwrap_or(u64::MAX))
                .and_then(|value| value.checked_add(1))
                .ok_or_else(|| DatatypeError::invalid("datatype elimination degree overflow"))?;
            if prepared.domains[variable].cardinality_at_least(required) {
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

    let mut candidates = BTreeMap::new();
    for variable in &active {
        work.add(1)?;
        let Domain::Finite(values) = &prepared.domains[variable] else {
            return Err(DatatypeError::invalid(
                "a non-eliminable inequality variable has an infinite domain",
            ));
        };
        let available = values
            .iter()
            .filter(|value| !forbidden_by_fixed[variable].contains(value))
            .cloned()
            .collect::<Vec<_>>();
        if available.is_empty() {
            return search_clash(&prepared, &active);
        }
        candidates.insert(*variable, available);
    }
    let Some(mut assignment) = search_colouring(&candidates, &prepared.adjacency, work)? else {
        return search_clash(&prepared, &active);
    };
    assignment.extend(
        fixed_values
            .into_iter()
            .map(|(variable, value)| (variable, DatatypeWitness::Concrete(value))),
    );
    for variable in eliminated.into_iter().rev() {
        let forbidden = prepared.adjacency[&variable]
            .iter()
            .filter_map(|neighbour| assignment.get(neighbour))
            .cloned()
            .collect::<BTreeSet<_>>();
        let witness = eliminated_witness(variable, &prepared.domains[&variable], &forbidden)?;
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
                .ok_or_else(|| DatatypeError::invalid("solver assignment is incomplete"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SolveResult::satisfiable(assignments))
}

fn eliminated_witness(
    representative: u32,
    domain: &Domain,
    forbidden: &BTreeSet<DatatypeWitness>,
) -> Result<DatatypeWitness, DatatypeError> {
    match domain {
        Domain::Finite(values) => values
            .iter()
            .map(|value| DatatypeWitness::Concrete(value.clone()))
            .find(|value| !forbidden.contains(value))
            .ok_or_else(|| {
                DatatypeError::invalid(
                    "sound datatype elimination failed to produce a finite witness",
                )
            }),
        Domain::Infinite { .. } => {
            let witness = DatatypeWitness::Symbolic {
                representative,
                ordinal: 0,
            };
            if forbidden.contains(&witness) {
                return Err(DatatypeError::invalid(
                    "symbolic datatype witness unexpectedly collides with a neighbour",
                ));
            }
            Ok(witness)
        }
    }
}

fn search_colouring<C: DatatypeControl>(
    candidates: &BTreeMap<u32, Vec<DataIdentity>>,
    adjacency: &BTreeMap<u32, BTreeSet<u32>>,
    work: &mut Work<'_, C>,
) -> Result<Option<BTreeMap<u32, DatatypeWitness>>, DatatypeError> {
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
            .ok_or_else(|| DatatypeError::invalid("solver lost an unassigned variable"))?;
        stack.push(SearchFrame {
            variable,
            values: available[&variable].clone(),
            next_index: 0,
        });
        if !advance_search(&mut stack, &mut assignment, adjacency, work)? {
            return Ok(None);
        }
    }
    Ok(Some(
        assignment
            .into_iter()
            .map(|(variable, value)| (variable, DatatypeWitness::Concrete(value)))
            .collect(),
    ))
}

fn advance_search<C: DatatypeControl>(
    stack: &mut Vec<SearchFrame>,
    assignment: &mut BTreeMap<u32, DataIdentity>,
    adjacency: &BTreeMap<u32, BTreeSet<u32>>,
    work: &mut Work<'_, C>,
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

fn search_clash(prepared: &Prepared, active: &BTreeSet<u32>) -> Result<SolveResult, DatatypeError> {
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
    variables.sort_unstable();
    variables.dedup();
    clash(ClashKind::UnsatisfiableInequalities, levels, variables)
}

fn clash(
    kind: ClashKind,
    levels: BTreeSet<u32>,
    mut variables: Vec<u32>,
) -> Result<SolveResult, DatatypeError> {
    variables.sort_unstable();
    variables.dedup();
    Ok(SolveResult::unsatisfiable(DatatypeClash {
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
