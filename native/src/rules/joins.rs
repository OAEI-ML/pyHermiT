//! Indexed semi-naive joins and an intentionally index-independent oracle.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::cancel::CancellationState;
use crate::error::{ErrorKind, NativeError, NativeResult};
use crate::model::{DependencySet, NodeHandle};
use crate::store::TableauKernel;

use super::model::{
    JoinMatch, PredicateKind, RuleAtom, RuleClause, RuleLimits, RuleProgram, Term, TermSort,
    VariableBinding,
};
use super::plans::ClauseJoinPlan;

type BindingKey = (TermSort, u32);
type Bindings = BTreeMap<BindingKey, NodeHandle>;
type MatchKey = (Vec<VariableBinding>, Vec<u32>);

#[derive(Clone, Debug)]
struct FactCandidate {
    row_id: u32,
    handles: Vec<NodeHandle>,
    lookup_dependency: DependencySet,
}

/// Execute compiled plans against the kernel's predicate/position indexes.
pub struct IndexedJoinEvaluator<'a> {
    program: &'a RuleProgram,
    kernel: &'a TableauKernel,
    source_nodes: Arc<BTreeMap<u32, NodeHandle>>,
    data_nodes: Arc<BTreeMap<u32, NodeHandle>>,
    cancellation: Arc<CancellationState>,
    limits: RuleLimits,
    steps: u64,
    poll_work: u64,
    matches_emitted: u64,
}

impl<'a> IndexedJoinEvaluator<'a> {
    pub fn new(
        program: &'a RuleProgram,
        kernel: &'a TableauKernel,
        source_nodes: BTreeMap<u32, NodeHandle>,
        data_nodes: BTreeMap<u32, NodeHandle>,
        cancellation: Arc<CancellationState>,
        limits: RuleLimits,
    ) -> NativeResult<Self> {
        let source_nodes = Arc::new(source_nodes);
        let data_nodes = Arc::new(data_nodes);
        Self::validate_node_maps(kernel, &source_nodes, &data_nodes)?;
        Self::from_prevalidated_maps(
            program,
            kernel,
            source_nodes,
            data_nodes,
            cancellation,
            limits,
        )
    }

    pub(crate) fn from_prevalidated_maps(
        program: &'a RuleProgram,
        kernel: &'a TableauKernel,
        source_nodes: Arc<BTreeMap<u32, NodeHandle>>,
        data_nodes: Arc<BTreeMap<u32, NodeHandle>>,
        cancellation: Arc<CancellationState>,
        limits: RuleLimits,
    ) -> NativeResult<Self> {
        cancellation.poll()?;
        Ok(Self {
            program,
            kernel,
            source_nodes,
            data_nodes,
            cancellation,
            limits,
            steps: 0,
            poll_work: 0,
            matches_emitted: 0,
        })
    }

    pub(crate) fn validate_node_maps(
        kernel: &TableauKernel,
        source_nodes: &BTreeMap<u32, NodeHandle>,
        data_nodes: &BTreeMap<u32, NodeHandle>,
    ) -> NativeResult<()> {
        for handle in source_nodes.values() {
            let (canonical, _dependency) = kernel.canonical_handle(*handle)?;
            if kernel.node_sort(canonical)? != TermSort::Object.node_sort() {
                return Err(NativeError::wire(
                    "source individual map contains a non-object node",
                ));
            }
        }
        for handle in data_nodes.values() {
            let (canonical, _dependency) = kernel.canonical_handle(*handle)?;
            if kernel.node_sort(canonical)? != TermSort::Data.node_sort() {
                return Err(NativeError::wire(
                    "data identity map contains a non-data node",
                ));
            }
        }
        Ok(())
    }

    #[must_use]
    pub const fn steps(&self) -> u64 {
        self.steps
    }

    #[must_use]
    pub const fn matches_emitted(&self) -> u64 {
        self.matches_emitted
    }

    /// Match one physical row as the plan's designated current-generation atom.
    pub fn matches(
        &mut self,
        plan: &ClauseJoinPlan,
        delta_row_id: u32,
    ) -> NativeResult<Vec<JoinMatch>> {
        self.cancellation.poll()?;
        self.validate_plan(plan)?;
        let clause = self.program.clause(plan.clause_id)?.clone();
        let trigger = clause
            .body
            .get(usize_from_u32(plan.delta_body_index, "delta body index")?)
            .ok_or_else(|| NativeError::wire("delta body index is out of bounds"))?
            .clone();
        let delta_row = self.kernel.fact(delta_row_id)?.clone();
        if !delta_row.active
            || delta_row.derivation_generation != self.kernel.read_generation()
            || delta_row.key.predicate_id != trigger.predicate_id
        {
            return Ok(Vec::new());
        }
        let Some((bindings, seed_dependency)) =
            self.unify_handles(&trigger, &delta_row.key.arguments, &Bindings::new())?
        else {
            return Ok(Vec::new());
        };
        if delta_row.supports.is_empty() {
            return Err(NativeError::invariant(
                "active delta fact row has no dependency support",
            ));
        }
        let mut found = BTreeMap::new();
        for support in delta_row.supports {
            self.poll_inner()?;
            let dependency = DependencySet::union(&[&seed_dependency, &support]);
            self.join_steps(
                plan,
                &clause,
                0,
                bindings.clone(),
                dependency,
                vec![delta_row_id],
                &mut found,
            )?;
        }
        self.cancellation.poll()?;
        Ok(found.into_values().collect())
    }

    #[allow(clippy::too_many_arguments)]
    fn join_steps(
        &mut self,
        plan: &ClauseJoinPlan,
        clause: &RuleClause,
        step_index: usize,
        bindings: Bindings,
        dependency: DependencySet,
        row_ids: Vec<u32>,
        found: &mut BTreeMap<MatchKey, JoinMatch>,
    ) -> NativeResult<()> {
        self.tick_join()?;
        if step_index == plan.steps.len() {
            let candidate = JoinMatch::new(
                plan.clause_id,
                plan.delta_body_index,
                freeze_bindings(&bindings),
                dependency,
                row_ids,
            )?;
            return self.insert_match(found, candidate);
        }
        let body_index = plan.steps[step_index].body_index;
        let atom = clause
            .body
            .get(usize_from_u32(body_index, "join body index")?)
            .ok_or_else(|| NativeError::wire("join body index is out of bounds"))?
            .clone();
        let kind = self.program.predicate_kind(atom.predicate_id)?;
        if kind == PredicateKind::OrderingGuard {
            if let Some((next_bindings, guard_dependency)) =
                self.ordering_guard(&atom, &bindings)?
            {
                let next_dependency = DependencySet::union(&[&dependency, &guard_dependency]);
                self.join_steps(
                    plan,
                    clause,
                    step_index + 1,
                    next_bindings,
                    next_dependency,
                    row_ids,
                    found,
                )?;
            }
            return Ok(());
        }
        if kind == PredicateKind::Equality {
            for (next_bindings, equality_dependency) in
                self.equality_candidates(&atom, &bindings)?
            {
                self.poll_inner()?;
                let next_dependency = DependencySet::union(&[&dependency, &equality_dependency]);
                self.join_steps(
                    plan,
                    clause,
                    step_index + 1,
                    next_bindings,
                    next_dependency,
                    row_ids.clone(),
                    found,
                )?;
            }
            return Ok(());
        }
        let candidates = if kind == PredicateKind::Inequality {
            self.inequality_candidates(&atom, &bindings, plan, body_index)?
        } else {
            self.relation_candidates(&atom, &bindings, plan, body_index)?
        };
        for candidate in candidates {
            self.poll_inner()?;
            let Some((next_bindings, unification_dependency)) =
                self.unify_handles(&atom, &candidate.handles, &bindings)?
            else {
                continue;
            };
            let row = self.kernel.fact(candidate.row_id)?.clone();
            if row.supports.is_empty() {
                return Err(NativeError::invariant(
                    "active fact row has no dependency support",
                ));
            }
            for support in row.supports {
                self.poll_inner()?;
                let next_dependency = DependencySet::union(&[
                    &dependency,
                    &candidate.lookup_dependency,
                    &unification_dependency,
                    &support,
                ]);
                let mut next_rows = row_ids.clone();
                next_rows.push(candidate.row_id);
                self.join_steps(
                    plan,
                    clause,
                    step_index + 1,
                    next_bindings.clone(),
                    next_dependency,
                    next_rows,
                    found,
                )?;
            }
        }
        Ok(())
    }

    fn relation_candidates(
        &mut self,
        atom: &RuleAtom,
        bindings: &Bindings,
        plan: &ClauseJoinPlan,
        body_index: u32,
    ) -> NativeResult<Vec<FactCandidate>> {
        let (lookup, lookup_dependency) = self.lookup_bindings(atom, bindings)?;
        let row_ids = self.kernel.candidate_fact_ids(atom.predicate_id, &lookup)?;
        let mut result = Vec::new();
        for row_id in row_ids {
            self.poll_inner()?;
            let row = self.kernel.fact(row_id)?;
            if self.in_plan_view(row.derivation_generation, plan, body_index) {
                result.push(FactCandidate {
                    row_id,
                    handles: row.key.arguments.clone(),
                    lookup_dependency: lookup_dependency.clone(),
                });
            }
        }
        Ok(result)
    }

    fn inequality_candidates(
        &mut self,
        atom: &RuleAtom,
        bindings: &Bindings,
        plan: &ClauseJoinPlan,
        body_index: u32,
    ) -> NativeResult<Vec<FactCandidate>> {
        let resolved = atom
            .arguments
            .iter()
            .map(|term| self.resolved_term(term, bindings))
            .collect::<NativeResult<Vec<_>>>()?;
        let dependencies: Vec<_> = resolved
            .iter()
            .filter_map(|value| value.as_ref().map(|(_handle, dependency)| dependency))
            .collect();
        let dependency = DependencySet::union(&dependencies);
        let known: Vec<_> = resolved
            .iter()
            .enumerate()
            .filter_map(|(index, value)| value.as_ref().map(|_| index))
            .collect();
        let queries = match known.as_slice() {
            [0, 1] => {
                let left = resolved[0]
                    .as_ref()
                    .ok_or_else(|| {
                        NativeError::invariant("resolved inequality lost its left term")
                    })?
                    .0;
                let right = resolved[1]
                    .as_ref()
                    .ok_or_else(|| {
                        NativeError::invariant("resolved inequality lost its right term")
                    })?
                    .0;
                let (first, second) =
                    if self.kernel.node_rank(left)? <= self.kernel.node_rank(right)? {
                        (left, right)
                    } else {
                        (right, left)
                    };
                vec![BTreeMap::from([(0, first), (1, second)])]
            }
            [_one] => {
                let handle = resolved[known[0]]
                    .as_ref()
                    .ok_or_else(|| NativeError::invariant("resolved inequality term disappeared"))?
                    .0;
                vec![BTreeMap::from([(0, handle)]), BTreeMap::from([(1, handle)])]
            }
            [] => vec![BTreeMap::new()],
            _ => {
                return Err(NativeError::invariant(
                    "inequality predicate does not have binary arity",
                ));
            }
        };
        let mut row_ids = BTreeSet::new();
        for query in queries {
            for row_id in self.kernel.candidate_fact_ids(atom.predicate_id, &query)? {
                self.poll_inner()?;
                let row = self.kernel.fact(row_id)?;
                if self.in_plan_view(row.derivation_generation, plan, body_index) {
                    row_ids.insert(row_id);
                }
            }
        }
        let mut result = Vec::new();
        for row_id in row_ids {
            let row = self.kernel.fact(row_id)?;
            let mut orientations = BTreeSet::new();
            orientations.insert(row.key.arguments.clone());
            orientations.insert(row.key.arguments.iter().rev().copied().collect());
            for handles in orientations {
                self.poll_inner()?;
                if self.unify_handles(atom, &handles, bindings)?.is_some() {
                    result.push(FactCandidate {
                        row_id,
                        handles,
                        lookup_dependency: dependency.clone(),
                    });
                }
            }
        }
        Ok(result)
    }

    fn equality_candidates(
        &mut self,
        atom: &RuleAtom,
        bindings: &Bindings,
    ) -> NativeResult<Vec<(Bindings, DependencySet)>> {
        let left = self.resolved_term(&atom.arguments[0], bindings)?;
        let right = self.resolved_term(&atom.arguments[1], bindings)?;
        match (left, right) {
            (Some(left), Some(right)) => {
                if left.0 != right.0 {
                    return Ok(Vec::new());
                }
                Ok(vec![(
                    bindings.clone(),
                    DependencySet::union(&[&left.1, &right.1]),
                )])
            }
            (Some((handle, dependency)), None) => Ok(self
                .bind_unresolved(&atom.arguments[1], handle, bindings)?
                .map(|next| vec![(next, dependency)])
                .unwrap_or_default()),
            (None, Some((handle, dependency))) => Ok(self
                .bind_unresolved(&atom.arguments[0], handle, bindings)?
                .map(|next| vec![(next, dependency)])
                .unwrap_or_default()),
            (None, None) => {
                let (first_sort, first_id) = atom.arguments[0].variable_key().ok_or_else(|| {
                    NativeError::invariant(
                        "unresolved equality constants are absent from node maps",
                    )
                })?;
                let (_second_sort, second_id) =
                    atom.arguments[1].variable_key().ok_or_else(|| {
                        NativeError::invariant(
                            "unresolved equality constants are absent from node maps",
                        )
                    })?;
                let mut result = Vec::new();
                for handle in self.kernel.active_node_handles() {
                    self.poll_inner()?;
                    if self.kernel.node_sort(handle)? != first_sort.node_sort() {
                        continue;
                    }
                    let mut candidate = bindings.clone();
                    candidate.insert((first_sort, first_id), handle);
                    candidate.insert((first_sort, second_id), handle);
                    result.push((candidate, DependencySet::empty()));
                }
                Ok(result)
            }
        }
    }

    fn ordering_guard(
        &self,
        atom: &RuleAtom,
        bindings: &Bindings,
    ) -> NativeResult<Option<(Bindings, DependencySet)>> {
        let left = self
            .resolved_term(&atom.arguments[0], bindings)?
            .ok_or_else(|| {
                NativeError::invariant("ordering guard was scheduled before its variables bound")
            })?;
        let right = self
            .resolved_term(&atom.arguments[1], bindings)?
            .ok_or_else(|| {
                NativeError::invariant("ordering guard was scheduled before its variables bound")
            })?;
        if self.kernel.node_rank(left.0)? >= self.kernel.node_rank(right.0)? {
            return Ok(None);
        }
        Ok(Some((
            bindings.clone(),
            DependencySet::union(&[&left.1, &right.1]),
        )))
    }

    fn lookup_bindings(
        &self,
        atom: &RuleAtom,
        bindings: &Bindings,
    ) -> NativeResult<(BTreeMap<u32, NodeHandle>, DependencySet)> {
        let mut result = BTreeMap::new();
        let mut dependencies = Vec::new();
        for (position, argument) in atom.arguments.iter().enumerate() {
            if let Some((handle, dependency)) = self.resolved_term(argument, bindings)? {
                result.insert(
                    u32::try_from(position)
                        .map_err(|_| NativeError::wire("atom position exceeds the u32 IR limit"))?,
                    handle,
                );
                dependencies.push(dependency);
            }
        }
        let refs: Vec<_> = dependencies.iter().collect();
        Ok((result, DependencySet::union(&refs)))
    }

    fn unify_handles(
        &self,
        atom: &RuleAtom,
        handles: &[NodeHandle],
        bindings: &Bindings,
    ) -> NativeResult<Option<(Bindings, DependencySet)>> {
        if atom.arguments.len() != handles.len() {
            return Ok(None);
        }
        let mut result = bindings.clone();
        let mut dependencies = Vec::new();
        for (term, raw_handle) in atom.arguments.iter().zip(handles) {
            let (representative, path) = self.kernel.canonical_handle(*raw_handle)?;
            if self.kernel.node_sort(representative)? != term.sort().node_sort() {
                return Ok(None);
            }
            dependencies.push(path);
            if let Some(key) = term.variable_key() {
                if result
                    .get(&key)
                    .is_some_and(|known| *known != representative)
                {
                    return Ok(None);
                }
                result.insert(key, representative);
            } else {
                let (expected, constant_dependency) = self.resolved_constant(term)?;
                dependencies.push(constant_dependency);
                if expected != representative {
                    return Ok(None);
                }
            }
        }
        let refs: Vec<_> = dependencies.iter().collect();
        Ok(Some((result, DependencySet::union(&refs))))
    }

    fn resolved_term(
        &self,
        term: &Term,
        bindings: &Bindings,
    ) -> NativeResult<Option<(NodeHandle, DependencySet)>> {
        if let Some(key) = term.variable_key() {
            let Some(handle) = bindings.get(&key) else {
                return Ok(None);
            };
            return self.kernel.canonical_handle(*handle).map(Some);
        }
        self.resolved_constant(term).map(Some)
    }

    fn resolved_constant(&self, term: &Term) -> NativeResult<(NodeHandle, DependencySet)> {
        let (handle, name) = match term {
            Term::Individual { individual_id } => (
                self.source_nodes.get(individual_id).copied(),
                format!("individual ID {individual_id}"),
            ),
            Term::DataConstant {
                data_identity_id, ..
            } => (
                self.data_nodes.get(data_identity_id).copied(),
                format!("data identity ID {data_identity_id}"),
            ),
            Term::Variable { .. } => {
                return Err(NativeError::invariant(
                    "unbound variables cannot resolve as constants",
                ));
            }
        };
        let handle = handle.ok_or_else(|| {
            NativeError::invariant(format!("compiled {name} has no tableau node"))
        })?;
        let (representative, dependency) = self.kernel.canonical_handle(handle)?;
        if self.kernel.node_sort(representative)? != term.sort().node_sort() {
            return Err(NativeError::invariant(format!(
                "compiled {name} maps to the wrong node sort"
            )));
        }
        Ok((representative, dependency))
    }

    fn bind_unresolved(
        &self,
        term: &Term,
        handle: NodeHandle,
        bindings: &Bindings,
    ) -> NativeResult<Option<Bindings>> {
        let Some(key) = term.variable_key() else {
            return Ok(None);
        };
        if self.kernel.node_sort(handle)? != key.0.node_sort() {
            return Ok(None);
        }
        let mut result = bindings.clone();
        result.insert(key, handle);
        Ok(Some(result))
    }

    const fn in_plan_view(
        &self,
        derivation_generation: u32,
        plan: &ClauseJoinPlan,
        body_index: u32,
    ) -> bool {
        let generation = self.kernel.read_generation();
        if body_index < plan.delta_body_index {
            derivation_generation < generation
        } else {
            derivation_generation <= generation
        }
    }

    fn validate_plan(&self, plan: &ClauseJoinPlan) -> NativeResult<()> {
        let clause = self.program.clause(plan.clause_id)?;
        let delta_index = usize_from_u32(plan.delta_body_index, "delta body index")?;
        let trigger = clause
            .body
            .get(delta_index)
            .ok_or_else(|| NativeError::wire("delta body index is out of bounds"))?;
        if !self
            .program
            .predicate_kind(trigger.predicate_id)?
            .can_trigger()
        {
            return Err(NativeError::wire(
                "ordering guards cannot designate a delta atom",
            ));
        }
        if plan.steps.len().checked_add(1) != Some(clause.body.len()) {
            return Err(NativeError::wire(
                "join plan must cover every body atom exactly once",
            ));
        }
        let mut indices = BTreeSet::from([plan.delta_body_index]);
        for step in &plan.steps {
            if !indices.insert(step.body_index)
                || usize_from_u32(step.body_index, "join body index")? >= clause.body.len()
            {
                return Err(NativeError::wire(
                    "join plan contains a duplicate or dangling body index",
                ));
            }
        }
        Ok(())
    }

    fn tick_join(&mut self) -> NativeResult<()> {
        self.steps = self
            .steps
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("join-step counter overflow"))?;
        if self.steps > self.limits.max_join_steps {
            return Err(resource_limit(
                "hyperresolution join-step limit exceeded",
                "max_join_steps",
                self.steps,
                self.limits.max_join_steps,
            ));
        }
        self.poll_inner()
    }

    fn poll_inner(&mut self) -> NativeResult<()> {
        self.poll_work = self
            .poll_work
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("join poll counter overflow"))?;
        if self.poll_work % self.limits.cancellation_interval == 0 {
            self.cancellation.poll()?;
        }
        Ok(())
    }

    fn insert_match(
        &mut self,
        found: &mut BTreeMap<MatchKey, JoinMatch>,
        candidate: JoinMatch,
    ) -> NativeResult<()> {
        let key = (
            candidate.bindings.clone(),
            candidate
                .dependency
                .as_slice()
                .iter()
                .rev()
                .copied()
                .collect(),
        );
        if let Some(previous) = found.get_mut(&key) {
            if candidate.premise_row_ids < previous.premise_row_ids {
                *previous = candidate;
            }
        } else {
            let observed = self
                .matches_emitted
                .checked_add(1)
                .ok_or_else(|| NativeError::invariant("join-match counter overflow"))?;
            if observed > self.limits.max_matches_per_generation {
                return Err(resource_limit(
                    "hyperresolution match limit exceeded",
                    "max_matches_per_generation",
                    observed,
                    self.limits.max_matches_per_generation,
                ));
            }
            self.matches_emitted = observed;
            found.insert(key, candidate);
        }
        Ok(())
    }
}

/// Slow complete substitution oracle that never consults predicate/position indexes.
pub struct NaiveJoinEvaluator<'e, 'a> {
    indexed: &'e mut IndexedJoinEvaluator<'a>,
}

impl<'e, 'a> NaiveJoinEvaluator<'e, 'a> {
    #[must_use]
    pub const fn new(indexed: &'e mut IndexedJoinEvaluator<'a>) -> Self {
        Self { indexed }
    }

    pub fn matches(&mut self, clause_id: u32, require_new: bool) -> NativeResult<Vec<JoinMatch>> {
        self.indexed.cancellation.poll()?;
        let clause = self.indexed.program.clause(clause_id)?.clone();
        let variables: Vec<_> = clause
            .body
            .iter()
            .flat_map(|atom| atom.arguments.iter().filter_map(Term::variable_key))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let mut domains = Vec::new();
        for (sort, _variable_id) in &variables {
            let mut domain = Vec::new();
            for handle in self.indexed.kernel.active_node_handles() {
                self.indexed.poll_inner()?;
                if self.indexed.kernel.node_sort(handle)? == sort.node_sort() {
                    domain.push(handle);
                }
            }
            domains.push(domain);
        }
        let mut found = BTreeMap::new();
        self.enumerate_assignments(
            &clause,
            &variables,
            &domains,
            0,
            &mut Bindings::new(),
            require_new,
            &mut found,
        )?;
        self.indexed.cancellation.poll()?;
        Ok(found.into_values().collect())
    }

    #[allow(clippy::too_many_arguments)]
    fn enumerate_assignments(
        &mut self,
        clause: &RuleClause,
        variables: &[BindingKey],
        domains: &[Vec<NodeHandle>],
        index: usize,
        bindings: &mut Bindings,
        require_new: bool,
        found: &mut BTreeMap<MatchKey, JoinMatch>,
    ) -> NativeResult<()> {
        self.indexed.tick_join()?;
        if index == variables.len() {
            return self.evaluate_assignment(clause, bindings, require_new, found);
        }
        for handle in &domains[index] {
            self.indexed.poll_inner()?;
            bindings.insert(variables[index], *handle);
            self.enumerate_assignments(
                clause,
                variables,
                domains,
                index + 1,
                bindings,
                require_new,
                found,
            )?;
        }
        bindings.remove(&variables[index]);
        Ok(())
    }

    fn evaluate_assignment(
        &mut self,
        clause: &RuleClause,
        bindings: &Bindings,
        require_new: bool,
        found: &mut BTreeMap<MatchKey, JoinMatch>,
    ) -> NativeResult<()> {
        let mut rows_by_atom: Vec<Vec<Option<u32>>> = Vec::new();
        let mut virtual_dependencies = Vec::new();
        for atom in &clause.body {
            let kind = self.indexed.program.predicate_kind(atom.predicate_id)?;
            if kind == PredicateKind::OrderingGuard {
                let Some((_bindings, dependency)) = self.indexed.ordering_guard(atom, bindings)?
                else {
                    return Ok(());
                };
                virtual_dependencies.push(dependency);
                rows_by_atom.push(vec![None]);
                continue;
            }
            if kind == PredicateKind::Equality {
                let equality = self.indexed.equality_candidates(atom, bindings)?;
                if equality.is_empty() {
                    return Ok(());
                }
                virtual_dependencies.push(equality[0].1.clone());
                rows_by_atom.push(vec![None]);
                continue;
            }
            let mut matching = Vec::new();
            for row_id in self.indexed.kernel.active_fact_ids() {
                self.indexed.poll_inner()?;
                let row = self.indexed.kernel.fact(row_id)?;
                if row.key.predicate_id == atom.predicate_id
                    && self.row_satisfies(atom, &row.key.arguments, kind, bindings)?
                {
                    matching.push(Some(row_id));
                }
            }
            if matching.is_empty() {
                return Ok(());
            }
            rows_by_atom.push(matching);
        }
        let virtual_refs: Vec<_> = virtual_dependencies.iter().collect();
        let virtual_dependency = DependencySet::union(&virtual_refs);
        self.enumerate_row_choices(
            clause,
            bindings,
            &rows_by_atom,
            0,
            &mut Vec::new(),
            require_new,
            &virtual_dependency,
            found,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn enumerate_row_choices(
        &mut self,
        clause: &RuleClause,
        bindings: &Bindings,
        rows_by_atom: &[Vec<Option<u32>>],
        index: usize,
        selected: &mut Vec<u32>,
        require_new: bool,
        virtual_dependency: &DependencySet,
        found: &mut BTreeMap<MatchKey, JoinMatch>,
    ) -> NativeResult<()> {
        self.indexed.poll_inner()?;
        if index == rows_by_atom.len() {
            if require_new
                && !selected.iter().try_fold(false, |found_new, row_id| {
                    Ok::<_, NativeError>(
                        found_new
                            || self.indexed.kernel.fact(*row_id)?.derivation_generation
                                == self.indexed.kernel.read_generation(),
                    )
                })?
            {
                return Ok(());
            }
            return self.enumerate_supports(
                clause,
                bindings,
                selected,
                0,
                virtual_dependency.clone(),
                &mut Vec::new(),
                found,
            );
        }
        for row_id in &rows_by_atom[index] {
            let old_len = selected.len();
            if let Some(value) = row_id {
                selected.push(*value);
            }
            self.enumerate_row_choices(
                clause,
                bindings,
                rows_by_atom,
                index + 1,
                selected,
                require_new,
                virtual_dependency,
                found,
            )?;
            selected.truncate(old_len);
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn enumerate_supports(
        &mut self,
        clause: &RuleClause,
        bindings: &Bindings,
        row_ids: &[u32],
        index: usize,
        dependency: DependencySet,
        selected_supports: &mut Vec<DependencySet>,
        found: &mut BTreeMap<MatchKey, JoinMatch>,
    ) -> NativeResult<()> {
        self.indexed.poll_inner()?;
        if index == row_ids.len() {
            let support_refs: Vec<_> = selected_supports.iter().collect();
            let support_dependency = DependencySet::union(&support_refs);
            let combined = DependencySet::union(&[&dependency, &support_dependency]);
            let candidate = JoinMatch::new(
                clause.clause_id,
                0,
                freeze_bindings(bindings),
                combined,
                row_ids.to_vec(),
            )?;
            return self.indexed.insert_match(found, candidate);
        }
        let row = self.indexed.kernel.fact(row_ids[index])?.clone();
        if row.supports.is_empty() {
            return Err(NativeError::invariant(
                "active fact row has no dependency support",
            ));
        }
        for support in row.supports {
            selected_supports.push(support);
            self.enumerate_supports(
                clause,
                bindings,
                row_ids,
                index + 1,
                dependency.clone(),
                selected_supports,
                found,
            )?;
            selected_supports.pop();
        }
        Ok(())
    }

    fn row_satisfies(
        &self,
        atom: &RuleAtom,
        handles: &[NodeHandle],
        kind: PredicateKind,
        bindings: &Bindings,
    ) -> NativeResult<bool> {
        if kind != PredicateKind::Inequality {
            return Ok(self
                .indexed
                .unify_handles(atom, handles, bindings)?
                .is_some());
        }
        if self
            .indexed
            .unify_handles(atom, handles, bindings)?
            .is_some()
        {
            return Ok(true);
        }
        let reversed: Vec<_> = handles.iter().rev().copied().collect();
        Ok(self
            .indexed
            .unify_handles(atom, &reversed, bindings)?
            .is_some())
    }
}

fn freeze_bindings(bindings: &Bindings) -> Vec<VariableBinding> {
    bindings
        .iter()
        .map(|((sort, variable_id), node)| VariableBinding {
            sort: *sort,
            variable_id: *variable_id,
            node: *node,
        })
        .collect()
}

fn resource_limit(
    message: &'static str,
    limit: &'static str,
    observed: u64,
    allowed: u64,
) -> NativeError {
    NativeError::new(ErrorKind::Resource, "RESOURCE_LIMIT", message)
        .with_context("limit", limit)
        .with_context("observed", observed.to_string())
        .with_context("allowed", allowed.to_string())
}

fn usize_from_u32(value: u32, name: &str) -> NativeResult<usize> {
    usize::try_from(value)
        .map_err(|_| NativeError::wire(format!("{name} cannot fit this platform")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cancel::CancellationHandle;
    use crate::model::NodeKind;
    use crate::rules::model::{RulePredicate, TermSort};
    use crate::rules::plans::compile_join_program;

    fn control() -> NativeResult<Arc<CancellationState>> {
        CancellationHandle::from_options(None, None).map(|handle| handle.state())
    }

    fn atom(predicate_id: u32, arguments: Vec<Term>) -> NativeResult<RuleAtom> {
        RuleAtom::new(predicate_id, arguments)
    }

    fn canonical(mut atoms: Vec<RuleAtom>) -> Vec<RuleAtom> {
        atoms.sort_by_cached_key(RuleAtom::canonical_bytes);
        atoms
    }

    fn plan_for_predicate<'a>(
        joins: &'a super::super::plans::JoinProgram,
        program: &RuleProgram,
        predicate_id: u32,
    ) -> NativeResult<&'a ClauseJoinPlan> {
        joins
            .plans()
            .iter()
            .find(|plan| {
                program
                    .clause(plan.clause_id)
                    .ok()
                    .and_then(|clause| {
                        usize::try_from(plan.delta_body_index)
                            .ok()
                            .and_then(|index| clause.body.get(index))
                    })
                    .is_some_and(|atom| atom.predicate_id == predicate_id)
            })
            .ok_or_else(|| NativeError::invariant("test join plan is absent"))
    }

    fn object_predicate(predicate_id: u32, kind: PredicateKind) -> NativeResult<RulePredicate> {
        let sorts = match kind {
            PredicateKind::ObjectRole | PredicateKind::Inequality | PredicateKind::Equality => {
                vec![TermSort::Object, TermSort::Object]
            }
            _ => vec![TermSort::Object],
        };
        let predicate = RulePredicate::new(predicate_id, kind, sorts)?;
        Ok(match kind {
            PredicateKind::Concept | PredicateKind::NegatedConcept => {
                predicate.with_symbol_id(predicate_id)
            }
            PredicateKind::ObjectRole => predicate.with_role_id(predicate_id),
            _ => predicate,
        })
    }

    fn root(kernel: &mut TableauKernel) -> NativeResult<NodeHandle> {
        kernel.create_node(NodeKind::Root, None, false, None, None, None)
    }

    fn logical_matches(values: Vec<JoinMatch>) -> BTreeSet<(Vec<VariableBinding>, DependencySet)> {
        values
            .into_iter()
            .map(|value| (value.bindings, value.dependency))
            .collect()
    }

    fn required_error<T>(result: NativeResult<T>) -> NativeResult<NativeError> {
        result
            .err()
            .ok_or_else(|| NativeError::invariant("test operation unexpectedly succeeded"))
    }

    #[test]
    fn indexed_join_unions_dependencies_and_honours_repeated_variables() -> NativeResult<()> {
        let predicates = vec![
            object_predicate(0, PredicateKind::Concept)?,
            object_predicate(1, PredicateKind::ObjectRole)?,
            object_predicate(2, PredicateKind::Concept)?,
        ];
        let x = Term::variable(0, TermSort::Object);
        let y = Term::variable(1, TermSort::Object);
        let clause = RuleClause::new(
            0,
            canonical(vec![
                atom(0, vec![x.clone()])?,
                atom(1, vec![x, y.clone()])?,
                atom(2, vec![y])?,
            ]),
            Vec::new(),
            vec![0],
            vec![0, 1, 2],
        )?;
        let program = RuleProgram::new(predicates, vec![clause])?;
        let joins = compile_join_program(&program)?;

        let mut kernel = TableauKernel::new();
        kernel.push_branch(
            "ground_disjunction".to_owned(),
            vec![10, 11],
            0,
            DependencySet::empty(),
        )?;
        kernel.push_branch(
            "ground_disjunction".to_owned(),
            vec![20, 21],
            1,
            DependencySet::empty(),
        )?;
        let left = root(&mut kernel)?;
        let right = root(&mut kernel)?;
        kernel.add_fact(0, vec![left], DependencySet::new(vec![0])?, false, None)?;
        let delta = kernel.add_fact(
            1,
            vec![left, right],
            DependencySet::new(vec![1])?,
            false,
            None,
        )?;
        kernel.add_fact(2, vec![right], DependencySet::empty(), false, None)?;

        let mut evaluator = IndexedJoinEvaluator::new(
            &program,
            &kernel,
            BTreeMap::new(),
            BTreeMap::new(),
            control()?,
            RuleLimits::default(),
        )?;
        let matches = evaluator.matches(plan_for_predicate(&joins, &program, 1)?, delta)?;
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].dependency.as_slice(), &[0, 1]);
        assert_eq!(matches[0].premise_row_ids.len(), 3);
        assert_eq!(matches[0].bindings[0].node, left);
        assert_eq!(matches[0].bindings[1].node, right);
        Ok(())
    }

    #[test]
    fn equality_constants_and_unbound_domains_match_python_semantics() -> NativeResult<()> {
        let predicates = vec![
            object_predicate(0, PredicateKind::Concept)?,
            object_predicate(1, PredicateKind::Equality)?,
        ];
        let x = Term::variable(0, TermSort::Object);
        let y = Term::variable(1, TermSort::Object);
        let clause = RuleClause::new(
            0,
            canonical(vec![
                atom(0, vec![Term::individual(7)])?,
                atom(1, vec![x, y])?,
            ]),
            Vec::new(),
            vec![0],
            vec![0, 1],
        )?;
        let program = RuleProgram::new(predicates, vec![clause])?;
        let joins = compile_join_program(&program)?;
        let mut kernel = TableauKernel::new();
        let first = root(&mut kernel)?;
        let second = root(&mut kernel)?;
        let delta = kernel.add_fact(0, vec![first], DependencySet::empty(), false, None)?;
        let mut evaluator = IndexedJoinEvaluator::new(
            &program,
            &kernel,
            BTreeMap::from([(7, first)]),
            BTreeMap::new(),
            control()?,
            RuleLimits::default(),
        )?;
        let matches = evaluator.matches(plan_for_predicate(&joins, &program, 0)?, delta)?;
        assert_eq!(matches.len(), 2);
        assert_eq!(matches[0].bindings[0].node, first);
        assert_eq!(matches[0].bindings[1].node, first);
        assert_eq!(matches[1].bindings[0].node, second);
        assert_eq!(matches[1].bindings[1].node, second);
        let expected = logical_matches(matches);
        let mut naive = NaiveJoinEvaluator::new(&mut evaluator);
        assert_eq!(logical_matches(naive.matches(0, true)?), expected);
        Ok(())
    }

    #[test]
    fn symmetric_inequality_and_ordering_guards_match_the_naive_oracle() -> NativeResult<()> {
        let x = Term::variable(0, TermSort::Object);
        let y = Term::variable(1, TermSort::Object);
        let inequality_program = RuleProgram::new(
            vec![
                object_predicate(0, PredicateKind::Concept)?,
                object_predicate(1, PredicateKind::Inequality)?,
            ],
            vec![RuleClause::new(
                0,
                canonical(vec![
                    atom(0, vec![x.clone()])?,
                    atom(1, vec![x.clone(), y.clone()])?,
                ]),
                Vec::new(),
                vec![0],
                vec![0, 1],
            )?],
        )?;
        let inequality_joins = compile_join_program(&inequality_program)?;
        let mut inequality_kernel = TableauKernel::new();
        let first = root(&mut inequality_kernel)?;
        let second = root(&mut inequality_kernel)?;
        inequality_kernel.add_fact(1, vec![first, second], DependencySet::empty(), false, None)?;
        inequality_kernel.prepare_next_delta()?;
        let concept =
            inequality_kernel.add_fact(0, vec![second], DependencySet::empty(), false, None)?;
        inequality_kernel.prepare_next_delta()?;
        let mut inequality = IndexedJoinEvaluator::new(
            &inequality_program,
            &inequality_kernel,
            BTreeMap::new(),
            BTreeMap::new(),
            control()?,
            RuleLimits::default(),
        )?;
        let indexed = inequality.matches(
            plan_for_predicate(&inequality_joins, &inequality_program, 0)?,
            concept,
        )?;
        assert_eq!(indexed.len(), 1);
        assert_eq!(indexed[0].bindings[0].node, second);
        assert_eq!(indexed[0].bindings[1].node, first);
        let expected = logical_matches(indexed);
        let mut naive = NaiveJoinEvaluator::new(&mut inequality);
        assert_eq!(logical_matches(naive.matches(0, true)?), expected);

        let ordering_program = RuleProgram::new(
            vec![
                object_predicate(0, PredicateKind::ObjectRole)?,
                RulePredicate::new(
                    1,
                    PredicateKind::OrderingGuard,
                    vec![TermSort::Object, TermSort::Object],
                )?
                .with_internal_key("canonical-object-order"),
            ],
            vec![RuleClause::new(
                0,
                canonical(vec![
                    atom(0, vec![x.clone(), y.clone()])?,
                    atom(1, vec![x, y])?,
                ]),
                Vec::new(),
                vec![0],
                vec![0, 1],
            )?],
        )?;
        let ordering_joins = compile_join_program(&ordering_program)?;
        let mut ordering_kernel = TableauKernel::new();
        let lower = root(&mut ordering_kernel)?;
        let higher = root(&mut ordering_kernel)?;
        let forward = ordering_kernel.add_fact(
            0,
            vec![lower, higher],
            DependencySet::empty(),
            false,
            None,
        )?;
        let reverse = ordering_kernel.add_fact(
            0,
            vec![higher, lower],
            DependencySet::empty(),
            false,
            None,
        )?;
        let mut ordering = IndexedJoinEvaluator::new(
            &ordering_program,
            &ordering_kernel,
            BTreeMap::new(),
            BTreeMap::new(),
            control()?,
            RuleLimits::default(),
        )?;
        let plan = plan_for_predicate(&ordering_joins, &ordering_program, 0)?;
        let accepted = ordering.matches(plan, forward)?;
        assert_eq!(accepted.len(), 1);
        assert!(ordering.matches(plan, reverse)?.is_empty());
        let expected = logical_matches(accepted);
        let mut naive = NaiveJoinEvaluator::new(&mut ordering);
        assert_eq!(logical_matches(naive.matches(0, true)?), expected);
        Ok(())
    }

    #[test]
    fn cancellation_and_rule_limits_return_typed_errors() -> NativeResult<()> {
        let predicates = vec![
            object_predicate(0, PredicateKind::Concept)?,
            object_predicate(1, PredicateKind::Concept)?,
        ];
        let variable = Term::variable(0, TermSort::Object);
        let clause = RuleClause::new(
            0,
            canonical(vec![
                atom(0, vec![variable.clone()])?,
                atom(1, vec![variable])?,
            ]),
            Vec::new(),
            vec![0],
            vec![0, 1],
        )?;
        let program = RuleProgram::new(predicates, vec![clause])?;
        let joins = compile_join_program(&program)?;
        let mut kernel = TableauKernel::new();
        let node = root(&mut kernel)?;
        let row = kernel.add_fact(0, vec![node], DependencySet::empty(), false, None)?;
        kernel.add_fact(1, vec![node], DependencySet::empty(), false, None)?;

        let cancellation = control()?;
        let mut cancelled = IndexedJoinEvaluator::new(
            &program,
            &kernel,
            BTreeMap::new(),
            BTreeMap::new(),
            Arc::clone(&cancellation),
            RuleLimits::default(),
        )?;
        cancellation.interrupt(Some("generated stop".to_owned()))?;
        let cancelled_error =
            required_error(cancelled.matches(plan_for_predicate(&joins, &program, 0)?, row))?;
        assert_eq!(cancelled_error.kind, ErrorKind::Cancelled);

        let mut limited = IndexedJoinEvaluator::new(
            &program,
            &kernel,
            BTreeMap::new(),
            BTreeMap::new(),
            control()?,
            RuleLimits::new(1, 10, 1)?,
        )?;
        let error = required_error(limited.matches(plan_for_predicate(&joins, &program, 0)?, row))?;
        assert_eq!(error.kind, ErrorKind::Resource);
        assert_eq!(
            error.context.get("limit").map(String::as_str),
            Some("max_join_steps")
        );
        Ok(())
    }

    #[test]
    fn dependency_bit_order_and_match_limits_match_python() -> NativeResult<()> {
        let program = RuleProgram::new(
            vec![object_predicate(0, PredicateKind::Concept)?],
            vec![RuleClause::new(
                0,
                vec![atom(0, vec![Term::variable(0, TermSort::Object)])?],
                Vec::new(),
                vec![0],
                vec![0],
            )?],
        )?;
        let joins = compile_join_program(&program)?;
        let mut kernel = TableauKernel::new();
        for source_id in 0..3 {
            kernel.push_branch(
                "ground_disjunction".to_owned(),
                vec![source_id * 2, source_id * 2 + 1],
                source_id,
                DependencySet::empty(),
            )?;
        }
        let node = root(&mut kernel)?;
        let row = kernel.add_fact(0, vec![node], DependencySet::new(vec![1])?, false, None)?;
        kernel.add_fact(0, vec![node], DependencySet::new(vec![0, 2])?, false, None)?;
        let plan = plan_for_predicate(&joins, &program, 0)?;
        let mut evaluator = IndexedJoinEvaluator::new(
            &program,
            &kernel,
            BTreeMap::new(),
            BTreeMap::new(),
            control()?,
            RuleLimits::default(),
        )?;
        let matches = evaluator.matches(plan, row)?;
        assert_eq!(matches.len(), 2);
        assert_eq!(matches[0].dependency.as_slice(), &[1]);
        assert_eq!(matches[1].dependency.as_slice(), &[0, 2]);

        let mut limited = IndexedJoinEvaluator::new(
            &program,
            &kernel,
            BTreeMap::new(),
            BTreeMap::new(),
            control()?,
            RuleLimits::new(10, 1, 1)?,
        )?;
        let error = required_error(limited.matches(plan, row))?;
        assert_eq!(error.kind, ErrorKind::Resource);
        assert_eq!(
            error.context.get("limit").map(String::as_str),
            Some("max_matches_per_generation")
        );
        Ok(())
    }

    #[test]
    fn generated_indexed_and_naive_matches_are_differentially_equal() -> NativeResult<()> {
        for seed in 0..32_u64 {
            generated_case(seed)?;
        }
        Ok(())
    }

    fn generated_case(mut seed: u64) -> NativeResult<()> {
        let predicates = vec![
            object_predicate(0, PredicateKind::Concept)?,
            object_predicate(1, PredicateKind::Concept)?,
            object_predicate(2, PredicateKind::ObjectRole)?,
        ];
        let x = Term::variable(0, TermSort::Object);
        let y = Term::variable(1, TermSort::Object);
        let clause = RuleClause::new(
            0,
            canonical(vec![
                atom(0, vec![x.clone()])?,
                atom(1, vec![y.clone()])?,
                atom(2, vec![x, y])?,
            ]),
            Vec::new(),
            vec![0],
            vec![0, 1, 2],
        )?;
        let program = RuleProgram::new(predicates, vec![clause])?;
        let joins = compile_join_program(&program)?;
        let mut kernel = TableauKernel::new();
        let mut nodes = Vec::new();
        for _ in 0..4 {
            nodes.push(root(&mut kernel)?);
        }
        for (index, node) in nodes.iter().copied().enumerate() {
            if pseudo_bool(&mut seed) || index == 0 {
                kernel.add_fact(0, vec![node], DependencySet::empty(), false, None)?;
            }
            if pseudo_bool(&mut seed) || index == 1 {
                kernel.add_fact(1, vec![node], DependencySet::empty(), false, None)?;
            }
        }
        for left in &nodes {
            for right in &nodes {
                if pseudo_bool(&mut seed) {
                    kernel.add_fact(2, vec![*left, *right], DependencySet::empty(), false, None)?;
                }
            }
        }
        let mut evaluator = IndexedJoinEvaluator::new(
            &program,
            &kernel,
            BTreeMap::new(),
            BTreeMap::new(),
            control()?,
            RuleLimits::default(),
        )?;
        let mut indexed = BTreeSet::new();
        for plan in joins.plans() {
            let trigger = &program.clause(plan.clause_id)?.body
                [usize_from_u32(plan.delta_body_index, "delta body index")?];
            for row_id in kernel.active_fact_ids() {
                if kernel.fact(row_id)?.key.predicate_id == trigger.predicate_id {
                    indexed.extend(logical_matches(evaluator.matches(plan, row_id)?));
                }
            }
        }
        let mut naive = NaiveJoinEvaluator::new(&mut evaluator);
        let expected = logical_matches(naive.matches(0, true)?);
        assert_eq!(indexed, expected, "generated seed {seed}");
        Ok(())
    }

    fn pseudo_bool(state: &mut u64) -> bool {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        *state >> 63 != 0
    }
}
