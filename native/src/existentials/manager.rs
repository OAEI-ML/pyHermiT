//! Deterministic expansion strategies over the narrow tableau adapters.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};

use super::distinct::pairwise_distinct_subset;
use super::model::{
    AtLeastPredicate, BranchTransition, CandidatePriority, ClashKind, ClashRecord, DependencySet,
    ExpansionControl, ExpansionError, ExpansionLimits, ExpansionProgram, ExpansionResult,
    ExpansionRuleAccess, ExpansionStateMutation, ExpansionStateRead, ExpansionStatus,
    ExpansionStrategy, FactBinding, GroundAtom, NodeKind, NodeSort, ObligationKind,
};

/// Stateless program-specific expansion kernel. Query-local reuse choices are
/// stored by `ExpansionStateMutation`, so state rollback also rolls them back.
#[derive(Clone, Debug)]
pub struct ExistentialExpansionManager {
    program: ExpansionProgram,
    strategy: ExpansionStrategy,
    limits: ExpansionLimits,
}

impl ExistentialExpansionManager {
    pub fn new(
        program: ExpansionProgram,
        strategy: ExpansionStrategy,
        limits: ExpansionLimits,
    ) -> Result<Self, ExpansionError> {
        let limits = ExpansionLimits::new(
            limits.max_witnesses_per_obligation,
            limits.max_distinct_search_steps,
            limits.cancellation_interval,
        )?;
        Ok(Self {
            program,
            strategy,
            limits,
        })
    }

    #[must_use]
    pub const fn strategy(&self) -> ExpansionStrategy {
        self.strategy
    }

    #[must_use]
    pub const fn limits(&self) -> ExpansionLimits {
        self.limits
    }

    #[must_use]
    pub const fn program(&self) -> &ExpansionProgram {
        &self.program
    }

    pub fn process_next<S, A, C>(
        &self,
        state: &mut S,
        access: &mut A,
        control: &mut C,
    ) -> Result<ExpansionResult<S::Node>, ExpansionError>
    where
        S: ExpansionStateMutation,
        A: ExpansionRuleAccess<S>,
        C: ExpansionControl,
    {
        let checkpoint = state.checkpoint()?;
        match self.process_next_inner(state, access, control) {
            Ok(result) => Ok(result),
            Err(error) => match state.restore(checkpoint) {
                Ok(()) => Err(error),
                Err(restore_error) => Err(ExpansionError::invariant(format!(
                    "expansion rollback failed after '{error}': {restore_error}"
                ))),
            },
        }
    }

    fn process_next_inner<S, A, C>(
        &self,
        state: &mut S,
        access: &mut A,
        control: &mut C,
    ) -> Result<ExpansionResult<S::Node>, ExpansionError>
    where
        S: ExpansionStateMutation,
        A: ExpansionRuleAccess<S>,
        C: ExpansionControl,
    {
        control.poll()?;
        let Some(root) = Self::take_unblocked_candidate(state)? else {
            return Ok(ExpansionResult::idle(if state.candidate_count()? == 0 {
                ExpansionStatus::NoWork
            } else {
                ExpansionStatus::Blocked
            }));
        };
        let node = state
            .node_record(root)?
            .ok_or_else(|| ExpansionError::invariant("selected existential node disappeared"))?;
        let existential_id = node
            .pending_existentials
            .iter()
            .next()
            .copied()
            .ok_or_else(|| ExpansionError::invariant("selected node has no pending obligation"))?;
        let predicate = self
            .program
            .obligation(existential_id)
            .cloned()
            .ok_or_else(|| {
                ExpansionError::invariant("existential queue contains a non-at-least predicate")
            })?;
        let supports = Self::obligation_supports(state, predicate.predicate_id, root)?;
        if supports.is_empty() {
            Self::mark_processed(state, root, existential_id, control)?;
            return Ok(ExpansionResult::for_obligation(
                ExpansionStatus::Satisfied,
                root,
                existential_id,
                Vec::new(),
            ));
        }
        if self.is_satisfied(state, access, &predicate, root, control)? {
            Self::mark_processed(state, root, existential_id, control)?;
            return Ok(ExpansionResult::for_obligation(
                ExpansionStatus::Satisfied,
                root,
                existential_id,
                Vec::new(),
            ));
        }
        self.check_witness_limit(&predicate)?;
        if self.uses_bottom_role(&predicate) {
            state.install_clash(ClashRecord {
                kind: ClashKind::ImpossibleCardinality,
                dependency: minimal_support(&supports)?.clone(),
                details: vec![predicate.predicate_id],
            })?;
            control.poll()?;
            return Ok(ExpansionResult::for_obligation(
                ExpansionStatus::Clashed,
                root,
                existential_id,
                Vec::new(),
            ));
        }
        if self.can_reuse(state, &predicate)? {
            return self.expand_with_reuse(state, access, &predicate, root, supports, control);
        }
        let witnesses = match predicate.kind {
            ObligationKind::Object => {
                self.expand_object(state, access, &predicate, root, &supports, control)?
            }
            ObligationKind::Data => {
                self.expand_data(state, access, &predicate, root, &supports, control)?
            }
        };
        Self::mark_processed(state, root, existential_id, control)?;
        Ok(ExpansionResult::for_obligation(
            ExpansionStatus::Expanded,
            root,
            existential_id,
            witnesses,
        ))
    }

    /// Cardinality satisfaction is public so benchmarks can isolate indexed
    /// successor collection and subset search from witness mutation.
    pub fn is_satisfied<S, A, C>(
        &self,
        state: &S,
        access: &mut A,
        predicate: &AtLeastPredicate,
        root: S::Node,
        control: &mut C,
    ) -> Result<bool, ExpansionError>
    where
        S: ExpansionStateMutation,
        A: ExpansionRuleAccess<S>,
        C: ExpansionControl,
    {
        if predicate.cardinality == 0 {
            return Ok(true);
        }
        match predicate.kind {
            ObligationKind::Object => {
                let candidates = self.object_satisfiers(state, predicate, root)?;
                let cardinality = usize_from_u32(predicate.cardinality)?;
                Ok(pairwise_distinct_subset(
                    &candidates,
                    cardinality,
                    self.limits,
                    control,
                    |left, right| {
                        self.known_different(state, access, *left, *right, NodeSort::Object)
                    },
                )?
                .satisfied)
            }
            ObligationKind::Data if predicate.role_ids.len() > 1 => {
                Ok(self.data_tuple_satisfiers(state, predicate, root, control)? > 0)
            }
            ObligationKind::Data => {
                let candidates = self.data_satisfiers(state, access, predicate, root, control)?;
                let cardinality = usize_from_u32(predicate.cardinality)?;
                Ok(pairwise_distinct_subset(
                    &candidates,
                    cardinality,
                    self.limits,
                    control,
                    |left, right| {
                        self.known_different(state, access, *left, *right, NodeSort::Data)
                    },
                )?
                .satisfied)
            }
        }
    }

    pub fn owns_branch<S: ExpansionStateRead>(
        &self,
        state: &S,
        level: u32,
    ) -> Result<bool, ExpansionError> {
        Ok(state.reuse_branch(level)?.is_some())
    }

    pub fn resolve_clash<S, A, C>(
        &self,
        state: &mut S,
        access: &mut A,
        control: &mut C,
    ) -> Result<BranchTransition, ExpansionError>
    where
        S: ExpansionStateMutation,
        A: ExpansionRuleAccess<S>,
        C: ExpansionControl,
    {
        let checkpoint = state.checkpoint()?;
        match self.resolve_clash_inner(state, access, control) {
            Ok(result) => Ok(result),
            Err(error) => match state.restore(checkpoint) {
                Ok(()) => Err(error),
                Err(restore_error) => Err(ExpansionError::invariant(format!(
                    "reuse-clash rollback failed after '{error}': {restore_error}"
                ))),
            },
        }
    }

    fn resolve_clash_inner<S, A, C>(
        &self,
        state: &mut S,
        access: &mut A,
        control: &mut C,
    ) -> Result<BranchTransition, ExpansionError>
    where
        S: ExpansionStateMutation,
        A: ExpansionRuleAccess<S>,
        C: ExpansionControl,
    {
        control.poll()?;
        let Some(clash) = state.current_clash()? else {
            return Ok(BranchTransition::NoWork);
        };
        let Some(level) = clash.dependency.maximum() else {
            return Ok(BranchTransition::Unsat);
        };
        let record = state
            .reuse_branch(level)?
            .ok_or_else(|| ExpansionError::invariant("clash is not owned by individual reuse"))?;
        let branch = state
            .branch(level)?
            .ok_or_else(|| ExpansionError::invariant("reuse branch level is unavailable"))?;
        let without_level = clash.dependency.without(level);
        let alternative = state.advance_reuse_branch(level, without_level.clone())?;
        control.poll()?;
        if let Some(alternative) = alternative {
            if alternative != 1 {
                return Err(ExpansionError::invariant(
                    "individual-reuse alternative is malformed",
                ));
            }
            state.set_reuse_disabled(record.predicate_id, true)?;
            let current = state.branch(level)?.ok_or_else(|| {
                ExpansionError::invariant("reuse branch disappeared after advance")
            })?;
            let dependency =
                DependencySet::union(&[&current.base_dependency, &without_level]).add(level);
            let predicate = self
                .program
                .obligation(record.predicate_id)
                .cloned()
                .ok_or_else(|| {
                    ExpansionError::invariant("reuse branch predicate is unavailable")
                })?;
            let witnesses = self.expand_object(
                state,
                access,
                &predicate,
                record.root,
                std::slice::from_ref(&dependency),
                control,
            )?;
            if witnesses.len() != 1 {
                return Err(ExpansionError::invariant(
                    "reuse fallback must create exactly one witness",
                ));
            }
            return Ok(BranchTransition::Advanced);
        }
        state.remove_reuse_branch(level)?;
        let propagated = DependencySet::union(&[
            &branch.base_dependency,
            &branch.learned_dependency,
            &without_level,
        ]);
        state.install_clash(ClashRecord {
            kind: ClashKind::EmptyHead,
            dependency: propagated,
            details: vec![record.predicate_id],
        })?;
        control.poll()?;
        Ok(BranchTransition::Exhausted)
    }

    fn take_unblocked_candidate<S: ExpansionStateMutation>(
        state: &mut S,
    ) -> Result<Option<S::Node>, ExpansionError> {
        let count = state.candidate_count()?;
        let mut deferred = Vec::<(S::Node, CandidatePriority)>::new();
        let mut selected = None;
        for _ in 0..count {
            let Some(node) = state.pop_candidate()? else {
                break;
            };
            let Some(record) = state.node_record(node)? else {
                continue;
            };
            if record.pending_existentials.is_empty() {
                continue;
            }
            if state.is_blocked(node)? {
                deferred.push((node, record.priority));
                continue;
            }
            selected = Some(node);
            break;
        }
        for (node, priority) in deferred {
            state.enqueue_candidate(node, priority)?;
        }
        Ok(selected)
    }

    fn obligation_supports<S: ExpansionStateRead>(
        state: &S,
        predicate_id: u32,
        root: S::Node,
    ) -> Result<Vec<DependencySet>, ExpansionError> {
        let rows = state.facts(
            predicate_id,
            &[FactBinding {
                position: 0,
                node: root,
            }],
        )?;
        Ok(rows.into_iter().flat_map(|row| row.supports).collect())
    }

    fn mark_processed<S, C>(
        state: &mut S,
        root: S::Node,
        predicate_id: u32,
        control: &mut C,
    ) -> Result<(), ExpansionError>
    where
        S: ExpansionStateMutation,
        C: ExpansionControl,
    {
        state.mark_processed(root, predicate_id)?;
        control.poll()?;
        let node = state
            .node_record(root)?
            .ok_or_else(|| ExpansionError::invariant("processed existential node disappeared"))?;
        if !node.pending_existentials.is_empty() {
            state.enqueue_candidate(root, node.priority)?;
            control.poll()?;
        }
        Ok(())
    }

    fn object_satisfiers<S: ExpansionStateRead>(
        &self,
        state: &S,
        predicate: &AtLeastPredicate,
        root: S::Node,
    ) -> Result<Vec<S::Node>, ExpansionError> {
        let role_id = only_role(predicate)?;
        let roles = self.program.roles();
        if role_id == roles.bottom_object_role_id {
            return Ok(Vec::new());
        }
        let targets = if role_id == roles.top_object_role_id {
            state
                .active_nodes()?
                .into_iter()
                .filter(|record| record.kind.sort() == NodeSort::Object)
                .map(|record| record.node)
                .collect()
        } else {
            let role_predicate = roles
                .role_predicate(NodeSort::Object, role_id)
                .ok_or_else(|| ExpansionError::invariant("object role predicate is unavailable"))?;
            state
                .facts(
                    role_predicate,
                    &[FactBinding {
                        position: 0,
                        node: root,
                    }],
                )?
                .into_iter()
                .map(|row| binary_target(&row.arguments))
                .collect::<Result<Vec<_>, _>>()?
        };
        let mut result = BTreeMap::<S::Node, CandidatePriority>::new();
        for target in targets {
            let Some(canonical) = state.canonical_node(target)? else {
                continue;
            };
            let Some(record) = state.node_record(canonical.node)? else {
                continue;
            };
            if record.kind.sort() != NodeSort::Object {
                return Err(ExpansionError::invariant(
                    "object role points to a concrete node",
                ));
            }
            if state.is_blocked(canonical.node)? && record.parent != Some(root) {
                continue;
            }
            if has_fact(state, predicate.filler_predicate_id, &[canonical.node])? {
                result.insert(canonical.node, record.priority);
            }
        }
        Ok(sorted_nodes(result))
    }

    fn data_satisfiers<S, A, C>(
        &self,
        state: &S,
        access: &mut A,
        predicate: &AtLeastPredicate,
        root: S::Node,
        control: &mut C,
    ) -> Result<Vec<S::Node>, ExpansionError>
    where
        S: ExpansionStateMutation,
        A: ExpansionRuleAccess<S>,
        C: ExpansionControl,
    {
        let role_id = only_role(predicate)?;
        let roles = self.program.roles();
        if role_id == roles.bottom_data_role_id {
            return Ok(Vec::new());
        }
        let targets = if role_id == roles.top_data_role_id {
            state
                .active_nodes()?
                .into_iter()
                .filter(|record| record.kind.sort() == NodeSort::Data)
                .map(|record| record.node)
                .collect()
        } else {
            let role_predicate = roles
                .role_predicate(NodeSort::Data, role_id)
                .ok_or_else(|| ExpansionError::invariant("data role predicate is unavailable"))?;
            state
                .facts(
                    role_predicate,
                    &[FactBinding {
                        position: 0,
                        node: root,
                    }],
                )?
                .into_iter()
                .map(|row| binary_target(&row.arguments))
                .collect::<Result<Vec<_>, _>>()?
        };
        let mut result = BTreeMap::<S::Node, CandidatePriority>::new();
        for target in targets {
            let Some(canonical) = state.canonical_node(target)? else {
                continue;
            };
            let Some(record) = state.node_record(canonical.node)? else {
                continue;
            };
            if record.kind.sort() != NodeSort::Data {
                return Err(ExpansionError::invariant(
                    "data role points to an object node",
                ));
            }
            if has_fact(state, predicate.filler_predicate_id, &[canonical.node])?
                || access.data_value_satisfies(
                    state,
                    canonical.node,
                    predicate.filler_predicate_id,
                    control,
                )?
            {
                result.insert(canonical.node, record.priority);
            }
        }
        Ok(sorted_nodes(result))
    }

    fn data_tuple_satisfiers<S, C>(
        &self,
        state: &S,
        predicate: &AtLeastPredicate,
        root: S::Node,
        control: &mut C,
    ) -> Result<usize, ExpansionError>
    where
        S: ExpansionStateRead,
        C: ExpansionControl,
    {
        let roles = self.program.roles();
        let mut domains = Vec::<BTreeSet<S::Node>>::new();
        for role_id in &predicate.role_ids {
            control.poll()?;
            if *role_id == roles.bottom_data_role_id {
                return Ok(0);
            }
            if *role_id == roles.top_data_role_id {
                domains.push(
                    state
                        .active_nodes()?
                        .into_iter()
                        .filter(|record| record.kind.sort() == NodeSort::Data)
                        .map(|record| record.node)
                        .collect(),
                );
                continue;
            }
            let role_predicate =
                roles
                    .role_predicate(NodeSort::Data, *role_id)
                    .ok_or_else(|| {
                        ExpansionError::invariant("n-ary data role predicate is unavailable")
                    })?;
            let mut domain = BTreeSet::new();
            for row in state.facts(
                role_predicate,
                &[FactBinding {
                    position: 0,
                    node: root,
                }],
            )? {
                let target = binary_target(&row.arguments)?;
                if let Some(canonical) = state.canonical_node(target)? {
                    domain.insert(canonical.node);
                }
            }
            domains.push(domain);
        }
        let mut count = 0_usize;
        for row in state.facts(predicate.filler_predicate_id, &[])? {
            control.poll()?;
            if row.arguments.len() == domains.len()
                && row
                    .arguments
                    .iter()
                    .zip(&domains)
                    .all(|(value, domain)| domain.contains(value))
            {
                count = count
                    .checked_add(1)
                    .ok_or_else(|| ExpansionError::invariant("n-ary tuple count overflow"))?;
            }
        }
        Ok(count)
    }

    fn known_different<S, A>(
        &self,
        state: &S,
        access: &A,
        left: S::Node,
        right: S::Node,
        sort: NodeSort,
    ) -> Result<bool, ExpansionError>
    where
        S: ExpansionStateMutation,
        A: ExpansionRuleAccess<S>,
    {
        if left == right {
            return Ok(false);
        }
        if let Some(predicate_id) = self.program.roles().inequality_predicate(sort) {
            let (first, second) = ordered_pair(state, left, right)?;
            let arguments: [S::Node; 2] = (first, second).into();
            if has_fact(state, predicate_id, &arguments)? {
                return Ok(true);
            }
        }
        Ok(sort == NodeSort::Data && access.data_values_known_different(state, left, right)?)
    }

    fn expand_object<S, A, C>(
        &self,
        state: &mut S,
        access: &mut A,
        predicate: &AtLeastPredicate,
        root: S::Node,
        supports: &[DependencySet],
        control: &mut C,
    ) -> Result<Vec<S::Node>, ExpansionError>
    where
        S: ExpansionStateMutation,
        A: ExpansionRuleAccess<S>,
        C: ExpansionControl,
    {
        let role_id = only_role(predicate)?;
        let roles = self.program.roles();
        let role_predicate = if role_id == roles.top_object_role_id {
            None
        } else {
            Some(
                roles
                    .role_predicate(NodeSort::Object, role_id)
                    .ok_or_else(|| {
                        ExpansionError::invariant("object witness role predicate is unavailable")
                    })?,
            )
        };
        let initial_support = minimal_support(supports)?.clone();
        let mut witnesses = Vec::new();
        for _ in 0..predicate.cardinality {
            control.poll()?;
            let witness = state.create_node(NodeKind::Tree, Some(root))?;
            control.poll()?;
            access.register_node(state, witness, initial_support.clone())?;
            control.poll()?;
            witnesses.push(witness);
            for support in supports {
                if let Some(role_predicate) = role_predicate {
                    dispatch(
                        state,
                        access,
                        role_predicate,
                        vec![root, witness],
                        support,
                        control,
                    )?;
                }
                dispatch(
                    state,
                    access,
                    predicate.filler_predicate_id,
                    vec![witness],
                    support,
                    control,
                )?;
            }
        }
        self.add_pairwise_inequalities(
            state,
            access,
            &witnesses,
            NodeSort::Object,
            supports,
            control,
        )?;
        Ok(witnesses)
    }

    fn expand_data<S, A, C>(
        &self,
        state: &mut S,
        access: &mut A,
        predicate: &AtLeastPredicate,
        root: S::Node,
        supports: &[DependencySet],
        control: &mut C,
    ) -> Result<Vec<S::Node>, ExpansionError>
    where
        S: ExpansionStateMutation,
        A: ExpansionRuleAccess<S>,
        C: ExpansionControl,
    {
        let witness_count = if predicate.role_ids.len() == 1 {
            usize_from_u32(predicate.cardinality)?
        } else {
            predicate.role_ids.len()
        };
        let initial_support = minimal_support(supports)?.clone();
        let mut witnesses = Vec::with_capacity(witness_count);
        for _ in 0..witness_count {
            control.poll()?;
            let witness = state.create_node(NodeKind::Concrete, None)?;
            control.poll()?;
            access.register_node(state, witness, initial_support.clone())?;
            control.poll()?;
            witnesses.push(witness);
        }
        for support in supports {
            for (index, witness) in witnesses.iter().copied().enumerate() {
                let role_id = if predicate.role_ids.len() == 1 {
                    predicate.role_ids[0]
                } else {
                    predicate.role_ids[index]
                };
                if role_id != self.program.roles().top_data_role_id {
                    let role_predicate = self
                        .program
                        .roles()
                        .role_predicate(NodeSort::Data, role_id)
                        .ok_or_else(|| {
                            ExpansionError::invariant("data witness role predicate is unavailable")
                        })?;
                    dispatch(
                        state,
                        access,
                        role_predicate,
                        vec![root, witness],
                        support,
                        control,
                    )?;
                }
            }
            if predicate.role_ids.len() > 1 {
                dispatch(
                    state,
                    access,
                    predicate.filler_predicate_id,
                    witnesses.clone(),
                    support,
                    control,
                )?;
            } else {
                for witness in &witnesses {
                    dispatch(
                        state,
                        access,
                        predicate.filler_predicate_id,
                        vec![*witness],
                        support,
                        control,
                    )?;
                }
            }
        }
        if predicate.role_ids.len() == 1 {
            self.add_pairwise_inequalities(
                state,
                access,
                &witnesses,
                NodeSort::Data,
                supports,
                control,
            )?;
        }
        Ok(witnesses)
    }

    fn add_pairwise_inequalities<S, A, C>(
        &self,
        state: &mut S,
        access: &mut A,
        witnesses: &[S::Node],
        sort: NodeSort,
        supports: &[DependencySet],
        control: &mut C,
    ) -> Result<(), ExpansionError>
    where
        S: ExpansionStateMutation,
        A: ExpansionRuleAccess<S>,
        C: ExpansionControl,
    {
        if witnesses.len() < 2 {
            return Ok(());
        }
        let predicate_id = self
            .program
            .roles()
            .inequality_predicate(sort)
            .ok_or_else(|| {
                ExpansionError::invariant("cardinality witnesses require an inequality predicate")
            })?;
        for left_index in 0..witnesses.len() {
            for right_index in (left_index + 1)..witnesses.len() {
                let (left, right) =
                    ordered_pair(state, witnesses[left_index], witnesses[right_index])?;
                for support in supports {
                    dispatch(
                        state,
                        access,
                        predicate_id,
                        vec![left, right],
                        support,
                        control,
                    )?;
                }
            }
        }
        Ok(())
    }

    fn can_reuse<S: ExpansionStateRead>(
        &self,
        state: &S,
        predicate: &AtLeastPredicate,
    ) -> Result<bool, ExpansionError> {
        Ok(self.strategy == ExpansionStrategy::IndividualReuse
            && predicate.kind == ObligationKind::Object
            && predicate.cardinality == 1
            && predicate.reusable_filler
            && !state.reuse_disabled(predicate.predicate_id)?)
    }

    fn expand_with_reuse<S, A, C>(
        &self,
        state: &mut S,
        access: &mut A,
        predicate: &AtLeastPredicate,
        root: S::Node,
        supports: Vec<DependencySet>,
        control: &mut C,
    ) -> Result<ExpansionResult<S::Node>, ExpansionError>
    where
        S: ExpansionStateMutation,
        A: ExpansionRuleAccess<S>,
        C: ExpansionControl,
    {
        Self::mark_processed(state, root, predicate.predicate_id, control)?;
        let base = minimal_support(&supports)?.clone();
        let branch =
            state.push_reuse_branch(root, predicate.predicate_id, supports, base.clone())?;
        if branch.current_alternative != 0 {
            return Err(ExpansionError::invariant(
                "new reuse branch did not select its first alternative",
            ));
        }
        control.poll()?;
        let mut dependency = base.add(branch.level);
        let candidate = if let Some(parent) = Self::parent_reuse_candidate(state, predicate, root)?
        {
            parent
        } else {
            Self::model_reuse_candidate(
                state,
                access,
                predicate.filler_predicate_id,
                &dependency,
                control,
            )?
        };
        let canonical = state.canonical_node(candidate)?.ok_or_else(|| {
            ExpansionError::invariant("individual-reuse candidate is unavailable")
        })?;
        dependency = DependencySet::union(&[&dependency, &canonical.dependency]);
        let role_id = only_role(predicate)?;
        if role_id != self.program.roles().top_object_role_id {
            let role_predicate = self
                .program
                .roles()
                .role_predicate(NodeSort::Object, role_id)
                .ok_or_else(|| ExpansionError::invariant("reuse role predicate is unavailable"))?;
            dispatch_owned(
                state,
                access,
                role_predicate,
                vec![root, canonical.node],
                dependency,
                control,
            )?;
        }
        Ok(ExpansionResult::for_obligation(
            ExpansionStatus::Expanded,
            root,
            predicate.predicate_id,
            vec![canonical.node],
        ))
    }

    fn parent_reuse_candidate<S: ExpansionStateRead>(
        state: &S,
        predicate: &AtLeastPredicate,
        root: S::Node,
    ) -> Result<Option<S::Node>, ExpansionError> {
        let Some(node) = state.node_record(root)? else {
            return Ok(None);
        };
        let Some(parent) = node.parent else {
            return Ok(None);
        };
        let Some(canonical) = state.canonical_node(parent)? else {
            return Ok(None);
        };
        Ok(
            has_fact(state, predicate.filler_predicate_id, &[canonical.node])?
                .then_some(canonical.node),
        )
    }

    fn model_reuse_candidate<S, A, C>(
        state: &mut S,
        access: &mut A,
        filler_predicate_id: u32,
        dependency: &DependencySet,
        control: &mut C,
    ) -> Result<S::Node, ExpansionError>
    where
        S: ExpansionStateMutation,
        A: ExpansionRuleAccess<S>,
        C: ExpansionControl,
    {
        if let Some(known) = state.reuse_node(filler_predicate_id)? {
            if let Some(canonical) = state.canonical_node(known)? {
                if state.node_record(canonical.node)?.is_some() {
                    return Ok(canonical.node);
                }
            }
            state.remove_reuse_node(filler_predicate_id)?;
            control.poll()?;
        }
        let witness = state.create_node(NodeKind::Ni, None)?;
        control.poll()?;
        access.register_node(state, witness, dependency.clone())?;
        control.poll()?;
        dispatch(
            state,
            access,
            filler_predicate_id,
            vec![witness],
            dependency,
            control,
        )?;
        state.set_reuse_node(filler_predicate_id, witness)?;
        control.poll()?;
        Ok(witness)
    }

    fn check_witness_limit(&self, predicate: &AtLeastPredicate) -> Result<(), ExpansionError> {
        let required = if predicate.kind == ObligationKind::Data && predicate.role_ids.len() > 1 {
            u64::try_from(predicate.role_ids.len())
                .map_err(|_| ExpansionError::invariant("n-ary witness count cannot fit u64"))?
        } else {
            u64::from(predicate.cardinality)
        };
        let allowed = u64::from(self.limits.max_witnesses_per_obligation);
        if required > allowed {
            return Err(ExpansionError::resource(
                "existential witness limit exceeded",
                "max_witnesses_per_obligation",
                required,
                allowed,
            ));
        }
        Ok(())
    }

    fn uses_bottom_role(&self, predicate: &AtLeastPredicate) -> bool {
        match predicate.kind {
            ObligationKind::Object => {
                predicate.role_ids.first().copied()
                    == Some(self.program.roles().bottom_object_role_id)
            }
            ObligationKind::Data => predicate
                .role_ids
                .contains(&self.program.roles().bottom_data_role_id),
        }
    }
}

fn dispatch<S, A, C>(
    state: &mut S,
    access: &mut A,
    predicate_id: u32,
    arguments: Vec<S::Node>,
    dependency: &DependencySet,
    control: &mut C,
) -> Result<(), ExpansionError>
where
    S: ExpansionStateMutation,
    A: ExpansionRuleAccess<S>,
    C: ExpansionControl,
{
    dispatch_owned(
        state,
        access,
        predicate_id,
        arguments,
        dependency.clone(),
        control,
    )
}

fn dispatch_owned<S, A, C>(
    state: &mut S,
    access: &mut A,
    predicate_id: u32,
    arguments: Vec<S::Node>,
    dependency: DependencySet,
    control: &mut C,
) -> Result<(), ExpansionError>
where
    S: ExpansionStateMutation,
    A: ExpansionRuleAccess<S>,
    C: ExpansionControl,
{
    access.dispatch_ground_atom(
        state,
        GroundAtom {
            predicate_id,
            arguments,
        },
        dependency,
        true,
    )?;
    control.poll()
}

fn has_fact<S: ExpansionStateRead>(
    state: &S,
    predicate_id: u32,
    arguments: &[S::Node],
) -> Result<bool, ExpansionError> {
    let bindings = arguments
        .iter()
        .copied()
        .enumerate()
        .map(|(position, node)| {
            Ok(FactBinding {
                position: u32::try_from(position)
                    .map_err(|_| ExpansionError::invariant("fact binding position exceeds u32"))?,
                node,
            })
        })
        .collect::<Result<Vec<_>, ExpansionError>>()?;
    Ok(!state.facts(predicate_id, &bindings)?.is_empty())
}

fn binary_target<N: Copy>(arguments: &[N]) -> Result<N, ExpansionError> {
    if arguments.len() != 2 {
        return Err(ExpansionError::invariant(
            "role extension row is not binary",
        ));
    }
    Ok(arguments[1])
}

fn only_role(predicate: &AtLeastPredicate) -> Result<u32, ExpansionError> {
    if predicate.role_ids.len() != 1 {
        return Err(ExpansionError::invariant(
            "unary existential does not have exactly one role",
        ));
    }
    Ok(predicate.role_ids[0])
}

fn minimal_support(supports: &[DependencySet]) -> Result<&DependencySet, ExpansionError> {
    supports
        .iter()
        .min_by_key(|support| dependency_rank(support))
        .ok_or_else(|| ExpansionError::invariant("existential obligation has no support"))
}

fn dependency_rank(value: &DependencySet) -> (usize, Option<u32>, Vec<u32>) {
    (
        value.as_slice().len(),
        value.maximum(),
        value.as_slice().to_vec(),
    )
}

fn ordered_pair<S: ExpansionStateRead>(
    state: &S,
    left: S::Node,
    right: S::Node,
) -> Result<(S::Node, S::Node), ExpansionError> {
    let left_rank = state
        .node_record(left)?
        .ok_or_else(|| ExpansionError::invariant("left distinctness node is unavailable"))?
        .priority;
    let right_rank = state
        .node_record(right)?
        .ok_or_else(|| ExpansionError::invariant("right distinctness node is unavailable"))?
        .priority;
    Ok(if (left_rank, left) <= (right_rank, right) {
        (left, right)
    } else {
        (right, left)
    })
}

fn sorted_nodes<N: Copy + Ord>(values: BTreeMap<N, CandidatePriority>) -> Vec<N> {
    let mut ranked = values
        .into_iter()
        .map(|(node, priority)| (priority, node))
        .collect::<Vec<_>>();
    ranked.sort_unstable();
    ranked.into_iter().map(|(_priority, node)| node).collect()
}

fn usize_from_u32(value: u32) -> Result<usize, ExpansionError> {
    usize::try_from(value)
        .map_err(|_| ExpansionError::invariant("cardinality cannot fit this platform"))
}
