//! Native compiled-clause validator for provisional core blocks.
//!
//! This is the Rust counterpart of the Python backend's
//! `CompiledClauseBlockingValidator`.  It snapshots the complete active extension
//! table once per validation pass, evaluates the two `HermiT` core-blocking checks
//! against that immutable view, and returns only deterministic repair deltas to
//! the blocking manager.  Unsupported non-hypertableau clause shapes reject a
//! provisional block conservatively; they can expose more expansion but cannot
//! make an invalid model appear satisfiable.
// Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
// Modifications Copyright 2026 pyHermiT contributors
// SPDX-License-Identifier: LGPL-3.0-or-later
// Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
// see reports/licensing/adapted-files.toml.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::{
    BlockValidator, BlockingControl, BlockingError, BlockingProjection, BlockingSignature,
    BlockingStateRead, CoreBlockingMode, DirectCheckerKind, FactRecord, NodeKind, NodeLifecycle,
    ValidationDecision,
};
use crate::model::NodeHandle;
use crate::rules::{
    PredicateKind, RuleAtom, RuleClause, RulePredicate, RuleProgram, Term, TermSort,
};
use crate::store::TableauKernel;

const DEFAULT_MAX_MATCHES_PER_BLOCK: u64 = 1_000_000;
const DEFAULT_POLL_INTERVAL: u64 = 256;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ValidationLimits {
    max_matches_per_block: u64,
    cancellation_poll_interval: u64,
}

impl Default for ValidationLimits {
    fn default() -> Self {
        Self {
            max_matches_per_block: DEFAULT_MAX_MATCHES_PER_BLOCK,
            cancellation_poll_interval: DEFAULT_POLL_INTERVAL,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClauseShape {
    clause_index: usize,
    x: u32,
    y_variables: Vec<u32>,
    #[allow(dead_code)]
    z_variables: Vec<u32>,
}

enum ShapeOutcome {
    Irrelevant,
    Unsupported,
    Supported(ClauseShape),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NodeMeta {
    creation_id: u32,
    parent: Option<NodeHandle>,
    blocker: Option<NodeHandle>,
    directly_blocked: bool,
}

#[derive(Clone, Debug)]
struct Snapshot {
    rows: Vec<FactRecord<NodeHandle>>,
    by_predicate: BTreeMap<u32, Vec<usize>>,
    object_nodes: Vec<NodeHandle>,
    nodes: BTreeMap<NodeHandle, NodeMeta>,
}

impl Snapshot {
    fn from_state<C: BlockingControl>(
        state: &TableauKernel,
        control: &C,
    ) -> Result<Self, BlockingError> {
        control.poll()?;
        let mut records = state.node_records()?;
        records.sort_by_key(|record| (record.creation_id, record.key));
        let mut nodes = BTreeMap::new();
        let mut object_nodes = Vec::new();
        for (index, record) in records.into_iter().enumerate() {
            if index % usize::try_from(DEFAULT_POLL_INTERVAL).unwrap_or(256) == 0 {
                control.poll()?;
            }
            if record.lifecycle != NodeLifecycle::Active {
                continue;
            }
            let node = state
                .active_node(record.node)
                .map_err(|error| BlockingError::invariant(error.message))?;
            if nodes
                .insert(
                    record.node,
                    NodeMeta {
                        creation_id: record.creation_id,
                        parent: record.parent,
                        blocker: node.blocker,
                        directly_blocked: node.directly_blocked,
                    },
                )
                .is_some()
            {
                return Err(BlockingError::invariant(
                    "duplicate active node in blocking validation snapshot",
                ));
            }
            if record.kind != NodeKind::Concrete {
                object_nodes.push(record.node);
            }
        }

        let mut rows = state.active_fact_records()?;
        rows.sort_by(|left, right| {
            (left.predicate_id, &left.arguments, left.row_id).cmp(&(
                right.predicate_id,
                &right.arguments,
                right.row_id,
            ))
        });
        let mut by_predicate: BTreeMap<u32, Vec<usize>> = BTreeMap::new();
        for (index, row) in rows.iter().enumerate() {
            if index % usize::try_from(DEFAULT_POLL_INTERVAL).unwrap_or(256) == 0 {
                control.poll()?;
            }
            by_predicate
                .entry(row.predicate_id)
                .or_default()
                .push(index);
        }
        let estimated = rows
            .len()
            .saturating_mul(std::mem::size_of::<FactRecord<NodeHandle>>())
            .saturating_add(
                nodes
                    .len()
                    .saturating_mul(std::mem::size_of::<(NodeHandle, NodeMeta)>()),
            );
        control.observe_memory(u64::try_from(estimated).unwrap_or(u64::MAX))?;
        control.poll()?;
        Ok(Self {
            rows,
            by_predicate,
            object_nodes,
            nodes,
        })
    }

    fn contains(&self, predicate_id: u32, arguments: &[NodeHandle]) -> bool {
        self.by_predicate.get(&predicate_id).is_some_and(|rows| {
            rows.binary_search_by(|index| self.rows[*index].arguments.as_slice().cmp(arguments))
                .is_ok()
        })
    }

    fn meta(&self, node: NodeHandle) -> Result<NodeMeta, BlockingError> {
        self.nodes.get(&node).copied().ok_or_else(|| {
            BlockingError::invariant("blocking validation references a non-active object node")
        })
    }

    fn mirror(&self, node: NodeHandle) -> Result<NodeHandle, BlockingError> {
        Ok(self.meta(node)?.blocker.unwrap_or(node))
    }
}

#[derive(Clone, Copy)]
struct MatchContext<'a> {
    shape: &'a ClauseShape,
    blocked: Option<NodeHandle>,
    distinguished_y: Option<u32>,
    mirror_y: bool,
}

struct Budget<'a, C: BlockingControl> {
    limits: ValidationLimits,
    steps: u64,
    control: &'a C,
}

impl<'a, C: BlockingControl> Budget<'a, C> {
    const fn new(limits: ValidationLimits, control: &'a C) -> Self {
        Self {
            limits,
            steps: 0,
            control,
        }
    }

    fn step(&mut self) -> Result<(), BlockingError> {
        self.steps = self.steps.saturating_add(1);
        if self.steps > self.limits.max_matches_per_block {
            return Err(BlockingError::resource(
                "blocking validation match limit exceeded",
                "blocking_validation_matches",
                self.steps,
                self.limits.max_matches_per_block,
            ));
        }
        if self.steps % self.limits.cancellation_poll_interval == 0 {
            self.control.poll()?;
        }
        Ok(())
    }
}

/// Source shape tables are immutable; a query retains them and compiles only local rows.
pub(crate) struct CompiledBlockingShapes {
    program: RuleProgram,
    base: Option<Arc<Self>>,
    concept_predicates: BTreeSet<u32>,
    object_roles_by_role_id: BTreeMap<u32, Vec<u32>>,
    shapes: Vec<ClauseShape>,
    unsupported_clause_ids: Vec<u32>,
}

impl CompiledBlockingShapes {
    pub(crate) fn new(program: &RuleProgram) -> Result<Self, BlockingError> {
        Self::build(program, None)
    }

    pub(crate) fn extend(base: Arc<Self>, program: &RuleProgram) -> Result<Self, BlockingError> {
        if !program.extends_storage(&base.program) {
            return Err(BlockingError::invalid(
                "blocking shapes require the retained immediate rule-program parent",
            ));
        }
        // RuleProgram checks that sparse overrides only add reciprocal opposite links
        // or union clause provenance. Neither changes a shape or predicate category.
        Self::build(program, Some(base))
    }

    fn build(program: &RuleProgram, base: Option<Arc<Self>>) -> Result<Self, BlockingError> {
        let mut concept_predicates = BTreeSet::new();
        let mut object_roles_by_role_id: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
        let predicate_start = base
            .as_ref()
            .map_or(0, |base| base.program.predicates().len());
        for index in predicate_start..program.predicates().len() {
            let predicate = &program.predicates()[index];
            if is_concept_kind(predicate.kind) {
                concept_predicates.insert(predicate.predicate_id);
            }
            if predicate.kind == PredicateKind::ObjectRole {
                let role_id = predicate.role_id.ok_or_else(|| {
                    BlockingError::invariant("object-role predicate has no role ID")
                })?;
                object_roles_by_role_id
                    .entry(role_id)
                    .or_default()
                    .push(predicate.predicate_id);
            }
        }
        for predicates in object_roles_by_role_id.values_mut() {
            predicates.sort_unstable();
            predicates.dedup();
        }
        let clause_start = base.as_ref().map_or(0, |base| base.program.clauses().len());
        let mut shapes = Vec::new();
        let mut unsupported_clause_ids = Vec::new();
        for clause_index in clause_start..program.clauses().len() {
            let clause = &program.clauses()[clause_index];
            match shape(program, clause_index, clause)? {
                ShapeOutcome::Irrelevant => {}
                ShapeOutcome::Unsupported => unsupported_clause_ids.push(clause.clause_id),
                ShapeOutcome::Supported(value) => shapes.push(value),
            }
        }
        unsupported_clause_ids.sort_unstable();
        Ok(Self {
            program: program.clone(),
            base,
            concept_predicates,
            object_roles_by_role_id,
            shapes,
            unsupported_clause_ids,
        })
    }

    fn segments(&self) -> Vec<&Self> {
        let mut segments = Vec::new();
        let mut current = Some(self);
        while let Some(segment) = current {
            segments.push(segment);
            current = segment.base.as_deref();
        }
        segments.reverse();
        segments
    }

    fn shapes(&self) -> impl Iterator<Item = &ClauseShape> {
        self.segments()
            .into_iter()
            .flat_map(|segment| segment.shapes.iter())
    }

    fn contains_concept(&self, predicate_id: u32) -> bool {
        let mut current = Some(self);
        while let Some(segment) = current {
            if segment.concept_predicates.contains(&predicate_id) {
                return true;
            }
            current = segment.base.as_deref();
        }
        false
    }

    fn role_predicates(&self, role_id: u32) -> impl Iterator<Item = &u32> {
        self.segments().into_iter().flat_map(move |segment| {
            segment
                .object_roles_by_role_id
                .get(&role_id)
                .into_iter()
                .flatten()
        })
    }

    fn first_unsupported(&self) -> Option<u32> {
        self.segments()
            .into_iter()
            .filter_map(|segment| segment.unsupported_clause_ids.first().copied())
            .min()
    }
}

/// Exact validator over retained shapes and one fresh active-state snapshot.
pub(crate) struct CompiledClauseBlockingValidator<'a> {
    program: &'a RuleProgram,
    #[allow(dead_code)]
    core_mode: CoreBlockingMode,
    limits: ValidationLimits,
    compiled: Arc<CompiledBlockingShapes>,
    prepared_snapshot: Option<Snapshot>,
}

impl<'a> CompiledClauseBlockingValidator<'a> {
    #[cfg(test)]
    pub(crate) fn new(
        program: &'a RuleProgram,
        core_mode: CoreBlockingMode,
    ) -> Result<Self, BlockingError> {
        Self::from_shapes(
            program,
            Arc::new(CompiledBlockingShapes::new(program)?),
            core_mode,
        )
    }

    pub(crate) fn from_shapes(
        program: &'a RuleProgram,
        compiled: Arc<CompiledBlockingShapes>,
        core_mode: CoreBlockingMode,
    ) -> Result<Self, BlockingError> {
        if core_mode == CoreBlockingMode::None {
            return Err(BlockingError::invalid(
                "compiled blocking validation requires a core mode",
            ));
        }
        if !program.shares_storage(&compiled.program) {
            return Err(BlockingError::invalid(
                "blocking shapes belong to a different rule program",
            ));
        }
        Ok(Self {
            program,
            core_mode,
            limits: ValidationLimits::default(),
            compiled,
            prepared_snapshot: None,
        })
    }

    fn predicate(&self, predicate_id: u32) -> Result<&RulePredicate, BlockingError> {
        self.program
            .predicate(predicate_id)
            .map_err(|error| BlockingError::invariant(error.message))
    }

    fn clause(&self, shape: &ClauseShape) -> &RuleClause {
        &self.program.clauses()[shape.clause_index]
    }

    fn first_violation<C: BlockingControl>(
        &self,
        snapshot: &Snapshot,
        blocked: NodeHandle,
        blocker: NodeHandle,
        budget: &mut Budget<'_, C>,
    ) -> Result<Option<u32>, BlockingError> {
        let blocked_meta = snapshot.meta(blocked)?;
        let blocker_meta = snapshot.meta(blocker)?;
        let parent = blocked_meta
            .parent
            .ok_or_else(|| BlockingError::invariant("directly blocked tree node has no parent"))?;
        if let Some(violation) =
            self.parent_at_least_violation(snapshot, parent, blocked, budget)?
        {
            return Ok(Some(violation));
        }
        for shape in self.compiled.shapes() {
            if self.parent_clause_invalidates(snapshot, shape, parent, blocked, budget)? {
                return Ok(Some(self.clause(shape).clause_id));
            }
        }
        if let Some(blocker_parent) = blocker_meta.parent {
            if let Some(violation) = self.blocked_at_least_violation(
                snapshot,
                blocked,
                blocker,
                parent,
                blocker_parent,
                budget,
            )? {
                return Ok(Some(violation));
            }
        }
        for shape in self.compiled.shapes() {
            if self.blocked_clause_violation(
                snapshot,
                shape,
                blocked,
                blocker,
                parent,
                blocker_meta.parent,
                budget,
            )? {
                return Ok(Some(self.clause(shape).clause_id));
            }
        }
        Ok(None)
    }

    #[allow(clippy::too_many_arguments)]
    fn blocked_clause_violation<C: BlockingControl>(
        &self,
        snapshot: &Snapshot,
        shape: &ClauseShape,
        blocked: NodeHandle,
        blocker: NodeHandle,
        parent: NodeHandle,
        blocker_parent: Option<NodeHandle>,
        budget: &mut Budget<'_, C>,
    ) -> Result<bool, BlockingError> {
        for distinguished in &shape.y_variables {
            let context = MatchContext {
                shape,
                blocked: Some(blocked),
                distinguished_y: Some(*distinguished),
                mirror_y: false,
            };
            let mut fixed = BTreeMap::new();
            fixed.insert(shape.x, blocker);
            fixed.insert(*distinguished, parent);
            let mut violated = false;
            self.for_each_match(snapshot, fixed, context, budget, &mut |binding| {
                if blocker_parent.is_some_and(|blocker_parent| {
                    shape.y_variables.iter().any(|variable| {
                        variable != distinguished && binding.get(variable) == Some(&blocker_parent)
                    })
                }) {
                    return Ok(true);
                }
                if !self.head_satisfied(snapshot, binding, context)? {
                    violated = true;
                    return Ok(false);
                }
                Ok(true)
            })?;
            if violated {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn parent_clause_invalidates<C: BlockingControl>(
        &self,
        snapshot: &Snapshot,
        shape: &ClauseShape,
        parent: NodeHandle,
        target: NodeHandle,
        budget: &mut Budget<'_, C>,
    ) -> Result<bool, BlockingError> {
        let context = MatchContext {
            shape,
            blocked: None,
            distinguished_y: None,
            mirror_y: true,
        };
        let mut fixed = BTreeMap::new();
        fixed.insert(shape.x, parent);
        let mut invalidates = false;
        self.for_each_match(snapshot, fixed, context, budget, &mut |binding| {
            let mut blocked_values = Vec::new();
            for variable in &shape.y_variables {
                if let Some(node) = binding.get(variable).copied() {
                    if snapshot.meta(node)?.blocker.is_some() {
                        blocked_values.push((*variable, node));
                    }
                }
            }
            if blocked_values.is_empty() || self.head_satisfied(snapshot, binding, context)? {
                return Ok(true);
            }
            let clause = self.clause(shape);
            let mut implicated: Vec<(Reverse<u32>, u32, NodeHandle)> = Vec::new();
            for atom in &clause.body {
                let predicate = self.predicate(atom.predicate_id)?;
                let Some(variable) = unary_y_variable(atom, shape, predicate.kind) else {
                    continue;
                };
                let node = binding[&variable];
                let mirror = snapshot.mirror(node)?;
                if mirror != node
                    && snapshot.contains(atom.predicate_id, &[mirror])
                    && !snapshot.contains(atom.predicate_id, &[node])
                {
                    implicated.push((Reverse(variable), snapshot.meta(node)?.creation_id, node));
                }
            }
            for atom in &clause.head {
                let predicate = self.predicate(atom.predicate_id)?;
                let Some(variable) = unary_y_variable(atom, shape, predicate.kind) else {
                    continue;
                };
                let node = binding[&variable];
                let mirror = snapshot.mirror(node)?;
                if mirror != node
                    && snapshot.contains(atom.predicate_id, &[node])
                    && !snapshot.contains(atom.predicate_id, &[mirror])
                {
                    implicated.push((Reverse(variable), snapshot.meta(node)?.creation_id, node));
                }
            }
            if implicated.is_empty() {
                for (variable, node) in blocked_values {
                    implicated.push((Reverse(variable), snapshot.meta(node)?.creation_id, node));
                }
            }
            implicated.sort_unstable();
            if implicated.first().is_some_and(|value| value.2 == target) {
                invalidates = true;
                return Ok(false);
            }
            Ok(true)
        })?;
        Ok(invalidates)
    }

    fn for_each_match<C, F>(
        &self,
        snapshot: &Snapshot,
        fixed: BTreeMap<u32, NodeHandle>,
        context: MatchContext<'_>,
        budget: &mut Budget<'_, C>,
        callback: &mut F,
    ) -> Result<bool, BlockingError>
    where
        C: BlockingControl,
        F: FnMut(&BTreeMap<u32, NodeHandle>) -> Result<bool, BlockingError>,
    {
        let mut binding = fixed;
        self.visit_match(snapshot, context, budget, callback, &mut binding, 0)
    }

    fn visit_match<C, F>(
        &self,
        snapshot: &Snapshot,
        context: MatchContext<'_>,
        budget: &mut Budget<'_, C>,
        callback: &mut F,
        binding: &mut BTreeMap<u32, NodeHandle>,
        position: usize,
    ) -> Result<bool, BlockingError>
    where
        C: BlockingControl,
        F: FnMut(&BTreeMap<u32, NodeHandle>) -> Result<bool, BlockingError>,
    {
        let clause = self.clause(context.shape);
        if position == clause.join_order.len() {
            return callback(binding);
        }
        let atom_index = usize::try_from(clause.join_order[position])
            .map_err(|_| BlockingError::invariant("join position cannot fit this platform"))?;
        let atom = clause
            .body
            .get(atom_index)
            .ok_or_else(|| BlockingError::invariant("join order references a missing atom"))?;
        let predicate = self.predicate(atom.predicate_id)?;
        if is_concept_kind(predicate.kind) {
            let variable = variable_id(atom.arguments.first()).ok_or_else(|| {
                BlockingError::invariant("validated concept body atom lacks an object variable")
            })?;
            if let Some(existing) = binding.get(&variable).copied() {
                budget.step()?;
                if self.atom_true(snapshot, atom, binding, context)?
                    && !self.visit_match(
                        snapshot,
                        context,
                        budget,
                        callback,
                        binding,
                        position + 1,
                    )?
                {
                    return Ok(false);
                }
                debug_assert_eq!(binding.get(&variable), Some(&existing));
                return Ok(true);
            }
            for candidate in &snapshot.object_nodes {
                budget.step()?;
                binding.insert(variable, *candidate);
                let keep_going = !self.atom_true(snapshot, atom, binding, context)?
                    || self.visit_match(
                        snapshot,
                        context,
                        budget,
                        callback,
                        binding,
                        position + 1,
                    )?;
                binding.remove(&variable);
                if !keep_going {
                    return Ok(false);
                }
            }
            return Ok(true);
        }

        if context.blocked.is_some()
            && context.distinguished_y.is_some()
            && atom_has_variable(atom, context.shape.x)
            && atom_has_variable(atom, context.distinguished_y.unwrap_or_default())
        {
            budget.step()?;
            if self.atom_true(snapshot, atom, binding, context)?
                && !self.visit_match(snapshot, context, budget, callback, binding, position + 1)?
            {
                return Ok(false);
            }
            return Ok(true);
        }

        let row_indices = snapshot.by_predicate.get(&atom.predicate_id);
        for row_index in row_indices.into_iter().flatten() {
            budget.step()?;
            let row = &snapshot.rows[*row_index];
            if row.arguments.len() != atom.arguments.len() {
                return Err(BlockingError::invariant(
                    "active fact arity differs from its validated predicate",
                ));
            }
            let mut added = Vec::new();
            let mut compatible = true;
            for (term, value) in atom.arguments.iter().zip(&row.arguments) {
                let Some(variable) = variable_id(Some(term)) else {
                    compatible = false;
                    break;
                };
                match binding.get(&variable) {
                    Some(known) if known != value => {
                        compatible = false;
                        break;
                    }
                    Some(_) => {}
                    None => {
                        binding.insert(variable, *value);
                        added.push(variable);
                    }
                }
            }
            let keep_going = !compatible
                || !self.atom_true(snapshot, atom, binding, context)?
                || self.visit_match(snapshot, context, budget, callback, binding, position + 1)?;
            for variable in added {
                binding.remove(&variable);
            }
            if !keep_going {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn head_satisfied(
        &self,
        snapshot: &Snapshot,
        binding: &BTreeMap<u32, NodeHandle>,
        context: MatchContext<'_>,
    ) -> Result<bool, BlockingError> {
        for atom in &self.clause(context.shape).head {
            if self.atom_true(snapshot, atom, binding, context)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn atom_true(
        &self,
        snapshot: &Snapshot,
        atom: &RuleAtom,
        binding: &BTreeMap<u32, NodeHandle>,
        context: MatchContext<'_>,
    ) -> Result<bool, BlockingError> {
        let predicate = self.predicate(atom.predicate_id)?;
        let mut arguments = Vec::with_capacity(atom.arguments.len());
        for term in &atom.arguments {
            let Some(variable) = variable_id(Some(term)) else {
                return Ok(false);
            };
            let Some(mut value) = binding.get(&variable).copied() else {
                return Ok(false);
            };
            if is_concept_kind(predicate.kind)
                && context.mirror_y
                && context.shape.y_variables.contains(&variable)
            {
                value = snapshot.mirror(value)?;
            }
            arguments.push(value);
        }
        if predicate.kind == PredicateKind::ObjectRole {
            if let (Some(blocked), Some(distinguished)) = (context.blocked, context.distinguished_y)
            {
                if atom_has_variable(atom, distinguished) {
                    for (index, term) in atom.arguments.iter().enumerate() {
                        if variable_id(Some(term)) == Some(context.shape.x) {
                            arguments[index] = blocked;
                        }
                    }
                }
            }
        }
        Ok(match predicate.kind {
            PredicateKind::Equality | PredicateKind::AnnotatedEquality => {
                arguments.len() >= 2 && arguments[0] == arguments[1]
            }
            PredicateKind::Inequality => {
                arguments.len() == 2 && snapshot.contains(atom.predicate_id, &arguments)
            }
            _ => snapshot.contains(atom.predicate_id, &arguments),
        })
    }

    fn parent_at_least_violation<C: BlockingControl>(
        &self,
        snapshot: &Snapshot,
        parent: NodeHandle,
        target: NodeHandle,
        budget: &mut Budget<'_, C>,
    ) -> Result<Option<u32>, BlockingError> {
        for row in &snapshot.rows {
            if row.arguments.as_slice() != [parent] {
                continue;
            }
            let predicate = self.predicate(row.predicate_id)?;
            if predicate.kind != PredicateKind::AtLeastObject {
                continue;
            }
            let (cardinality, filler) = at_least_parts(predicate)?;
            let successors = self.successors(snapshot, predicate, parent)?;
            let mut suitable = 0_u32;
            let mut candidates = Vec::new();
            for successor in successors {
                budget.step()?;
                let mirror = snapshot.mirror(successor)?;
                if snapshot.contains(filler, &[mirror]) {
                    suitable = suitable.saturating_add(1);
                } else if mirror != successor && snapshot.contains(filler, &[successor]) {
                    candidates.push(successor);
                }
            }
            if suitable >= cardinality {
                continue;
            }
            let needed = usize::try_from(cardinality - suitable).unwrap_or(usize::MAX);
            candidates.sort_by_key(|node| {
                snapshot
                    .meta(*node)
                    .map_or((u32::MAX, *node), |meta| (meta.creation_id, *node))
            });
            if candidates
                .into_iter()
                .take(needed)
                .any(|node| node == target)
            {
                return self
                    .validation_predicate_violation(predicate.predicate_id)
                    .map(Some);
            }
        }
        Ok(None)
    }

    #[allow(clippy::too_many_arguments)]
    fn blocked_at_least_violation<C: BlockingControl>(
        &self,
        snapshot: &Snapshot,
        blocked: NodeHandle,
        blocker: NodeHandle,
        parent: NodeHandle,
        blocker_parent: NodeHandle,
        budget: &mut Budget<'_, C>,
    ) -> Result<Option<u32>, BlockingError> {
        for row in &snapshot.rows {
            if row.arguments.as_slice() != [blocker] {
                continue;
            }
            let predicate = self.predicate(row.predicate_id)?;
            if predicate.kind != PredicateKind::AtLeastObject {
                continue;
            }
            let (cardinality, filler) = at_least_parts(predicate)?;
            let blocker_successors = self.successors(snapshot, predicate, blocker)?;
            if !blocker_successors.contains(&blocker_parent)
                || !snapshot.contains(filler, &[blocker_parent])
            {
                continue;
            }
            let blocked_successors = self.successors(snapshot, predicate, blocked)?;
            if blocked_successors.contains(&parent) && snapshot.contains(filler, &[parent]) {
                continue;
            }
            let mut suitable = 0_u32;
            for successor in blocker_successors {
                budget.step()?;
                if successor != blocker_parent && snapshot.contains(filler, &[successor]) {
                    suitable = suitable.saturating_add(1);
                }
            }
            if suitable < cardinality {
                return self
                    .validation_predicate_violation(predicate.predicate_id)
                    .map(Some);
            }
        }
        Ok(None)
    }

    fn successors(
        &self,
        snapshot: &Snapshot,
        predicate: &RulePredicate,
        source: NodeHandle,
    ) -> Result<Vec<NodeHandle>, BlockingError> {
        let role_id = predicate
            .role_id
            .ok_or_else(|| BlockingError::invariant("at-least predicate has no role ID"))?;
        let mut values = BTreeSet::new();
        for predicate_id in self.compiled.role_predicates(role_id) {
            for row_index in snapshot
                .by_predicate
                .get(predicate_id)
                .into_iter()
                .flatten()
            {
                let row = &snapshot.rows[*row_index];
                if row.arguments.len() == 2 && row.arguments[0] == source {
                    values.insert(row.arguments[1]);
                }
            }
        }
        Ok(values.into_iter().collect())
    }

    fn validation_predicate_violation(&self, predicate_id: u32) -> Result<u32, BlockingError> {
        let clause_count = u32::try_from(self.program.clauses().len()).map_err(|_| {
            BlockingError::invariant("compiled clause count exceeds validation ID domain")
        })?;
        clause_count
            .checked_add(predicate_id)
            .ok_or_else(|| BlockingError::invariant("blocking validation violation ID overflow"))
    }

    fn repair_rows(
        &self,
        snapshot: &Snapshot,
        blocked: NodeHandle,
        blocker: NodeHandle,
    ) -> Result<Vec<u32>, BlockingError> {
        let mut pairs = vec![(blocked, blocker)];
        let blocked_parent = snapshot.meta(blocked)?.parent;
        let blocker_parent = snapshot.meta(blocker)?.parent;
        if let (Some(left), Some(right)) = (blocked_parent, blocker_parent) {
            pairs.push((left, right));
        }
        let mut selected = BTreeSet::new();
        for (left, right) in pairs {
            let left_labels = self.concept_labels(snapshot, left);
            let right_labels = self.concept_labels(snapshot, right);
            let difference = left_labels
                .symmetric_difference(&right_labels)
                .copied()
                .collect::<BTreeSet<_>>();
            for row in &snapshot.rows {
                if !row.core
                    && difference.contains(&row.predicate_id)
                    && (row.arguments.as_slice() == [left] || row.arguments.as_slice() == [right])
                {
                    selected.insert(row.row_id);
                }
            }
        }
        Ok(selected.into_iter().collect())
    }

    fn concept_labels(&self, snapshot: &Snapshot, node: NodeHandle) -> BTreeSet<u32> {
        snapshot
            .rows
            .iter()
            .filter(|row| {
                row.arguments.as_slice() == [node]
                    && self.compiled.contains_concept(row.predicate_id)
            })
            .map(|row| row.predicate_id)
            .collect()
    }
}

impl BlockValidator<TableauKernel> for CompiledClauseBlockingValidator<'_> {
    fn begin_pass<C: BlockingControl>(
        &mut self,
        state: &TableauKernel,
        _projection: &BlockingProjection<NodeHandle>,
        control: &C,
    ) -> Result<(), BlockingError> {
        if self.prepared_snapshot.is_some() {
            return Err(BlockingError::invariant(
                "blocking validator already has an active pass",
            ));
        }
        self.prepared_snapshot = Some(Snapshot::from_state(state, control)?);
        Ok(())
    }

    fn validate_block<C: BlockingControl>(
        &mut self,
        state: &TableauKernel,
        _projection: &BlockingProjection<NodeHandle>,
        blocked: NodeHandle,
        blocker: NodeHandle,
        signature: &BlockingSignature,
        control: &C,
    ) -> Result<ValidationDecision<NodeHandle>, BlockingError> {
        if !matches!(
            signature.kind,
            DirectCheckerKind::ValidatedSingle | DirectCheckerKind::ValidatedPairwise
        ) {
            return Err(BlockingError::invalid(
                "compiled validation requires a validated signature",
            ));
        }
        control.poll()?;
        let local_snapshot;
        let snapshot = if let Some(value) = self.prepared_snapshot.as_ref() {
            value
        } else {
            local_snapshot = Snapshot::from_state(state, control)?;
            &local_snapshot
        };
        let blocked_meta = snapshot.meta(blocked)?;
        snapshot.meta(blocker)?;
        if !blocked_meta.directly_blocked || blocked_meta.blocker != Some(blocker) {
            return Err(BlockingError::invalid(
                "blocked must be directly blocked by blocker",
            ));
        }
        let mut budget = Budget::new(self.limits, control);
        let mut violation = self.first_violation(snapshot, blocked, blocker, &mut budget)?;
        if violation.is_none() {
            violation = self.compiled.first_unsupported();
        }
        let Some(violation) = violation else {
            return Ok(ValidationDecision::valid());
        };
        ValidationDecision::invalid(
            self.repair_rows(snapshot, blocked, blocker)?,
            vec![blocked],
            vec![violation],
        )
    }

    fn end_pass(&mut self) {
        self.prepared_snapshot = None;
    }
}

fn shape(
    program: &RuleProgram,
    clause_index: usize,
    clause: &RuleClause,
) -> Result<ShapeOutcome, BlockingError> {
    let mut relevant = false;
    for atom in clause.body.iter().chain(&clause.head) {
        let kind = program
            .predicate_kind(atom.predicate_id)
            .map_err(|error| BlockingError::invariant(error.message))?;
        relevant |= is_concept_kind(kind)
            || matches!(
                kind,
                PredicateKind::AtLeastObject | PredicateKind::AnnotatedEquality
            );
    }
    if !relevant {
        return Ok(ShapeOutcome::Irrelevant);
    }
    let x = 0_u32;
    let mut variables = BTreeSet::new();
    for atom in clause.body.iter().chain(&clause.head) {
        for term in &atom.arguments {
            let Term::Variable { sort, variable_id } = term else {
                return Ok(ShapeOutcome::Unsupported);
            };
            if *sort != TermSort::Object {
                return Ok(ShapeOutcome::Unsupported);
            }
            variables.insert(*variable_id);
        }
    }
    if !variables.contains(&x) {
        return Ok(ShapeOutcome::Irrelevant);
    }
    let mut y_variables = BTreeSet::new();
    for atom in &clause.body {
        let kind = program
            .predicate_kind(atom.predicate_id)
            .map_err(|error| BlockingError::invariant(error.message))?;
        if is_concept_kind(kind) {
            if atom.arguments.len() != 1 {
                return Ok(ShapeOutcome::Unsupported);
            }
            continue;
        }
        if kind != PredicateKind::ObjectRole || atom.arguments.len() != 2 {
            return Ok(ShapeOutcome::Unsupported);
        }
        let Some(left) = variable_id(atom.arguments.first()) else {
            return Ok(ShapeOutcome::Unsupported);
        };
        let Some(right) = variable_id(atom.arguments.get(1)) else {
            return Ok(ShapeOutcome::Unsupported);
        };
        if left != x && right != x {
            return Ok(ShapeOutcome::Unsupported);
        }
        if left != x {
            y_variables.insert(left);
        }
        if right != x {
            y_variables.insert(right);
        }
    }
    for atom in &clause.head {
        let kind = program
            .predicate_kind(atom.predicate_id)
            .map_err(|error| BlockingError::invariant(error.message))?;
        if atom.arguments.iter().any(|term| {
            !matches!(
                term,
                Term::Variable {
                    sort: TermSort::Object,
                    ..
                }
            )
        }) || matches!(
            kind,
            PredicateKind::DataRole
                | PredicateKind::NegatedDataRole
                | PredicateKind::DataRange
                | PredicateKind::NegatedDataRange
                | PredicateKind::AtLeastData
        ) {
            return Ok(ShapeOutcome::Unsupported);
        }
    }
    let z_variables = variables
        .difference(&y_variables)
        .copied()
        .filter(|variable| *variable != x)
        .collect::<Vec<_>>();
    if y_variables.is_empty() && z_variables.is_empty() {
        return Ok(ShapeOutcome::Irrelevant);
    }
    Ok(ShapeOutcome::Supported(ClauseShape {
        clause_index,
        x,
        y_variables: y_variables.into_iter().collect(),
        z_variables,
    }))
}

const fn is_concept_kind(kind: PredicateKind) -> bool {
    matches!(
        kind,
        PredicateKind::Concept
            | PredicateKind::NegatedConcept
            | PredicateKind::Nominal
            | PredicateKind::NegatedNominal
            | PredicateKind::AutomatonState
            | PredicateKind::DisjointGuard
            | PredicateKind::NamedIndividual
    )
}

const fn variable_id(term: Option<&Term>) -> Option<u32> {
    match term {
        Some(Term::Variable {
            sort: TermSort::Object,
            variable_id,
        }) => Some(*variable_id),
        _ => None,
    }
}

fn atom_has_variable(atom: &RuleAtom, variable: u32) -> bool {
    atom.arguments
        .iter()
        .any(|term| variable_id(Some(term)) == Some(variable))
}

fn unary_y_variable(atom: &RuleAtom, shape: &ClauseShape, kind: PredicateKind) -> Option<u32> {
    if !is_concept_kind(kind) || atom.arguments.len() != 1 {
        return None;
    }
    variable_id(atom.arguments.first()).filter(|value| shape.y_variables.contains(value))
}

fn at_least_parts(predicate: &RulePredicate) -> Result<(u32, u32), BlockingError> {
    predicate
        .cardinality
        .zip(predicate.filler_predicate_id)
        .ok_or_else(|| BlockingError::invariant("at-least predicate metadata is incomplete"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blocking::{BlockingVocabulary, NeverCancel};
    use crate::model::{DependencySet, NodeKind as StoreNodeKind};

    fn predicate(
        id: u32,
        kind: PredicateKind,
        sorts: Vec<TermSort>,
    ) -> Result<RulePredicate, BlockingError> {
        let predicate = RulePredicate::new(id, kind, sorts)
            .map_err(|error| BlockingError::invariant(error.message))?;
        Ok(
            if matches!(
                kind,
                PredicateKind::Concept
                    | PredicateKind::NegatedConcept
                    | PredicateKind::Nominal
                    | PredicateKind::NegatedNominal
                    | PredicateKind::DataRange
                    | PredicateKind::NegatedDataRange
            ) {
                predicate.with_symbol_id(id)
            } else {
                predicate
            },
        )
    }

    fn node(
        kernel: &mut TableauKernel,
        kind: StoreNodeKind,
        parent: Option<NodeHandle>,
    ) -> Result<NodeHandle, BlockingError> {
        kernel
            .create_node(kind, parent, false, None, None, None)
            .map_err(|error| BlockingError::invariant(error.message))
    }

    fn fact(
        kernel: &mut TableauKernel,
        predicate_id: u32,
        arguments: Vec<NodeHandle>,
        core: bool,
    ) -> Result<u32, BlockingError> {
        kernel
            .add_fact(predicate_id, arguments, DependencySet::empty(), core, None)
            .map_err(|error| BlockingError::invariant(error.message))
    }

    fn validated_signature() -> Result<BlockingSignature, BlockingError> {
        BlockingSignature::new(
            DirectCheckerKind::ValidatedSingle,
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
    }

    fn clause(
        clause_id: u32,
        body: Vec<RuleAtom>,
        head: Vec<RuleAtom>,
        join_order: Vec<u32>,
    ) -> Result<RuleClause, BlockingError> {
        RuleClause::new(clause_id, body, head, vec![0], join_order)
            .map_err(|error| BlockingError::invariant(error.message))
    }

    fn atom(predicate_id: u32, variables: &[u32]) -> Result<RuleAtom, BlockingError> {
        RuleAtom::new(
            predicate_id,
            variables
                .iter()
                .map(|variable| Term::variable(*variable, TermSort::Object))
                .collect(),
        )
        .map_err(|error| BlockingError::invariant(error.message))
    }

    struct Cancelled;

    impl BlockingControl for Cancelled {
        fn poll(&self) -> Result<(), BlockingError> {
            Err(BlockingError::cancelled("test cancellation"))
        }
    }

    fn shape_program(unrelated: u32) -> Result<RuleProgram, BlockingError> {
        let mut predicates = vec![
            predicate(0, PredicateKind::Concept, vec![TermSort::Object])?,
            predicate(
                1,
                PredicateKind::ObjectRole,
                vec![TermSort::Object, TermSort::Object],
            )?
            .with_role_id(4),
            predicate(2, PredicateKind::Concept, vec![TermSort::Object])?,
        ];
        let mut clauses = Vec::new();
        for id in 0..unrelated {
            predicates.push(predicate(
                id + 3,
                PredicateKind::Concept,
                vec![TermSort::Object],
            )?);
            clauses.push(clause(
                id,
                vec![atom(id + 3, &[0])?],
                vec![atom(2, &[0])?],
                vec![0],
            )?);
        }
        RuleProgram::new(predicates, clauses)
            .map_err(|error| BlockingError::invariant(error.message))
    }

    fn edge_clause(id: u32) -> Result<RuleClause, BlockingError> {
        clause(
            id,
            vec![atom(1, &[0, 1])?, atom(0, &[0])?],
            vec![atom(2, &[1])?],
            vec![1, 0],
        )
    }

    #[test]
    fn retained_shapes_only_compile_query_rows_with_unrelated_source_clauses(
    ) -> Result<(), BlockingError> {
        for unrelated in [0, 1_000] {
            let source = shape_program(unrelated)?;
            let base = Arc::new(CompiledBlockingShapes::new(&source)?);
            let query = RuleProgram::extend(
                &source,
                Vec::new(),
                Vec::new(),
                vec![edge_clause(unrelated)?],
            )
            .map_err(|error| BlockingError::invariant(error.message))?;
            let derived = CompiledBlockingShapes::extend(Arc::clone(&base), &query)?;
            assert!(derived
                .base
                .as_ref()
                .is_some_and(|parent| Arc::ptr_eq(parent, &base)));
            assert_eq!(derived.shapes.len(), 1);
            assert!(derived.concept_predicates.is_empty());
            assert!(derived.object_roles_by_role_id.is_empty());
            assert!(derived.unsupported_clause_ids.is_empty());
            assert_eq!(
                derived.shapes().collect::<Vec<_>>(),
                CompiledBlockingShapes::new(&query)?
                    .shapes()
                    .collect::<Vec<_>>()
            );
            assert_eq!(
                derived.role_predicates(4).copied().collect::<Vec<_>>(),
                vec![1]
            );
            assert!(derived.contains_concept(0));
            assert!(!derived.contains_concept(1));
        }
        Ok(())
    }

    #[test]
    fn sparse_same_semantics_overrides_reuse_shapes_and_preserve_current_rows(
    ) -> Result<(), BlockingError> {
        let source = RuleProgram::extend(
            &shape_program(0)?,
            Vec::new(),
            Vec::new(),
            vec![edge_clause(0)?],
        )
        .map_err(|error| BlockingError::invariant(error.message))?;
        let base = Arc::new(CompiledBlockingShapes::new(&source)?);
        let negative = predicate(3, PredicateKind::NegatedConcept, vec![TermSort::Object])?
            .with_symbol_id(0)
            .with_opposite(0);
        let opposite = source
            .predicate(0)
            .map_err(|error| BlockingError::invariant(error.message))?
            .clone()
            .with_opposite(3);
        let mut duplicate = edge_clause(1)?;
        duplicate.provenance_ids = vec![9];
        let query = RuleProgram::extend(&source, vec![negative], vec![opposite], vec![duplicate])
            .map_err(|error| BlockingError::invariant(error.message))?;
        let derived = Arc::new(CompiledBlockingShapes::extend(Arc::clone(&base), &query)?);
        assert!(derived.shapes.is_empty());
        assert_eq!(derived.concept_predicates, BTreeSet::from([3]));
        assert_eq!(
            derived.shapes().collect::<Vec<_>>(),
            CompiledBlockingShapes::new(&query)?
                .shapes()
                .collect::<Vec<_>>()
        );
        let validator = CompiledClauseBlockingValidator::from_shapes(
            &query,
            Arc::clone(&derived),
            CoreBlockingMode::Simple,
        )?;
        let first = derived
            .shapes()
            .next()
            .ok_or_else(|| BlockingError::invariant("missing retained shape"))?;
        assert_eq!(validator.clause(first).provenance_ids, vec![0, 9]);
        assert_eq!(source.clauses()[0].provenance_ids, vec![0]);
        assert_eq!(source.predicates()[0].opposite_predicate_id, None);
        assert!(derived.contains_concept(3));
        assert!(!base.contains_concept(3));
        assert!(validator.prepared_snapshot.is_none());
        Ok(())
    }

    #[test]
    fn shape_handoff_rejects_equal_but_independently_owned_programs() -> Result<(), BlockingError> {
        let source = shape_program(0)?;
        let identical = shape_program(0)?;
        let base = Arc::new(CompiledBlockingShapes::new(&source)?);
        assert!(CompiledClauseBlockingValidator::from_shapes(
            &identical,
            Arc::clone(&base),
            CoreBlockingMode::Simple
        )
        .is_err());
        let query = RuleProgram::extend(&identical, Vec::new(), Vec::new(), vec![edge_clause(0)?])
            .map_err(|error| BlockingError::invariant(error.message))?;
        assert!(CompiledBlockingShapes::extend(Arc::clone(&base), &query).is_err());
        assert!(CompiledClauseBlockingValidator::from_shapes(
            &source,
            Arc::clone(&base),
            CoreBlockingMode::None
        )
        .is_err());
        let cloned = source.clone();
        let validator =
            CompiledClauseBlockingValidator::from_shapes(&cloned, base, CoreBlockingMode::Simple)?;
        assert!(validator.prepared_snapshot.is_none());
        Ok(())
    }

    #[test]
    fn unsupported_source_shapes_remain_conservative_after_query_extension(
    ) -> Result<(), BlockingError> {
        let initial = shape_program(0)?;
        let body = RuleAtom::new(0, vec![Term::individual(0)])
            .map_err(|error| BlockingError::invariant(error.message))?;
        let head = RuleAtom::new(2, vec![Term::individual(0)])
            .map_err(|error| BlockingError::invariant(error.message))?;
        let source = RuleProgram::extend(
            &initial,
            Vec::new(),
            Vec::new(),
            vec![clause(0, vec![body], vec![head], vec![0])?],
        )
        .map_err(|error| BlockingError::invariant(error.message))?;
        let base = Arc::new(CompiledBlockingShapes::new(&source)?);
        let query = RuleProgram::extend(&source, Vec::new(), Vec::new(), vec![edge_clause(1)?])
            .map_err(|error| BlockingError::invariant(error.message))?;
        let derived = CompiledBlockingShapes::extend(base, &query)?;
        assert_eq!(derived.first_unsupported(), Some(0));
        assert_eq!(
            derived.first_unsupported(),
            CompiledBlockingShapes::new(&query)?.first_unsupported()
        );
        assert!(derived.unsupported_clause_ids.is_empty());
        Ok(())
    }

    #[test]
    fn retained_query_shapes_match_fresh_validation_and_capture_new_fact_state(
    ) -> Result<(), BlockingError> {
        let source = shape_program(0)?;
        let base = Arc::new(CompiledBlockingShapes::new(&source)?);
        let query = RuleProgram::extend(&source, Vec::new(), Vec::new(), vec![edge_clause(0)?])
            .map_err(|error| BlockingError::invariant(error.message))?;
        let derived = Arc::new(CompiledBlockingShapes::extend(base, &query)?);
        let mut kernel = TableauKernel::new();
        let blocker_parent = node(&mut kernel, StoreNodeKind::Ni, None)?;
        let blocker = node(&mut kernel, StoreNodeKind::Tree, Some(blocker_parent))?;
        let blocked_parent = node(&mut kernel, StoreNodeKind::Ni, None)?;
        let blocked = node(&mut kernel, StoreNodeKind::Tree, Some(blocked_parent))?;
        kernel
            .set_blocked(blocked, Some(blocker), true)
            .map_err(|error| BlockingError::invariant(error.message))?;
        fact(&mut kernel, 0, vec![blocker], true)?;
        fact(&mut kernel, 0, vec![blocked], true)?;
        fact(&mut kernel, 1, vec![blocker, blocker_parent], false)?;
        fact(&mut kernel, 2, vec![blocker_parent], false)?;
        fact(&mut kernel, 1, vec![blocked, blocked_parent], false)?;
        let vocabulary = BlockingVocabulary::new([0, 2], [1])?;
        let projection = BlockingProjection::from_state(
            &kernel,
            &vocabulary,
            super::super::BlockingLimits::default(),
            &NeverCancel,
        )?;
        let mut retained = CompiledClauseBlockingValidator::from_shapes(
            &query,
            Arc::clone(&derived),
            CoreBlockingMode::Simple,
        )?;
        let mut fresh = CompiledClauseBlockingValidator::new(&query, CoreBlockingMode::Simple)?;
        assert!(retained
            .begin_pass(&kernel, &projection, &Cancelled)
            .is_err());
        assert!(retained.prepared_snapshot.is_none());
        retained.begin_pass(&kernel, &projection, &NeverCancel)?;
        let decision = retained.validate_block(
            &kernel,
            &projection,
            blocked,
            blocker,
            &validated_signature()?,
            &NeverCancel,
        )?;
        let expected = fresh.validate_block(
            &kernel,
            &projection,
            blocked,
            blocker,
            &validated_signature()?,
            &NeverCancel,
        )?;
        assert_eq!(decision, expected);
        assert_eq!(decision.violation_ids, vec![0]);
        retained.end_pass();
        fact(&mut kernel, 2, vec![blocked_parent], false)?;
        retained.begin_pass(&kernel, &projection, &NeverCancel)?;
        let repaired = retained.validate_block(
            &kernel,
            &projection,
            blocked,
            blocker,
            &validated_signature()?,
            &NeverCancel,
        )?;
        assert!(repaired.valid);
        let second = CompiledClauseBlockingValidator::from_shapes(
            &query,
            Arc::clone(&derived),
            CoreBlockingMode::Simple,
        )?;
        assert!(Arc::ptr_eq(&retained.compiled, &second.compiled));
        assert!(retained.prepared_snapshot.is_some());
        assert!(second.prepared_snapshot.is_none());
        Ok(())
    }

    #[test]
    fn blocked_x_edge_context_detects_missing_filler() -> Result<(), BlockingError> {
        let source = predicate(0, PredicateKind::Concept, vec![TermSort::Object])?;
        let role = predicate(
            1,
            PredicateKind::ObjectRole,
            vec![TermSort::Object, TermSort::Object],
        )?
        .with_role_id(4);
        let filler = predicate(2, PredicateKind::Concept, vec![TermSort::Object])?;
        let rule = clause(
            0,
            vec![atom(1, &[0, 1])?, atom(0, &[0])?],
            vec![atom(2, &[1])?],
            vec![1, 0],
        )?;
        let program = RuleProgram::new(vec![source, role, filler], vec![rule])
            .map_err(|error| BlockingError::invariant(error.message))?;
        let mut kernel = TableauKernel::new();
        let blocker_parent = node(&mut kernel, StoreNodeKind::Ni, None)?;
        let blocker = node(&mut kernel, StoreNodeKind::Tree, Some(blocker_parent))?;
        let blocked_parent = node(&mut kernel, StoreNodeKind::Ni, None)?;
        let blocked = node(&mut kernel, StoreNodeKind::Tree, Some(blocked_parent))?;
        kernel
            .set_blocked(blocked, Some(blocker), true)
            .map_err(|error| BlockingError::invariant(error.message))?;
        fact(&mut kernel, 0, vec![blocker], true)?;
        fact(&mut kernel, 0, vec![blocked], true)?;
        fact(&mut kernel, 1, vec![blocker, blocker_parent], false)?;
        fact(&mut kernel, 2, vec![blocker_parent], false)?;
        fact(&mut kernel, 1, vec![blocked, blocked_parent], false)?;
        let vocabulary = BlockingVocabulary::new([0, 2], [1])?;
        let projection = BlockingProjection::from_state(
            &kernel,
            &vocabulary,
            super::super::BlockingLimits::default(),
            &NeverCancel,
        )?;
        let mut validator =
            CompiledClauseBlockingValidator::new(&program, CoreBlockingMode::Simple)?;
        let decision = validator.validate_block(
            &kernel,
            &projection,
            blocked,
            blocker,
            &validated_signature()?,
            &NeverCancel,
        )?;
        assert!(!decision.valid);
        assert_eq!(decision.violation_ids, vec![0]);

        fact(&mut kernel, 2, vec![blocked_parent], false)?;
        let repaired = validator.validate_block(
            &kernel,
            &projection,
            blocked,
            blocker,
            &validated_signature()?,
            &NeverCancel,
        )?;
        assert!(repaired.valid);
        Ok(())
    }

    #[test]
    fn parent_mirroring_selects_target_and_noncore_repair_row() -> Result<(), BlockingError> {
        let filler = predicate(0, PredicateKind::Concept, vec![TermSort::Object])?;
        let role = predicate(
            1,
            PredicateKind::ObjectRole,
            vec![TermSort::Object, TermSort::Object],
        )?
        .with_role_id(4);
        let consequence = predicate(2, PredicateKind::Concept, vec![TermSort::Object])?;
        let rule = clause(
            0,
            vec![atom(1, &[0, 1])?, atom(0, &[1])?],
            vec![atom(2, &[0])?],
            vec![0, 1],
        )?;
        let program = RuleProgram::new(vec![filler, role, consequence], vec![rule])
            .map_err(|error| BlockingError::invariant(error.message))?;
        let mut kernel = TableauKernel::new();
        let blocker_parent = node(&mut kernel, StoreNodeKind::Ni, None)?;
        let blocker = node(&mut kernel, StoreNodeKind::Tree, Some(blocker_parent))?;
        let blocked_parent = node(&mut kernel, StoreNodeKind::Ni, None)?;
        let blocked = node(&mut kernel, StoreNodeKind::Tree, Some(blocked_parent))?;
        kernel
            .set_blocked(blocked, Some(blocker), true)
            .map_err(|error| BlockingError::invariant(error.message))?;
        let filler_row = fact(&mut kernel, 0, vec![blocker], false)?;
        fact(&mut kernel, 1, vec![blocked_parent, blocked], false)?;
        let vocabulary = BlockingVocabulary::new([0, 2], [1])?;
        let projection = BlockingProjection::from_state(
            &kernel,
            &vocabulary,
            super::super::BlockingLimits::default(),
            &NeverCancel,
        )?;
        let mut validator =
            CompiledClauseBlockingValidator::new(&program, CoreBlockingMode::Simple)?;
        let decision = validator.validate_block(
            &kernel,
            &projection,
            blocked,
            blocker,
            &validated_signature()?,
            &NeverCancel,
        )?;
        assert!(!decision.valid);
        assert_eq!(decision.promote_fact_ids, vec![filler_row]);
        assert_eq!(decision.reschedule_nodes, vec![blocked]);
        assert_eq!(decision.violation_ids, vec![0]);
        Ok(())
    }

    #[test]
    fn parent_at_least_rejection_matches_python_repair_contract() -> Result<(), BlockingError> {
        let filler = predicate(0, PredicateKind::Concept, vec![TermSort::Object])?;
        let role = predicate(
            1,
            PredicateKind::ObjectRole,
            vec![TermSort::Object, TermSort::Object],
        )?
        .with_role_id(7);
        let at_least = predicate(2, PredicateKind::AtLeastObject, vec![TermSort::Object])?
            .with_cardinality(1, 7, 0);
        let program = RuleProgram::new(vec![filler, role, at_least], Vec::new())
            .map_err(|error| BlockingError::invariant(error.message))?;
        let mut kernel = TableauKernel::new();
        let parent = kernel
            .create_node(StoreNodeKind::Root, None, false, None, None, None)
            .map_err(|error| BlockingError::invariant(error.message))?;
        let blocker = kernel
            .create_node(StoreNodeKind::Tree, Some(parent), false, None, None, None)
            .map_err(|error| BlockingError::invariant(error.message))?;
        let blocked = kernel
            .create_node(StoreNodeKind::Tree, Some(parent), false, None, None, None)
            .map_err(|error| BlockingError::invariant(error.message))?;
        kernel
            .set_blocked(blocked, Some(blocker), true)
            .map_err(|error| BlockingError::invariant(error.message))?;
        kernel
            .add_fact(2, vec![parent], DependencySet::empty(), true, None)
            .map_err(|error| BlockingError::invariant(error.message))?;
        kernel
            .add_fact(1, vec![parent, blocked], DependencySet::empty(), true, None)
            .map_err(|error| BlockingError::invariant(error.message))?;
        let filler_row = kernel
            .add_fact(0, vec![blocked], DependencySet::empty(), false, None)
            .map_err(|error| BlockingError::invariant(error.message))?;
        let vocabulary = BlockingVocabulary::new([0], [1])?;
        let projection = BlockingProjection::from_state(
            &kernel,
            &vocabulary,
            super::super::BlockingLimits::default(),
            &NeverCancel,
        )?;
        let signature = BlockingSignature::new(
            DirectCheckerKind::ValidatedSingle,
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )?;
        let mut validator =
            CompiledClauseBlockingValidator::new(&program, CoreBlockingMode::Simple)?;
        validator.begin_pass(&kernel, &projection, &NeverCancel)?;
        let decision = validator.validate_block(
            &kernel,
            &projection,
            blocked,
            blocker,
            &signature,
            &NeverCancel,
        )?;
        validator.end_pass();
        assert!(!decision.valid);
        assert_eq!(decision.promote_fact_ids, vec![filler_row]);
        assert_eq!(decision.reschedule_nodes, vec![blocked]);
        assert_eq!(decision.violation_ids, vec![2]);
        Ok(())
    }

    #[test]
    fn mirrored_filler_makes_parent_at_least_block_valid() -> Result<(), BlockingError> {
        let filler = predicate(0, PredicateKind::Concept, vec![TermSort::Object])?;
        let role = predicate(
            1,
            PredicateKind::ObjectRole,
            vec![TermSort::Object, TermSort::Object],
        )?
        .with_role_id(7);
        let at_least = predicate(2, PredicateKind::AtLeastObject, vec![TermSort::Object])?
            .with_cardinality(1, 7, 0);
        let program = RuleProgram::new(vec![filler, role, at_least], Vec::new())
            .map_err(|error| BlockingError::invariant(error.message))?;
        let mut kernel = TableauKernel::new();
        let parent = kernel
            .create_node(StoreNodeKind::Root, None, false, None, None, None)
            .map_err(|error| BlockingError::invariant(error.message))?;
        let blocker = kernel
            .create_node(StoreNodeKind::Tree, Some(parent), false, None, None, None)
            .map_err(|error| BlockingError::invariant(error.message))?;
        let blocked = kernel
            .create_node(StoreNodeKind::Tree, Some(parent), false, None, None, None)
            .map_err(|error| BlockingError::invariant(error.message))?;
        kernel
            .set_blocked(blocked, Some(blocker), true)
            .map_err(|error| BlockingError::invariant(error.message))?;
        for (predicate_id, arguments) in [
            (2, vec![parent]),
            (1, vec![parent, blocked]),
            (0, vec![blocked]),
            (0, vec![blocker]),
        ] {
            kernel
                .add_fact(predicate_id, arguments, DependencySet::empty(), true, None)
                .map_err(|error| BlockingError::invariant(error.message))?;
        }
        let vocabulary = BlockingVocabulary::new([0], [1])?;
        let projection = BlockingProjection::from_state(
            &kernel,
            &vocabulary,
            super::super::BlockingLimits::default(),
            &NeverCancel,
        )?;
        let signature = BlockingSignature::new(
            DirectCheckerKind::ValidatedSingle,
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )?;
        let mut validator =
            CompiledClauseBlockingValidator::new(&program, CoreBlockingMode::Simple)?;
        let decision = validator.validate_block(
            &kernel,
            &projection,
            blocked,
            blocker,
            &signature,
            &NeverCancel,
        )?;
        assert!(decision.valid);
        Ok(())
    }
}
