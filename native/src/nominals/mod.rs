//! Rollback-safe nominal introduction over queued annotated equalities.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::BTreeMap;

use crate::cancel::CancellationState;
use crate::error::{ErrorKind, NativeError, NativeResult};
use crate::model::{DependencySet, NodeHandle, NodeKind, NodeLifecycle};
use crate::rules::{
    BranchTransition, PendingAnnotatedEquality, PredicateKind, RuleEngine, RulePredicate,
};
use crate::store::TableauKernel;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NominalLimits {
    pub max_branch_choices: u32,
    pub max_actions_per_run: u64,
}

impl NominalLimits {
    pub fn new(max_branch_choices: u32, max_actions_per_run: u64) -> NativeResult<Self> {
        if max_branch_choices == 0 || max_actions_per_run == 0 {
            return Err(NativeError::wire(
                "nominal-introduction limits must be strictly positive",
            ));
        }
        Ok(Self {
            max_branch_choices,
            max_actions_per_run,
        })
    }
}

impl Default for NominalLimits {
    fn default() -> Self {
        Self {
            max_branch_choices: 1_000_000,
            max_actions_per_run: 1_000_000,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NominalRootKey {
    pub root: NodeHandle,
    pub predicate_id: u32,
    pub role_id: u32,
    pub filler_predicate_id: u32,
    pub cardinality: u32,
    pub level: u32,
}

impl NominalRootKey {
    pub fn new(root: NodeHandle, predicate: &RulePredicate, level: u32) -> NativeResult<Self> {
        if predicate.kind != PredicateKind::AnnotatedEquality {
            return Err(NativeError::wire(
                "nominal root keys require an annotated equality predicate",
            ));
        }
        let cardinality = required(predicate.cardinality, "annotation cardinality")?;
        if level == 0 || level > cardinality {
            return Err(NativeError::wire(
                "nominal root level must lie within the annotation cardinality",
            ));
        }
        Ok(Self {
            root,
            predicate_id: predicate.predicate_id,
            role_id: required(predicate.role_id, "annotation role")?,
            filler_predicate_id: required(predicate.filler_predicate_id, "annotation filler")?,
            cardinality,
            level,
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NominalEvent {
    IgnoredPruned,
    ForgotAnnotation,
    BranchCreated,
    BranchAdvanced,
    BranchExhausted,
    RootCreated,
    RootReused,
    TargetMerged,
    OtherMerged,
}

impl NominalEvent {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::IgnoredPruned => "ignored_pruned",
            Self::ForgotAnnotation => "forgot_annotation",
            Self::BranchCreated => "branch_created",
            Self::BranchAdvanced => "branch_advanced",
            Self::BranchExhausted => "branch_exhausted",
            Self::RootCreated => "root_created",
            Self::RootReused => "root_reused",
            Self::TargetMerged => "target_merged",
            Self::OtherMerged => "other_merged",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NominalTraceEvent {
    pub sequence: usize,
    pub event: NominalEvent,
    pub action_id: u32,
    pub predicate_id: u32,
    pub dependency: DependencySet,
    pub handles: Vec<NodeHandle>,
    pub choice: Option<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct BranchContext {
    action_id: u32,
    predicate_id: u32,
    root: NodeHandle,
    target: NodeHandle,
    other: NodeHandle,
    cardinality: u32,
    provenance_ids: Vec<u32>,
    trace_checkpoint: usize,
}

#[derive(Clone, Debug)]
struct ManagerCheckpoint {
    roots: BTreeMap<NominalRootKey, NodeHandle>,
    branch_contexts: BTreeMap<u32, BranchContext>,
    trace: Vec<NominalTraceEvent>,
}

/// Query-local nominal-introduction state. Kernel and manager checkpoints are
/// paired at every public mutation boundary.
#[derive(Clone, Debug, Default)]
pub struct NominalIntroductionManager {
    limits: NominalLimits,
    roots: BTreeMap<NominalRootKey, NodeHandle>,
    branch_contexts: BTreeMap<u32, BranchContext>,
    trace: Vec<NominalTraceEvent>,
}

impl NominalIntroductionManager {
    pub fn new(limits: NominalLimits) -> NativeResult<Self> {
        let limits = NominalLimits::new(limits.max_branch_choices, limits.max_actions_per_run)?;
        Ok(Self {
            limits,
            roots: BTreeMap::new(),
            branch_contexts: BTreeMap::new(),
            trace: Vec::new(),
        })
    }

    #[must_use]
    pub fn trace(&self) -> &[NominalTraceEvent] {
        &self.trace
    }

    #[must_use]
    pub fn root_keys(&self) -> Vec<NominalRootKey> {
        self.roots.keys().copied().collect()
    }

    pub fn can_forget(
        &self,
        kernel: &TableauKernel,
        first: NodeHandle,
        second: NodeHandle,
        root: NodeHandle,
    ) -> NativeResult<bool> {
        let Some((nodes, _dependency)) = canonical_nodes(
            kernel,
            &[first, second, root],
            &DependencySet::empty(),
            true,
        )?
        else {
            return Ok(true);
        };
        Self::can_forget_canonical(kernel, nodes[0], nodes[1], nodes[2])
    }

    pub fn target_for(
        &self,
        kernel: &TableauKernel,
        first: NodeHandle,
        second: NodeHandle,
        root: NodeHandle,
    ) -> NativeResult<Option<(NodeHandle, NodeHandle)>> {
        let Some((nodes, _dependency)) = canonical_nodes(
            kernel,
            &[first, second, root],
            &DependencySet::empty(),
            true,
        )?
        else {
            return Ok(None);
        };
        if Self::can_forget_canonical(kernel, nodes[0], nodes[1], nodes[2])? {
            return Ok(None);
        }
        if kernel.active_node(nodes[0])?.parent == Some(nodes[2]) {
            Ok(Some((nodes[1], nodes[0])))
        } else {
            Ok(Some((nodes[0], nodes[1])))
        }
    }

    pub fn root_for(
        &mut self,
        kernel: &TableauKernel,
        root: NodeHandle,
        predicate: &RulePredicate,
        level: u32,
    ) -> NativeResult<Option<NodeHandle>> {
        let Ok((root, _path)) = kernel.canonical_handle(root) else {
            return Ok(None);
        };
        let Some(key) = self.find_root_key(kernel, root, predicate, level)? else {
            return Ok(None);
        };
        let stored = self.roots[&key];
        match kernel.canonical_handle(stored) {
            Ok((representative, _path)) => Ok(Some(representative)),
            Err(_) => Err(NativeError::invariant(
                "nominal root key references an unavailable node",
            )),
        }
    }

    pub fn process_next(
        &mut self,
        kernel: &mut TableauKernel,
        engine: &mut RuleEngine,
        cancellation: &CancellationState,
    ) -> NativeResult<BranchTransition> {
        let checkpoint = self.checkpoint();
        let result = kernel.atomic(|kernel| self.process_next_inner(kernel, engine, cancellation));
        if result.is_err() {
            self.restore(checkpoint);
        }
        result
    }

    pub fn process_all(
        &mut self,
        kernel: &mut TableauKernel,
        engine: &mut RuleEngine,
        cancellation: &CancellationState,
    ) -> NativeResult<u64> {
        let mut processed = 0_u64;
        while processed < self.limits.max_actions_per_run {
            if self.process_next(kernel, engine, cancellation)? == BranchTransition::NoWork {
                return Ok(processed);
            }
            processed = processed
                .checked_add(1)
                .ok_or_else(|| NativeError::invariant("nominal action counter overflow"))?;
        }
        Err(resource_limit(
            "nominal-introduction action limit exceeded",
            "max_actions_per_run",
            processed.saturating_add(1),
            self.limits.max_actions_per_run,
        ))
    }

    pub fn resolve_clash(
        &mut self,
        kernel: &mut TableauKernel,
        engine: &mut RuleEngine,
        cancellation: &CancellationState,
    ) -> NativeResult<BranchTransition> {
        let checkpoint = self.checkpoint();
        let result = kernel.atomic(|kernel| self.resolve_clash_inner(kernel, engine, cancellation));
        if result.is_err() {
            self.restore(checkpoint);
        }
        result
    }

    fn process_next_inner(
        &mut self,
        kernel: &mut TableauKernel,
        engine: &mut RuleEngine,
        cancellation: &CancellationState,
    ) -> NativeResult<BranchTransition> {
        cancellation.poll()?;
        self.purge_unavailable_roots(kernel);
        let Some(pending) = engine.take_pending_annotated_equality(kernel)? else {
            return Ok(BranchTransition::NoWork);
        };
        cancellation.poll()?;
        let predicate = annotation_predicate(engine, pending.atom.predicate_id)?.clone();
        let support = pending
            .supports
            .iter()
            .min_by_key(|value| dependency_rank(value))
            .cloned()
            .ok_or_else(|| NativeError::invariant("nominal action has no support"))?;
        let Some((nodes, dependency)) =
            canonical_nodes(kernel, &pending.atom.arguments, &support, true)?
        else {
            self.record(
                NominalEvent::IgnoredPruned,
                &pending,
                support,
                pending.atom.arguments.clone(),
                None,
            );
            return Ok(BranchTransition::Satisfied);
        };
        let (first, second, root) = (nodes[0], nodes[1], nodes[2]);
        if Self::can_forget_canonical(kernel, first, second, root)? {
            engine.merge_nodes_semantic(
                kernel,
                first,
                second,
                dependency.clone(),
                Some(cancellation),
            )?;
            self.record(
                NominalEvent::ForgotAnnotation,
                &pending,
                dependency,
                vec![first, second, root],
                None,
            );
            return Ok(BranchTransition::Deterministic);
        }
        let (target, other) = if kernel.active_node(first)?.parent == Some(root) {
            (second, first)
        } else {
            (first, second)
        };
        let cardinality = required(predicate.cardinality, "annotation cardinality")?;
        let context = BranchContext {
            action_id: pending.action_id,
            predicate_id: predicate.predicate_id,
            root,
            target,
            other,
            cardinality,
            provenance_ids: pending.provenance_ids,
            trace_checkpoint: self.trace.len(),
        };
        if cardinality == 1 {
            self.apply_choice(kernel, engine, &context, 1, dependency, cancellation)?;
            return Ok(BranchTransition::Deterministic);
        }
        if cardinality > self.limits.max_branch_choices {
            return Err(resource_limit(
                "nominal-introduction cardinality exceeds the branch-choice limit",
                "max_branch_choices",
                u64::from(cardinality),
                u64::from(self.limits.max_branch_choices),
            ));
        }
        if self
            .branch_contexts
            .insert(context.action_id, context.clone())
            .is_some()
        {
            return Err(NativeError::invariant(
                "annotated equality already owns a nominal branch",
            ));
        }
        let alternatives = (1..=cardinality).collect::<Vec<_>>();
        let level = kernel.push_branch(
            "merge".to_owned(),
            alternatives,
            context.action_id,
            dependency.clone(),
        )?;
        self.record_context(
            NominalEvent::BranchCreated,
            &context,
            dependency.clone(),
            vec![root, target, other],
            Some(1),
        );
        self.apply_choice(
            kernel,
            engine,
            &context,
            1,
            dependency.add(level),
            cancellation,
        )?;
        Ok(BranchTransition::Branched)
    }

    fn resolve_clash_inner(
        &mut self,
        kernel: &mut TableauKernel,
        engine: &mut RuleEngine,
        cancellation: &CancellationState,
    ) -> NativeResult<BranchTransition> {
        cancellation.poll()?;
        let Some(clash) = kernel.clash().cloned() else {
            return Ok(BranchTransition::NoWork);
        };
        let Some(level) = clash.dependency.maximum() else {
            return Ok(BranchTransition::Unsat);
        };
        let branch = kernel.branch(level)?.clone();
        let Some(context) = self.branch_contexts.get(&branch.source_id).cloned() else {
            return Ok(BranchTransition::NoWork);
        };
        if branch.choice_kind != "merge" {
            return Ok(BranchTransition::NoWork);
        }
        let without_level = clash.dependency.without(level);
        let alternative = kernel.advance_branch(level, without_level.clone())?;
        cancellation.poll()?;
        self.purge_unavailable_roots(kernel);
        self.trace.truncate(context.trace_checkpoint);
        if let Some(choice) = alternative {
            let dependency = if choice == context.cardinality {
                without_level
            } else {
                clash.dependency
            };
            self.record_context(
                NominalEvent::BranchAdvanced,
                &context,
                dependency.clone(),
                vec![context.root, context.target, context.other],
                Some(choice),
            );
            self.apply_choice(kernel, engine, &context, choice, dependency, cancellation)?;
            return Ok(BranchTransition::Advanced);
        }
        self.branch_contexts.remove(&context.action_id);
        let propagated = DependencySet::union(&[
            &branch.base_dependency,
            &branch.learned_dependency,
            &without_level,
        ]);
        kernel.install_clash(
            "impossible_cardinality".to_owned(),
            propagated.clone(),
            vec![context.action_id],
            context.provenance_ids.first().copied(),
        )?;
        self.record_context(
            NominalEvent::BranchExhausted,
            &context,
            propagated,
            vec![context.root, context.target, context.other],
            None,
        );
        Ok(BranchTransition::Exhausted)
    }

    fn apply_choice(
        &mut self,
        kernel: &mut TableauKernel,
        engine: &mut RuleEngine,
        context: &BranchContext,
        choice: u32,
        dependency: DependencySet,
        cancellation: &CancellationState,
    ) -> NativeResult<()> {
        cancellation.poll()?;
        let predicate = annotation_predicate(engine, context.predicate_id)?.clone();
        let Some((nodes, support)) = canonical_nodes(
            kernel,
            &[context.target, context.other, context.root],
            &dependency,
            false,
        )?
        else {
            return Ok(());
        };
        let (target, other, root) = (nodes[0], nodes[1], nodes[2]);
        let (ni_root, support) =
            self.get_or_create_root(kernel, engine, root, &predicate, choice, support, context)?;
        let target_result = engine.merge_nodes_semantic(
            kernel,
            target,
            ni_root,
            support.clone(),
            Some(cancellation),
        )?;
        self.record_context(
            NominalEvent::TargetMerged,
            context,
            support.clone(),
            vec![target, ni_root, target_result.representative],
            Some(choice),
        );
        if target_result.clashed {
            return Ok(());
        }
        cancellation.poll()?;
        let Ok(other_node) = kernel.node(other) else {
            return Ok(());
        };
        if other_node.lifecycle == NodeLifecycle::Pruned {
            return Ok(());
        }
        let (other_rep, other_path) = kernel.canonical_handle(other)?;
        let (ni_rep, ni_path) = kernel.canonical_handle(ni_root)?;
        let other_support = DependencySet::union(&[&support, &other_path, &ni_path]);
        let other_result = engine.merge_nodes_semantic(
            kernel,
            other_rep,
            ni_rep,
            other_support.clone(),
            Some(cancellation),
        )?;
        self.record_context(
            NominalEvent::OtherMerged,
            context,
            other_support,
            vec![other_rep, ni_rep, other_result.representative],
            Some(choice),
        );
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn get_or_create_root(
        &mut self,
        kernel: &mut TableauKernel,
        engine: &mut RuleEngine,
        root: NodeHandle,
        predicate: &RulePredicate,
        level: u32,
        dependency: DependencySet,
        context: &BranchContext,
    ) -> NativeResult<(NodeHandle, DependencySet)> {
        if let Some(key) = self.find_root_key(kernel, root, predicate, level)? {
            let stored = self.roots[&key];
            let (representative, path) = kernel.canonical_handle(stored)?;
            let support = DependencySet::union(&[&dependency, &path]);
            self.record_context(
                NominalEvent::RootReused,
                context,
                support.clone(),
                vec![root, representative],
                Some(level),
            );
            return Ok((representative, support));
        }
        let key = NominalRootKey::new(root, predicate, level)?;
        let created = kernel.create_node(
            NodeKind::Ni,
            None,
            false,
            None,
            Some(level),
            Some(predicate.predicate_id),
        )?;
        engine.register_node(kernel, created, dependency.clone())?;
        self.roots.insert(key, created);
        self.record_context(
            NominalEvent::RootCreated,
            context,
            dependency.clone(),
            vec![root, created],
            Some(level),
        );
        Ok((created, dependency))
    }

    fn find_root_key(
        &mut self,
        kernel: &TableauKernel,
        root: NodeHandle,
        predicate: &RulePredicate,
        level: u32,
    ) -> NativeResult<Option<NominalRootKey>> {
        let direct = NominalRootKey::new(root, predicate, level)?;
        if let Some(stored) = self.roots.get(&direct).copied() {
            if kernel.canonical_handle(stored).is_ok() {
                return Ok(Some(direct));
            }
            self.roots.remove(&direct);
        }
        let mut matches = Vec::new();
        let keys = self.roots.keys().copied().collect::<Vec<_>>();
        for candidate in keys {
            if candidate.predicate_id != direct.predicate_id
                || candidate.role_id != direct.role_id
                || candidate.filler_predicate_id != direct.filler_predicate_id
                || candidate.cardinality != direct.cardinality
                || candidate.level != level
            {
                continue;
            }
            let Ok((candidate_root, _path)) = kernel.canonical_handle(candidate.root) else {
                self.roots.remove(&candidate);
                continue;
            };
            let stored = self.roots[&candidate];
            if kernel.canonical_handle(stored).is_err() {
                self.roots.remove(&candidate);
                continue;
            }
            if candidate_root == root {
                matches.push(candidate);
            }
        }
        matches.sort_unstable();
        Ok(matches.first().copied())
    }

    fn purge_unavailable_roots(&mut self, kernel: &TableauKernel) {
        self.roots
            .retain(|_key, handle| kernel.canonical_handle(*handle).is_ok());
    }

    fn can_forget_canonical(
        kernel: &TableauKernel,
        first: NodeHandle,
        second: NodeHandle,
        root: NodeHandle,
    ) -> NativeResult<bool> {
        let first_node = kernel.active_node(first)?;
        let second_node = kernel.active_node(second)?;
        let root_node = kernel.active_node(root)?;
        Ok(first_node.parent.is_none()
            || second_node.parent.is_none()
            || root_node.parent.is_some()
            || (first_node.parent == Some(root) && second_node.parent == Some(root)))
    }

    fn record(
        &mut self,
        event: NominalEvent,
        pending: &PendingAnnotatedEquality,
        dependency: DependencySet,
        handles: Vec<NodeHandle>,
        choice: Option<u32>,
    ) {
        self.append_trace(
            event,
            pending.action_id,
            pending.atom.predicate_id,
            dependency,
            handles,
            choice,
        );
    }

    fn record_context(
        &mut self,
        event: NominalEvent,
        context: &BranchContext,
        dependency: DependencySet,
        handles: Vec<NodeHandle>,
        choice: Option<u32>,
    ) {
        self.append_trace(
            event,
            context.action_id,
            context.predicate_id,
            dependency,
            handles,
            choice,
        );
    }

    fn append_trace(
        &mut self,
        event: NominalEvent,
        action_id: u32,
        predicate_id: u32,
        dependency: DependencySet,
        handles: Vec<NodeHandle>,
        choice: Option<u32>,
    ) {
        self.trace.push(NominalTraceEvent {
            sequence: self.trace.len(),
            event,
            action_id,
            predicate_id,
            dependency,
            handles,
            choice,
        });
    }

    fn checkpoint(&self) -> ManagerCheckpoint {
        ManagerCheckpoint {
            roots: self.roots.clone(),
            branch_contexts: self.branch_contexts.clone(),
            trace: self.trace.clone(),
        }
    }

    fn restore(&mut self, checkpoint: ManagerCheckpoint) {
        self.roots = checkpoint.roots;
        self.branch_contexts = checkpoint.branch_contexts;
        self.trace = checkpoint.trace;
    }
}

fn annotation_predicate(engine: &RuleEngine, predicate_id: u32) -> NativeResult<&RulePredicate> {
    let predicate = engine.program().predicate(predicate_id)?;
    if predicate.kind != PredicateKind::AnnotatedEquality
        || predicate.cardinality.is_none()
        || predicate.role_id.is_none()
        || predicate.filler_predicate_id.is_none()
    {
        return Err(NativeError::invariant(
            "pending nominal action has incomplete annotated-equality metadata",
        ));
    }
    Ok(predicate)
}

fn canonical_nodes(
    kernel: &TableauKernel,
    handles: &[NodeHandle],
    dependency: &DependencySet,
    sort_pair: bool,
) -> NativeResult<Option<(Vec<NodeHandle>, DependencySet)>> {
    let mut canonical = Vec::new();
    let mut dependencies = vec![dependency.clone()];
    for handle in handles {
        let Ok(node) = kernel.node(*handle) else {
            return Ok(None);
        };
        if matches!(
            node.lifecycle,
            NodeLifecycle::Pruned | NodeLifecycle::Retired
        ) {
            return Ok(None);
        }
        let (representative, path) = kernel.canonical_handle(*handle)?;
        canonical.push(representative);
        dependencies.push(path);
    }
    if sort_pair
        && canonical.len() == 3
        && kernel.node_rank(canonical[1])? < kernel.node_rank(canonical[0])?
    {
        canonical.swap(0, 1);
    }
    let refs = dependencies.iter().collect::<Vec<_>>();
    Ok(Some((canonical, DependencySet::union(&refs))))
}

fn dependency_rank(value: &DependencySet) -> (usize, Option<u32>, Vec<u32>) {
    (
        value.as_slice().len(),
        value.maximum(),
        value.as_slice().iter().rev().copied().collect(),
    )
}

fn required(value: Option<u32>, label: &str) -> NativeResult<u32> {
    value.ok_or_else(|| NativeError::invariant(format!("{label} is absent")))
}

fn resource_limit(message: &str, limit: &'static str, observed: u64, allowed: u64) -> NativeError {
    NativeError::new(ErrorKind::Resource, "RESOURCE_LIMIT", message)
        .with_context("limit", limit)
        .with_context("observed", observed.to_string())
        .with_context("allowed", allowed.to_string())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::cancel::CancellationHandle;
    use crate::rules::{GroundAtom, RulePredicate, RuleProgram, TermSort};

    fn program(cardinality: u32) -> NativeResult<RuleProgram> {
        RuleProgram::new(
            vec![
                RulePredicate::new(0, PredicateKind::Concept, vec![TermSort::Object])?
                    .with_symbol_id(0),
                RulePredicate::new(
                    1,
                    PredicateKind::Equality,
                    vec![TermSort::Object, TermSort::Object],
                )?
                .with_opposite(2),
                RulePredicate::new(
                    2,
                    PredicateKind::Inequality,
                    vec![TermSort::Object, TermSort::Object],
                )?
                .with_opposite(1),
                RulePredicate::new(
                    3,
                    PredicateKind::AnnotatedEquality,
                    vec![TermSort::Object; 3],
                )?
                .with_cardinality(cardinality, 7, 0),
            ],
            Vec::new(),
        )
    }

    fn fixture(
        cardinality: u32,
    ) -> NativeResult<(
        TableauKernel,
        RuleEngine,
        NodeHandle,
        NodeHandle,
        NodeHandle,
    )> {
        let mut kernel = TableauKernel::new();
        let root = kernel.create_node(NodeKind::Root, None, false, None, None, None)?;
        let direct = kernel.create_node(NodeKind::Tree, Some(root), false, None, None, None)?;
        let nested = kernel.create_node(NodeKind::Tree, Some(direct), false, None, None, None)?;
        let mut engine = RuleEngine::new(
            program(cardinality)?,
            BTreeMap::new(),
            BTreeMap::new(),
            true,
        )?;
        engine.dispatch_ground_atom(
            &mut kernel,
            GroundAtom::new(3, vec![direct, nested, root])?,
            DependencySet::empty(),
            false,
            &[5],
        )?;
        Ok((kernel, engine, root, direct, nested))
    }

    fn cancellation() -> NativeResult<std::sync::Arc<CancellationState>> {
        Ok(CancellationHandle::from_options(None, None)?.state())
    }

    #[test]
    fn formal_forgetting_and_target_side_conditions_match_python() -> NativeResult<()> {
        let (kernel, _engine, root, direct, nested) = fixture(2)?;
        let manager = NominalIntroductionManager::default();
        assert!(!manager.can_forget(&kernel, direct, nested, root)?);
        assert_eq!(
            manager.target_for(&kernel, direct, nested, root)?,
            Some((nested, direct))
        );
        assert!(manager.can_forget(&kernel, root, nested, root)?);
        assert_eq!(manager.target_for(&kernel, root, nested, root)?, None);
        Ok(())
    }

    #[test]
    fn cardinality_one_creates_and_reuses_one_ni_root_deterministically() -> NativeResult<()> {
        let (mut kernel, mut engine, root, direct, nested) = fixture(1)?;
        let mut manager = NominalIntroductionManager::default();
        let control = cancellation()?;
        assert_eq!(
            manager.process_next(&mut kernel, &mut engine, &control)?,
            BranchTransition::Deterministic
        );
        let direct_rep = kernel.canonical_handle(direct)?.0;
        let nested_rep = kernel.canonical_handle(nested)?.0;
        assert_eq!(direct_rep, nested_rep);
        assert_eq!(kernel.active_node(direct_rep)?.kind, NodeKind::Ni);
        let predicate = engine.program().predicate(3)?.clone();
        assert_eq!(
            manager.root_for(&kernel, root, &predicate, 1)?,
            Some(direct_rep)
        );
        assert_eq!(manager.root_keys().len(), 1);
        assert_eq!(
            manager
                .trace()
                .iter()
                .map(|event| event.event)
                .collect::<Vec<_>>(),
            vec![
                NominalEvent::RootCreated,
                NominalEvent::TargetMerged,
                NominalEvent::OtherMerged,
            ]
        );
        kernel.check_invariants()
    }

    #[test]
    fn merge_choice_advance_and_exhaustion_roll_back_roots_and_trace() -> NativeResult<()> {
        let (mut kernel, mut engine, _root, _direct, _nested) = fixture(2)?;
        let mut manager = NominalIntroductionManager::default();
        let control = cancellation()?;
        assert_eq!(
            manager.process_next(&mut kernel, &mut engine, &control)?,
            BranchTransition::Branched
        );
        assert_eq!(manager.root_keys().len(), 1);
        kernel.install_clash(
            "empty_head".to_owned(),
            DependencySet::new(vec![0])?,
            vec![99],
            None,
        )?;
        assert_eq!(
            manager.resolve_clash(&mut kernel, &mut engine, &control)?,
            BranchTransition::Advanced
        );
        assert_eq!(manager.root_keys().len(), 1);
        assert_eq!(manager.root_keys()[0].level, 2);
        assert_eq!(manager.trace()[0].event, NominalEvent::BranchAdvanced);

        kernel.install_clash(
            "empty_head".to_owned(),
            DependencySet::new(vec![0])?,
            vec![100],
            None,
        )?;
        assert_eq!(
            manager.resolve_clash(&mut kernel, &mut engine, &control)?,
            BranchTransition::Exhausted
        );
        assert!(manager.root_keys().is_empty());
        assert_eq!(manager.trace().len(), 1);
        assert_eq!(manager.trace()[0].event, NominalEvent::BranchExhausted);
        assert_eq!(
            kernel
                .clash()
                .ok_or_else(|| NativeError::invariant("exhaustion did not install a clash"))?
                .kind,
            "impossible_cardinality"
        );
        kernel.check_invariants()
    }

    #[test]
    fn cancellation_restores_the_pending_action_and_manager_state() -> NativeResult<()> {
        let (mut kernel, mut engine, _root, _direct, _nested) = fixture(1)?;
        let mut manager = NominalIntroductionManager::default();
        let cancelled = CancellationHandle::from_options(None, None)?;
        cancelled
            .state()
            .interrupt(Some("cancel nominal action".to_owned()))?;
        let before = kernel.canonical_snapshot()?;
        assert!(manager
            .process_next(&mut kernel, &mut engine, &cancelled.state())
            .is_err());
        assert_eq!(kernel.canonical_snapshot()?, before);
        assert!(manager.trace().is_empty());
        let control = cancellation()?;
        assert_eq!(
            manager.process_next(&mut kernel, &mut engine, &control)?,
            BranchTransition::Deterministic
        );
        Ok(())
    }
}
