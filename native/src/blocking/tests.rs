//! Focused WPR2 blocking tests live with the independently compilable module.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

use super::*;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct NodeId(u32);

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct FakeState {
    revision: u64,
    nodes: Vec<NodeRecord<NodeId>>,
    facts: Vec<FactRecord<NodeId>>,
    assignments: BTreeMap<NodeId, BlockingAssignment<NodeId>>,
    rescheduled: BTreeSet<NodeId>,
    fail_assignment: bool,
    fail_promotion: bool,
}

impl FakeState {
    fn create(&mut self, kind: NodeKind, parent: Option<NodeId>) -> NodeId {
        let slot = u32::try_from(self.nodes.len()).unwrap_or(u32::MAX);
        let node = NodeId(slot);
        self.nodes.push(NodeRecord {
            node,
            key: NodeKey::new(slot, 1),
            creation_id: slot,
            kind,
            lifecycle: NodeLifecycle::Active,
            parent,
            has_pending_existentials: false,
        });
        self.revision = self.revision.saturating_add(1);
        node
    }

    fn root(&mut self) -> NodeId {
        self.create(NodeKind::Root, None)
    }

    fn tree(&mut self, parent: NodeId) -> NodeId {
        self.create(NodeKind::Tree, Some(parent))
    }

    fn ni(&mut self) -> NodeId {
        self.create(NodeKind::Ni, None)
    }

    fn add_fact(&mut self, predicate_id: u32, arguments: &[NodeId], core: bool) -> u32 {
        let row_id = u32::try_from(self.facts.len()).unwrap_or(u32::MAX);
        self.facts.push(FactRecord {
            row_id,
            predicate_id,
            arguments: arguments.to_vec(),
            core,
            active: true,
        });
        self.revision = self.revision.saturating_add(1);
        row_id
    }

    fn deactivate(&mut self, row_id: u32) {
        if let Some(row) = self.facts.iter_mut().find(|row| row.row_id == row_id) {
            row.active = false;
            self.revision = self.revision.saturating_add(1);
        }
    }

    fn set_core(&mut self, row_id: u32) -> Result<(), BlockingError> {
        let row = self
            .facts
            .iter_mut()
            .find(|row| row.row_id == row_id && row.active)
            .ok_or_else(|| BlockingError::invalid("fake core row is unavailable"))?;
        if !row.core {
            row.core = true;
            self.revision = self.revision.saturating_add(1);
        }
        Ok(())
    }

    fn set_pending(&mut self, node: NodeId, value: bool) {
        if let Some(record) = self.nodes.iter_mut().find(|record| record.node == node) {
            record.has_pending_existentials = value;
            self.revision = self.revision.saturating_add(1);
        }
    }

    fn set_lifecycle(&mut self, node: NodeId, lifecycle: NodeLifecycle) {
        if let Some(record) = self.nodes.iter_mut().find(|record| record.node == node) {
            record.lifecycle = lifecycle;
            self.revision = self.revision.saturating_add(1);
        }
    }

    fn fact(&self, row_id: u32) -> Option<&FactRecord<NodeId>> {
        self.facts.iter().find(|row| row.row_id == row_id)
    }
}

impl BlockingStateRead for FakeState {
    type Node = NodeId;

    fn revision(&self) -> u64 {
        self.revision
    }

    fn node_records(&self) -> Result<Vec<NodeRecord<Self::Node>>, BlockingError> {
        Ok(self.nodes.clone())
    }

    fn active_fact_records(&self) -> Result<Vec<FactRecord<Self::Node>>, BlockingError> {
        Ok(self.facts.clone())
    }
}

impl BlockingStateMutate for FakeState {
    fn blocking_atomic<T, F>(&mut self, operation: F) -> Result<T, BlockingError>
    where
        F: FnOnce(&mut Self) -> Result<T, BlockingError>,
    {
        let before = self.clone();
        let outcome = operation(self);
        if outcome.is_err() {
            *self = before;
        }
        outcome
    }

    fn apply_assignment_change(
        &mut self,
        change: &AssignmentChange<Self::Node>,
    ) -> Result<(), BlockingError> {
        if self.fail_assignment {
            self.assignments.insert(
                change.node,
                change
                    .after
                    .unwrap_or_else(|| BlockingAssignment::unblocked(change.node)),
            );
            return Err(BlockingError::invariant("fake assignment failure"));
        }
        match change.after {
            Some(assignment) => {
                self.assignments.insert(change.node, assignment);
            }
            None => {
                self.assignments.remove(&change.node);
            }
        }
        Ok(())
    }

    fn promote_core_fact(&mut self, row_id: u32) -> Result<(), BlockingError> {
        self.set_core(row_id)?;
        if self.fail_promotion {
            return Err(BlockingError::cancelled(
                "fake cancellation after promotion",
            ));
        }
        Ok(())
    }

    fn reschedule_existentials(&mut self, node: Self::Node) -> Result<(), BlockingError> {
        self.rescheduled.insert(node);
        Ok(())
    }
}

#[derive(Debug, Default)]
struct TestControl {
    polls: Cell<usize>,
    cancel_at: Option<usize>,
    max_memory: Option<u64>,
}

impl TestControl {
    fn cancelling(cancel_at: usize) -> Self {
        Self {
            polls: Cell::new(0),
            cancel_at: Some(cancel_at),
            max_memory: None,
        }
    }
}

impl BlockingControl for TestControl {
    fn poll(&self) -> Result<(), BlockingError> {
        let next = self.polls.get().saturating_add(1);
        self.polls.set(next);
        if self.cancel_at.is_some_and(|limit| next >= limit) {
            return Err(BlockingError::cancelled("test cancellation"));
        }
        Ok(())
    }

    fn observe_memory(&self, bytes: u64) -> Result<(), BlockingError> {
        if let Some(allowed) = self.max_memory {
            if bytes > allowed {
                return Err(BlockingError::resource(
                    "test memory limit",
                    "blocking_memory",
                    bytes,
                    allowed,
                ));
            }
        }
        Ok(())
    }
}

fn vocabulary() -> BlockingVocabulary {
    BlockingVocabulary::new([1, 2, 3], [10, 11]).unwrap_or_else(|error| {
        abort_with_message(&error.to_string());
    })
}

fn plan(mode: BlockingMode, requirements: BlockingRequirements) -> BlockingPlan {
    select_blocking_plan(mode, requirements).unwrap_or_else(|error| {
        abort_with_message(&error.to_string());
    })
}

fn checker(
    kind: DirectCheckerKind,
    vocabulary: BlockingVocabulary,
    has_inverses: bool,
) -> DirectChecker {
    DirectChecker::new(kind, vocabulary, has_inverses).unwrap_or_else(|error| {
        abort_with_message(&error.to_string());
    })
}

fn new_manager(
    mode: BlockingMode,
    requirements: BlockingRequirements,
    cache: Option<BlockingSignatureCache>,
) -> BlockingManager<NodeId> {
    let selected = plan(mode, requirements);
    BlockingManager::new(
        selected,
        checker(
            selected.direct_checker_kind,
            vocabulary(),
            requirements.has_inverse_roles,
        ),
        cache,
        BlockingLimits::default(),
        10_000,
    )
    .unwrap_or_else(|error| {
        abort_with_message(&error.to_string());
    })
}

fn projection(state: &FakeState, vocabulary: &BlockingVocabulary) -> BlockingProjection<NodeId> {
    BlockingProjection::from_state(state, vocabulary, BlockingLimits::default(), &NeverCancel)
        .unwrap_or_else(|error| {
            abort_with_message(&error.to_string());
        })
}

fn abort_with_message(message: &str) -> ! {
    eprintln!("blocking test setup failed: {message}");
    std::process::abort();
}

fn branched_state() -> (FakeState, NodeId, NodeId, NodeId) {
    let mut state = FakeState::default();
    let root = state.root();
    let blocker = state.tree(root);
    let blocked = state.tree(root);
    let descendant = state.tree(blocked);
    state.add_fact(1, &[blocker], false);
    state.add_fact(1, &[blocked], false);
    state.add_fact(3, &[descendant], false);
    state.set_pending(descendant, true);
    (state, blocker, blocked, descendant)
}

#[test]
fn sha256_standard_vector() {
    assert_eq!(
        super::sha256::hex(&super::sha256::digest(b"abc")),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
    );
}

#[test]
fn strategy_selection_matches_python_wp11() -> Result<(), BlockingError> {
    let simple = select_blocking_plan(BlockingMode::Auto, BlockingRequirements::default())?;
    assert_eq!(simple.manager_kind, BlockingManagerKind::Anywhere);
    assert_eq!(simple.direct_checker_kind, DirectCheckerKind::Single);
    assert!(simple.cache_allowed);

    let inverse = select_blocking_plan(
        BlockingMode::Auto,
        BlockingRequirements {
            has_inverse_roles: true,
            ..BlockingRequirements::default()
        },
    )?;
    assert_eq!(inverse.direct_checker_kind, DirectCheckerKind::Pairwise);

    let validated = select_blocking_plan(
        BlockingMode::Auto,
        BlockingRequirements {
            has_inverse_roles: true,
            has_nominals: true,
            requires_validated_core: true,
            complex_core: true,
            ..BlockingRequirements::default()
        },
    )?;
    assert_eq!(
        validated.manager_kind,
        BlockingManagerKind::ValidatedAnywhere
    );
    assert_eq!(
        validated.direct_checker_kind,
        DirectCheckerKind::ValidatedSingle
    );
    assert_eq!(validated.core_mode, CoreBlockingMode::Complex);
    assert!(!validated.cache_allowed);
    Ok(())
}

#[test]
fn frozen_python_pairwise_signature_trace_matches_exactly() -> Result<(), BlockingError> {
    let vocabulary = vocabulary();
    let mut state = FakeState::default();
    let root = state.root();
    let first_parent = state.tree(root);
    let first = state.tree(first_parent);
    let second_parent = state.tree(root);
    let second = state.tree(second_parent);
    for node in [first_parent, first, second_parent, second] {
        state.add_fact(1, &[node], false);
    }
    for (parent, child) in [(first_parent, first), (second_parent, second)] {
        state.add_fact(10, &[parent, child], false);
        state.add_fact(11, &[child, parent], false);
    }
    let projection = projection(&state, &vocabulary);
    let checker = checker(DirectCheckerKind::Pairwise, vocabulary.clone(), true);
    assert_eq!(
        vocabulary.fingerprint(),
        "afef482dafc98b2e6ba3609daffe8b3454aebd38e5e7e920979c8e4515c4f9fe"
    );
    assert_eq!(
        projection.state_digest_hex(),
        "7a3e473b7645ea487009830e281bd4841bf7397cf81cf4ca08a155de57bf3871"
    );
    assert_eq!(
        checker.signature(&projection, second)?.sha256(),
        "ca28b8412213a75045055e07b19a54add4e1cf86f1b1b4e61001d3696842cfb5"
    );
    Ok(())
}

#[test]
fn single_and_pairwise_differ_only_on_parent_or_edge_context() -> Result<(), BlockingError> {
    let vocabulary = vocabulary();
    let mut state = FakeState::default();
    let root = state.root();
    let first_parent = state.tree(root);
    let first = state.tree(first_parent);
    let second_parent = state.tree(root);
    let second = state.tree(second_parent);
    for node in [first_parent, first, second_parent, second] {
        state.add_fact(1, &[node], false);
    }
    for (parent, child) in [(first_parent, first), (second_parent, second)] {
        state.add_fact(10, &[parent, child], false);
        state.add_fact(11, &[child, parent], false);
    }
    let ni = state.ni();
    state.add_fact(1, &[ni], false);
    let labels = projection(&state, &vocabulary);
    let single = checker(DirectCheckerKind::Single, vocabulary.clone(), false);
    let pairwise = checker(DirectCheckerKind::Pairwise, vocabulary.clone(), true);
    assert!(!single.can_be_blocked(&labels, ni));
    assert!(single.is_blocked_by(&labels, first, second)?);
    assert!(pairwise.is_blocked_by(&labels, first, second)?);

    state.add_fact(2, &[second_parent], false);
    let labels = projection(&state, &vocabulary);
    assert!(single.is_blocked_by(&labels, first, second)?);
    assert!(!pairwise.is_blocked_by(&labels, first, second)?);
    Ok(())
}

#[test]
fn validated_projection_blocks_on_core_and_serializes_full_context() -> Result<(), BlockingError> {
    let vocabulary = vocabulary();
    let mut state = FakeState::default();
    let root = state.root();
    let first = state.tree(root);
    let second = state.tree(root);
    state.add_fact(1, &[first], true);
    state.add_fact(1, &[second], true);
    let extra = state.add_fact(2, &[second], false);
    state.add_fact(10, &[root, second], false);
    let labels = projection(&state, &vocabulary);
    let checker = checker(
        DirectCheckerKind::ValidatedSingle,
        vocabulary.clone(),
        false,
    );
    let first_signature = checker.signature(&labels, first)?;
    let second_signature = checker.signature(&labels, second)?;
    assert!(first_signature.blocks(&second_signature));
    assert_eq!(first_signature.full_node_concepts, vec![1]);
    assert_eq!(second_signature.full_node_concepts, vec![1, 2]);
    assert_eq!(second_signature.full_from_parent_roles, vec![10]);
    assert_ne!(
        first_signature.canonical_bytes(),
        second_signature.canonical_bytes()
    );

    state.set_core(extra)?;
    let labels = projection(&state, &vocabulary);
    assert!(!checker.is_blocked_by(&labels, first, second)?);
    Ok(())
}

#[test]
fn anywhere_nonancestor_indirect_blocking_and_unblocking_delta() -> Result<(), BlockingError> {
    let (mut state, blocker, blocked, descendant) = branched_state();
    let mut manager = new_manager(
        BlockingMode::Anywhere,
        BlockingRequirements::default(),
        None,
    );
    let first = manager.compute_and_apply(&mut state, &NeverCancel, false)?;
    assert_eq!(first.changed_count(), 2);
    assert_eq!(manager.blocker(blocked), Some(blocker));
    assert!(manager.is_directly_blocked(blocked));
    assert_eq!(manager.blocker(descendant), Some(blocked));
    assert!(!manager.is_directly_blocked(descendant));

    let changed = state.add_fact(2, &[blocked], false);
    let row = state
        .fact(changed)
        .cloned()
        .ok_or_else(|| BlockingError::invariant("changed fake fact is absent"))?;
    manager.notify_fact_change(&row);
    let result = manager.compute_and_apply(&mut state, &NeverCancel, false)?;
    assert!(!manager.is_blocked(blocked));
    assert!(!manager.is_blocked(descendant));
    assert_eq!(result.reschedule_nodes, vec![descendant]);
    assert!(state.rescheduled.contains(&descendant));
    manager.check_invariants(&NeverCancel)?;
    Ok(())
}

#[test]
fn ancestor_does_not_use_nonancestor_and_anywhere_does() -> Result<(), BlockingError> {
    let (state, blocker, blocked, _descendant) = branched_state();
    let mut ancestor = new_manager(
        BlockingMode::Ancestor,
        BlockingRequirements::default(),
        None,
    );
    ancestor.compute_unbounded(&state, false)?;
    assert!(!ancestor.is_blocked(blocked));

    let mut anywhere = new_manager(
        BlockingMode::Anywhere,
        BlockingRequirements::default(),
        None,
    );
    anywhere.compute_unbounded(&state, false)?;
    assert_eq!(anywhere.blocker(blocked), Some(blocker));
    Ok(())
}

#[test]
fn unannounced_changes_and_checkpoint_restore_match_full_recompute() -> Result<(), BlockingError> {
    let (mut state, _blocker, blocked, descendant) = branched_state();
    let mut manager = new_manager(
        BlockingMode::Anywhere,
        BlockingRequirements::default(),
        None,
    );
    manager.compute_unbounded(&state, false)?;
    let baseline = manager.canonical_snapshot();
    let manager_checkpoint = manager.checkpoint();
    let state_checkpoint = state.clone();

    state.set_lifecycle(blocked, NodeLifecycle::Pruned);
    state.set_lifecycle(descendant, NodeLifecycle::Pruned);
    manager.compute_unbounded(&state, false)?;
    manager.check_invariants(&NeverCancel)?;
    assert!(!manager.is_blocked(descendant));

    state = state_checkpoint;
    manager.restore(manager_checkpoint);
    manager.compute_unbounded(&state, false)?;
    assert_eq!(manager.canonical_snapshot(), baseline);
    Ok(())
}

#[test]
fn inactive_and_stale_generation_facts_cannot_pollute_labels() {
    let vocabulary = vocabulary();
    let mut state = FakeState::default();
    let root = state.root();
    let old = state.tree(root);
    let stale_row = state.add_fact(2, &[old], false);
    state.set_lifecycle(old, NodeLifecycle::Retired);
    let replacement = state.tree(root);
    state.nodes[usize::try_from(replacement.0).unwrap_or(0)].key = NodeKey::new(old.0, 2);
    state.add_fact(1, &[replacement], false);
    let labels = projection(&state, &vocabulary);
    assert_eq!(labels.concept_label(replacement, false), &[1]);
    assert!(labels.concept_label(old, false).is_empty());
    state.deactivate(stale_row);
    let after = projection(&state, &vocabulary);
    assert_eq!(labels.state_digest(), after.state_digest());
}

fn cache_namespace(
    vocabulary: &BlockingVocabulary,
) -> Result<BlockingCacheNamespace, BlockingError> {
    BlockingCacheNamespace::new(
        "aaaaaaaa",
        vocabulary.fingerprint(),
        DirectCheckerKind::Single,
        CoreBlockingMode::None,
        "default",
    )
}

#[test]
fn cache_promotes_only_sound_models_and_blocks_without_old_nodes() -> Result<(), BlockingError> {
    let vocabulary = vocabulary();
    let mut first_state = FakeState::default();
    let root = first_state.root();
    let first = first_state.tree(root);
    first_state.add_fact(1, &[first], false);
    let labels = projection(&first_state, &vocabulary);
    let checker = checker(DirectCheckerKind::Single, vocabulary.clone(), false);
    let signature = checker.signature(&labels, first)?;
    let mut cache = BlockingSignatureCache::new(cache_namespace(&vocabulary)?, 2, 4096)?;
    let skipped = cache.promote_model(
        [signature.clone()],
        CachePromotionContext {
            satisfiable: true,
            completed: false,
            has_nominals: false,
            has_additional_ontology: false,
            query_local_axioms: false,
            aborted: false,
        },
        &NeverCancel,
    )?;
    assert_eq!(skipped.inserted, 0);
    let promoted = cache.promote_model(
        [signature],
        CachePromotionContext {
            satisfiable: true,
            completed: true,
            has_nominals: false,
            has_additional_ontology: false,
            query_local_axioms: false,
            aborted: false,
        },
        &NeverCancel,
    )?;
    assert_eq!(promoted.inserted, 1);

    let mut second_state = FakeState::default();
    let root = second_state.root();
    let second = second_state.tree(root);
    second_state.add_fact(1, &[second], false);
    let mut manager = new_manager(
        BlockingMode::Anywhere,
        BlockingRequirements::default(),
        Some(cache),
    );
    manager.compute_unbounded(&second_state, false)?;
    assert!(manager.is_directly_blocked(second));
    assert_eq!(manager.blocker(second), None);
    assert!(manager.assignments()[1].from_cache);
    Ok(())
}

#[test]
fn cache_is_bounded_and_cancelled_promotion_is_atomic() -> Result<(), BlockingError> {
    let vocabulary = vocabulary();
    let mut state = FakeState::default();
    let root = state.root();
    let nodes = [state.tree(root), state.tree(root), state.tree(root)];
    for (predicate, node) in [1_u32, 2, 3].into_iter().zip(nodes) {
        state.add_fact(predicate, &[node], false);
    }
    let labels = projection(&state, &vocabulary);
    let checker = checker(DirectCheckerKind::Single, vocabulary.clone(), false);
    let signatures = nodes
        .into_iter()
        .map(|node| checker.signature(&labels, node))
        .collect::<Result<Vec<_>, _>>()?;
    let mut cache = BlockingSignatureCache::new(cache_namespace(&vocabulary)?, 2, 4096)?;
    cache.promote_model(
        signatures.clone(),
        CachePromotionContext {
            satisfiable: true,
            completed: true,
            has_nominals: false,
            has_additional_ontology: false,
            query_local_axioms: false,
            aborted: false,
        },
        &NeverCancel,
    )?;
    assert!(cache.entry_count() <= 2);
    assert!(cache.size_bytes() <= cache.max_bytes());

    let before = cache.clone();
    let error = cache
        .promote_model(
            signatures,
            CachePromotionContext {
                satisfiable: true,
                completed: true,
                has_nominals: false,
                has_additional_ontology: false,
                query_local_axioms: false,
                aborted: false,
            },
            &TestControl::cancelling(1),
        )
        .err()
        .ok_or_else(|| BlockingError::invariant("cache cancellation did not fire"))?;
    assert_eq!(error.kind, BlockingErrorKind::Cancelled);
    assert_eq!(cache, before);
    Ok(())
}

#[derive(Debug)]
struct RepairValidator {
    blocked: NodeId,
    row_id: u32,
    reject: bool,
    begins: usize,
    ends: usize,
}

impl BlockValidator<FakeState> for RepairValidator {
    fn begin_pass<C: BlockingControl>(
        &mut self,
        _state: &FakeState,
        _projection: &BlockingProjection<NodeId>,
        control: &C,
    ) -> Result<(), BlockingError> {
        control.poll()?;
        self.begins = self.begins.saturating_add(1);
        Ok(())
    }

    fn validate_block<C: BlockingControl>(
        &mut self,
        _state: &FakeState,
        _projection: &BlockingProjection<NodeId>,
        blocked: NodeId,
        _blocker: NodeId,
        _signature: &BlockingSignature,
        control: &C,
    ) -> Result<ValidationDecision<NodeId>, BlockingError> {
        control.poll()?;
        if self.reject && blocked == self.blocked {
            self.reject = false;
            return ValidationDecision::invalid(vec![self.row_id], vec![blocked], vec![99]);
        }
        Ok(ValidationDecision::valid())
    }

    fn end_pass(&mut self) {
        self.ends = self.ends.saturating_add(1);
    }
}

fn validated_state() -> (FakeState, NodeId, NodeId, u32) {
    let mut state = FakeState::default();
    let root = state.root();
    let blocker = state.tree(root);
    let blocked = state.tree(root);
    state.add_fact(1, &[blocker], true);
    state.add_fact(1, &[blocked], true);
    let extra = state.add_fact(2, &[blocked], false);
    state.set_pending(blocked, true);
    (state, blocker, blocked, extra)
}

#[test]
fn validated_rejection_promotes_core_reschedules_and_gates_sat() -> Result<(), BlockingError> {
    let (mut state, blocker, blocked, extra) = validated_state();
    let requirements = BlockingRequirements {
        requires_validated_core: true,
        ..BlockingRequirements::default()
    };
    let mut manager = new_manager(BlockingMode::ValidatedAnywhere, requirements, None);
    let mut validator = RepairValidator {
        blocked,
        row_id: extra,
        reject: true,
        begins: 0,
        ends: 0,
    };
    let (_compute, rejected) =
        manager.validation_and_apply(&mut state, &mut validator, &NeverCancel, false)?;
    assert!(!rejected.valid);
    assert_eq!(rejected.violation_ids, vec![99]);
    assert_eq!(rejected.promote_fact_ids, vec![extra]);
    assert_eq!(rejected.reschedule_nodes, vec![blocked]);
    assert_eq!(manager.blocker(blocked), None);
    assert!(state.fact(extra).is_some_and(|row| row.core));
    assert!(state.rescheduled.contains(&blocked));
    assert_eq!(validator.begins, validator.ends);
    assert!(!manager.ready_for_sat(&state, &NeverCancel)?);

    let (_compute, accepted) =
        manager.validation_and_apply(&mut state, &mut validator, &NeverCancel, false)?;
    assert!(accepted.valid);
    assert_eq!(manager.blocker(blocked), None);
    assert_eq!(manager.blocker(blocker), None);
    assert!(manager.ready_for_sat(&state, &NeverCancel)?);
    Ok(())
}

#[derive(Debug)]
struct FailingValidator;

impl BlockValidator<FakeState> for FailingValidator {
    fn validate_block<C: BlockingControl>(
        &mut self,
        _state: &FakeState,
        _projection: &BlockingProjection<NodeId>,
        _blocked: NodeId,
        _blocker: NodeId,
        _signature: &BlockingSignature,
        _control: &C,
    ) -> Result<ValidationDecision<NodeId>, BlockingError> {
        Err(BlockingError::cancelled("validator cancelled"))
    }
}

#[test]
fn coarse_compute_and_validation_transactions_restore_both_sides() -> Result<(), BlockingError> {
    let (mut state, _blocker, _blocked, _descendant) = branched_state();
    state.fail_assignment = true;
    let state_before = state.clone();
    let mut manager = new_manager(
        BlockingMode::Anywhere,
        BlockingRequirements::default(),
        None,
    );
    let manager_before = manager.canonical_snapshot();
    let error = manager
        .compute_and_apply(&mut state, &NeverCancel, false)
        .err()
        .ok_or_else(|| BlockingError::invariant("fake assignment failure did not fire"))?;
    assert_eq!(error.kind, BlockingErrorKind::Invariant);
    assert_eq!(state, state_before);
    assert_eq!(manager.canonical_snapshot(), manager_before);

    let (mut state, _blocker, _blocked, _extra) = validated_state();
    let state_before = state.clone();
    let requirements = BlockingRequirements {
        requires_validated_core: true,
        ..BlockingRequirements::default()
    };
    let mut manager = new_manager(BlockingMode::ValidatedAnywhere, requirements, None);
    let before = manager.canonical_snapshot();
    let error = manager
        .validation_and_apply(&mut state, &mut FailingValidator, &NeverCancel, false)
        .err()
        .ok_or_else(|| BlockingError::invariant("validator cancellation did not fire"))?;
    assert_eq!(error.kind, BlockingErrorKind::Cancelled);
    assert_eq!(state, state_before);
    assert_eq!(manager.canonical_snapshot(), before);

    let (mut state, _blocker, blocked, extra) = validated_state();
    state.fail_promotion = true;
    let state_before = state.clone();
    let mut manager = new_manager(BlockingMode::ValidatedAnywhere, requirements, None);
    let before = manager.canonical_snapshot();
    let mut validator = RepairValidator {
        blocked,
        row_id: extra,
        reject: true,
        begins: 0,
        ends: 0,
    };
    let error = manager
        .validation_and_apply(&mut state, &mut validator, &NeverCancel, false)
        .err()
        .ok_or_else(|| BlockingError::invariant("post-promotion cancellation did not fire"))?;
    assert_eq!(error.kind, BlockingErrorKind::Cancelled);
    assert_eq!(state, state_before);
    assert_eq!(manager.canonical_snapshot(), before);
    Ok(())
}

#[test]
fn cancellation_and_resource_limits_leave_manager_unchanged() -> Result<(), BlockingError> {
    let (mut state, _blocker, blocked, _descendant) = branched_state();
    let mut manager = new_manager(
        BlockingMode::Anywhere,
        BlockingRequirements::default(),
        None,
    );
    manager.compute_unbounded(&state, false)?;
    let before = manager.canonical_snapshot();
    state.add_fact(2, &[blocked], false);
    let error = manager
        .compute(&state, &TestControl::cancelling(1), false)
        .err()
        .ok_or_else(|| BlockingError::invariant("compute cancellation did not fire"))?;
    assert_eq!(error.kind, BlockingErrorKind::Cancelled);
    assert_eq!(manager.canonical_snapshot(), before);

    let limits = BlockingLimits {
        max_candidate_checks: 1,
        ..BlockingLimits::default()
    };
    let selected = plan(BlockingMode::Anywhere, BlockingRequirements::default());
    let mut limited = BlockingManager::new(
        selected,
        checker(DirectCheckerKind::Single, vocabulary(), false),
        None,
        limits,
        100,
    )?;
    let mut equal = FakeState::default();
    let root = equal.root();
    for _index in 0..3 {
        let node = equal.tree(root);
        equal.add_fact(1, &[node], false);
    }
    let error = limited
        .compute_unbounded(&equal, false)
        .err()
        .ok_or_else(|| BlockingError::invariant("candidate limit did not fire"))?;
    assert_eq!(error.kind, BlockingErrorKind::Resource);
    assert!(limited.assignments().is_empty());
    Ok(())
}

#[test]
fn anywhere_equal_bucket_has_linear_candidate_work() -> Result<(), BlockingError> {
    let mut state = FakeState::default();
    let root = state.root();
    let mut nodes = Vec::new();
    for _index in 0..5_000 {
        let node = state.tree(root);
        state.add_fact(1, &[node], false);
        nodes.push(node);
    }
    let mut manager = new_manager(
        BlockingMode::Anywhere,
        BlockingRequirements::default(),
        None,
    );
    let result = manager.compute_unbounded(&state, false)?;
    assert_eq!(result.changed_count(), nodes.len() - 1);
    assert!(!manager.is_blocked(nodes[0]));
    assert!(nodes[1..]
        .iter()
        .all(|node| manager.blocker(*node) == Some(nodes[0])));
    assert_eq!(result.stats.nodes_visited, nodes.len() + 1);
    assert_eq!(result.stats.candidate_checks, nodes.len() - 1);
    Ok(())
}

#[derive(Clone, Copy, Debug)]
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        self.0
    }

    fn index(&mut self, length: usize) -> usize {
        usize::try_from(self.next() % u64::try_from(length).unwrap_or(1)).unwrap_or(0)
    }
}

#[test]
fn randomized_mutations_and_rollbacks_equal_full_recompute() -> Result<(), BlockingError> {
    for seed in 0_u64..12 {
        let mut random = Lcg(seed.saturating_add(1));
        let mut state = FakeState::default();
        let root = state.root();
        let mut nodes = Vec::new();
        for index in 0..10 {
            let parent = if index < 3 {
                root
            } else {
                nodes[random.index(nodes.len())]
            };
            let node = state.tree(parent);
            state.add_fact(
                u32::try_from(random.index(3) + 1).unwrap_or(1),
                &[node],
                false,
            );
            nodes.push(node);
        }
        let mut manager = new_manager(
            BlockingMode::Anywhere,
            BlockingRequirements::default(),
            None,
        );
        manager.compute_unbounded(&state, false)?;
        let mut checkpoints = Vec::new();
        for step in 0..120 {
            match random.index(5) {
                0 | 1 => {
                    let node = nodes[random.index(nodes.len())];
                    let predicate = u32::try_from(random.index(3) + 1).unwrap_or(1);
                    let row = state.add_fact(predicate, &[node], random.index(2) == 0);
                    if random.index(2) == 0 {
                        let record = state
                            .fact(row)
                            .cloned()
                            .ok_or_else(|| BlockingError::invariant("random fact disappeared"))?;
                        manager.notify_fact_change(&record);
                    }
                }
                2 => {
                    let active = state
                        .facts
                        .iter()
                        .filter(|row| row.active)
                        .map(|row| row.row_id)
                        .collect::<Vec<_>>();
                    if !active.is_empty() {
                        state.deactivate(active[random.index(active.len())]);
                    }
                }
                3 => checkpoints.push((state.clone(), manager.checkpoint())),
                _ if !checkpoints.is_empty() && step % 3 == 0 => {
                    let (saved_state, saved_manager) = checkpoints
                        .pop()
                        .ok_or_else(|| BlockingError::invariant("checkpoint vanished"))?;
                    state = saved_state;
                    manager.restore(saved_manager);
                }
                _ => {
                    let node = nodes[random.index(nodes.len())];
                    let parent = state
                        .nodes
                        .iter()
                        .find(|record| record.node == node)
                        .and_then(|record| record.parent);
                    if let Some(parent) = parent {
                        state.add_fact(10, &[parent, node], false);
                    }
                }
            }
            manager.compute_unbounded(&state, false)?;
            let labels = projection(&state, &vocabulary());
            let (expected, _stats) = full_recompute(
                &labels,
                manager.checker(),
                manager.plan(),
                manager.cache(),
                BlockingLimits::default(),
                &NeverCancel,
            )?;
            assert_eq!(manager.assignments(), expected);
            manager.check_invariants(&NeverCancel)?;
        }
    }
    Ok(())
}
