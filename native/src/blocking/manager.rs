//! Deterministic ancestor/anywhere maintenance and full-recompute oracle.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write as _};

use super::cache::{BlockingSignatureCache, CachePromotion, CachePromotionContext};
use super::checker::DirectChecker;
use super::model::{
    BlockingAssignment, BlockingControl, BlockingError, BlockingLimits, BlockingManagerKind,
    BlockingPlan, BlockingStateRead, FactRecord, NeverCancel, NodeKind,
};
use super::projection::{BlockingKey, BlockingProjection, BlockingSignature};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BlockingEvent {
    Invalidated,
    DirectBlock,
    IndirectBlock,
    CacheBlock,
    Unblocked,
    Recomputed,
    BlockValidated,
    BlockRejected,
}

impl BlockingEvent {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Invalidated => "invalidated",
            Self::DirectBlock => "direct_block",
            Self::IndirectBlock => "indirect_block",
            Self::CacheBlock => "cache_block",
            Self::Unblocked => "unblocked",
            Self::Recomputed => "recomputed",
            Self::BlockValidated => "block_validated",
            Self::BlockRejected => "block_rejected",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockingTraceEvent<N> {
    pub sequence: usize,
    pub event: BlockingEvent,
    pub node: Option<N>,
    pub blocker: Option<N>,
    pub state_digest: Option<String>,
    pub details: Vec<u64>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ComputeStats {
    pub nodes_visited: usize,
    pub signatures_built: usize,
    pub candidate_checks: usize,
    pub indexed_blockers: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AssignmentChange<N> {
    pub node: N,
    pub before: Option<BlockingAssignment<N>>,
    pub after: Option<BlockingAssignment<N>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ComputeResult<N> {
    pub changed: Vec<AssignmentChange<N>>,
    pub reschedule_nodes: Vec<N>,
    pub earliest_recomputed_creation_id: Option<u32>,
    pub state_digest: String,
    pub stats: ComputeStats,
}

/// Coarse mutation boundary implemented by the native tableau kernel.
///
/// `blocking_atomic` must restore every kernel mutation when the closure
/// returns an error.  Manager helpers independently restore their checkpoint,
/// so neither side can survive a half-applied blocking operation.
pub trait BlockingStateMutate: BlockingStateRead {
    fn blocking_atomic<T, F>(&mut self, operation: F) -> Result<T, BlockingError>
    where
        Self: Sized,
        F: FnOnce(&mut Self) -> Result<T, BlockingError>;

    fn apply_assignment_change(
        &mut self,
        change: &AssignmentChange<Self::Node>,
    ) -> Result<(), BlockingError>;

    fn promote_core_fact(&mut self, row_id: u32) -> Result<(), BlockingError>;

    fn reschedule_existentials(&mut self, node: Self::Node) -> Result<(), BlockingError>;
}

impl<N> ComputeResult<N> {
    #[must_use]
    // `Vec::len` was not const until after the crate's Rust 1.83 MSRV.
    #[allow(clippy::missing_const_for_fn)]
    pub fn changed_count(&self) -> usize {
        self.changed.len()
    }
}

#[derive(Clone, Debug)]
pub struct BlockingManager<N> {
    plan: BlockingPlan,
    checker: DirectChecker,
    limits: BlockingLimits,
    cache: Option<BlockingSignatureCache>,
    assignments: BTreeMap<N, BlockingAssignment<N>>,
    blocker_index: BTreeMap<BlockingKey, Vec<N>>,
    last_projection: Option<BlockingProjection<N>>,
    dirty_creation_id: Option<u32>,
    last_recomputed_from: Option<u32>,
    rejected_blocks: BTreeMap<(N, N), [u8; 32]>,
    validated_digest: Option<[u8; 32]>,
    trace: Vec<BlockingTraceEvent<N>>,
    max_trace_events: usize,
}

#[derive(Clone, Debug)]
pub struct BlockingCheckpoint<N> {
    manager: BlockingManager<N>,
}

type ReusablePrefix<N> = (
    BTreeMap<N, BlockingAssignment<N>>,
    BTreeMap<BlockingKey, Vec<N>>,
    u32,
);

type RecomputeResult<N> = (
    BTreeMap<N, BlockingAssignment<N>>,
    BTreeMap<BlockingKey, Vec<N>>,
    ComputeStats,
);

impl<N: Copy + fmt::Debug + Eq + Ord> BlockingManager<N> {
    pub fn new(
        plan: BlockingPlan,
        checker: DirectChecker,
        cache: Option<BlockingSignatureCache>,
        limits: BlockingLimits,
        max_trace_events: usize,
    ) -> Result<Self, BlockingError> {
        let limits = limits.validate()?;
        if checker.kind() != plan.direct_checker_kind {
            return Err(BlockingError::invalid(
                "direct checker kind does not match blocking plan",
            ));
        }
        if let Some(value) = &cache {
            if !plan.cache_allowed {
                return Err(BlockingError::invalid(
                    "selected blocking plan forbids signature caching",
                ));
            }
            if value.namespace().checker_kind != checker.kind() {
                return Err(BlockingError::invalid(
                    "blocking cache checker kind does not match manager",
                ));
            }
            if value.namespace().core_mode != plan.core_mode {
                return Err(BlockingError::invalid(
                    "blocking cache core mode does not match manager",
                ));
            }
            if value.namespace().vocabulary_fingerprint != checker.vocabulary().fingerprint() {
                return Err(BlockingError::invalid(
                    "blocking cache vocabulary does not match manager",
                ));
            }
        }
        Ok(Self {
            plan,
            checker,
            limits,
            cache,
            assignments: BTreeMap::new(),
            blocker_index: BTreeMap::new(),
            last_projection: None,
            dirty_creation_id: Some(0),
            last_recomputed_from: None,
            rejected_blocks: BTreeMap::new(),
            validated_digest: None,
            trace: Vec::new(),
            max_trace_events,
        })
    }

    #[must_use]
    pub const fn plan(&self) -> BlockingPlan {
        self.plan
    }

    #[must_use]
    pub const fn checker(&self) -> &DirectChecker {
        &self.checker
    }

    #[must_use]
    pub const fn cache(&self) -> Option<&BlockingSignatureCache> {
        self.cache.as_ref()
    }

    #[must_use]
    pub fn assignments(&self) -> Vec<BlockingAssignment<N>> {
        let Some(projection) = &self.last_projection else {
            return Vec::new();
        };
        projection
            .ordered_nodes
            .iter()
            .filter_map(|node| self.assignments.get(node).copied())
            .collect()
    }

    #[must_use]
    pub fn trace(&self) -> &[BlockingTraceEvent<N>] {
        &self.trace
    }

    #[must_use]
    pub const fn last_recomputed_from(&self) -> Option<u32> {
        self.last_recomputed_from
    }

    #[must_use]
    pub fn checkpoint(&self) -> BlockingCheckpoint<N> {
        BlockingCheckpoint {
            manager: self.clone(),
        }
    }

    pub fn restore(&mut self, checkpoint: BlockingCheckpoint<N>) {
        *self = checkpoint.manager;
    }

    pub fn invalidate_all(&mut self) {
        self.invalidate_creation(0, None);
    }

    pub fn invalidate_node(&mut self, node: N) {
        let creation_id = self
            .last_projection
            .as_ref()
            .and_then(|projection| projection.node(node))
            .map_or(0, |record| record.creation_id);
        self.invalidate_creation(creation_id, Some(node));
    }

    pub fn notify_fact_change(&mut self, fact: &FactRecord<N>) {
        let relevant = self
            .checker
            .vocabulary()
            .atomic_concepts
            .contains(&fact.predicate_id)
            || self
                .checker
                .vocabulary()
                .atomic_object_roles
                .contains(&fact.predicate_id);
        if !relevant {
            return;
        }
        let earliest = fact
            .arguments
            .iter()
            .filter_map(|node| {
                self.last_projection
                    .as_ref()
                    .and_then(|projection| projection.node(*node))
                    .map(|record| record.creation_id)
            })
            .min()
            .unwrap_or(0);
        self.invalidate_creation(earliest, fact.arguments.first().copied());
    }

    pub fn compute<S: BlockingStateRead<Node = N>, C: BlockingControl>(
        &mut self,
        state: &S,
        control: &C,
        force_full: bool,
    ) -> Result<ComputeResult<N>, BlockingError> {
        let projection =
            BlockingProjection::from_state(state, self.checker.vocabulary(), self.limits, control)?;
        let previous_digest = self
            .last_projection
            .as_ref()
            .map(BlockingProjection::state_digest);
        if !force_full
            && self.dirty_creation_id.is_none()
            && previous_digest == Some(projection.state_digest())
        {
            let digest = projection.state_digest_hex();
            self.last_projection = Some(projection);
            return Ok(ComputeResult {
                changed: Vec::new(),
                reschedule_nodes: Vec::new(),
                earliest_recomputed_creation_id: None,
                state_digest: digest,
                stats: ComputeStats::default(),
            });
        }
        let earliest = if force_full || previous_digest.is_none() {
            0
        } else {
            let projected = self
                .last_projection
                .as_ref()
                .and_then(|value| value.earliest_difference(&projection));
            min_option(self.dirty_creation_id, projected).unwrap_or(0)
        };
        let before = self.clone();
        let result = (|| {
            control.poll()?;
            let digest = projection.state_digest();
            self.rejected_blocks
                .retain(|_pair, rejected_digest| *rejected_digest == digest);
            let previous_assignments = std::mem::take(&mut self.assignments);
            let previous_blocker_index = std::mem::take(&mut self.blocker_index);
            let reusable_prefix = (!force_full && earliest > 0).then_some((
                previous_assignments,
                previous_blocker_index,
                earliest,
            ));
            let (assignments, blocker_index, metrics) = recompute_internal(
                &projection,
                &self.checker,
                self.plan,
                self.cache.as_mut(),
                &self.rejected_blocks,
                reusable_prefix,
                self.limits,
                control,
            )?;
            let changes = assignment_changes(&before.assignments, &assignments);
            let mut reschedule_nodes = Vec::new();
            for change in &changes {
                let was_blocked = change.before.is_some_and(BlockingAssignment::blocked);
                let now_blocked = change.after.is_some_and(BlockingAssignment::blocked);
                if was_blocked
                    && !now_blocked
                    && projection
                        .node(change.node)
                        .is_some_and(|record| record.has_pending_existentials)
                {
                    reschedule_nodes.push(change.node);
                }
            }
            reschedule_nodes.sort_by_key(|node| node_order(&projection, *node));
            reschedule_nodes.dedup();
            let digest_changed = previous_digest != Some(projection.state_digest());
            if digest_changed {
                self.validated_digest = None;
            }
            self.assignments = assignments;
            self.blocker_index = blocker_index;
            self.last_projection = Some(projection);
            self.dirty_creation_id = None;
            self.last_recomputed_from = Some(earliest);
            let digest_hex = self
                .last_projection
                .as_ref()
                .map(BlockingProjection::state_digest_hex)
                .ok_or_else(|| BlockingError::invariant("blocking projection disappeared"))?;
            for change in &changes {
                if let Some(after) = change.after {
                    let event = if after.from_cache {
                        BlockingEvent::CacheBlock
                    } else if after.blocker.is_none() {
                        BlockingEvent::Unblocked
                    } else if after.directly {
                        BlockingEvent::DirectBlock
                    } else {
                        BlockingEvent::IndirectBlock
                    };
                    self.record(
                        event,
                        Some(change.node),
                        after.blocker,
                        Some(digest_hex.clone()),
                        Vec::new(),
                    );
                }
            }
            self.record(
                BlockingEvent::Recomputed,
                None,
                None,
                Some(digest_hex.clone()),
                vec![
                    u64::from(earliest),
                    u64::try_from(self.assignments.len()).unwrap_or(u64::MAX),
                    u64::try_from(changes.len()).unwrap_or(u64::MAX),
                    u64::try_from(metrics.candidate_checks).unwrap_or(u64::MAX),
                ],
            );
            self.check_structural_invariants()?;
            Ok(ComputeResult {
                changed: changes,
                reschedule_nodes,
                earliest_recomputed_creation_id: Some(earliest),
                state_digest: digest_hex,
                stats: metrics,
            })
        })();
        if result.is_err() {
            *self = before;
        }
        result
    }

    pub fn compute_unbounded<S: BlockingStateRead<Node = N>>(
        &mut self,
        state: &S,
        force_full: bool,
    ) -> Result<ComputeResult<N>, BlockingError> {
        self.compute(state, &NeverCancel, force_full)
    }

    pub fn compute_and_apply<S: BlockingStateMutate<Node = N>, C: BlockingControl>(
        &mut self,
        state: &mut S,
        control: &C,
        force_full: bool,
    ) -> Result<ComputeResult<N>, BlockingError> {
        let checkpoint = self.checkpoint();
        let outcome = state.blocking_atomic(|state| {
            let result = self.compute(state, control, force_full)?;
            control.poll()?;
            for change in &result.changed {
                state.apply_assignment_change(change)?;
                control.poll()?;
            }
            for node in &result.reschedule_nodes {
                state.reschedule_existentials(*node)?;
                control.poll()?;
            }
            Ok(result)
        });
        if outcome.is_err() {
            self.restore(checkpoint);
        }
        outcome
    }

    pub fn reference_assignments<C: BlockingControl>(
        &self,
        control: &C,
    ) -> Result<Vec<BlockingAssignment<N>>, BlockingError> {
        let projection = self
            .last_projection
            .as_ref()
            .ok_or_else(|| BlockingError::invalid("blocking manager has not computed a state"))?;
        let mut cache = self.cache.clone();
        let (assignments, _index, _stats) = recompute_internal(
            projection,
            &self.checker,
            self.plan,
            cache.as_mut(),
            &self.rejected_blocks,
            None,
            self.limits,
            control,
        )?;
        Ok(projection
            .ordered_nodes
            .iter()
            .filter_map(|node| assignments.get(node).copied())
            .collect())
    }

    pub fn check_invariants<C: BlockingControl>(&self, control: &C) -> Result<(), BlockingError> {
        self.check_structural_invariants()?;
        let expected = self.reference_assignments(control)?;
        let actual = self.assignments();
        if actual != expected {
            return Err(BlockingError::invariant(
                "incremental blocking assignments differ from full recomputation",
            ));
        }
        Ok(())
    }

    fn check_structural_invariants(&self) -> Result<(), BlockingError> {
        let projection = self
            .last_projection
            .as_ref()
            .ok_or_else(|| BlockingError::invariant("blocking projection is unavailable"))?;
        if self.assignments.len() != projection.ordered_nodes.len() {
            return Err(BlockingError::invariant(
                "blocking assignment count differs from the projected node count",
            ));
        }
        for assignment in self.assignments() {
            let record = projection.node(assignment.node).ok_or_else(|| {
                BlockingError::invariant("blocking assignment refers to a stale node")
            })?;
            if let Some(blocker) = assignment.blocker {
                let blocker_record = projection.node(blocker).ok_or_else(|| {
                    BlockingError::invariant("blocking assignment has a stale blocker")
                })?;
                if blocker_record.creation_id >= record.creation_id {
                    return Err(BlockingError::invariant(
                        "blocker does not precede blocked node",
                    ));
                }
            }
        }
        for nodes in self.blocker_index.values() {
            for node in nodes {
                let assignment = self.assignments.get(node).ok_or_else(|| {
                    BlockingError::invariant("blocking index refers to an unassigned node")
                })?;
                if assignment.blocked() || !self.checker.can_be_blocker(projection, *node) {
                    return Err(BlockingError::invariant(
                        "blocking index contains an ineligible or stale entry",
                    ));
                }
            }
        }
        Ok(())
    }

    #[must_use]
    pub fn is_blocked(&self, node: N) -> bool {
        self.assignments
            .get(&node)
            .copied()
            .is_some_and(BlockingAssignment::blocked)
    }

    #[must_use]
    pub fn is_directly_blocked(&self, node: N) -> bool {
        self.assignments
            .get(&node)
            .is_some_and(|assignment| assignment.directly && assignment.blocked())
    }

    #[must_use]
    pub fn blocker(&self, node: N) -> Option<N> {
        self.assignments.get(&node).and_then(|value| value.blocker)
    }

    pub fn ready_for_sat<S: BlockingStateRead<Node = N>, C: BlockingControl>(
        &mut self,
        state: &S,
        control: &C,
    ) -> Result<bool, BlockingError> {
        self.compute(state, control, false)?;
        if !self.plan.validated() {
            return Ok(true);
        }
        Ok(self
            .last_projection
            .as_ref()
            .is_some_and(|projection| self.validated_digest == Some(projection.state_digest())))
    }

    pub fn model_found<S: BlockingStateRead<Node = N>, C: BlockingControl>(
        &mut self,
        state: &S,
        context: CachePromotionContext,
        control: &C,
    ) -> Result<CachePromotion, BlockingError> {
        self.compute(state, control, false)?;
        if context.satisfiable && context.completed && !self.ready_for_sat(state, control)? {
            return Err(BlockingError::invariant(
                "SAT cannot be reported before blocking validation",
            ));
        }
        let Some(projection) = &self.last_projection else {
            return Err(BlockingError::invariant(
                "blocking projection is unavailable",
            ));
        };
        let mut signatures = Vec::new();
        for node in &projection.ordered_nodes {
            if !self.is_blocked(*node) && self.checker.can_be_blocker(projection, *node) {
                signatures.push(self.checker.signature(projection, *node)?);
            }
        }
        let Some(cache) = self.cache.as_mut() else {
            return Ok(CachePromotion {
                inserted: 0,
                entry_count: 0,
                size_bytes: 0,
            });
        };
        cache.promote_model(signatures, context, control)
    }

    #[must_use]
    pub fn canonical_snapshot(&self) -> String {
        let Some(projection) = &self.last_projection else {
            return "{\"assignments\":[]}".to_owned();
        };
        let mut output = String::from("{\"assignments\":[");
        for (index, node) in projection.ordered_nodes.iter().enumerate() {
            if index != 0 {
                output.push(',');
            }
            let assignment = self.assignments[node];
            let key = projection.nodes[node].key;
            let _ = write!(
                output,
                "{{\"blocker\":{},\"directly\":{},\"from_cache\":{},\"node\":[{},{}]}}",
                assignment.blocker.map_or_else(
                    || "null".to_owned(),
                    |blocker| {
                        let blocker_key = projection.nodes[&blocker].key;
                        format!("[{},{}]", blocker_key.slot, blocker_key.generation)
                    }
                ),
                assignment.directly,
                assignment.from_cache,
                key.slot,
                key.generation,
            );
        }
        output.push_str("],\"checker\":\"");
        output.push_str(self.checker.kind().as_str());
        output.push_str("\",\"manager\":\"");
        output.push_str(self.plan.manager_kind.as_str());
        output.push_str("\",\"state_digest\":\"");
        output.push_str(&projection.state_digest_hex());
        output.push_str("\"}");
        output
    }

    fn invalidate_creation(&mut self, creation_id: u32, node: Option<N>) {
        self.dirty_creation_id = Some(
            self.dirty_creation_id
                .map_or(creation_id, |known| known.min(creation_id)),
        );
        self.validated_digest = None;
        self.record(
            BlockingEvent::Invalidated,
            node,
            None,
            None,
            vec![u64::from(creation_id)],
        );
    }

    pub(crate) const fn projection(&self) -> Option<&BlockingProjection<N>> {
        self.last_projection.as_ref()
    }

    pub(crate) const fn limits(&self) -> BlockingLimits {
        self.limits
    }

    pub(crate) const fn rejected_blocks_mut(&mut self) -> &mut BTreeMap<(N, N), [u8; 32]> {
        &mut self.rejected_blocks
    }

    pub(crate) fn replace_assignment(
        &mut self,
        assignment: BlockingAssignment<N>,
    ) -> Option<BlockingAssignment<N>> {
        self.assignments.insert(assignment.node, assignment)
    }

    pub(crate) const fn set_validated_digest(&mut self, value: Option<[u8; 32]>) {
        self.validated_digest = value;
    }

    pub(crate) fn record_validation(
        &mut self,
        event: BlockingEvent,
        node: N,
        blocker: N,
        digest: String,
        details: Vec<u64>,
    ) {
        self.record(event, Some(node), Some(blocker), Some(digest), details);
    }

    fn record(
        &mut self,
        event: BlockingEvent,
        node: Option<N>,
        blocker: Option<N>,
        state_digest: Option<String>,
        details: Vec<u64>,
    ) {
        if self.trace.len() >= self.max_trace_events {
            return;
        }
        self.trace.push(BlockingTraceEvent {
            sequence: self.trace.len(),
            event,
            node,
            blocker,
            state_digest,
            details,
        });
    }
}

pub fn full_recompute<N: Copy + fmt::Debug + Eq + Ord, C: BlockingControl>(
    projection: &BlockingProjection<N>,
    checker: &DirectChecker,
    plan: BlockingPlan,
    cache: Option<&BlockingSignatureCache>,
    limits: BlockingLimits,
    control: &C,
) -> Result<(Vec<BlockingAssignment<N>>, ComputeStats), BlockingError> {
    let mut cache = cache.cloned();
    let (assignments, _index, stats) = recompute_internal(
        projection,
        checker,
        plan,
        cache.as_mut(),
        &BTreeMap::new(),
        None,
        limits.validate()?,
        control,
    )?;
    Ok((
        projection
            .ordered_nodes
            .iter()
            .filter_map(|node| assignments.get(node).copied())
            .collect(),
        stats,
    ))
}

#[allow(clippy::too_many_arguments)]
fn recompute_internal<N: Copy + fmt::Debug + Eq + Ord, C: BlockingControl>(
    projection: &BlockingProjection<N>,
    checker: &DirectChecker,
    plan: BlockingPlan,
    mut cache: Option<&mut BlockingSignatureCache>,
    rejected_blocks: &BTreeMap<(N, N), [u8; 32]>,
    reusable_prefix: Option<ReusablePrefix<N>>,
    limits: BlockingLimits,
    control: &C,
) -> Result<RecomputeResult<N>, BlockingError> {
    if checker.kind() != plan.direct_checker_kind {
        return Err(BlockingError::invalid(
            "direct checker kind does not match blocking plan",
        ));
    }
    let frontier = reusable_prefix
        .as_ref()
        .map(|(_previous, _previous_index, value)| *value);
    let (mut assignments, mut index) = reusable_prefix.map_or_else(
        || (BTreeMap::new(), BTreeMap::new()),
        |(mut previous, mut previous_index, frontier)| {
            previous.retain(|node, _assignment| {
                projection
                    .node(*node)
                    .is_some_and(|record| record.creation_id < frontier)
            });
            previous_index.retain(|_key, nodes| {
                nodes.retain(|node| {
                    projection
                        .node(*node)
                        .is_some_and(|record| record.creation_id < frontier)
                });
                !nodes.is_empty()
            });
            (previous, previous_index)
        },
    );
    let first_recomputed = frontier.map_or(0, |value| {
        projection.ordered_nodes.partition_point(|node| {
            projection
                .node(*node)
                .is_some_and(|record| record.creation_id < value)
        })
    });
    let mut stats = ComputeStats::default();
    let digest = projection.state_digest();
    for node in &projection.ordered_nodes[first_recomputed..] {
        stats.nodes_visited = stats.nodes_visited.saturating_add(1);
        if stats.nodes_visited % limits.cancellation_poll_interval == 0 {
            control.poll()?;
        }
        let record = projection
            .node(*node)
            .ok_or_else(|| BlockingError::invariant("ordered blocking node is absent"))?;
        let mut assignment = BlockingAssignment::unblocked(*node);
        if record.kind == NodeKind::Tree {
            let parent = record.parent.ok_or_else(|| {
                BlockingError::invariant("active tree blocking node has no parent")
            })?;
            if assignments
                .get(&parent)
                .copied()
                .is_some_and(BlockingAssignment::blocked)
            {
                assignment = BlockingAssignment::indirect(*node, parent);
            } else if checker.can_be_blocked(projection, *node) {
                let signature = checker.signature(projection, *node)?;
                stats.signatures_built = stats.signatures_built.saturating_add(1);
                let cache_hit = if plan.cache_allowed {
                    match cache.as_deref_mut() {
                        Some(value) => value.contains(&signature)?,
                        None => false,
                    }
                } else {
                    false
                };
                if cache_hit {
                    assignment = BlockingAssignment::cached(*node);
                } else {
                    let blocker = find_blocker(
                        projection,
                        checker,
                        plan.manager_kind,
                        *node,
                        &signature,
                        &assignments,
                        &index,
                        rejected_blocks,
                        digest,
                        &mut stats,
                        limits,
                        control,
                    )?;
                    if let Some(blocker) = blocker {
                        assignment = BlockingAssignment::direct(*node, blocker);
                    }
                }
            }
        }
        assignments.insert(*node, assignment);
        if !assignment.blocked() && checker.can_be_blocker(projection, *node) {
            let signature = checker.signature(projection, *node)?;
            stats.signatures_built = stats.signatures_built.saturating_add(1);
            index
                .entry(signature.blocking_key())
                .or_default()
                .push(*node);
            stats.indexed_blockers = stats.indexed_blockers.saturating_add(1);
        }
    }
    control.poll()?;
    Ok((assignments, index, stats))
}

#[allow(clippy::too_many_arguments)]
fn find_blocker<N: Copy + fmt::Debug + Eq + Ord, C: BlockingControl>(
    projection: &BlockingProjection<N>,
    checker: &DirectChecker,
    manager_kind: BlockingManagerKind,
    node: N,
    signature: &BlockingSignature,
    assignments: &BTreeMap<N, BlockingAssignment<N>>,
    index: &BTreeMap<BlockingKey, Vec<N>>,
    rejected_blocks: &BTreeMap<(N, N), [u8; 32]>,
    digest: [u8; 32],
    stats: &mut ComputeStats,
    limits: BlockingLimits,
    control: &C,
) -> Result<Option<N>, BlockingError> {
    if matches!(manager_kind, BlockingManagerKind::Ancestor) {
        let mut parent = projection.node(node).and_then(|record| record.parent);
        let mut remaining = projection.nodes.len();
        while let Some(candidate) = parent {
            candidate_step(stats, limits, control)?;
            let assignment = assignments.get(&candidate).copied();
            if assignment.is_some_and(|value| !value.blocked())
                && checker.can_be_blocker(projection, candidate)
                && checker.signature(projection, candidate)?.blocks(signature)
                && rejected_blocks.get(&(node, candidate)) != Some(&digest)
            {
                return Ok(Some(candidate));
            }
            parent = projection.node(candidate).and_then(|record| record.parent);
            if remaining == 0 {
                return Err(BlockingError::invariant(
                    "cycle detected in blocking parent chain",
                ));
            }
            remaining -= 1;
        }
        return Ok(None);
    }
    if let Some(candidates) = index.get(&signature.blocking_key()) {
        for candidate in candidates {
            candidate_step(stats, limits, control)?;
            if assignments
                .get(candidate)
                .copied()
                .is_some_and(|assignment| !assignment.blocked())
                && !projection.is_ancestor(node, *candidate)
                && rejected_blocks.get(&(node, *candidate)) != Some(&digest)
            {
                return Ok(Some(*candidate));
            }
        }
    }
    Ok(None)
}

fn candidate_step<C: BlockingControl>(
    stats: &mut ComputeStats,
    limits: BlockingLimits,
    control: &C,
) -> Result<(), BlockingError> {
    stats.candidate_checks = stats.candidate_checks.saturating_add(1);
    if stats.candidate_checks > limits.max_candidate_checks {
        return Err(BlockingError::resource(
            "blocking candidate limit exceeded",
            "blocking_candidate_checks",
            u64::try_from(stats.candidate_checks).unwrap_or(u64::MAX),
            u64::try_from(limits.max_candidate_checks).unwrap_or(u64::MAX),
        ));
    }
    if stats.candidate_checks % limits.cancellation_poll_interval == 0 {
        control.poll()?;
    }
    Ok(())
}

fn assignment_changes<N: Copy + Eq + Ord>(
    before: &BTreeMap<N, BlockingAssignment<N>>,
    after: &BTreeMap<N, BlockingAssignment<N>>,
) -> Vec<AssignmentChange<N>> {
    let nodes = before
        .keys()
        .chain(after.keys())
        .copied()
        .collect::<BTreeSet<_>>();
    nodes
        .into_iter()
        .filter_map(|node| {
            let old = before.get(&node).copied();
            let new = after.get(&node).copied();
            let semantically_unchanged_default = matches!(
                (old, new),
                (None, Some(value)) if !value.blocked()
            ) || matches!(
                (old, new),
                (Some(value), None) if !value.blocked()
            );
            if semantically_unchanged_default {
                return None;
            }
            (old != new).then_some(AssignmentChange {
                node,
                before: old,
                after: new,
            })
        })
        .collect()
}

fn min_option(left: Option<u32>, right: Option<u32>) -> Option<u32> {
    match (left, right) {
        (Some(left), Some(right)) => Some(left.min(right)),
        (Some(value), None) | (None, Some(value)) => Some(value),
        (None, None) => None,
    }
}

fn node_order<N: Copy + fmt::Debug + Eq + Ord>(
    projection: &BlockingProjection<N>,
    node: N,
) -> (u32, super::model::NodeKey) {
    projection.node(node).map_or(
        (u32::MAX, super::model::NodeKey::new(u32::MAX, u32::MAX)),
        |record| (record.creation_id, record.key),
    )
}
