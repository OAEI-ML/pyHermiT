//! Validated/core blocking lifecycle and repair deltas.
//!
//! Clause interpretation remains a native Rust validator concern.  The manager
//! brackets a stable read-only projection, rejects the first invalid provisional
//! block, and returns core-promotion/rescheduling actions for the kernel's atomic
//! mutation boundary.  SAT remains unavailable until a complete pass validates
//! the current projection digest.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::fmt;

use super::manager::{
    AssignmentChange, BlockingEvent, BlockingManager, BlockingStateMutate, ComputeResult,
};
use super::model::{BlockingAssignment, BlockingControl, BlockingError, BlockingStateRead};
use super::projection::{BlockingProjection, BlockingSignature};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidationDecision<N> {
    pub valid: bool,
    pub promote_fact_ids: Vec<u32>,
    pub reschedule_nodes: Vec<N>,
    pub violation_ids: Vec<u32>,
}

impl<N: Copy + Eq + Ord> ValidationDecision<N> {
    #[must_use]
    pub const fn valid() -> Self {
        Self {
            valid: true,
            promote_fact_ids: Vec::new(),
            reschedule_nodes: Vec::new(),
            violation_ids: Vec::new(),
        }
    }

    pub fn invalid(
        mut promote_fact_ids: Vec<u32>,
        mut reschedule_nodes: Vec<N>,
        mut violation_ids: Vec<u32>,
    ) -> Result<Self, BlockingError> {
        promote_fact_ids.sort_unstable();
        promote_fact_ids.dedup();
        reschedule_nodes.sort_unstable();
        reschedule_nodes.dedup();
        violation_ids.sort_unstable();
        violation_ids.dedup();
        if violation_ids.is_empty() {
            return Err(BlockingError::invalid(
                "invalid blocking validation decision requires a violation ID",
            ));
        }
        Ok(Self {
            valid: false,
            promote_fact_ids,
            reschedule_nodes,
            violation_ids,
        })
    }

    pub fn validate(&self) -> Result<(), BlockingError> {
        if self.valid
            && (!self.promote_fact_ids.is_empty()
                || !self.reschedule_nodes.is_empty()
                || !self.violation_ids.is_empty())
        {
            return Err(BlockingError::invalid(
                "valid blocking decision cannot request repair side effects",
            ));
        }
        if !strictly_sorted(&self.promote_fact_ids)
            || !strictly_sorted(&self.reschedule_nodes)
            || !strictly_sorted(&self.violation_ids)
        {
            return Err(BlockingError::invalid(
                "blocking validation actions must be sorted and unique",
            ));
        }
        if !self.valid && self.violation_ids.is_empty() {
            return Err(BlockingError::invalid(
                "invalid blocking decision requires a violation ID",
            ));
        }
        Ok(())
    }
}

pub trait BlockValidator<S: BlockingStateRead> {
    fn begin_pass<C: BlockingControl>(
        &mut self,
        _state: &S,
        _projection: &BlockingProjection<S::Node>,
        control: &C,
    ) -> Result<(), BlockingError> {
        control.poll()
    }

    fn validate_block<C: BlockingControl>(
        &mut self,
        state: &S,
        projection: &BlockingProjection<S::Node>,
        blocked: S::Node,
        blocker: S::Node,
        signature: &BlockingSignature,
        control: &C,
    ) -> Result<ValidationDecision<S::Node>, BlockingError>;

    fn end_pass(&mut self) {}
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidationPassResult<N> {
    pub valid: bool,
    pub checked_blocks: usize,
    pub invalidated_blocks: usize,
    pub promote_fact_ids: Vec<u32>,
    pub reschedule_nodes: Vec<N>,
    pub violation_ids: Vec<u32>,
    pub state_digest: String,
    pub assignment_changes: Vec<AssignmentChange<N>>,
}

impl<N: Copy + fmt::Debug + Eq + Ord> BlockingManager<N> {
    pub fn validation_pass<
        S: BlockingStateRead<Node = N>,
        C: BlockingControl,
        V: BlockValidator<S>,
    >(
        &mut self,
        state: &S,
        validator: &mut V,
        control: &C,
    ) -> Result<ValidationPassResult<N>, BlockingError> {
        if !self.plan().validated() {
            return Err(BlockingError::invalid(
                "validation is available only for validated-anywhere blocking",
            ));
        }
        self.compute(state, control, false)?;
        let checkpoint = self.checkpoint();
        let projection = self
            .projection()
            .cloned()
            .ok_or_else(|| BlockingError::invariant("blocking projection is unavailable"))?;
        let direct = self
            .assignments()
            .into_iter()
            .filter(|assignment| {
                assignment.directly && !assignment.from_cache && assignment.blocker.is_some()
            })
            .collect::<Vec<_>>();
        let allowed = self.limits().max_validation_blocks;
        if direct.len() > allowed {
            return Err(BlockingError::resource(
                "blocking validation block limit exceeded",
                "blocking_validation_blocks",
                u64::try_from(direct.len()).unwrap_or(u64::MAX),
                u64::try_from(allowed).unwrap_or(u64::MAX),
            ));
        }
        let mut pass_started = false;
        let outcome = (|| {
            if !direct.is_empty() {
                validator.begin_pass(state, &projection, control)?;
                pass_started = true;
            }
            let mut checked = 0_usize;
            for assignment in direct {
                control.poll()?;
                let blocker = assignment.blocker.ok_or_else(|| {
                    BlockingError::invariant("direct provisional block has no blocker")
                })?;
                let signature = self.checker().signature(&projection, assignment.node)?;
                let decision = validator.validate_block(
                    state,
                    &projection,
                    assignment.node,
                    blocker,
                    &signature,
                    control,
                )?;
                decision.validate()?;
                checked = checked.saturating_add(1);
                control.poll()?;
                if decision.valid {
                    self.record_validation(
                        BlockingEvent::BlockValidated,
                        assignment.node,
                        blocker,
                        projection.state_digest_hex(),
                        Vec::new(),
                    );
                    continue;
                }
                self.rejected_blocks_mut()
                    .insert((assignment.node, blocker), projection.state_digest());
                self.set_validated_digest(None);
                let replacement = BlockingAssignment::unblocked(assignment.node);
                let before = self.replace_assignment(replacement);
                let assignment_changes = vec![AssignmentChange {
                    node: assignment.node,
                    before,
                    after: Some(replacement),
                }];
                let mut reschedule_nodes = decision.reschedule_nodes;
                reschedule_nodes.push(assignment.node);
                reschedule_nodes.sort_unstable();
                reschedule_nodes.dedup();
                self.record_validation(
                    BlockingEvent::BlockRejected,
                    assignment.node,
                    blocker,
                    projection.state_digest_hex(),
                    decision
                        .violation_ids
                        .iter()
                        .copied()
                        .map(u64::from)
                        .collect(),
                );
                self.invalidate_node(assignment.node);
                return Ok(ValidationPassResult {
                    valid: false,
                    checked_blocks: checked,
                    invalidated_blocks: 1,
                    promote_fact_ids: decision.promote_fact_ids,
                    reschedule_nodes,
                    violation_ids: decision.violation_ids,
                    state_digest: projection.state_digest_hex(),
                    assignment_changes,
                });
            }
            self.set_validated_digest(Some(projection.state_digest()));
            control.poll()?;
            Ok(ValidationPassResult {
                valid: true,
                checked_blocks: checked,
                invalidated_blocks: 0,
                promote_fact_ids: Vec::new(),
                reschedule_nodes: Vec::new(),
                violation_ids: Vec::new(),
                state_digest: projection.state_digest_hex(),
                assignment_changes: Vec::new(),
            })
        })();
        if pass_started {
            validator.end_pass();
        }
        if outcome.is_err() {
            self.restore(checkpoint);
        }
        outcome
    }

    pub fn validation_and_apply<
        S: BlockingStateMutate<Node = N>,
        C: BlockingControl,
        V: BlockValidator<S>,
    >(
        &mut self,
        state: &mut S,
        validator: &mut V,
        control: &C,
        force_full: bool,
    ) -> Result<(ComputeResult<N>, ValidationPassResult<N>), BlockingError> {
        let checkpoint = self.checkpoint();
        let outcome = state.blocking_atomic(|state| {
            let compute = self.compute(state, control, force_full)?;
            control.poll()?;
            for change in &compute.changed {
                state.apply_assignment_change(change)?;
                control.poll()?;
            }
            for node in &compute.reschedule_nodes {
                state.reschedule_existentials(*node)?;
                control.poll()?;
            }
            let validation = self.validation_pass(state, validator, control)?;
            control.poll()?;
            for change in &validation.assignment_changes {
                state.apply_assignment_change(change)?;
                control.poll()?;
            }
            for row_id in &validation.promote_fact_ids {
                state.promote_core_fact(*row_id)?;
                control.poll()?;
            }
            for node in &validation.reschedule_nodes {
                state.reschedule_existentials(*node)?;
                control.poll()?;
            }
            Ok((compute, validation))
        });
        if outcome.is_err() {
            self.restore(checkpoint);
        }
        outcome
    }
}

fn strictly_sorted<T: Ord>(values: &[T]) -> bool {
    values.windows(2).all(|pair| pair[0] < pair[1])
}
