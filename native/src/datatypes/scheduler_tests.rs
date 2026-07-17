// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::BTreeSet;
use std::sync::atomic::{AtomicU64, Ordering};

use num_bigint::BigInt;

use super::*;
use crate::datatypes::value::{DatatypeErrorKind, ExactRational, NeverCancel};

fn variable(stable_id: u32, slot: u32, generation: u32) -> Result<DatatypeVariable, DatatypeError> {
    DatatypeVariable::new(stable_id, NodeHandle::new(slot, generation))
}

fn handle(slot: u32, generation: u32) -> Result<DatatypeConstraintHandle, DatatypeError> {
    DatatypeConstraintHandle::new(slot, generation)
}

fn dependencies(levels: &[u32]) -> Result<DependencySet, Box<dyn std::error::Error>> {
    Ok(DependencySet::new(levels.to_vec())?)
}

fn number(value: i64) -> Result<DataIdentity, DatatypeError> {
    Ok(DataIdentity::Numeric(ExactRational::new(
        BigInt::from(value),
        BigInt::from(1_u8),
    )?))
}

fn finite(values: &[i64]) -> Result<DomainKind, DatatypeError> {
    Ok(DomainKind::Finite(
        values
            .iter()
            .map(|value| number(*value))
            .collect::<Result<BTreeSet<_>, _>>()?,
    ))
}

fn domain(
    constraint: DatatypeConstraintHandle,
    participant_id: u32,
    variable: DatatypeVariable,
    values: &[i64],
    levels: &[u32],
) -> Result<ScheduledConstraintRecord, Box<dyn std::error::Error>> {
    Ok(ScheduledConstraintRecord {
        handle: constraint,
        participant_id,
        constraint: ScheduledConstraint::Domain {
            variable,
            domain: finite(values)?,
            dependencies: dependencies(levels)?,
        },
    })
}

fn fixed(
    constraint: DatatypeConstraintHandle,
    participant_id: u32,
    variable: DatatypeVariable,
    value: i64,
    levels: &[u32],
) -> Result<ScheduledConstraintRecord, Box<dyn std::error::Error>> {
    Ok(ScheduledConstraintRecord {
        handle: constraint,
        participant_id,
        constraint: ScheduledConstraint::FixedValue {
            variable,
            value: number(value)?,
            dependencies: dependencies(levels)?,
        },
    })
}

fn inequality(
    constraint: DatatypeConstraintHandle,
    participant_id: u32,
    left: DatatypeVariable,
    right: DatatypeVariable,
    levels: &[u32],
) -> Result<ScheduledConstraintRecord, Box<dyn std::error::Error>> {
    Ok(ScheduledConstraintRecord {
        handle: constraint,
        participant_id,
        constraint: ScheduledConstraint::Inequality {
            left,
            right,
            dependencies: dependencies(levels)?,
        },
    })
}

fn scheduler() -> Result<DatatypeScheduler, DatatypeError> {
    DatatypeScheduler::new(SchedulerLimits::default())
}

#[test]
fn dirty_variables_coalesce_and_only_the_affected_component_rechecks(
) -> Result<(), Box<dyn std::error::Error>> {
    let (a, b, c, d) = (
        variable(10, 0, 1)?,
        variable(11, 1, 1)?,
        variable(12, 2, 1)?,
        variable(13, 3, 1)?,
    );
    let mut selected = scheduler()?;
    selected.upsert_constraint(domain(handle(0, 1)?, 100, a, &[0, 1], &[])?)?;
    selected.upsert_constraint(domain(handle(1, 1)?, 101, b, &[0, 1], &[])?)?;
    selected.upsert_constraint(inequality(handle(2, 1)?, 102, a, b, &[])?)?;
    selected.upsert_constraint(domain(handle(3, 1)?, 103, c, &[2], &[])?)?;
    selected.upsert_constraint(domain(handle(4, 1)?, 104, d, &[3], &[])?)?;

    let first = selected.check_dirty(SolverLimits::default(), &NeverCancel)?;
    assert_eq!(first.checked_components, 3);
    assert_eq!(first.checked_variables, 4);
    assert!(first.clash.is_none());
    assert_eq!(selected.cached_components().len(), 3);
    assert_eq!(
        selected
            .check_dirty(SolverLimits::default(), &NeverCancel)?
            .checked_components,
        0
    );

    selected.upsert_constraint(domain(handle(0, 1)?, 105, a, &[0, 1, 2], &[2])?)?;
    assert!(selected.cached_component(a).is_none());
    assert!(selected.cached_component(c).is_some());
    let second = selected.check_dirty(SolverLimits::default(), &NeverCancel)?;
    assert_eq!(second.checked_components, 1);
    assert_eq!(second.checked_variables, 2);
    assert!(selected.cached_component(a).is_some());
    assert!(selected.cached_component(c).is_some());
    selected.check_invariants()?;
    Ok(())
}

#[test]
fn bridge_addition_merges_once_and_removal_rechecks_each_split(
) -> Result<(), Box<dyn std::error::Error>> {
    let variables = [
        variable(20, 0, 1)?,
        variable(21, 1, 1)?,
        variable(22, 2, 1)?,
        variable(23, 3, 1)?,
    ];
    let mut selected = scheduler()?;
    for (index, current) in variables.iter().enumerate() {
        let slot = u32::try_from(index)?;
        selected.upsert_constraint(domain(
            handle(slot, 1)?,
            200 + slot,
            *current,
            &[0, 1, 2, 3],
            &[],
        )?)?;
    }
    selected.upsert_constraint(inequality(
        handle(4, 1)?,
        204,
        variables[0],
        variables[1],
        &[],
    )?)?;
    selected.upsert_constraint(inequality(
        handle(5, 1)?,
        205,
        variables[2],
        variables[3],
        &[],
    )?)?;
    assert_eq!(
        selected
            .check_dirty(SolverLimits::default(), &NeverCancel)?
            .checked_components,
        2
    );

    let bridge = handle(6, 1)?;
    selected.upsert_constraint(inequality(bridge, 206, variables[1], variables[2], &[])?)?;
    let merged = selected.check_dirty(SolverLimits::default(), &NeverCancel)?;
    assert_eq!(
        (merged.checked_components, merged.checked_variables),
        (1, 4)
    );
    assert_eq!(selected.cached_components().len(), 1);

    assert!(selected.remove_constraint(bridge)?);
    let split = selected.check_dirty(SolverLimits::default(), &NeverCancel)?;
    assert_eq!((split.checked_components, split.checked_variables), (2, 4));
    assert_eq!(selected.cached_components().len(), 2);
    selected.check_invariants()?;
    Ok(())
}

#[test]
fn solver_clash_keeps_dependencies_and_deterministic_participants(
) -> Result<(), Box<dyn std::error::Error>> {
    let a = variable(30, 0, 1)?;
    let mut selected = scheduler()?;
    selected.upsert_constraint(domain(handle(3, 1)?, 91, a, &[1], &[3])?)?;
    selected.upsert_constraint(fixed(handle(1, 1)?, 17, a, 2, &[7])?)?;
    let result = selected.check_dirty(SolverLimits::default(), &NeverCancel)?;
    let clash = result
        .clash
        .ok_or_else(|| DatatypeError::invalid("expected scheduled datatype clash"))?;
    assert_eq!(clash.clash.dependencies.as_slice(), &[3, 7]);
    assert_eq!(clash.variables, vec![a]);
    assert_eq!(clash.constraints, vec![handle(1, 1)?, handle(3, 1)?]);
    assert_eq!(clash.participants, vec![17, 91]);
    assert_eq!(result.checked_components, 1);
    assert_eq!(selected.dirty_count(), 0);
    selected.check_invariants()?;
    Ok(())
}

#[test]
fn checkpoint_rollback_restores_cache_dirty_state_and_invalidates_future_tokens(
) -> Result<(), Box<dyn std::error::Error>> {
    let a = variable(40, 0, 1)?;
    let mut selected = scheduler()?;
    selected.upsert_constraint(domain(handle(0, 1)?, 400, a, &[1, 2], &[])?)?;
    selected.check_dirty(SolverLimits::default(), &NeverCancel)?;
    let baseline = selected.diagnostics();
    let root = selected.checkpoint(&NeverCancel)?;

    selected.upsert_constraint(fixed(handle(1, 1)?, 401, a, 3, &[0])?)?;
    assert!(selected
        .check_dirty(SolverLimits::default(), &NeverCancel)?
        .clash
        .is_some());
    let future = selected.checkpoint(&NeverCancel)?;
    selected.rollback(root)?;
    assert_eq!(selected.diagnostics(), baseline);
    assert_eq!(
        selected
            .check_dirty(SolverLimits::default(), &NeverCancel)?
            .checked_components,
        0
    );
    assert_eq!(
        selected.rollback(future).err().map(|error| error.kind),
        Some(DatatypeErrorKind::Invalid)
    );
    selected.rollback(root)?;

    let mut other = scheduler()?;
    assert_eq!(
        other.rollback(root).err().map(|error| error.kind),
        Some(DatatypeErrorKind::Invalid)
    );
    selected.check_invariants()?;
    Ok(())
}

#[test]
fn recycled_slots_never_alias_stale_variable_or_constraint_generations(
) -> Result<(), Box<dyn std::error::Error>> {
    let old = variable(50, 7, 1)?;
    let new = variable(51, 7, 2)?;
    let old_constraint = handle(9, 1)?;
    let new_constraint = handle(9, 2)?;
    let mut selected = scheduler()?;
    selected.upsert_constraint(domain(old_constraint, 500, old, &[1], &[])?)?;
    selected.check_dirty(SolverLimits::default(), &NeverCancel)?;
    assert!(selected.remove_constraint(old_constraint)?);
    selected.upsert_constraint(domain(new_constraint, 501, new, &[2], &[])?)?;
    let checked = selected.check_dirty(SolverLimits::default(), &NeverCancel)?;
    assert_eq!(
        (checked.checked_components, checked.checked_variables),
        (1, 1)
    );
    assert!(selected.cached_component(old).is_none());
    assert!(selected.cached_component(new).is_some());

    assert_eq!(
        selected.mark_dirty(old).err().map(|error| error.kind),
        Some(DatatypeErrorKind::Invalid)
    );
    assert_eq!(
        selected
            .remove_constraint(old_constraint)
            .err()
            .map(|error| error.kind),
        Some(DatatypeErrorKind::Invalid)
    );
    let changed_stable_handle = variable(50, 8, 1)?;
    assert_eq!(
        selected
            .upsert_constraint(domain(
                handle(10, 1)?,
                502,
                changed_stable_handle,
                &[1],
                &[],
            )?)
            .err()
            .map(|error| error.kind),
        Some(DatatypeErrorKind::Invalid)
    );
    selected.check_invariants()?;
    Ok(())
}

struct CancelAfter {
    polls: AtomicU64,
    allowed: u64,
}

impl DatatypeControl for CancelAfter {
    fn poll(&self) -> Result<(), DatatypeError> {
        let prior = self.polls.fetch_add(1, Ordering::Relaxed);
        if prior >= self.allowed {
            Err(DatatypeError::cancelled(
                "scheduled datatype test cancellation",
            ))
        } else {
            Ok(())
        }
    }
}

struct RejectMemory;

impl DatatypeControl for RejectMemory {
    fn poll(&self) -> Result<(), DatatypeError> {
        Ok(())
    }

    fn observe_memory(&self, bytes: u64) -> Result<(), DatatypeError> {
        Err(DatatypeError::resource("memory_bytes", bytes, 0))
    }
}

#[test]
fn cancellation_and_solver_resource_errors_leave_dirty_state_unmodified(
) -> Result<(), Box<dyn std::error::Error>> {
    let (a, b) = (variable(60, 0, 1)?, variable(61, 1, 1)?);
    let mut selected = scheduler()?;
    selected.upsert_constraint(domain(handle(0, 1)?, 600, a, &[0, 1], &[])?)?;
    selected.upsert_constraint(domain(handle(1, 1)?, 601, b, &[0, 1], &[])?)?;
    selected.upsert_constraint(inequality(handle(2, 1)?, 602, a, b, &[])?)?;
    let before = selected.diagnostics();
    let control = CancelAfter {
        polls: AtomicU64::new(0),
        allowed: 1,
    };
    assert_eq!(
        selected
            .check_dirty(SolverLimits::default(), &control)
            .err()
            .map(|error| error.kind),
        Some(DatatypeErrorKind::Cancelled)
    );
    assert_eq!(selected.diagnostics(), before);

    let constrained = SolverLimits {
        max_steps: 1,
        ..SolverLimits::default()
    };
    assert_eq!(
        selected
            .check_dirty(constrained, &NeverCancel)
            .err()
            .map(|error| error.kind),
        Some(DatatypeErrorKind::Resource)
    );
    assert_eq!(selected.diagnostics(), before);

    assert_eq!(
        selected
            .check_dirty(SolverLimits::default(), &RejectMemory)
            .err()
            .map(|error| error.limit),
        Some(Some("memory_bytes"))
    );
    assert_eq!(selected.diagnostics(), before);
    assert_eq!(selected.checkpoint_count(), 0);
    assert_eq!(
        selected
            .checkpoint(&RejectMemory)
            .err()
            .map(|error| error.limit),
        Some(Some("memory_bytes"))
    );
    assert_eq!(selected.checkpoint_count(), 0);
    selected.check_invariants()?;
    Ok(())
}

#[test]
fn scheduler_limits_reject_mutation_and_check_without_partial_state(
) -> Result<(), Box<dyn std::error::Error>> {
    let limits = SchedulerLimits {
        max_dirty_variables: 1,
        max_scheduler_steps: 1,
        ..SchedulerLimits::default()
    };
    let (a, b) = (variable(70, 0, 1)?, variable(71, 1, 1)?);
    let mut selected = DatatypeScheduler::new(limits)?;
    selected.upsert_constraint(domain(handle(0, 1)?, 700, a, &[0], &[])?)?;
    let before_add = selected.diagnostics();
    assert_eq!(
        selected
            .upsert_constraint(domain(handle(1, 1)?, 701, b, &[1], &[])?)
            .err()
            .map(|error| error.kind),
        Some(DatatypeErrorKind::Resource)
    );
    assert_eq!(selected.diagnostics(), before_add);
    assert_eq!(selected.constraint_count(), 1);

    let before_check = selected.diagnostics();
    assert_eq!(
        selected
            .check_dirty(SolverLimits::default(), &NeverCancel)
            .err()
            .map(|error| error.kind),
        Some(DatatypeErrorKind::Resource)
    );
    assert_eq!(selected.diagnostics(), before_check);
    selected.check_invariants()?;
    Ok(())
}

#[test]
fn early_clash_stays_visible_and_leaves_later_components_dirty_until_rollback(
) -> Result<(), Box<dyn std::error::Error>> {
    let (a, b) = (variable(80, 0, 1)?, variable(81, 1, 1)?);
    let mut selected = scheduler()?;
    selected.upsert_constraint(domain(handle(0, 1)?, 800, a, &[1], &[0])?)?;
    selected.upsert_constraint(fixed(handle(1, 1)?, 801, a, 2, &[1])?)?;
    selected.upsert_constraint(domain(handle(2, 1)?, 802, b, &[3], &[])?)?;
    let first = selected.check_dirty(SolverLimits::default(), &NeverCancel)?;
    assert!(first.clash.is_some());
    assert_eq!(first.checked_components, 1);
    assert_eq!(selected.dirty_count(), 1);

    let repeated = selected.check_dirty(SolverLimits::default(), &NeverCancel)?;
    assert!(repeated.clash.is_some());
    assert_eq!(repeated.checked_components, 0);
    assert_eq!(selected.dirty_count(), 1);

    assert!(selected.remove_constraint(handle(1, 1)?)?);
    let resumed = selected.check_dirty(SolverLimits::default(), &NeverCancel)?;
    assert!(resumed.clash.is_none());
    assert_eq!(resumed.checked_components, 2);
    assert_eq!(selected.dirty_count(), 0);
    assert_eq!(selected.cached_components().len(), 2);
    selected.check_invariants()?;
    Ok(())
}

#[test]
fn checkpoint_limit_and_release_are_bounded_and_owner_safe(
) -> Result<(), Box<dyn std::error::Error>> {
    let limits = SchedulerLimits {
        max_checkpoints: 1,
        ..SchedulerLimits::default()
    };
    let mut selected = DatatypeScheduler::new(limits)?;
    let checkpoint = selected.checkpoint(&NeverCancel)?;
    assert_eq!(selected.checkpoint_count(), 1);
    assert_eq!(
        selected
            .checkpoint(&NeverCancel)
            .err()
            .map(|error| error.kind),
        Some(DatatypeErrorKind::Resource)
    );
    assert!(selected.release_checkpoint(checkpoint)?);
    assert!(!selected.release_checkpoint(checkpoint)?);
    assert_eq!(selected.checkpoint_count(), 0);
    Ok(())
}
