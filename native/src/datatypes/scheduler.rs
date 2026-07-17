//! Deterministic dirty-component scheduling for native datatype constraints.
//!
//! The scheduler owns no tableau rows or node lifecycle.  Its integration contract is
//! deliberately narrow: the tableau adapter projects every active datatype assertion
//! into a generation-stamped constraint record and captures this scheduler's checkpoint
//! beside the store checkpoint.  Constraint mutation, component caching, and rollback
//! then remain independent of store allocation order.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::model::{DependencySet, NodeHandle};

use super::solver::{
    solve_component, CardinalityConstraint, ConstraintComponent, DatatypeClash, DomainConstraint,
    DomainKind, EqualityConstraint, FixedValueConstraint, InequalityConstraint, SolveResult,
    SolverLimits,
};
use super::value::{DataIdentity, DatatypeControl, DatatypeError};

static NEXT_SCHEDULER_ID: AtomicU64 = AtomicU64::new(1);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DatatypeVariable {
    stable_id: u32,
    node: NodeHandle,
}

impl DatatypeVariable {
    pub fn new(stable_id: u32, node: NodeHandle) -> Result<Self, DatatypeError> {
        if node.generation == 0 {
            return Err(DatatypeError::invalid(
                "datatype variable node generations must be positive",
            ));
        }
        Ok(Self { stable_id, node })
    }

    #[must_use]
    pub const fn stable_id(self) -> u32 {
        self.stable_id
    }

    #[must_use]
    pub const fn node(self) -> NodeHandle {
        self.node
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DatatypeConstraintHandle {
    slot: u32,
    generation: u32,
}

impl DatatypeConstraintHandle {
    pub fn new(slot: u32, generation: u32) -> Result<Self, DatatypeError> {
        if generation == 0 {
            return Err(DatatypeError::invalid(
                "datatype constraint generations must be positive",
            ));
        }
        Ok(Self { slot, generation })
    }

    #[must_use]
    pub const fn slot(self) -> u32 {
        self.slot
    }

    #[must_use]
    pub const fn generation(self) -> u32 {
        self.generation
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ScheduledConstraint {
    Domain {
        variable: DatatypeVariable,
        domain: DomainKind,
        dependencies: DependencySet,
    },
    FixedValue {
        variable: DatatypeVariable,
        value: DataIdentity,
        dependencies: DependencySet,
    },
    Equality {
        left: DatatypeVariable,
        right: DatatypeVariable,
        dependencies: DependencySet,
    },
    Inequality {
        left: DatatypeVariable,
        right: DatatypeVariable,
        dependencies: DependencySet,
    },
    Cardinality {
        variable: DatatypeVariable,
        minimum: u32,
        dependencies: DependencySet,
    },
}

impl ScheduledConstraint {
    #[must_use]
    pub fn variables(&self) -> Vec<DatatypeVariable> {
        let mut variables = match self {
            Self::Domain { variable, .. }
            | Self::FixedValue { variable, .. }
            | Self::Cardinality { variable, .. } => vec![*variable],
            Self::Equality { left, right, .. } | Self::Inequality { left, right, .. } => {
                vec![*left, *right]
            }
        };
        variables.sort_unstable();
        variables.dedup();
        variables
    }

    #[must_use]
    pub const fn dependencies(&self) -> &DependencySet {
        match self {
            Self::Domain { dependencies, .. }
            | Self::FixedValue { dependencies, .. }
            | Self::Equality { dependencies, .. }
            | Self::Inequality { dependencies, .. }
            | Self::Cardinality { dependencies, .. } => dependencies,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScheduledConstraintRecord {
    pub handle: DatatypeConstraintHandle,
    pub participant_id: u32,
    pub constraint: ScheduledConstraint,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SchedulerLimits {
    pub max_active_constraints: u32,
    pub max_active_variables: u32,
    pub max_dirty_variables: u32,
    pub max_components_per_check: u32,
    pub max_scheduler_steps: u64,
    pub max_checkpoints: u32,
    pub cancellation_poll_stride: u64,
}

impl Default for SchedulerLimits {
    fn default() -> Self {
        Self {
            max_active_constraints: 5_000_000,
            max_active_variables: 1_000_000,
            max_dirty_variables: 1_000_000,
            max_components_per_check: 1_000_000,
            max_scheduler_steps: 5_000_000,
            max_checkpoints: 100_000,
            cancellation_poll_stride: 64,
        }
    }
}

impl SchedulerLimits {
    fn validate(self) -> Result<Self, DatatypeError> {
        let values = [
            (
                "max_active_constraints",
                u64::from(self.max_active_constraints),
            ),
            ("max_active_variables", u64::from(self.max_active_variables)),
            ("max_dirty_variables", u64::from(self.max_dirty_variables)),
            (
                "max_components_per_check",
                u64::from(self.max_components_per_check),
            ),
            ("max_scheduler_steps", self.max_scheduler_steps),
            ("max_checkpoints", u64::from(self.max_checkpoints)),
            ("cancellation_poll_stride", self.cancellation_poll_stride),
        ];
        if let Some((name, _value)) = values.into_iter().find(|(_name, value)| *value == 0) {
            return Err(DatatypeError::invalid(format!(
                "native datatype scheduler limit must be positive: {name}"
            )));
        }
        Ok(self)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScheduledComponentResult {
    pub variables: Vec<DatatypeVariable>,
    pub constraints: Vec<DatatypeConstraintHandle>,
    pub participants: Vec<u32>,
    pub result: SolveResult,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScheduledDatatypeClash {
    pub clash: DatatypeClash,
    pub variables: Vec<DatatypeVariable>,
    pub constraints: Vec<DatatypeConstraintHandle>,
    pub participants: Vec<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SchedulerCheckResult {
    pub checked_components: u32,
    pub checked_variables: u32,
    pub changed: bool,
    pub clash: Option<ScheduledDatatypeClash>,
}

impl SchedulerCheckResult {
    const fn no_work() -> Self {
        Self {
            checked_components: 0,
            checked_variables: 0,
            changed: false,
            clash: None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SchedulerCheckpoint {
    owner: u64,
    sequence: u64,
}

impl SchedulerCheckpoint {
    #[must_use]
    pub const fn sequence(self) -> u64 {
        self.sequence
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SchedulerDiagnostics {
    pub revision: u64,
    pub active_constraints: u32,
    pub active_variables: u32,
    pub dirty_variables: Vec<DatatypeVariable>,
    pub cached_components: Vec<Vec<DatatypeVariable>>,
}

#[derive(Clone, Debug)]
struct SchedulerState {
    constraints: BTreeMap<DatatypeConstraintHandle, ScheduledConstraintRecord>,
    constraint_by_slot: BTreeMap<u32, DatatypeConstraintHandle>,
    maximum_constraint_generation: BTreeMap<u32, u32>,
    constraints_by_variable: BTreeMap<DatatypeVariable, BTreeSet<DatatypeConstraintHandle>>,
    variable_references: BTreeMap<DatatypeVariable, u32>,
    active_variable_by_stable_id: BTreeMap<u32, DatatypeVariable>,
    active_variable_by_slot: BTreeMap<u32, DatatypeVariable>,
    seen_handle_by_stable_id: BTreeMap<u32, NodeHandle>,
    seen_variable_by_handle: BTreeMap<NodeHandle, u32>,
    maximum_variable_generation: BTreeMap<u32, u32>,
    dirty: BTreeSet<DatatypeVariable>,
    cached: BTreeMap<Vec<DatatypeVariable>, ScheduledComponentResult>,
    revision: u64,
}

impl SchedulerState {
    const fn new() -> Self {
        Self {
            constraints: BTreeMap::new(),
            constraint_by_slot: BTreeMap::new(),
            maximum_constraint_generation: BTreeMap::new(),
            constraints_by_variable: BTreeMap::new(),
            variable_references: BTreeMap::new(),
            active_variable_by_stable_id: BTreeMap::new(),
            active_variable_by_slot: BTreeMap::new(),
            seen_handle_by_stable_id: BTreeMap::new(),
            seen_variable_by_handle: BTreeMap::new(),
            maximum_variable_generation: BTreeMap::new(),
            dirty: BTreeSet::new(),
            cached: BTreeMap::new(),
            revision: 0,
        }
    }
}

#[derive(Clone, Debug)]
struct StoredCheckpoint {
    state: SchedulerState,
}

#[derive(Debug)]
pub struct DatatypeScheduler {
    owner: u64,
    limits: SchedulerLimits,
    state: SchedulerState,
    checkpoints: BTreeMap<u64, StoredCheckpoint>,
    next_checkpoint_sequence: u64,
}

impl DatatypeScheduler {
    pub fn new(limits: SchedulerLimits) -> Result<Self, DatatypeError> {
        let limits = limits.validate()?;
        let owner = NEXT_SCHEDULER_ID
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
                value.checked_add(1)
            })
            .map_err(|_| DatatypeError::invalid("datatype scheduler owner ID overflow"))?;
        Ok(Self {
            owner,
            limits,
            state: SchedulerState::new(),
            checkpoints: BTreeMap::new(),
            next_checkpoint_sequence: 1,
        })
    }

    #[must_use]
    pub const fn limits(&self) -> SchedulerLimits {
        self.limits
    }

    #[must_use]
    pub fn constraint_count(&self) -> usize {
        self.state.constraints.len()
    }

    #[must_use]
    pub fn dirty_count(&self) -> usize {
        self.state.dirty.len()
    }

    #[must_use]
    pub fn checkpoint_count(&self) -> usize {
        self.checkpoints.len()
    }

    #[must_use]
    pub fn diagnostics(&self) -> SchedulerDiagnostics {
        SchedulerDiagnostics {
            revision: self.state.revision,
            active_constraints: u32::try_from(self.state.constraints.len()).unwrap_or(u32::MAX),
            active_variables: u32::try_from(self.state.variable_references.len())
                .unwrap_or(u32::MAX),
            dirty_variables: self.state.dirty.iter().copied().collect(),
            cached_components: self.state.cached.keys().cloned().collect(),
        }
    }

    #[must_use]
    pub fn cached_component(
        &self,
        variable: DatatypeVariable,
    ) -> Option<&ScheduledComponentResult> {
        self.state
            .cached
            .values()
            .find(|component| component.variables.binary_search(&variable).is_ok())
    }

    #[must_use]
    pub fn cached_components(&self) -> Vec<&ScheduledComponentResult> {
        self.state.cached.values().collect()
    }

    pub fn upsert_constraint(
        &mut self,
        record: ScheduledConstraintRecord,
    ) -> Result<bool, DatatypeError> {
        Self::validate_record(&record)?;
        if self.state.constraints.get(&record.handle) == Some(&record) {
            return Ok(false);
        }
        self.validate_constraint_handle(record.handle)?;
        let old = self.state.constraints.get(&record.handle).cloned();
        let old_variables = old
            .as_ref()
            .map_or_else(Vec::new, |value| value.constraint.variables());
        let new_variables = record.constraint.variables();
        self.validate_variable_transition(&old_variables, &new_variables)?;
        self.validate_prospective_sizes(old.as_ref(), &record, &old_variables, &new_variables)?;
        let dirty = old_variables
            .iter()
            .chain(&new_variables)
            .copied()
            .collect::<BTreeSet<_>>();
        self.validate_dirty_union(&dirty)?;
        let revision = self
            .state
            .revision
            .checked_add(1)
            .ok_or_else(|| DatatypeError::invalid("datatype scheduler revision overflow"))?;

        if let Some(prior) = old.as_ref() {
            self.detach_record(prior);
        }
        let handle = record.handle;
        self.attach_record(&record);
        self.state.constraints.insert(handle, record);
        self.state.constraint_by_slot.insert(handle.slot, handle);
        self.state
            .maximum_constraint_generation
            .entry(handle.slot)
            .and_modify(|value| *value = (*value).max(handle.generation))
            .or_insert(handle.generation);
        self.state.dirty.extend(dirty.iter().copied());
        self.invalidate_cache_for(&dirty);
        self.state.revision = revision;
        Ok(true)
    }

    pub fn remove_constraint(
        &mut self,
        handle: DatatypeConstraintHandle,
    ) -> Result<bool, DatatypeError> {
        let Some(record) = self.state.constraints.get(&handle).cloned() else {
            if self
                .state
                .constraint_by_slot
                .get(&handle.slot)
                .is_some_and(|active| *active != handle)
            {
                return Err(DatatypeError::invalid("stale datatype constraint handle"));
            }
            return Ok(false);
        };
        let variables = record.constraint.variables();
        let dirty = variables.iter().copied().collect::<BTreeSet<_>>();
        self.validate_dirty_union(&dirty)?;
        let revision = self
            .state
            .revision
            .checked_add(1)
            .ok_or_else(|| DatatypeError::invalid("datatype scheduler revision overflow"))?;
        self.detach_record(&record);
        self.state.constraints.remove(&handle);
        self.state.constraint_by_slot.remove(&handle.slot);
        self.state.dirty.extend(variables);
        self.invalidate_cache_for(&dirty);
        self.state.revision = revision;
        Ok(true)
    }

    pub fn mark_dirty(&mut self, variable: DatatypeVariable) -> Result<bool, DatatypeError> {
        self.validate_active_variable(variable)?;
        if self.state.dirty.contains(&variable) {
            return Ok(false);
        }
        self.validate_dirty_union(&BTreeSet::from([variable]))?;
        let revision = self
            .state
            .revision
            .checked_add(1)
            .ok_or_else(|| DatatypeError::invalid("datatype scheduler revision overflow"))?;
        self.state.dirty.insert(variable);
        self.invalidate_cache_for(&BTreeSet::from([variable]));
        self.state.revision = revision;
        Ok(true)
    }

    pub fn mark_all_dirty(&mut self) -> Result<bool, DatatypeError> {
        let variables: BTreeSet<_> = self.state.variable_references.keys().copied().collect();
        if variables.is_subset(&self.state.dirty) {
            return Ok(false);
        }
        self.validate_dirty_union(&variables)?;
        let revision = self
            .state
            .revision
            .checked_add(1)
            .ok_or_else(|| DatatypeError::invalid("datatype scheduler revision overflow"))?;
        self.state.dirty.extend(variables);
        self.state.cached.clear();
        self.state.revision = revision;
        Ok(true)
    }

    pub fn checkpoint(
        &mut self,
        control: &impl DatatypeControl,
    ) -> Result<SchedulerCheckpoint, DatatypeError> {
        let observed = u64::try_from(self.checkpoints.len())
            .unwrap_or(u64::MAX)
            .saturating_add(1);
        if observed > u64::from(self.limits.max_checkpoints) {
            return Err(DatatypeError::resource(
                "max_scheduler_checkpoints",
                observed,
                u64::from(self.limits.max_checkpoints),
            ));
        }
        control.poll()?;
        control.observe_memory(self.estimated_state_bytes())?;
        let sequence = self.next_checkpoint_sequence;
        let next = sequence
            .checked_add(1)
            .ok_or_else(|| DatatypeError::invalid("datatype scheduler checkpoint overflow"))?;
        let snapshot = StoredCheckpoint {
            state: self.state.clone(),
        };
        self.checkpoints.insert(sequence, snapshot);
        self.next_checkpoint_sequence = next;
        Ok(SchedulerCheckpoint {
            owner: self.owner,
            sequence,
        })
    }

    pub fn rollback(&mut self, checkpoint: SchedulerCheckpoint) -> Result<(), DatatypeError> {
        self.validate_checkpoint(checkpoint)?;
        let state = self
            .checkpoints
            .get(&checkpoint.sequence)
            .map(|value| value.state.clone())
            .ok_or_else(|| DatatypeError::invalid("datatype scheduler checkpoint is stale"))?;
        self.state = state;
        self.checkpoints
            .retain(|sequence, _snapshot| *sequence <= checkpoint.sequence);
        self.check_invariants()
    }

    pub fn release_checkpoint(
        &mut self,
        checkpoint: SchedulerCheckpoint,
    ) -> Result<bool, DatatypeError> {
        if checkpoint.owner != self.owner {
            return Err(DatatypeError::invalid(
                "datatype scheduler checkpoint belongs to another scheduler",
            ));
        }
        Ok(self.checkpoints.remove(&checkpoint.sequence).is_some())
    }

    pub fn check_dirty(
        &mut self,
        solver_limits: SolverLimits,
        control: &impl DatatypeControl,
    ) -> Result<SchedulerCheckResult, DatatypeError> {
        control.poll()?;
        if let Some(component) = self
            .state
            .cached
            .values()
            .find(|component| component.result.clash.is_some())
        {
            return Ok(SchedulerCheckResult {
                checked_components: 0,
                checked_variables: 0,
                changed: false,
                clash: scheduled_clash(component),
            });
        }
        if self.state.dirty.is_empty() {
            return Ok(SchedulerCheckResult::no_work());
        }
        control.observe_memory(self.estimated_check_bytes())?;
        self.state
            .revision
            .checked_add(1)
            .ok_or_else(|| DatatypeError::invalid("datatype scheduler revision overflow"))?;
        let mut work = SchedulerWork::new(self.limits, control);
        let (plans, orphaned) = self.affected_components(&mut work)?;
        if plans.len() > usize::try_from(self.limits.max_components_per_check).unwrap_or(usize::MAX)
        {
            return Err(DatatypeError::resource(
                "max_scheduler_components",
                u64::try_from(plans.len()).unwrap_or(u64::MAX),
                u64::from(self.limits.max_components_per_check),
            ));
        }

        let mut checked = Vec::new();
        let mut checked_variables = 0_u32;
        let mut clash = None;
        for plan in plans {
            work.add(
                u64::try_from(plan.variables.len())
                    .unwrap_or(u64::MAX)
                    .saturating_add(u64::try_from(plan.constraints.len()).unwrap_or(u64::MAX)),
            )?;
            control.observe_memory(estimate_plan_bytes(&plan))?;
            let component = self.compile_component(&plan)?;
            let result = solve_component(&component, solver_limits, control)?;
            checked_variables = checked_variables
                .checked_add(u32::try_from(plan.variables.len()).unwrap_or(u32::MAX))
                .ok_or_else(|| {
                    DatatypeError::invalid("datatype scheduler checked-variable overflow")
                })?;
            let scheduled = ScheduledComponentResult {
                variables: plan.variables.clone(),
                constraints: plan.constraints.clone(),
                participants: plan.participants.clone(),
                result,
            };
            if let Some(found) = scheduled.result.clash.as_ref() {
                clash = Some(ScheduledDatatypeClash {
                    clash: found.clone(),
                    variables: scheduled.variables.clone(),
                    constraints: scheduled.constraints.clone(),
                    participants: scheduled.participants.clone(),
                });
                checked.push(CheckedPlan {
                    dirty: plan.dirty,
                    result: scheduled,
                });
                break;
            }
            checked.push(CheckedPlan {
                dirty: plan.dirty,
                result: scheduled,
            });
        }
        control.poll()?;
        let checked_components = u32::try_from(checked.len()).unwrap_or(u32::MAX);
        self.commit_checked(&checked, &orphaned)?;
        Ok(SchedulerCheckResult {
            checked_components,
            checked_variables,
            changed: true,
            clash,
        })
    }

    pub fn check_invariants(&self) -> Result<(), DatatypeError> {
        if self.state.constraints.len() != self.state.constraint_by_slot.len() {
            return Err(DatatypeError::invalid(
                "datatype scheduler constraint slot index is inconsistent",
            ));
        }
        for (handle, record) in &self.state.constraints {
            if record.handle != *handle
                || self.state.constraint_by_slot.get(&handle.slot) != Some(handle)
            {
                return Err(DatatypeError::invalid(
                    "datatype scheduler constraint index points to the wrong record",
                ));
            }
            if self
                .state
                .maximum_constraint_generation
                .get(&handle.slot)
                .is_none_or(|maximum| *maximum < handle.generation)
            {
                return Err(DatatypeError::invalid(
                    "datatype scheduler constraint generation history is inconsistent",
                ));
            }
            for variable in record.constraint.variables() {
                if !self
                    .state
                    .constraints_by_variable
                    .get(&variable)
                    .is_some_and(|values| values.contains(handle))
                {
                    return Err(DatatypeError::invalid(
                        "datatype scheduler variable index omits a constraint",
                    ));
                }
            }
        }
        for (variable, handles) in &self.state.constraints_by_variable {
            if handles.is_empty()
                || self.state.variable_references.get(variable)
                    != u32::try_from(handles.len()).ok().as_ref()
            {
                return Err(DatatypeError::invalid(
                    "datatype scheduler variable reference count is inconsistent",
                ));
            }
            if self
                .state
                .active_variable_by_stable_id
                .get(&variable.stable_id)
                != Some(variable)
                || self.state.active_variable_by_slot.get(&variable.node.slot) != Some(variable)
                || self.state.seen_handle_by_stable_id.get(&variable.stable_id)
                    != Some(&variable.node)
                || self.state.seen_variable_by_handle.get(&variable.node)
                    != Some(&variable.stable_id)
                || self
                    .state
                    .maximum_variable_generation
                    .get(&variable.node.slot)
                    .is_none_or(|maximum| *maximum < variable.node.generation)
            {
                return Err(DatatypeError::invalid(
                    "datatype scheduler active variable registry is inconsistent",
                ));
            }
            for handle in handles {
                if !self
                    .state
                    .constraints
                    .get(handle)
                    .is_some_and(|record| record.constraint.variables().contains(variable))
                {
                    return Err(DatatypeError::invalid(
                        "datatype scheduler variable index contains a foreign constraint",
                    ));
                }
            }
        }
        if self.state.variable_references.len() != self.state.active_variable_by_stable_id.len()
            || self.state.variable_references.len() != self.state.active_variable_by_slot.len()
        {
            return Err(DatatypeError::invalid(
                "datatype scheduler active variable indexes differ in size",
            ));
        }
        for (key, result) in &self.state.cached {
            if key.is_empty() || key.windows(2).any(|pair| pair[0] >= pair[1]) {
                return Err(DatatypeError::invalid(
                    "datatype scheduler cached component key is not canonical",
                ));
            }
            if key
                .iter()
                .any(|variable| self.state.dirty.contains(variable))
            {
                return Err(DatatypeError::invalid(
                    "datatype scheduler retained a dirty cached component",
                ));
            }
            if key != &result.variables
                || result
                    .constraints
                    .iter()
                    .any(|handle| !self.state.constraints.contains_key(handle))
            {
                return Err(DatatypeError::invalid(
                    "datatype scheduler cached component payload is stale",
                ));
            }
        }
        Ok(())
    }

    fn validate_record(record: &ScheduledConstraintRecord) -> Result<(), DatatypeError> {
        let variables = record.constraint.variables();
        if variables.is_empty() {
            return Err(DatatypeError::invalid(
                "scheduled datatype constraints require a variable",
            ));
        }
        if variables.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(DatatypeError::invalid(
                "scheduled datatype constraint variables are not canonical",
            ));
        }
        Ok(())
    }

    fn validate_constraint_handle(
        &self,
        handle: DatatypeConstraintHandle,
    ) -> Result<(), DatatypeError> {
        if self
            .state
            .constraint_by_slot
            .get(&handle.slot)
            .is_some_and(|active| *active != handle)
        {
            return Err(DatatypeError::invalid(
                "datatype constraint slot already has another active generation",
            ));
        }
        if self
            .state
            .maximum_constraint_generation
            .get(&handle.slot)
            .is_some_and(|maximum| handle.generation < *maximum)
        {
            return Err(DatatypeError::invalid(
                "stale datatype constraint generation",
            ));
        }
        Ok(())
    }

    fn validate_variable_transition(
        &self,
        old_variables: &[DatatypeVariable],
        new_variables: &[DatatypeVariable],
    ) -> Result<(), DatatypeError> {
        let prospective: BTreeSet<_> = new_variables.iter().copied().collect();
        if prospective.len() != new_variables.len() {
            return Err(DatatypeError::invalid(
                "scheduled constraint repeats a datatype variable",
            ));
        }
        let mut stable_ids = BTreeSet::new();
        let mut slots = BTreeSet::new();
        for variable in new_variables {
            if !stable_ids.insert(variable.stable_id) || !slots.insert(variable.node.slot) {
                return Err(DatatypeError::invalid(
                    "scheduled constraint aliases distinct variable handles",
                ));
            }
            if variable.node.generation == 0 {
                return Err(DatatypeError::invalid(
                    "datatype variable node generations must be positive",
                ));
            }
            if self
                .state
                .seen_handle_by_stable_id
                .get(&variable.stable_id)
                .is_some_and(|node| *node != variable.node)
            {
                return Err(DatatypeError::invalid(
                    "datatype stable variable ID changed its node handle",
                ));
            }
            if self
                .state
                .seen_variable_by_handle
                .get(&variable.node)
                .is_some_and(|stable_id| *stable_id != variable.stable_id)
            {
                return Err(DatatypeError::invalid(
                    "datatype node handle changed its stable variable ID",
                ));
            }
            if self
                .state
                .maximum_variable_generation
                .get(&variable.node.slot)
                .is_some_and(|maximum| variable.node.generation < *maximum)
            {
                return Err(DatatypeError::invalid("stale datatype variable generation"));
            }
            if let Some(active) = self
                .state
                .active_variable_by_stable_id
                .get(&variable.stable_id)
            {
                if active != variable && self.variable_survives_replacement(*active, old_variables)
                {
                    return Err(DatatypeError::invalid(
                        "datatype stable variable ID has another active handle",
                    ));
                }
            }
            if let Some(active) = self.state.active_variable_by_slot.get(&variable.node.slot) {
                if active != variable && self.variable_survives_replacement(*active, old_variables)
                {
                    return Err(DatatypeError::invalid(
                        "datatype node slot has another active generation",
                    ));
                }
            }
        }
        Ok(())
    }

    fn variable_survives_replacement(
        &self,
        variable: DatatypeVariable,
        old_variables: &[DatatypeVariable],
    ) -> bool {
        !old_variables.contains(&variable)
            || self
                .state
                .variable_references
                .get(&variable)
                .copied()
                .unwrap_or(0)
                > 1
    }

    fn validate_prospective_sizes(
        &self,
        old: Option<&ScheduledConstraintRecord>,
        _new: &ScheduledConstraintRecord,
        old_variables: &[DatatypeVariable],
        new_variables: &[DatatypeVariable],
    ) -> Result<(), DatatypeError> {
        let constraint_count = self
            .state
            .constraints
            .len()
            .saturating_add(usize::from(old.is_none()));
        if constraint_count
            > usize::try_from(self.limits.max_active_constraints).unwrap_or(usize::MAX)
        {
            return Err(DatatypeError::resource(
                "max_scheduler_active_constraints",
                u64::try_from(constraint_count).unwrap_or(u64::MAX),
                u64::from(self.limits.max_active_constraints),
            ));
        }
        let mut variable_count = self.state.variable_references.len();
        let removed = old_variables
            .iter()
            .filter(|variable| self.state.variable_references.get(variable) == Some(&1))
            .copied()
            .collect::<BTreeSet<_>>();
        for variable in old_variables {
            if removed.contains(variable) {
                variable_count = variable_count.saturating_sub(1);
            }
        }
        for variable in new_variables {
            let survives = self.state.variable_references.contains_key(variable)
                && !removed.contains(variable);
            if !survives {
                variable_count = variable_count.saturating_add(1);
            }
        }
        if variable_count > usize::try_from(self.limits.max_active_variables).unwrap_or(usize::MAX)
        {
            return Err(DatatypeError::resource(
                "max_scheduler_active_variables",
                u64::try_from(variable_count).unwrap_or(u64::MAX),
                u64::from(self.limits.max_active_variables),
            ));
        }
        Ok(())
    }

    fn validate_dirty_union(
        &self,
        additional: &BTreeSet<DatatypeVariable>,
    ) -> Result<(), DatatypeError> {
        let observed = self.state.dirty.union(additional).count();
        if observed > usize::try_from(self.limits.max_dirty_variables).unwrap_or(usize::MAX) {
            return Err(DatatypeError::resource(
                "max_scheduler_dirty_variables",
                u64::try_from(observed).unwrap_or(u64::MAX),
                u64::from(self.limits.max_dirty_variables),
            ));
        }
        Ok(())
    }

    fn validate_active_variable(&self, variable: DatatypeVariable) -> Result<(), DatatypeError> {
        if self.state.variable_references.contains_key(&variable) {
            return Ok(());
        }
        if self
            .state
            .active_variable_by_stable_id
            .get(&variable.stable_id)
            .is_some_and(|active| *active != variable)
            || self
                .state
                .active_variable_by_slot
                .get(&variable.node.slot)
                .is_some_and(|active| *active != variable)
            || self
                .state
                .maximum_variable_generation
                .get(&variable.node.slot)
                .is_some_and(|maximum| variable.node.generation < *maximum)
        {
            return Err(DatatypeError::invalid("stale datatype variable handle"));
        }
        Err(DatatypeError::invalid(
            "datatype variable has no active constraints",
        ))
    }

    fn validate_checkpoint(&self, checkpoint: SchedulerCheckpoint) -> Result<(), DatatypeError> {
        if checkpoint.owner != self.owner {
            return Err(DatatypeError::invalid(
                "datatype scheduler checkpoint belongs to another scheduler",
            ));
        }
        if !self.checkpoints.contains_key(&checkpoint.sequence) {
            return Err(DatatypeError::invalid(
                "datatype scheduler checkpoint is stale",
            ));
        }
        Ok(())
    }

    fn attach_record(&mut self, record: &ScheduledConstraintRecord) {
        for variable in record.constraint.variables() {
            self.state
                .constraints_by_variable
                .entry(variable)
                .or_default()
                .insert(record.handle);
            self.state
                .variable_references
                .entry(variable)
                .and_modify(|value| *value = value.saturating_add(1))
                .or_insert(1);
            self.state
                .active_variable_by_stable_id
                .insert(variable.stable_id, variable);
            self.state
                .active_variable_by_slot
                .insert(variable.node.slot, variable);
            self.state
                .seen_handle_by_stable_id
                .insert(variable.stable_id, variable.node);
            self.state
                .seen_variable_by_handle
                .insert(variable.node, variable.stable_id);
            self.state
                .maximum_variable_generation
                .entry(variable.node.slot)
                .and_modify(|value| *value = (*value).max(variable.node.generation))
                .or_insert(variable.node.generation);
        }
    }

    fn detach_record(&mut self, record: &ScheduledConstraintRecord) {
        for variable in record.constraint.variables() {
            let remove_index = self
                .state
                .constraints_by_variable
                .get_mut(&variable)
                .is_some_and(|handles| {
                    handles.remove(&record.handle);
                    handles.is_empty()
                });
            if remove_index {
                self.state.constraints_by_variable.remove(&variable);
            }
            let remove_variable = self
                .state
                .variable_references
                .get_mut(&variable)
                .is_some_and(|references| {
                    if *references <= 1 {
                        true
                    } else {
                        *references -= 1;
                        false
                    }
                });
            if remove_variable {
                self.state.variable_references.remove(&variable);
                self.state
                    .active_variable_by_stable_id
                    .remove(&variable.stable_id);
                self.state
                    .active_variable_by_slot
                    .remove(&variable.node.slot);
            }
        }
    }

    fn affected_components<C: DatatypeControl>(
        &self,
        work: &mut SchedulerWork<'_, C>,
    ) -> Result<(Vec<ComponentPlan>, BTreeSet<DatatypeVariable>), DatatypeError> {
        let mut remaining = self.state.dirty.clone();
        let mut plans = Vec::new();
        let mut orphaned = BTreeSet::new();
        while let Some(first) = remaining.pop_first() {
            work.add(1)?;
            if !self.state.constraints_by_variable.contains_key(&first) {
                orphaned.insert(first);
                continue;
            }
            let mut pending = VecDeque::from([first]);
            let mut members = BTreeSet::new();
            let mut constraints = BTreeSet::new();
            while let Some(variable) = pending.pop_front() {
                if !members.insert(variable) {
                    continue;
                }
                work.add(1)?;
                let handles = self
                    .state
                    .constraints_by_variable
                    .get(&variable)
                    .ok_or_else(|| {
                        DatatypeError::invalid("datatype component traversal lost a variable index")
                    })?;
                for handle in handles {
                    work.add(1)?;
                    constraints.insert(*handle);
                    let record = self.state.constraints.get(handle).ok_or_else(|| {
                        DatatypeError::invalid("datatype component traversal lost a constraint")
                    })?;
                    for neighbour in record.constraint.variables() {
                        if !members.contains(&neighbour) {
                            pending.push_back(neighbour);
                        }
                    }
                }
            }
            let dirty = members
                .intersection(&self.state.dirty)
                .copied()
                .collect::<BTreeSet<_>>();
            for variable in &dirty {
                remaining.remove(variable);
            }
            let participants = constraints
                .iter()
                .filter_map(|handle| {
                    self.state
                        .constraints
                        .get(handle)
                        .map(|record| record.participant_id)
                })
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            plans.push(ComponentPlan {
                variables: members.into_iter().collect(),
                constraints: constraints.into_iter().collect(),
                participants,
                dirty,
            });
        }
        Ok((plans, orphaned))
    }

    fn compile_component(
        &self,
        plan: &ComponentPlan,
    ) -> Result<ConstraintComponent, DatatypeError> {
        let variables = plan
            .variables
            .iter()
            .map(|variable| variable.stable_id)
            .collect::<Vec<_>>();
        if variables.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(DatatypeError::invalid(
                "datatype component stable variable IDs are not unique",
            ));
        }
        let mut component = ConstraintComponent {
            variables,
            domains: Vec::new(),
            fixed_values: Vec::new(),
            equalities: Vec::new(),
            inequalities: Vec::new(),
            cardinalities: Vec::new(),
        };
        for handle in &plan.constraints {
            let record = self.state.constraints.get(handle).ok_or_else(|| {
                DatatypeError::invalid("datatype component constraint disappeared")
            })?;
            match &record.constraint {
                ScheduledConstraint::Domain {
                    variable,
                    domain,
                    dependencies,
                } => component.domains.push(DomainConstraint {
                    variable: variable.stable_id,
                    domain: domain.clone(),
                    dependencies: dependencies.clone(),
                }),
                ScheduledConstraint::FixedValue {
                    variable,
                    value,
                    dependencies,
                } => component.fixed_values.push(FixedValueConstraint {
                    variable: variable.stable_id,
                    value: value.clone(),
                    dependencies: dependencies.clone(),
                }),
                ScheduledConstraint::Equality {
                    left,
                    right,
                    dependencies,
                } => component.equalities.push(EqualityConstraint {
                    left: left.stable_id,
                    right: right.stable_id,
                    dependencies: dependencies.clone(),
                }),
                ScheduledConstraint::Inequality {
                    left,
                    right,
                    dependencies,
                } => component.inequalities.push(InequalityConstraint {
                    left: left.stable_id,
                    right: right.stable_id,
                    dependencies: dependencies.clone(),
                }),
                ScheduledConstraint::Cardinality {
                    variable,
                    minimum,
                    dependencies,
                } => component.cardinalities.push(CardinalityConstraint {
                    variable: variable.stable_id,
                    minimum: *minimum,
                    dependencies: dependencies.clone(),
                }),
            }
        }
        Ok(component)
    }

    fn commit_checked(
        &mut self,
        checked: &[CheckedPlan],
        orphaned: &BTreeSet<DatatypeVariable>,
    ) -> Result<(), DatatypeError> {
        let mut processed = orphaned.clone();
        for value in checked {
            processed.extend(&value.dirty);
        }
        self.state.cached.retain(|variables, _result| {
            variables
                .iter()
                .all(|variable| !processed.contains(variable))
        });
        for value in checked {
            self.state
                .cached
                .insert(value.result.variables.clone(), value.result.clone());
        }
        for variable in &processed {
            self.state.dirty.remove(variable);
        }
        self.state.revision = self
            .state
            .revision
            .checked_add(1)
            .ok_or_else(|| DatatypeError::invalid("datatype scheduler revision overflow"))?;
        Ok(())
    }

    fn estimated_state_bytes(&self) -> u64 {
        let constraints = u64::try_from(self.state.constraints.len())
            .unwrap_or(u64::MAX)
            .saturating_mul(
                u64::try_from(std::mem::size_of::<ScheduledConstraintRecord>()).unwrap_or(u64::MAX),
            );
        let variables = u64::try_from(self.state.variable_references.len())
            .unwrap_or(u64::MAX)
            .saturating_mul(
                u64::try_from(std::mem::size_of::<DatatypeVariable>()).unwrap_or(u64::MAX),
            );
        let cached = u64::try_from(self.state.cached.len())
            .unwrap_or(u64::MAX)
            .saturating_mul(
                u64::try_from(std::mem::size_of::<ScheduledComponentResult>()).unwrap_or(u64::MAX),
            );
        constraints.saturating_add(variables).saturating_add(cached)
    }

    fn estimated_check_bytes(&self) -> u64 {
        let dirty = u64::try_from(self.state.dirty.len())
            .unwrap_or(u64::MAX)
            .saturating_mul(
                u64::try_from(std::mem::size_of::<DatatypeVariable>()).unwrap_or(u64::MAX),
            );
        self.estimated_state_bytes().saturating_add(dirty)
    }

    fn invalidate_cache_for(&mut self, variables: &BTreeSet<DatatypeVariable>) {
        self.state
            .cached
            .retain(|key, _result| key.iter().all(|variable| !variables.contains(variable)));
    }
}

#[derive(Debug)]
struct ComponentPlan {
    variables: Vec<DatatypeVariable>,
    constraints: Vec<DatatypeConstraintHandle>,
    participants: Vec<u32>,
    dirty: BTreeSet<DatatypeVariable>,
}

#[derive(Debug)]
struct CheckedPlan {
    dirty: BTreeSet<DatatypeVariable>,
    result: ScheduledComponentResult,
}

struct SchedulerWork<'a, C> {
    limits: SchedulerLimits,
    control: &'a C,
    steps: u64,
    since_poll: u64,
}

impl<'a, C: DatatypeControl> SchedulerWork<'a, C> {
    const fn new(limits: SchedulerLimits, control: &'a C) -> Self {
        Self {
            limits,
            control,
            steps: 0,
            since_poll: 0,
        }
    }

    fn add(&mut self, amount: u64) -> Result<(), DatatypeError> {
        self.steps = self
            .steps
            .checked_add(amount)
            .ok_or_else(|| DatatypeError::invalid("datatype scheduler step counter overflow"))?;
        if self.steps > self.limits.max_scheduler_steps {
            return Err(DatatypeError::resource(
                "max_scheduler_steps",
                self.steps,
                self.limits.max_scheduler_steps,
            ));
        }
        self.since_poll = self.since_poll.checked_add(amount).ok_or_else(|| {
            DatatypeError::invalid("datatype scheduler cancellation counter overflow")
        })?;
        if self.since_poll >= self.limits.cancellation_poll_stride {
            self.control.poll()?;
            self.since_poll %= self.limits.cancellation_poll_stride;
        }
        Ok(())
    }
}

fn estimate_plan_bytes(plan: &ComponentPlan) -> u64 {
    let variables = u64::try_from(plan.variables.len())
        .unwrap_or(u64::MAX)
        .saturating_mul(u64::try_from(std::mem::size_of::<DatatypeVariable>()).unwrap_or(u64::MAX));
    let constraints = u64::try_from(plan.constraints.len())
        .unwrap_or(u64::MAX)
        .saturating_mul(
            u64::try_from(std::mem::size_of::<DatatypeConstraintHandle>()).unwrap_or(u64::MAX),
        );
    variables.saturating_add(constraints)
}

fn scheduled_clash(component: &ScheduledComponentResult) -> Option<ScheduledDatatypeClash> {
    component
        .result
        .clash
        .as_ref()
        .map(|clash| ScheduledDatatypeClash {
            clash: clash.clone(),
            variables: component.variables.clone(),
            constraints: component.constraints.clone(),
            participants: component.participants.clone(),
        })
}

#[cfg(test)]
#[path = "scheduler_tests.rs"]
mod tests;
