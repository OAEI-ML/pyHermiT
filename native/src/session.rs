//! Transactional lifecycle and exact phase scheduler for one native reasoner session.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::collections::VecDeque;
use std::mem::size_of;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use crate::error::{ErrorKind, NativeError, NativeResult};

/// Operation-scoped cancellation and resource accounting.
///
/// Implementations may be shared across threads. Recovery methods on [`NativeTableau`]
/// deliberately do not receive this control: rollback must finish even after the operation's
/// cancellation token has fired.
pub trait OperationControl: Send + Sync {
    fn poll(&self) -> NativeResult<()>;
    fn observe_memory(&self, bytes: u64) -> NativeResult<()>;
}

/// An unbounded control used by pure-Rust tests and deterministic tools.
#[derive(Clone, Copy, Debug, Default)]
pub struct NeverAbort;

impl OperationControl for NeverAbort {
    fn poll(&self) -> NativeResult<()> {
        Ok(())
    }

    fn observe_memory(&self, _bytes: u64) -> NativeResult<()> {
        Ok(())
    }
}

impl OperationControl for crate::CancellationState {
    fn poll(&self) -> NativeResult<()> {
        Self::poll(self)
    }

    fn observe_memory(&self, bytes: u64) -> NativeResult<()> {
        Self::observe_memory(self, bytes);
        Self::poll(self)
    }
}

/// Stable query identity carried into diagnostic events without exposing native IDs.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct QueryKey([u8; 32]);

impl QueryKey {
    #[must_use]
    pub const fn new(value: [u8; 32]) -> Self {
        Self(value)
    }

    #[must_use]
    pub const fn as_bytes(self) -> [u8; 32] {
        self.0
    }
}

/// One validated query payload and its stable content identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SessionQuery<Q> {
    key: QueryKey,
    payload: Q,
}

impl<Q> SessionQuery<Q> {
    #[must_use]
    pub const fn new(key: QueryKey, payload: Q) -> Self {
        Self { key, payload }
    }

    #[must_use]
    pub const fn key(&self) -> QueryKey {
        self.key
    }

    #[must_use]
    pub const fn payload(&self) -> &Q {
        &self.payload
    }
}

/// Whether a phase found and consumed deterministic work.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PhaseProgress {
    NoWork,
    Progress,
}

/// Hyperresolution/role work performed for one promoted delta generation.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct DeltaPhaseResult {
    pub processed_rows: u64,
    pub rule_matches: u64,
    pub role_propagations: u64,
}

/// Result of checking all currently dirty datatype components.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct DatatypePhaseResult {
    pub checked_components: u64,
    pub changed: bool,
    pub clashed: bool,
}

/// Result of resolving the currently installed clash.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClashResolution {
    Backtracked,
    Unsatisfiable,
}

/// Validated-blocking state at the model-found boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValidationStatus {
    NotRequired,
    Valid,
    Invalidated,
}

/// How the operation checkpoint is finalized.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OperationDisposition {
    CommitPermanent,
    RollbackQuery,
}

/// Deterministic counters for one complete scheduler run.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SchedulerStatistics {
    pub scheduler_steps: u64,
    pub delta_generations: u64,
    pub delta_rows: u64,
    pub rule_matches: u64,
    pub role_propagations: u64,
    pub nominal_actions: u64,
    pub existential_actions: u64,
    pub disjunction_actions: u64,
    pub datatype_components: u64,
    pub blocking_refreshes: u64,
    pub blocking_checks: u64,
    pub validation_passes: u64,
    pub backtracks: u64,
}

impl SchedulerStatistics {
    const fn saturating_add(self, other: Self) -> Self {
        Self {
            scheduler_steps: self.scheduler_steps.saturating_add(other.scheduler_steps),
            delta_generations: self
                .delta_generations
                .saturating_add(other.delta_generations),
            delta_rows: self.delta_rows.saturating_add(other.delta_rows),
            rule_matches: self.rule_matches.saturating_add(other.rule_matches),
            role_propagations: self
                .role_propagations
                .saturating_add(other.role_propagations),
            nominal_actions: self.nominal_actions.saturating_add(other.nominal_actions),
            existential_actions: self
                .existential_actions
                .saturating_add(other.existential_actions),
            disjunction_actions: self
                .disjunction_actions
                .saturating_add(other.disjunction_actions),
            datatype_components: self
                .datatype_components
                .saturating_add(other.datatype_components),
            blocking_refreshes: self
                .blocking_refreshes
                .saturating_add(other.blocking_refreshes),
            blocking_checks: self.blocking_checks.saturating_add(other.blocking_checks),
            validation_passes: self
                .validation_passes
                .saturating_add(other.validation_passes),
            backtracks: self.backtracks.saturating_add(other.backtracks),
        }
    }
}

/// One isolated satisfiability result. Statistics are diagnostic and nonsemantic.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SessionCheckResult {
    pub satisfiable: bool,
    pub cache_hit: bool,
    pub statistics: SchedulerStatistics,
}

impl SessionCheckResult {
    #[must_use]
    pub const fn computed(satisfiable: bool, statistics: SchedulerStatistics) -> Self {
        Self {
            satisfiable,
            cache_hit: false,
            statistics,
        }
    }

    #[must_use]
    pub const fn cached(satisfiable: bool) -> Self {
        Self {
            satisfiable,
            cache_hit: true,
            statistics: SchedulerStatistics {
                scheduler_steps: 0,
                delta_generations: 0,
                delta_rows: 0,
                rule_matches: 0,
                role_propagations: 0,
                nominal_actions: 0,
                existential_actions: 0,
                disjunction_actions: 0,
                datatype_components: 0,
                blocking_refreshes: 0,
                blocking_checks: 0,
                validation_passes: 0,
                backtracks: 0,
            },
        }
    }
}

/// Adapter contract implemented by the eventual integrated WPR1-WPR3 tableau.
///
/// `OperationCheckpoint` must cover every query-local mutable owner as one logical unit:
/// `TableauKernel`, mutable rule/branch state, nominal-introduction state,
/// `BlockingManager`, and `DatatypeScheduler`. Role automata are immutable and may be shared.
/// Checkpoint creation is atomic on error. `finish_operation` is uninterruptible and either
/// restores the complete permanent root or atomically promotes the completed permanent run.
/// A successful rollback must also restore diagnostic caches/counters that could affect a later
/// operation. Query installation validates the permanent fingerprint and all symbol/predicate
/// prefix boundaries before adding operation-local rows or constraints.
pub trait NativeTableau: Send {
    type Query;
    type OperationCheckpoint;

    fn estimated_memory_bytes(&self) -> NativeResult<u64>;

    fn operation_checkpoint(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<Self::OperationCheckpoint>;

    fn install_query(
        &mut self,
        query: &SessionQuery<Self::Query>,
        control: &dyn OperationControl,
    ) -> NativeResult<()>;

    fn finish_operation(
        &mut self,
        checkpoint: Self::OperationCheckpoint,
        disposition: OperationDisposition,
    ) -> NativeResult<()>;

    fn reset_to_permanent(&mut self) -> NativeResult<()>;

    fn has_clash(&self) -> bool;

    fn process_nominals(&mut self, control: &dyn OperationControl) -> NativeResult<u64>;

    fn apply_next_delta(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<DeltaPhaseResult>;

    fn check_datatypes(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<DatatypePhaseResult>;

    fn has_existential_candidates(&self) -> bool;

    fn refresh_blocking(&mut self, control: &dyn OperationControl) -> NativeResult<u64>;

    fn process_existential(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<PhaseProgress>;

    fn process_disjunction(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<PhaseProgress>;

    fn resolve_clash(&mut self, control: &dyn OperationControl) -> NativeResult<ClashResolution>;

    fn invalidate_after_backtrack(&mut self) -> NativeResult<()>;

    fn validate_blocking(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<(ValidationStatus, u64)>;

    fn ready_for_sat(&self) -> NativeResult<bool>;

    fn check_invariants(&self) -> NativeResult<()>;
}

/// Resource limits owned by the session coordinator rather than a component kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SessionLimits {
    pub max_scheduler_steps: u64,
    pub max_batch_queries: u32,
    pub max_batch_result_bytes: u64,
    pub max_event_queue: u32,
}

impl Default for SessionLimits {
    fn default() -> Self {
        Self {
            max_scheduler_steps: 10_000_000,
            max_batch_queries: 1_000_000,
            max_batch_result_bytes: 256 * 1024 * 1024,
            max_event_queue: 4_096,
        }
    }
}

impl SessionLimits {
    fn validate(self) -> NativeResult<Self> {
        if self.max_scheduler_steps == 0 {
            return Err(NativeError::wire(
                "max_scheduler_steps must be strictly positive",
            ));
        }
        if self.max_batch_queries == 0 {
            return Err(NativeError::wire(
                "max_batch_queries must be strictly positive",
            ));
        }
        if self.max_batch_result_bytes == 0 {
            return Err(NativeError::wire(
                "max_batch_result_bytes must be strictly positive",
            ));
        }
        if self.max_event_queue < 2 {
            return Err(NativeError::wire(
                "max_event_queue must retain at least start and terminal events",
            ));
        }
        Ok(self)
    }
}

/// Run the exact complete tableau phase order for one already prepared operation.
pub fn drive_tableau(
    tableau: &mut impl NativeTableau,
    control: &dyn OperationControl,
    max_scheduler_steps: u64,
) -> NativeResult<SessionCheckResult> {
    if max_scheduler_steps == 0 {
        return Err(NativeError::wire(
            "max_scheduler_steps must be strictly positive",
        ));
    }
    let mut statistics = SchedulerStatistics::default();
    loop {
        control.poll()?;
        statistics.scheduler_steps = statistics
            .scheduler_steps
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("scheduler-step counter overflow"))?;
        if statistics.scheduler_steps > max_scheduler_steps {
            return Err(resource_limit(
                "native tableau scheduler step limit exceeded",
                "max_scheduler_steps",
                statistics.scheduler_steps,
                max_scheduler_steps,
            ));
        }

        if !tableau.has_clash() {
            let nominal_actions = tableau.process_nominals(control)?;
            statistics.nominal_actions = statistics
                .nominal_actions
                .checked_add(nominal_actions)
                .ok_or_else(|| NativeError::invariant("nominal-action counter overflow"))?;
            if nominal_actions != 0 {
                continue;
            }

            let delta = tableau.apply_next_delta(control)?;
            validate_delta(delta)?;
            statistics.delta_rows = statistics
                .delta_rows
                .checked_add(delta.processed_rows)
                .ok_or_else(|| NativeError::invariant("delta-row counter overflow"))?;
            statistics.rule_matches = statistics
                .rule_matches
                .checked_add(delta.rule_matches)
                .ok_or_else(|| NativeError::invariant("rule-match counter overflow"))?;
            statistics.role_propagations = statistics
                .role_propagations
                .checked_add(delta.role_propagations)
                .ok_or_else(|| NativeError::invariant("role-propagation counter overflow"))?;
            if delta.processed_rows != 0 {
                statistics.delta_generations = statistics
                    .delta_generations
                    .checked_add(1)
                    .ok_or_else(|| NativeError::invariant("delta-generation counter overflow"))?;
                let datatypes = tableau.check_datatypes(control)?;
                record_datatypes(&mut statistics, datatypes)?;
                validate_datatype_clash(tableau, datatypes)?;
                if !tableau.has_clash() {
                    let actions = tableau.process_nominals(control)?;
                    statistics.nominal_actions = statistics
                        .nominal_actions
                        .checked_add(actions)
                        .ok_or_else(|| NativeError::invariant("nominal-action counter overflow"))?;
                }
                continue;
            }

            let datatypes = tableau.check_datatypes(control)?;
            record_datatypes(&mut statistics, datatypes)?;
            validate_datatype_clash(tableau, datatypes)?;
            if datatypes.changed || datatypes.clashed {
                continue;
            }

            if tableau.has_existential_candidates() {
                statistics.blocking_refreshes = statistics
                    .blocking_refreshes
                    .checked_add(1)
                    .ok_or_else(|| NativeError::invariant("blocking-refresh counter overflow"))?;
                let checks = tableau.refresh_blocking(control)?;
                statistics.blocking_checks = statistics
                    .blocking_checks
                    .checked_add(checks)
                    .ok_or_else(|| NativeError::invariant("blocking-check counter overflow"))?;
            }
            if tableau.process_existential(control)? == PhaseProgress::Progress {
                statistics.existential_actions = statistics
                    .existential_actions
                    .checked_add(1)
                    .ok_or_else(|| NativeError::invariant("existential-action counter overflow"))?;
                continue;
            }
            if tableau.process_disjunction(control)? == PhaseProgress::Progress {
                statistics.disjunction_actions = statistics
                    .disjunction_actions
                    .checked_add(1)
                    .ok_or_else(|| NativeError::invariant("disjunction-action counter overflow"))?;
                continue;
            }
        }

        if tableau.has_clash() {
            match tableau.resolve_clash(control)? {
                ClashResolution::Unsatisfiable => {
                    tableau.check_invariants()?;
                    return Ok(SessionCheckResult::computed(false, statistics));
                }
                ClashResolution::Backtracked => {
                    tableau.invalidate_after_backtrack()?;
                    statistics.backtracks = statistics
                        .backtracks
                        .checked_add(1)
                        .ok_or_else(|| NativeError::invariant("backtrack counter overflow"))?;
                    continue;
                }
            }
        }

        let (validation, checks) = tableau.validate_blocking(control)?;
        statistics.blocking_checks = statistics
            .blocking_checks
            .checked_add(checks)
            .ok_or_else(|| NativeError::invariant("blocking-check counter overflow"))?;
        if validation != ValidationStatus::NotRequired {
            statistics.validation_passes = statistics
                .validation_passes
                .checked_add(1)
                .ok_or_else(|| NativeError::invariant("validation-pass counter overflow"))?;
        }
        if validation == ValidationStatus::Invalidated {
            continue;
        }
        if !tableau.ready_for_sat()? {
            return Err(NativeError::invariant(
                "native scheduler reached SAT with pending or unvalidated work",
            ));
        }
        tableau.check_invariants()?;
        return Ok(SessionCheckResult::computed(true, statistics));
    }
}

fn validate_delta(result: DeltaPhaseResult) -> NativeResult<()> {
    if result.processed_rows == 0 && (result.rule_matches != 0 || result.role_propagations != 0) {
        return Err(NativeError::invariant(
            "delta phase reported consequences without a promoted row",
        ));
    }
    Ok(())
}

fn record_datatypes(
    statistics: &mut SchedulerStatistics,
    result: DatatypePhaseResult,
) -> NativeResult<()> {
    statistics.datatype_components = statistics
        .datatype_components
        .checked_add(result.checked_components)
        .ok_or_else(|| NativeError::invariant("datatype-component counter overflow"))?;
    Ok(())
}

fn validate_datatype_clash(
    tableau: &impl NativeTableau,
    result: DatatypePhaseResult,
) -> NativeResult<()> {
    if result.clashed && !tableau.has_clash() {
        return Err(NativeError::invariant(
            "datatype phase reported a clash without installing it in tableau state",
        ));
    }
    Ok(())
}

/// Coarse operation kind used in stable native event records.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SessionOperationKind {
    PermanentCheck,
    QueryCheck,
    BatchCheck,
    ResetQueryState,
}

/// Stable event kind. The Python adapter attaches monotonic elapsed time on drain.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SessionEventKind {
    OperationStarted,
    CheckCompleted,
    QueryStateReset,
    OperationCompleted,
    OperationAborted,
}

/// Immutable event record produced in deterministic sequence order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SessionEvent {
    pub version: u16,
    pub sequence: u64,
    pub operation_id: u64,
    pub operation: SessionOperationKind,
    pub kind: SessionEventKind,
    pub completed: u32,
    pub total: u32,
    pub query_key: Option<QueryKey>,
    pub satisfiable: Option<bool>,
    pub error_code: Option<&'static str>,
}

/// Cumulative committed session work. Saturation is diagnostic and never changes answers.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SessionStatistics {
    pub operations_started: u64,
    pub operations_completed: u64,
    pub operations_aborted: u64,
    pub permanent_checks: u64,
    pub query_checks: u64,
    pub batch_calls: u64,
    pub resets: u64,
    pub cache_hits: u64,
    pub scheduler: SchedulerStatistics,
}

/// Read-only lifecycle snapshot available only while the session is healthy and idle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SessionSnapshot {
    pub owner_process_id: u32,
    pub permanent_satisfiable: Option<bool>,
    pub statistics: SessionStatistics,
    pub queued_events: u32,
    pub dropped_events: u64,
    pub next_operation_id: u64,
}

#[derive(Clone, Copy, Debug)]
struct OperationContext {
    id: u64,
    kind: SessionOperationKind,
    total: u32,
}

#[derive(Clone, Copy, Debug)]
struct CompletedCheck {
    query_key: Option<QueryKey>,
    result: SessionCheckResult,
}

#[derive(Clone, Copy, Debug, Default)]
struct OperationRecord {
    permanent_checks: u64,
    query_checks: u64,
    batch_calls: u64,
    resets: u64,
    cache_hits: u64,
    scheduler: SchedulerStatistics,
}

struct SessionOwned<K> {
    kernel: K,
    permanent_satisfiable: Option<bool>,
    statistics: SessionStatistics,
    events: VecDeque<SessionEvent>,
    dropped_events: u64,
    next_operation_id: u64,
    next_event_sequence: u64,
}

impl<K> SessionOwned<K> {
    fn new(kernel: K, event_capacity: u32) -> NativeResult<Self> {
        let capacity = usize::try_from(event_capacity)
            .map_err(|_| NativeError::wire("event capacity cannot fit this platform"))?;
        let mut events = VecDeque::new();
        events.try_reserve(capacity).map_err(|_| {
            resource_limit(
                "native event queue allocation failed",
                "max_event_queue",
                u64::from(event_capacity),
                u64::from(event_capacity),
            )
        })?;
        Ok(Self {
            kernel,
            permanent_satisfiable: None,
            statistics: SessionStatistics::default(),
            events,
            dropped_events: 0,
            next_operation_id: 1,
            next_event_sequence: 1,
        })
    }

    fn start_operation(
        &mut self,
        kind: SessionOperationKind,
        total: u32,
    ) -> NativeResult<OperationContext> {
        let event_count = u64::from(total).saturating_add(2);
        self.next_event_sequence
            .checked_add(event_count)
            .ok_or_else(|| NativeError::invariant("native event sequence overflow"))?;
        let id = self.next_operation_id;
        self.next_operation_id = id
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("native operation ID overflow"))?;
        self.statistics.operations_started = self.statistics.operations_started.saturating_add(1);
        Ok(OperationContext { id, kind, total })
    }

    fn complete_operation(
        &mut self,
        context: OperationContext,
        record: OperationRecord,
        checks: &[CompletedCheck],
        event_capacity: u32,
    ) -> NativeResult<()> {
        if u32::try_from(checks.len())
            .ok()
            .is_some_and(|count| count > context.total)
        {
            return Err(NativeError::invariant(
                "operation produced more check events than its declared total",
            ));
        }
        self.push_event(
            event_capacity,
            event(context, SessionEventKind::OperationStarted, 0),
        )?;
        for (offset, check) in checks.iter().enumerate() {
            let completed = u32::try_from(offset).unwrap_or(u32::MAX).saturating_add(1);
            let mut value = event(context, SessionEventKind::CheckCompleted, completed);
            value.query_key = check.query_key;
            value.satisfiable = Some(check.result.satisfiable);
            self.push_event(event_capacity, value)?;
        }
        if record.resets != 0 {
            self.push_event(
                event_capacity,
                event(context, SessionEventKind::QueryStateReset, context.total),
            )?;
        }
        self.push_event(
            event_capacity,
            event(context, SessionEventKind::OperationCompleted, context.total),
        )?;

        self.statistics.operations_completed =
            self.statistics.operations_completed.saturating_add(1);
        self.statistics.permanent_checks = self
            .statistics
            .permanent_checks
            .saturating_add(record.permanent_checks);
        self.statistics.query_checks = self
            .statistics
            .query_checks
            .saturating_add(record.query_checks);
        self.statistics.batch_calls = self
            .statistics
            .batch_calls
            .saturating_add(record.batch_calls);
        self.statistics.resets = self.statistics.resets.saturating_add(record.resets);
        self.statistics.cache_hits = self.statistics.cache_hits.saturating_add(record.cache_hits);
        self.statistics.scheduler = self.statistics.scheduler.saturating_add(record.scheduler);
        Ok(())
    }

    fn abort_operation(
        &mut self,
        context: OperationContext,
        error: &NativeError,
        event_capacity: u32,
    ) -> NativeResult<()> {
        self.push_event(
            event_capacity,
            event(context, SessionEventKind::OperationStarted, 0),
        )?;
        let mut aborted = event(context, SessionEventKind::OperationAborted, 0);
        aborted.error_code = Some(error.code);
        self.push_event(event_capacity, aborted)?;
        self.statistics.operations_aborted = self.statistics.operations_aborted.saturating_add(1);
        Ok(())
    }

    fn push_event(&mut self, capacity: u32, mut value: SessionEvent) -> NativeResult<()> {
        value.sequence = self.next_event_sequence;
        self.next_event_sequence = self
            .next_event_sequence
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("native event sequence overflow"))?;
        let limit = usize::try_from(capacity)
            .map_err(|_| NativeError::invariant("event capacity cannot fit this platform"))?;
        if self.events.len() == limit {
            self.events.pop_front();
            self.dropped_events = self.dropped_events.saturating_add(1);
        }
        self.events.push_back(value);
        Ok(())
    }
}

const fn event(context: OperationContext, kind: SessionEventKind, completed: u32) -> SessionEvent {
    SessionEvent {
        version: 1,
        sequence: 0,
        operation_id: context.id,
        operation: context.kind,
        kind,
        completed,
        total: context.total,
        query_key: None,
        satisfiable: None,
        error_code: None,
    }
}

struct LifecycleControl<K> {
    owner_process_id: u32,
    limits: SessionLimits,
    closed: AtomicBool,
    busy: AtomicBool,
    poisoned: AtomicBool,
    owned: Mutex<Option<SessionOwned<K>>>,
}

/// Thread-safe coarse coordinator for one complete native tableau.
pub struct SessionScheduler<K> {
    control: Arc<LifecycleControl<K>>,
}

impl<K> Clone for SessionScheduler<K> {
    fn clone(&self) -> Self {
        Self {
            control: Arc::clone(&self.control),
        }
    }
}

impl<K: NativeTableau> SessionScheduler<K> {
    pub fn new(kernel: K, limits: SessionLimits) -> NativeResult<Self> {
        Self::with_owner_process_id(kernel, limits, std::process::id())
    }

    /// Explicit owner identity is an integration seam for deterministic fork tests.
    pub fn with_owner_process_id(
        kernel: K,
        limits: SessionLimits,
        owner_process_id: u32,
    ) -> NativeResult<Self> {
        if owner_process_id == 0 {
            return Err(NativeError::wire("owner process ID must be nonzero"));
        }
        let limits = limits.validate()?;
        let owned = SessionOwned::new(kernel, limits.max_event_queue)?;
        Ok(Self {
            control: Arc::new(LifecycleControl {
                owner_process_id,
                limits,
                closed: AtomicBool::new(false),
                busy: AtomicBool::new(false),
                poisoned: AtomicBool::new(false),
                owned: Mutex::new(Some(owned)),
            }),
        })
    }

    #[must_use]
    pub fn is_closed(&self) -> bool {
        self.control.closed.load(Ordering::Acquire)
    }

    #[must_use]
    pub fn is_poisoned(&self) -> bool {
        self.control.poisoned.load(Ordering::Acquire)
    }

    pub fn check_permanent(
        &self,
        operation_control: &dyn OperationControl,
    ) -> NativeResult<SessionCheckResult> {
        let poisoned = &self.control.poisoned;
        let limits = self.control.limits;
        self.run_locked(|owned| {
            let context = owned.start_operation(SessionOperationKind::PermanentCheck, 1)?;
            let attempt = if let Some(satisfiable) = owned.permanent_satisfiable {
                controlled_poll(operation_control, poisoned)
                    .map(|()| SessionCheckResult::cached(satisfiable))
            } else {
                run_transaction(
                    &mut owned.kernel,
                    None,
                    OperationDisposition::CommitPermanent,
                    operation_control,
                    limits,
                    poisoned,
                )
            };
            match attempt {
                Ok(result) => {
                    let record = OperationRecord {
                        permanent_checks: 1,
                        cache_hits: u64::from(result.cache_hit),
                        scheduler: result.statistics,
                        ..OperationRecord::default()
                    };
                    let checks = [CompletedCheck {
                        query_key: None,
                        result,
                    }];
                    owned.complete_operation(context, record, &checks, limits.max_event_queue)?;
                    if !result.cache_hit {
                        owned.permanent_satisfiable = Some(result.satisfiable);
                    }
                    Ok(result)
                }
                Err(error) => abort(owned, context, error, limits.max_event_queue),
            }
        })
    }

    pub fn check_query(
        &self,
        query: &SessionQuery<K::Query>,
        operation_control: &dyn OperationControl,
    ) -> NativeResult<SessionCheckResult> {
        let poisoned = &self.control.poisoned;
        let limits = self.control.limits;
        self.run_locked(|owned| {
            let context = owned.start_operation(SessionOperationKind::QueryCheck, 1)?;
            let attempt = if owned.permanent_satisfiable == Some(false) {
                controlled_poll(operation_control, poisoned)
                    .map(|()| SessionCheckResult::cached(false))
            } else {
                run_transaction(
                    &mut owned.kernel,
                    Some(query),
                    OperationDisposition::RollbackQuery,
                    operation_control,
                    limits,
                    poisoned,
                )
            };
            match attempt {
                Ok(result) => {
                    let record = OperationRecord {
                        query_checks: 1,
                        cache_hits: u64::from(result.cache_hit),
                        scheduler: result.statistics,
                        ..OperationRecord::default()
                    };
                    let checks = [CompletedCheck {
                        query_key: Some(query.key()),
                        result,
                    }];
                    owned.complete_operation(context, record, &checks, limits.max_event_queue)?;
                    Ok(result)
                }
                Err(error) => abort(owned, context, error, limits.max_event_queue),
            }
        })
    }

    pub fn check_many(
        &self,
        queries: &[SessionQuery<K::Query>],
        operation_control: &dyn OperationControl,
    ) -> NativeResult<Vec<SessionCheckResult>> {
        let poisoned = &self.control.poisoned;
        let limits = self.control.limits;
        self.run_locked(|owned| {
            let total = u32::try_from(queries.len()).unwrap_or(u32::MAX);
            let context = owned.start_operation(SessionOperationKind::BatchCheck, total)?;
            let attempt = run_batch(owned, queries, operation_control, limits, poisoned);
            match attempt {
                Ok((results, checks, record)) => {
                    owned.complete_operation(context, record, &checks, limits.max_event_queue)?;
                    Ok(results)
                }
                Err(error) => abort(owned, context, error, limits.max_event_queue),
            }
        })
    }

    pub fn reset_query_state(&self) -> NativeResult<()> {
        let limits = self.control.limits;
        let poisoned = &self.control.poisoned;
        self.run_locked(|owned| {
            let context = owned.start_operation(SessionOperationKind::ResetQueryState, 1)?;
            let attempt = owned
                .kernel
                .reset_to_permanent()
                .and_then(|()| owned.kernel.check_invariants());
            match attempt {
                Ok(()) => {
                    let record = OperationRecord {
                        resets: 1,
                        ..OperationRecord::default()
                    };
                    owned.complete_operation(context, record, &[], limits.max_event_queue)
                }
                Err(error) => {
                    poisoned.store(true, Ordering::Release);
                    abort(owned, context, error, limits.max_event_queue)
                }
            }
        })
    }

    pub fn snapshot(&self) -> NativeResult<SessionSnapshot> {
        self.run_locked(|owned| {
            Ok(SessionSnapshot {
                owner_process_id: self.control.owner_process_id,
                permanent_satisfiable: owned.permanent_satisfiable,
                statistics: owned.statistics,
                queued_events: u32::try_from(owned.events.len()).unwrap_or(u32::MAX),
                dropped_events: owned.dropped_events,
                next_operation_id: owned.next_operation_id,
            })
        })
    }

    pub fn drain_events(&self) -> NativeResult<Vec<SessionEvent>> {
        self.run_locked(|owned| {
            let mut result = Vec::new();
            result.try_reserve_exact(owned.events.len()).map_err(|_| {
                resource_limit(
                    "native event drain allocation failed",
                    "max_event_queue",
                    u64::try_from(owned.events.len()).unwrap_or(u64::MAX),
                    u64::from(self.control.limits.max_event_queue),
                )
            })?;
            result.extend(owned.events.drain(..));
            Ok(result)
        })
    }

    pub fn close(&self) -> NativeResult<()> {
        if self.control.closed.load(Ordering::Acquire) {
            return Ok(());
        }
        if std::process::id() != self.control.owner_process_id {
            return Err(fork_error());
        }
        if self
            .control
            .busy
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return Err(busy_error(
                "cannot close a native session while an operation is active",
            ));
        }
        let guard = BusyGuard {
            busy: &self.control.busy,
        };
        let mut slot = self
            .control
            .owned
            .lock()
            .map_err(|_| NativeError::invariant("native session mutex is poisoned"))?;
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            let owned = slot.take();
            drop(owned);
        }));
        self.control.closed.store(true, Ordering::Release);
        drop(slot);
        drop(guard);
        if outcome.is_ok() {
            Ok(())
        } else {
            self.control.poisoned.store(true, Ordering::Release);
            Err(panic_error("native session close panic was contained"))
        }
    }

    #[allow(clippy::significant_drop_tightening)]
    fn run_locked<T>(
        &self,
        operation: impl FnOnce(&mut SessionOwned<K>) -> NativeResult<T>,
    ) -> NativeResult<T> {
        let _guard = self.preflight()?;
        let mut slot = self
            .control
            .owned
            .lock()
            .map_err(|_| NativeError::invariant("native session mutex is poisoned"))?;
        let owned = slot.as_mut().ok_or_else(disposed_error)?;
        let outcome = catch_unwind(AssertUnwindSafe(|| operation(owned)));
        drop(slot);
        if let Ok(result) = outcome {
            result
        } else {
            self.control.poisoned.store(true, Ordering::Release);
            Err(panic_error("native session operation panic was contained"))
        }
    }

    fn preflight(&self) -> NativeResult<BusyGuard<'_>> {
        if self.control.closed.load(Ordering::Acquire) {
            return Err(disposed_error());
        }
        if std::process::id() != self.control.owner_process_id {
            return Err(fork_error());
        }
        if self.control.poisoned.load(Ordering::Acquire) {
            return Err(poisoned_error(
                "NATIVE_SESSION_POISONED",
                "native session is poisoned and only close is permitted",
            ));
        }
        if self
            .control
            .busy
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return Err(busy_error("native session already has an active operation"));
        }
        Ok(BusyGuard {
            busy: &self.control.busy,
        })
    }
}

struct BusyGuard<'a> {
    busy: &'a AtomicBool,
}

impl Drop for BusyGuard<'_> {
    fn drop(&mut self) {
        self.busy.store(false, Ordering::Release);
    }
}

fn run_batch<K: NativeTableau>(
    owned: &mut SessionOwned<K>,
    queries: &[SessionQuery<K::Query>],
    control: &dyn OperationControl,
    limits: SessionLimits,
    poisoned: &AtomicBool,
) -> NativeResult<(
    Vec<SessionCheckResult>,
    Vec<CompletedCheck>,
    OperationRecord,
)> {
    let observed = u64::try_from(queries.len()).unwrap_or(u64::MAX);
    if observed > u64::from(limits.max_batch_queries) {
        return Err(resource_limit(
            "native query batch exceeds the configured item limit",
            "max_batch_queries",
            observed,
            u64::from(limits.max_batch_queries),
        ));
    }
    let item_bytes = u64::try_from(size_of::<SessionCheckResult>())
        .unwrap_or(u64::MAX)
        .saturating_add(u64::try_from(size_of::<CompletedCheck>()).unwrap_or(u64::MAX));
    let result_bytes = observed
        .checked_mul(item_bytes)
        .ok_or_else(|| NativeError::invariant("native batch result-size overflow"))?;
    if result_bytes > limits.max_batch_result_bytes {
        return Err(resource_limit(
            "native query batch result staging exceeds its byte limit",
            "max_batch_result_bytes",
            result_bytes,
            limits.max_batch_result_bytes,
        ));
    }
    let kernel_bytes = match owned.kernel.estimated_memory_bytes() {
        Ok(value) => value,
        Err(error) => {
            poison_on_invariant(poisoned, &error);
            return Err(error);
        }
    };
    controlled_observe(control, kernel_bytes.saturating_add(result_bytes), poisoned)?;
    controlled_poll(control, poisoned)?;

    let mut results = Vec::new();
    results.try_reserve_exact(queries.len()).map_err(|_| {
        resource_limit(
            "native query result allocation failed",
            "max_batch_result_bytes",
            result_bytes,
            limits.max_batch_result_bytes,
        )
    })?;
    let mut checks = Vec::new();
    checks.try_reserve_exact(queries.len()).map_err(|_| {
        resource_limit(
            "native query event allocation failed",
            "max_batch_result_bytes",
            result_bytes,
            limits.max_batch_result_bytes,
        )
    })?;
    let mut scheduler = SchedulerStatistics::default();
    let mut cache_hits = 0_u64;
    for query in queries {
        controlled_poll(control, poisoned)?;
        let result = if owned.permanent_satisfiable == Some(false) {
            SessionCheckResult::cached(false)
        } else {
            run_transaction(
                &mut owned.kernel,
                Some(query),
                OperationDisposition::RollbackQuery,
                control,
                limits,
                poisoned,
            )?
        };
        scheduler = scheduler.saturating_add(result.statistics);
        cache_hits = cache_hits.saturating_add(u64::from(result.cache_hit));
        checks.push(CompletedCheck {
            query_key: Some(query.key()),
            result,
        });
        results.push(result);
    }
    controlled_poll(control, poisoned)?;
    Ok((
        results,
        checks,
        OperationRecord {
            query_checks: observed,
            batch_calls: 1,
            cache_hits,
            scheduler,
            ..OperationRecord::default()
        },
    ))
}

fn run_transaction<K: NativeTableau>(
    kernel: &mut K,
    query: Option<&SessionQuery<K::Query>>,
    disposition: OperationDisposition,
    control: &dyn OperationControl,
    limits: SessionLimits,
    poisoned: &AtomicBool,
) -> NativeResult<SessionCheckResult> {
    controlled_poll(control, poisoned)?;
    let memory_bytes = match kernel.estimated_memory_bytes() {
        Ok(value) => value,
        Err(error) => {
            poison_on_invariant(poisoned, &error);
            return Err(error);
        }
    };
    controlled_observe(control, memory_bytes, poisoned)?;
    let checkpoint = match kernel.operation_checkpoint(control) {
        Ok(value) => value,
        Err(error) => {
            poison_on_invariant(poisoned, &error);
            return Err(error);
        }
    };
    if let Some(value) = query {
        if let Err(error) = kernel.install_query(value, control) {
            return recover(kernel, checkpoint, error, poisoned);
        }
    }
    let result = match drive_tableau(kernel, control, limits.max_scheduler_steps) {
        Ok(value) => value,
        Err(error) => return recover(kernel, checkpoint, error, poisoned),
    };
    if let Err(error) = control.poll() {
        return recover(kernel, checkpoint, error, poisoned);
    }
    if let Err(error) = kernel.check_invariants() {
        return recover(kernel, checkpoint, error, poisoned);
    }
    if let Err(error) = kernel.finish_operation(checkpoint, disposition) {
        poisoned.store(true, Ordering::Release);
        return Err(poisoned_error(
            "NATIVE_OPERATION_FINISH_FAILED",
            format!(
                "native operation could not establish a safe committed root: {} ({})",
                error.code, error.message
            ),
        ));
    }
    if let Err(error) = kernel.check_invariants() {
        poisoned.store(true, Ordering::Release);
        return Err(poisoned_error(
            "NATIVE_OPERATION_INVARIANT_FAILED",
            format!(
                "native operation finalized with invalid state: {}",
                error.code
            ),
        ));
    }
    Ok(result)
}

fn recover<K: NativeTableau>(
    kernel: &mut K,
    checkpoint: K::OperationCheckpoint,
    original: NativeError,
    poisoned: &AtomicBool,
) -> NativeResult<SessionCheckResult> {
    if let Err(rollback) = kernel.finish_operation(checkpoint, OperationDisposition::RollbackQuery)
    {
        poisoned.store(true, Ordering::Release);
        return Err(poisoned_error(
            "NATIVE_RECOVERY_FAILED",
            format!(
                "native operation recovery failed after {}: {}",
                original.code, rollback.code
            ),
        ));
    }
    if let Err(invariant) = kernel.check_invariants() {
        poisoned.store(true, Ordering::Release);
        return Err(poisoned_error(
            "NATIVE_RECOVERY_INVARIANT_FAILED",
            format!(
                "native recovery after {} restored invalid state: {}",
                original.code, invariant.code
            ),
        ));
    }
    poison_on_invariant(poisoned, &original);
    Err(original)
}

fn poison_on_invariant(poisoned: &AtomicBool, error: &NativeError) {
    if matches!(error.kind, ErrorKind::Invariant | ErrorKind::Poisoned) {
        poisoned.store(true, Ordering::Release);
    }
}

fn controlled_poll(control: &dyn OperationControl, poisoned: &AtomicBool) -> NativeResult<()> {
    control.poll().inspect_err(|error| {
        poison_on_invariant(poisoned, error);
    })
}

fn controlled_observe(
    control: &dyn OperationControl,
    bytes: u64,
    poisoned: &AtomicBool,
) -> NativeResult<()> {
    control.observe_memory(bytes).inspect_err(|error| {
        poison_on_invariant(poisoned, error);
    })
}

fn abort<T, K>(
    owned: &mut SessionOwned<K>,
    context: OperationContext,
    error: NativeError,
    event_capacity: u32,
) -> NativeResult<T> {
    owned.abort_operation(context, &error, event_capacity)?;
    Err(error)
}

fn resource_limit(
    message: impl Into<String>,
    limit: &'static str,
    observed: u64,
    allowed: u64,
) -> NativeError {
    NativeError::new(ErrorKind::Resource, "RESOURCE_LIMIT", message)
        .with_context("limit", limit)
        .with_context("observed", observed.to_string())
        .with_context("allowed", allowed.to_string())
}

fn disposed_error() -> NativeError {
    NativeError::new(
        ErrorKind::Disposed,
        "DISPOSED_REASONER",
        "native session is closed",
    )
}

fn fork_error() -> NativeError {
    NativeError::new(
        ErrorKind::Fork,
        "NATIVE_FORK",
        "native session cannot be reused after fork",
    )
}

fn busy_error(message: &'static str) -> NativeError {
    NativeError::new(ErrorKind::Busy, "CONCURRENT_MUTATION", message)
}

fn panic_error(message: &'static str) -> NativeError {
    poisoned_error("NATIVE_PANIC", message)
}

fn poisoned_error(code: &'static str, message: impl Into<String>) -> NativeError {
    NativeError::new(ErrorKind::Poisoned, code, message)
}
