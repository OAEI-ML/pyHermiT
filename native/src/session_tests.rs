// SPDX-License-Identifier: LGPL-3.0-or-later

use std::sync::atomic::{AtomicBool, AtomicI64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;

use crate::error::{ErrorKind, NativeError, NativeResult};
use crate::session::{
    drive_tableau, ClashResolution, DatatypePhaseResult, DeltaPhaseResult, NativeTableau,
    NeverAbort, OperationControl, OperationDisposition, PhaseProgress, QueryKey,
    SchedulerStatistics, SessionCheckResult, SessionEventKind, SessionLimits, SessionOperationKind,
    SessionQuery, SessionScheduler, ValidationStatus,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FakeBehavior {
    Normal,
    Cancelled,
    Malformed,
    Panic,
    Loop,
    NotReady,
    Invariant,
    FinishFailure,
    RecoveryFailure,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FakeQuery {
    delta: i64,
    behavior: FakeBehavior,
}

impl FakeQuery {
    const fn normal(delta: i64) -> Self {
        Self {
            delta,
            behavior: FakeBehavior::Normal,
        }
    }
}

#[derive(Debug, Default)]
struct GateState {
    entered: bool,
    released: bool,
}

#[derive(Debug, Default)]
struct Gate {
    state: Mutex<GateState>,
    changed: Condvar,
}

impl Gate {
    fn enter_and_wait(&self) -> NativeResult<()> {
        let mut state = self
            .state
            .lock()
            .map_err(|_| NativeError::invariant("test gate mutex is poisoned"))?;
        state.entered = true;
        self.changed.notify_all();
        while !state.released {
            state = self
                .changed
                .wait(state)
                .map_err(|_| NativeError::invariant("test gate mutex is poisoned"))?;
        }
        drop(state);
        Ok(())
    }

    fn wait_until_entered(&self) -> NativeResult<()> {
        let mut state = self
            .state
            .lock()
            .map_err(|_| NativeError::invariant("test gate mutex is poisoned"))?;
        while !state.entered {
            state = self
                .changed
                .wait(state)
                .map_err(|_| NativeError::invariant("test gate mutex is poisoned"))?;
        }
        drop(state);
        Ok(())
    }

    fn release(&self) -> NativeResult<()> {
        let mut state = self
            .state
            .lock()
            .map_err(|_| NativeError::invariant("test gate mutex is poisoned"))?;
        state.released = true;
        self.changed.notify_all();
        drop(state);
        Ok(())
    }
}

#[derive(Debug)]
struct FakeShared {
    logical_value: AtomicI64,
    runs: AtomicUsize,
    checkpoints: AtomicUsize,
    resets: AtomicUsize,
    fail_reset: AtomicBool,
    gate: Option<Arc<Gate>>,
    log: Mutex<Vec<String>>,
}

impl FakeShared {
    fn new(value: i64) -> Self {
        Self {
            logical_value: AtomicI64::new(value),
            runs: AtomicUsize::new(0),
            checkpoints: AtomicUsize::new(0),
            resets: AtomicUsize::new(0),
            fail_reset: AtomicBool::new(false),
            gate: None,
            log: Mutex::new(Vec::new()),
        }
    }

    fn with_gate(value: i64, gate: Arc<Gate>) -> Self {
        Self {
            gate: Some(gate),
            ..Self::new(value)
        }
    }

    fn record(&self, value: impl Into<String>) -> NativeResult<()> {
        self.log
            .lock()
            .map_err(|_| NativeError::invariant("fake log mutex is poisoned"))?
            .push(value.into());
        Ok(())
    }

    fn log(&self) -> NativeResult<Vec<String>> {
        self.log
            .lock()
            .map_err(|_| NativeError::invariant("fake log mutex is poisoned"))
            .map(|value| value.clone())
    }
}

#[derive(Clone, Copy, Debug)]
struct FakeCheckpoint {
    permanent: i64,
    active: i64,
    delta_pending: bool,
    clash: bool,
    behavior: FakeBehavior,
}

#[derive(Debug)]
struct FakeTableau {
    permanent: i64,
    active: i64,
    delta_pending: bool,
    clash: bool,
    behavior: FakeBehavior,
    shared: Arc<FakeShared>,
}

impl FakeTableau {
    fn new(value: i64) -> (Self, Arc<FakeShared>) {
        let shared = Arc::new(FakeShared::new(value));
        (Self::with_shared(value, Arc::clone(&shared)), shared)
    }

    fn with_gate(value: i64, gate: Arc<Gate>) -> (Self, Arc<FakeShared>) {
        let shared = Arc::new(FakeShared::with_gate(value, gate));
        (Self::with_shared(value, Arc::clone(&shared)), shared)
    }

    fn with_shared(value: i64, shared: Arc<FakeShared>) -> Self {
        Self {
            permanent: value,
            active: value,
            delta_pending: true,
            clash: false,
            behavior: FakeBehavior::Normal,
            shared,
        }
    }

    fn sync_logical_value(&self) {
        self.shared
            .logical_value
            .store(self.active, Ordering::Release);
    }

    fn restore(&mut self, checkpoint: FakeCheckpoint) {
        self.permanent = checkpoint.permanent;
        self.active = checkpoint.active;
        self.delta_pending = checkpoint.delta_pending;
        self.clash = checkpoint.clash;
        self.behavior = checkpoint.behavior;
        self.sync_logical_value();
    }
}

impl NativeTableau for FakeTableau {
    type Query = FakeQuery;
    type OperationCheckpoint = FakeCheckpoint;

    fn estimated_memory_bytes(&self) -> NativeResult<u64> {
        Ok(256)
    }

    fn operation_checkpoint(
        &mut self,
        control: &dyn OperationControl,
    ) -> NativeResult<Self::OperationCheckpoint> {
        control.poll()?;
        self.shared.checkpoints.fetch_add(1, Ordering::AcqRel);
        self.shared.record("checkpoint")?;
        Ok(FakeCheckpoint {
            permanent: self.permanent,
            active: self.active,
            delta_pending: self.delta_pending,
            clash: self.clash,
            behavior: self.behavior,
        })
    }

    fn install_query(
        &mut self,
        query: &SessionQuery<Self::Query>,
        control: &dyn OperationControl,
    ) -> NativeResult<()> {
        control.poll()?;
        self.active = self
            .active
            .checked_add(query.payload().delta)
            .ok_or_else(|| NativeError::wire("fake query delta overflow"))?;
        self.delta_pending = true;
        self.clash = false;
        self.behavior = query.payload().behavior;
        self.sync_logical_value();
        self.shared.record(format!("query:{}", self.active))?;
        if self.behavior == FakeBehavior::Malformed {
            return Err(NativeError::wire("injected malformed query"));
        }
        Ok(())
    }

    fn finish_operation(
        &mut self,
        checkpoint: Self::OperationCheckpoint,
        disposition: OperationDisposition,
    ) -> NativeResult<()> {
        if self.behavior == FakeBehavior::RecoveryFailure
            || self.behavior == FakeBehavior::FinishFailure
        {
            return Err(NativeError::invariant("injected finish failure"));
        }
        match disposition {
            OperationDisposition::CommitPermanent => {
                self.permanent = self.active;
                self.delta_pending = false;
                self.behavior = FakeBehavior::Normal;
                self.shared.record("commit")?;
            }
            OperationDisposition::RollbackQuery => {
                self.restore(checkpoint);
                self.shared.record("rollback")?;
            }
        }
        self.sync_logical_value();
        Ok(())
    }

    fn reset_to_permanent(&mut self) -> NativeResult<()> {
        self.shared.resets.fetch_add(1, Ordering::AcqRel);
        if self.shared.fail_reset.load(Ordering::Acquire) {
            return Err(NativeError::invariant("injected reset failure"));
        }
        self.active = self.permanent;
        self.delta_pending = false;
        self.clash = self.permanent < 0;
        self.behavior = FakeBehavior::Normal;
        self.sync_logical_value();
        self.shared.record("reset")
    }

    fn has_clash(&self) -> bool {
        self.clash
    }

    fn process_nominals(&mut self, _control: &dyn OperationControl) -> NativeResult<u64> {
        if self.behavior == FakeBehavior::Loop {
            return Ok(1);
        }
        Ok(0)
    }

    #[allow(clippy::panic)]
    fn apply_next_delta(
        &mut self,
        _control: &dyn OperationControl,
    ) -> NativeResult<DeltaPhaseResult> {
        if self.behavior == FakeBehavior::Panic {
            std::panic::panic_any(());
        }
        if self.behavior == FakeBehavior::Invariant {
            return Err(NativeError::invariant("injected engine invariant failure"));
        }
        if matches!(
            self.behavior,
            FakeBehavior::Cancelled | FakeBehavior::RecoveryFailure
        ) {
            return Err(NativeError::new(
                ErrorKind::Cancelled,
                "REASONER_INTERRUPTED",
                "injected cancellation",
            ));
        }
        if !self.delta_pending {
            return Ok(DeltaPhaseResult::default());
        }
        if let Some(gate) = &self.shared.gate {
            gate.enter_and_wait()?;
        }
        self.delta_pending = false;
        self.shared.runs.fetch_add(1, Ordering::AcqRel);
        self.shared.record(format!("run:{}", self.active))?;
        if self.active < 0 {
            self.clash = true;
        }
        Ok(DeltaPhaseResult {
            processed_rows: 1,
            rule_matches: 1,
            role_propagations: 1,
        })
    }

    fn check_datatypes(
        &mut self,
        _control: &dyn OperationControl,
    ) -> NativeResult<DatatypePhaseResult> {
        Ok(DatatypePhaseResult::default())
    }

    fn has_existential_candidates(&self) -> bool {
        false
    }

    fn refresh_blocking(&mut self, _control: &dyn OperationControl) -> NativeResult<u64> {
        Ok(0)
    }

    fn process_existential(
        &mut self,
        _control: &dyn OperationControl,
    ) -> NativeResult<PhaseProgress> {
        Ok(PhaseProgress::NoWork)
    }

    fn process_disjunction(
        &mut self,
        _control: &dyn OperationControl,
    ) -> NativeResult<PhaseProgress> {
        Ok(PhaseProgress::NoWork)
    }

    fn resolve_clash(&mut self, _control: &dyn OperationControl) -> NativeResult<ClashResolution> {
        Ok(ClashResolution::Unsatisfiable)
    }

    fn invalidate_after_backtrack(&mut self) -> NativeResult<()> {
        Ok(())
    }

    fn validate_blocking(
        &mut self,
        _control: &dyn OperationControl,
    ) -> NativeResult<(ValidationStatus, u64)> {
        Ok((ValidationStatus::Valid, 0))
    }

    fn ready_for_sat(&self) -> NativeResult<bool> {
        Ok(self.behavior != FakeBehavior::NotReady && !self.clash)
    }

    fn check_invariants(&self) -> NativeResult<()> {
        Ok(())
    }
}

#[derive(Debug)]
struct FaultControl {
    fail_at_poll: usize,
    polls: AtomicUsize,
}

impl FaultControl {
    fn counting() -> Self {
        Self {
            fail_at_poll: usize::MAX,
            polls: AtomicUsize::new(0),
        }
    }

    fn fail_at(poll: usize) -> Self {
        Self {
            fail_at_poll: poll,
            polls: AtomicUsize::new(0),
        }
    }

    fn poll_count(&self) -> usize {
        self.polls.load(Ordering::Acquire)
    }
}

impl OperationControl for FaultControl {
    fn poll(&self) -> NativeResult<()> {
        let current = self.polls.fetch_add(1, Ordering::AcqRel).saturating_add(1);
        if current == self.fail_at_poll {
            return Err(NativeError::new(
                ErrorKind::Cancelled,
                "REASONER_INTERRUPTED",
                "injected poll cancellation",
            ));
        }
        Ok(())
    }

    fn observe_memory(&self, _bytes: u64) -> NativeResult<()> {
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
struct RejectMemory;

impl OperationControl for RejectMemory {
    fn poll(&self) -> NativeResult<()> {
        Ok(())
    }

    fn observe_memory(&self, bytes: u64) -> NativeResult<()> {
        Err(NativeError::new(
            ErrorKind::Resource,
            "RESOURCE_LIMIT",
            "injected memory rejection",
        )
        .with_context("limit", "max_memory_bytes")
        .with_context("observed", bytes.to_string())
        .with_context("allowed", "1"))
    }
}

fn key(value: u8) -> QueryKey {
    QueryKey::new([value; 32])
}

fn query(value: u8, delta: i64) -> SessionQuery<FakeQuery> {
    SessionQuery::new(key(value), FakeQuery::normal(delta))
}

fn query_with(value: u8, delta: i64, behavior: FakeBehavior) -> SessionQuery<FakeQuery> {
    SessionQuery::new(key(value), FakeQuery { delta, behavior })
}

#[test]
fn permanent_cache_and_query_batches_preserve_one_committed_root() -> NativeResult<()> {
    let (kernel, shared) = FakeTableau::new(10);
    let session = SessionScheduler::new(kernel, SessionLimits::default())?;

    let first = session.check_permanent(&NeverAbort)?;
    let second = session.check_permanent(&NeverAbort)?;
    assert!(first.satisfiable);
    assert!(!first.cache_hit);
    assert!(second.cache_hit);
    assert_eq!(shared.runs.load(Ordering::Acquire), 1);

    let positive = query(1, 5);
    let negative = query(2, -30);
    let results = session.check_many(&[positive, negative, query(3, 0)], &NeverAbort)?;
    assert_eq!(
        results
            .iter()
            .map(|value| value.satisfiable)
            .collect::<Vec<_>>(),
        vec![true, false, true]
    );
    assert_eq!(shared.logical_value.load(Ordering::Acquire), 10);
    assert_eq!(
        shared
            .log()?
            .into_iter()
            .filter(|value| value.starts_with("run:"))
            .collect::<Vec<_>>(),
        vec!["run:10", "run:15", "run:-20", "run:10"]
    );
    let snapshot = session.snapshot()?;
    assert_eq!(snapshot.permanent_satisfiable, Some(true));
    assert_eq!(snapshot.statistics.operations_completed, 3);
    assert_eq!(snapshot.statistics.permanent_checks, 2);
    assert_eq!(snapshot.statistics.query_checks, 3);
    assert_eq!(snapshot.statistics.batch_calls, 1);
    assert_eq!(snapshot.statistics.cache_hits, 1);
    Ok(())
}

#[test]
fn cancellation_at_every_coordinator_poll_restores_query_state() -> NativeResult<()> {
    let (kernel, _shared) = FakeTableau::new(10);
    let session = SessionScheduler::new(kernel, SessionLimits::default())?;
    let counting = FaultControl::counting();
    assert!(session.check_query(&query(1, 2), &counting)?.satisfiable);
    let polls = counting.poll_count();
    assert!(polls >= 5);

    for fault in 1..=polls {
        let (kernel, shared) = FakeTableau::new(10);
        let candidate = SessionScheduler::new(kernel, SessionLimits::default())?;
        let error = candidate
            .check_query(&query(2, 7), &FaultControl::fail_at(fault))
            .err()
            .ok_or_else(|| NativeError::invariant("fault injection unexpectedly succeeded"))?;
        assert_eq!(error.kind, ErrorKind::Cancelled);
        assert!(!candidate.is_poisoned());
        assert_eq!(shared.logical_value.load(Ordering::Acquire), 10);
        let snapshot = candidate.snapshot()?;
        assert_eq!(snapshot.statistics.operations_completed, 0);
        assert_eq!(snapshot.statistics.operations_aborted, 1);
        assert_eq!(snapshot.statistics.query_checks, 0);
        assert!(
            candidate
                .check_query(&query(3, 1), &NeverAbort)?
                .satisfiable
        );
        assert_eq!(shared.logical_value.load(Ordering::Acquire), 10);
    }
    Ok(())
}

#[test]
fn resource_and_scheduler_limits_fail_without_partial_mutation() -> NativeResult<()> {
    let (kernel, shared) = FakeTableau::new(10);
    let session = SessionScheduler::new(kernel, SessionLimits::default())?;
    let error = session
        .check_query(&query(1, 5), &RejectMemory)
        .err()
        .ok_or_else(|| NativeError::invariant("memory rejection unexpectedly succeeded"))?;
    assert_eq!(error.kind, ErrorKind::Resource);
    assert_eq!(shared.checkpoints.load(Ordering::Acquire), 0);
    assert_eq!(shared.logical_value.load(Ordering::Acquire), 10);

    let limits = SessionLimits {
        max_scheduler_steps: 3,
        ..SessionLimits::default()
    };
    let (kernel, shared) = FakeTableau::new(10);
    let limited = SessionScheduler::new(kernel, limits)?;
    let error = limited
        .check_query(&query_with(2, 4, FakeBehavior::Loop), &NeverAbort)
        .err()
        .ok_or_else(|| NativeError::invariant("scheduler limit unexpectedly succeeded"))?;
    assert_eq!(error.kind, ErrorKind::Resource);
    assert_eq!(
        error.context.get("limit").map(String::as_str),
        Some("max_scheduler_steps")
    );
    assert_eq!(shared.logical_value.load(Ordering::Acquire), 10);
    assert!(limited.check_query(&query(3, 1), &NeverAbort)?.satisfiable);
    Ok(())
}

#[test]
fn failed_batch_publishes_no_prefix_statistics_or_item_events() -> NativeResult<()> {
    let (kernel, shared) = FakeTableau::new(10);
    let session = SessionScheduler::new(kernel, SessionLimits::default())?;
    let queries = [
        query(1, 1),
        query_with(2, 2, FakeBehavior::Cancelled),
        query(3, 3),
    ];
    let error = session
        .check_many(&queries, &NeverAbort)
        .err()
        .ok_or_else(|| NativeError::invariant("failed batch unexpectedly succeeded"))?;
    assert_eq!(error.kind, ErrorKind::Cancelled);
    assert_eq!(shared.logical_value.load(Ordering::Acquire), 10);
    let snapshot = session.snapshot()?;
    assert_eq!(snapshot.statistics.operations_aborted, 1);
    assert_eq!(snapshot.statistics.operations_completed, 0);
    assert_eq!(snapshot.statistics.query_checks, 0);
    assert_eq!(
        snapshot.statistics.scheduler,
        SchedulerStatistics::default()
    );
    let events = session.drain_events()?;
    assert_eq!(events.len(), 2);
    assert_eq!(events[0].kind, SessionEventKind::OperationStarted);
    assert_eq!(events[1].kind, SessionEventKind::OperationAborted);
    assert_eq!(events[1].error_code, Some("REASONER_INTERRUPTED"));

    let recovered = session.check_many(&[query(4, 4), query(5, -20)], &NeverAbort)?;
    assert_eq!(
        recovered
            .iter()
            .map(|value| value.satisfiable)
            .collect::<Vec<_>>(),
        vec![true, false]
    );
    Ok(())
}

#[test]
fn malformed_queries_recover_but_invariants_and_finish_failures_poison() -> NativeResult<()> {
    let (kernel, shared) = FakeTableau::new(10);
    let recoverable = SessionScheduler::new(kernel, SessionLimits::default())?;
    let malformed = recoverable
        .check_query(&query_with(1, 9, FakeBehavior::Malformed), &NeverAbort)
        .err()
        .ok_or_else(|| NativeError::invariant("malformed query unexpectedly succeeded"))?;
    assert_eq!(malformed.kind, ErrorKind::Wire);
    assert!(!recoverable.is_poisoned());
    assert_eq!(shared.logical_value.load(Ordering::Acquire), 10);
    assert!(
        recoverable
            .check_query(&query(2, 1), &NeverAbort)?
            .satisfiable
    );

    let (kernel, _shared) = FakeTableau::new(10);
    let invariant = SessionScheduler::new(kernel, SessionLimits::default())?;
    let error = invariant
        .check_query(&query_with(3, 1, FakeBehavior::Invariant), &NeverAbort)
        .err()
        .ok_or_else(|| NativeError::invariant("invariant injection unexpectedly succeeded"))?;
    assert_eq!(error.kind, ErrorKind::Invariant);
    assert!(invariant.is_poisoned());
    assert_eq!(
        invariant
            .check_permanent(&NeverAbort)
            .err()
            .map(|value| value.kind),
        Some(ErrorKind::Poisoned)
    );
    invariant.close()?;

    let (kernel, _shared) = FakeTableau::new(10);
    let finish = SessionScheduler::new(kernel, SessionLimits::default())?;
    let error = finish
        .check_query(&query_with(4, 1, FakeBehavior::FinishFailure), &NeverAbort)
        .err()
        .ok_or_else(|| NativeError::invariant("finish injection unexpectedly succeeded"))?;
    assert_eq!(error.kind, ErrorKind::Poisoned);
    assert_eq!(error.code, "NATIVE_OPERATION_FINISH_FAILED");
    assert!(finish.is_poisoned());
    finish.close()?;

    let (kernel, _shared) = FakeTableau::new(10);
    let recovery = SessionScheduler::new(kernel, SessionLimits::default())?;
    let error = recovery
        .check_query(
            &query_with(5, 1, FakeBehavior::RecoveryFailure),
            &NeverAbort,
        )
        .err()
        .ok_or_else(|| NativeError::invariant("recovery injection unexpectedly succeeded"))?;
    assert_eq!(error.kind, ErrorKind::Poisoned);
    assert_eq!(error.code, "NATIVE_RECOVERY_FAILED");
    assert!(recovery.is_poisoned());
    recovery.close()
}

#[test]
fn same_session_is_exclusive_while_independent_sessions_can_progress() -> NativeResult<()> {
    let gate = Arc::new(Gate::default());
    let (kernel, _shared) = FakeTableau::with_gate(10, Arc::clone(&gate));
    let session = SessionScheduler::new(kernel, SessionLimits::default())?;
    let worker_session = session.clone();
    let worker = thread::spawn(move || worker_session.check_query(&query(1, 1), &NeverAbort));
    gate.wait_until_entered()?;
    assert_eq!(
        session.snapshot().err().map(|value| value.kind),
        Some(ErrorKind::Busy)
    );
    assert_eq!(
        session.close().err().map(|value| value.kind),
        Some(ErrorKind::Busy)
    );

    let (independent_kernel, _shared) = FakeTableau::new(20);
    let independent = SessionScheduler::new(independent_kernel, SessionLimits::default())?;
    assert!(
        independent
            .check_query(&query(2, 1), &NeverAbort)?
            .satisfiable
    );
    gate.release()?;
    let worker_result = worker
        .join()
        .map_err(|_| NativeError::invariant("session worker panicked"))??;
    assert!(worker_result.satisfiable);
    session.close()?;
    independent.close()
}

#[test]
fn fork_close_reset_and_panic_boundaries_are_fail_closed() -> NativeResult<()> {
    let process_id = std::process::id();
    let foreign_owner = if process_id == u32::MAX {
        process_id.saturating_sub(1)
    } else {
        process_id.saturating_add(1)
    };
    let (kernel, _shared) = FakeTableau::new(10);
    let inherited =
        SessionScheduler::with_owner_process_id(kernel, SessionLimits::default(), foreign_owner)?;
    assert_eq!(
        inherited.snapshot().err().map(|value| value.code),
        Some("NATIVE_FORK")
    );
    assert_eq!(
        inherited.close().err().map(|value| value.code),
        Some("NATIVE_FORK")
    );

    let (kernel, shared) = FakeTableau::new(10);
    let reset = SessionScheduler::new(kernel, SessionLimits::default())?;
    assert!(reset.check_permanent(&NeverAbort)?.satisfiable);
    reset.reset_query_state()?;
    assert_eq!(shared.resets.load(Ordering::Acquire), 1);
    assert!(reset.check_permanent(&NeverAbort)?.cache_hit);
    assert_eq!(reset.snapshot()?.statistics.resets, 1);

    shared.fail_reset.store(true, Ordering::Release);
    let error = reset
        .reset_query_state()
        .err()
        .ok_or_else(|| NativeError::invariant("reset failure unexpectedly succeeded"))?;
    assert_eq!(error.kind, ErrorKind::Invariant);
    assert!(reset.is_poisoned());
    reset.close()?;

    let (kernel, _shared) = FakeTableau::new(10);
    let panicking = SessionScheduler::new(kernel, SessionLimits::default())?;
    let error = panicking
        .check_query(&query_with(4, 1, FakeBehavior::Panic), &NeverAbort)
        .err()
        .ok_or_else(|| NativeError::invariant("panic injection unexpectedly succeeded"))?;
    assert_eq!(error.kind, ErrorKind::Poisoned);
    assert_eq!(error.code, "NATIVE_PANIC");
    assert!(panicking.is_poisoned());
    panicking.close()?;

    let (kernel, _shared) = FakeTableau::new(10);
    let closed = SessionScheduler::new(kernel, SessionLimits::default())?;
    let clone = closed.clone();
    closed.close()?;
    closed.close()?;
    assert!(clone.is_closed());
    assert_eq!(
        clone
            .check_permanent(&NeverAbort)
            .err()
            .map(|value| value.kind),
        Some(ErrorKind::Disposed)
    );
    assert_eq!(
        clone.reset_query_state().err().map(|value| value.kind),
        Some(ErrorKind::Disposed)
    );
    Ok(())
}

#[test]
fn events_and_statistics_are_deterministic_and_bounded() -> NativeResult<()> {
    let limits = SessionLimits {
        max_event_queue: 3,
        ..SessionLimits::default()
    };
    let run = || -> NativeResult<_> {
        let (kernel, _shared) = FakeTableau::new(10);
        let session = SessionScheduler::new(kernel, limits)?;
        session.check_query(&query(1, 1), &NeverAbort)?;
        session.check_query(&query(2, -20), &NeverAbort)?;
        session.check_query(&query(3, 0), &NeverAbort)?;
        let snapshot = session.snapshot()?;
        let events = session.drain_events()?;
        Ok((snapshot, events))
    };

    let first = run()?;
    let second = run()?;
    assert_eq!(first, second);
    assert_eq!(first.0.queued_events, 3);
    assert_eq!(first.0.dropped_events, 6);
    assert_eq!(first.0.statistics.operations_completed, 3);
    assert_eq!(first.0.statistics.query_checks, 3);
    assert_eq!(
        first
            .1
            .iter()
            .map(|value| value.sequence)
            .collect::<Vec<_>>(),
        vec![7, 8, 9]
    );
    assert_eq!(first.1[0].operation_id, 3);
    assert_eq!(first.1[0].operation, SessionOperationKind::QueryCheck);
    assert_eq!(first.1[0].kind, SessionEventKind::OperationStarted);
    assert_eq!(first.1[1].query_key, Some(key(3)));
    assert_eq!(first.1[2].kind, SessionEventKind::OperationCompleted);
    Ok(())
}

#[test]
fn batch_limits_reject_before_engine_mutation_and_empty_batches_remain_operations(
) -> NativeResult<()> {
    let limits = SessionLimits {
        max_batch_queries: 2,
        max_batch_result_bytes: 1_024,
        ..SessionLimits::default()
    };
    let (kernel, shared) = FakeTableau::new(10);
    let session = SessionScheduler::new(kernel, limits)?;
    let error = session
        .check_many(&[query(1, 1), query(2, 2), query(3, 3)], &NeverAbort)
        .err()
        .ok_or_else(|| NativeError::invariant("oversized batch unexpectedly succeeded"))?;
    assert_eq!(error.kind, ErrorKind::Resource);
    assert_eq!(
        error.context.get("limit").map(String::as_str),
        Some("max_batch_queries")
    );
    assert_eq!(shared.checkpoints.load(Ordering::Acquire), 0);
    assert_eq!(shared.logical_value.load(Ordering::Acquire), 10);
    assert!(session.check_many(&[], &NeverAbort)?.is_empty());
    let snapshot = session.snapshot()?;
    assert_eq!(snapshot.statistics.operations_completed, 1);
    assert_eq!(snapshot.statistics.operations_aborted, 1);
    assert_eq!(snapshot.statistics.batch_calls, 1);
    Ok(())
}

#[allow(clippy::struct_excessive_bools)]
#[derive(Debug)]
struct ScriptTableau {
    log: Vec<&'static str>,
    nominal_pending: bool,
    delta_pending: bool,
    datatype_calls: u8,
    existential_pending: bool,
    disjunction_pending: bool,
    clash: bool,
    validation_invalid_pending: bool,
}

impl ScriptTableau {
    fn new() -> Self {
        Self {
            log: Vec::new(),
            nominal_pending: true,
            delta_pending: true,
            datatype_calls: 0,
            existential_pending: true,
            disjunction_pending: true,
            clash: false,
            validation_invalid_pending: true,
        }
    }
}

impl NativeTableau for ScriptTableau {
    type Query = ();
    type OperationCheckpoint = ();

    fn estimated_memory_bytes(&self) -> NativeResult<u64> {
        Ok(0)
    }

    fn operation_checkpoint(
        &mut self,
        _control: &dyn OperationControl,
    ) -> NativeResult<Self::OperationCheckpoint> {
        Ok(())
    }

    fn install_query(
        &mut self,
        _query: &SessionQuery<Self::Query>,
        _control: &dyn OperationControl,
    ) -> NativeResult<()> {
        Ok(())
    }

    fn finish_operation(
        &mut self,
        _checkpoint: Self::OperationCheckpoint,
        _disposition: OperationDisposition,
    ) -> NativeResult<()> {
        Ok(())
    }

    fn reset_to_permanent(&mut self) -> NativeResult<()> {
        Ok(())
    }

    fn has_clash(&self) -> bool {
        self.clash
    }

    fn process_nominals(&mut self, _control: &dyn OperationControl) -> NativeResult<u64> {
        self.log.push("nominals");
        if self.nominal_pending {
            self.nominal_pending = false;
            return Ok(1);
        }
        Ok(0)
    }

    fn apply_next_delta(
        &mut self,
        _control: &dyn OperationControl,
    ) -> NativeResult<DeltaPhaseResult> {
        self.log.push("delta");
        if self.delta_pending {
            self.delta_pending = false;
            return Ok(DeltaPhaseResult {
                processed_rows: 1,
                rule_matches: 2,
                role_propagations: 3,
            });
        }
        Ok(DeltaPhaseResult::default())
    }

    fn check_datatypes(
        &mut self,
        _control: &dyn OperationControl,
    ) -> NativeResult<DatatypePhaseResult> {
        self.log.push("datatypes");
        self.datatype_calls = self
            .datatype_calls
            .checked_add(1)
            .ok_or_else(|| NativeError::invariant("script datatype-call overflow"))?;
        Ok(DatatypePhaseResult {
            checked_components: 1,
            changed: self.datatype_calls == 2,
            clashed: false,
        })
    }

    fn has_existential_candidates(&self) -> bool {
        self.existential_pending
    }

    fn refresh_blocking(&mut self, _control: &dyn OperationControl) -> NativeResult<u64> {
        self.log.push("blocking-refresh");
        Ok(2)
    }

    fn process_existential(
        &mut self,
        _control: &dyn OperationControl,
    ) -> NativeResult<PhaseProgress> {
        self.log.push("existential");
        if self.existential_pending {
            self.existential_pending = false;
            return Ok(PhaseProgress::Progress);
        }
        Ok(PhaseProgress::NoWork)
    }

    fn process_disjunction(
        &mut self,
        _control: &dyn OperationControl,
    ) -> NativeResult<PhaseProgress> {
        self.log.push("disjunction");
        if self.disjunction_pending {
            self.disjunction_pending = false;
            self.clash = true;
            return Ok(PhaseProgress::Progress);
        }
        Ok(PhaseProgress::NoWork)
    }

    fn resolve_clash(&mut self, _control: &dyn OperationControl) -> NativeResult<ClashResolution> {
        self.log.push("resolve");
        self.clash = false;
        Ok(ClashResolution::Backtracked)
    }

    fn invalidate_after_backtrack(&mut self) -> NativeResult<()> {
        self.log.push("invalidate");
        Ok(())
    }

    fn validate_blocking(
        &mut self,
        _control: &dyn OperationControl,
    ) -> NativeResult<(ValidationStatus, u64)> {
        self.log.push("validate");
        if self.validation_invalid_pending {
            self.validation_invalid_pending = false;
            return Ok((ValidationStatus::Invalidated, 4));
        }
        Ok((ValidationStatus::Valid, 5))
    }

    fn ready_for_sat(&self) -> NativeResult<bool> {
        Ok(true)
    }

    fn check_invariants(&self) -> NativeResult<()> {
        Ok(())
    }
}

#[test]
fn exact_phase_driver_reaches_only_a_validated_fixed_point() -> NativeResult<()> {
    let mut tableau = ScriptTableau::new();
    let result = drive_tableau(&mut tableau, &NeverAbort, 100)?;
    assert_eq!(
        result,
        SessionCheckResult::computed(
            true,
            SchedulerStatistics {
                scheduler_steps: 8,
                delta_generations: 1,
                delta_rows: 1,
                rule_matches: 2,
                role_propagations: 3,
                nominal_actions: 1,
                existential_actions: 1,
                disjunction_actions: 1,
                datatype_components: 6,
                blocking_refreshes: 1,
                blocking_checks: 11,
                validation_passes: 2,
                backtracks: 1,
            }
        )
    );
    assert_eq!(
        tableau.log,
        vec![
            "nominals",
            "nominals",
            "delta",
            "datatypes",
            "nominals",
            "nominals",
            "delta",
            "datatypes",
            "nominals",
            "delta",
            "datatypes",
            "blocking-refresh",
            "existential",
            "nominals",
            "delta",
            "datatypes",
            "existential",
            "disjunction",
            "resolve",
            "invalidate",
            "nominals",
            "delta",
            "datatypes",
            "existential",
            "disjunction",
            "validate",
            "nominals",
            "delta",
            "datatypes",
            "existential",
            "disjunction",
            "validate",
        ]
    );

    let (kernel, shared) = FakeTableau::new(10);
    let session = SessionScheduler::new(kernel, SessionLimits::default())?;
    let error = session
        .check_query(&query_with(9, 0, FakeBehavior::NotReady), &NeverAbort)
        .err()
        .ok_or_else(|| NativeError::invariant("unready SAT unexpectedly succeeded"))?;
    assert_eq!(error.kind, ErrorKind::Invariant);
    assert_eq!(shared.logical_value.load(Ordering::Acquire), 10);
    assert!(session.is_poisoned());
    session.close()
}
