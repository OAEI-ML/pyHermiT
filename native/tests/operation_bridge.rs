// SPDX-License-Identifier: LGPL-3.0-or-later

pub use _native::{blocking, datatypes, error, existentials, roles, session};

#[path = "../src/operation_bridge.rs"]
mod bridge;

use std::sync::atomic::{AtomicU64, Ordering};

use _native::blocking::{BlockingControl, BlockingError, BlockingErrorKind};
use _native::datatypes::{DatatypeControl, DatatypeError, DatatypeErrorKind};
use _native::error::{ErrorKind, NativeError, NativeResult};
use _native::existentials::{ExpansionControl, ExpansionError, ExpansionErrorKind};
use _native::roles::{RoleControl, RoleError, RoleErrorKind};
use _native::session::{NeverAbort, OperationControl};

use bridge::{
    blocking_error_to_native, datatype_error_to_native, expansion_error_to_native,
    role_error_to_native, OperationControlBridge,
};

#[derive(Debug)]
struct FixedFailureControl {
    kind: ErrorKind,
    polls: AtomicU64,
    memory: AtomicU64,
}

impl FixedFailureControl {
    const fn new(kind: ErrorKind) -> Self {
        Self {
            kind,
            polls: AtomicU64::new(0),
            memory: AtomicU64::new(0),
        }
    }

    fn failure(&self, observed: u64) -> NativeError {
        match self.kind {
            ErrorKind::Cancelled => NativeError::new(
                ErrorKind::Cancelled,
                "REASONER_INTERRUPTED",
                "injected operation cancellation",
            ),
            ErrorKind::Timeout => NativeError::new(
                ErrorKind::Timeout,
                "REASONER_TIMEOUT",
                "injected operation timeout",
            ),
            ErrorKind::Resource => NativeError::new(
                ErrorKind::Resource,
                "RESOURCE_LIMIT",
                "injected operation memory limit",
            )
            .with_context("limit", "dynamic_test_memory")
            .with_context("observed", observed.to_string())
            .with_context("allowed", "64"),
            ErrorKind::Invariant => NativeError::new(
                ErrorKind::Invariant,
                "NATIVE_TEST_INVARIANT",
                "injected operation invariant",
            )
            .with_context("owner", "test-tableau"),
            _ => NativeError::new(
                self.kind,
                "NATIVE_TEST_FAILURE",
                "injected generic operation failure",
            ),
        }
    }
}

impl OperationControl for FixedFailureControl {
    fn poll(&self) -> NativeResult<()> {
        self.polls.fetch_add(1, Ordering::AcqRel);
        Err(self.failure(0))
    }

    fn observe_memory(&self, bytes: u64) -> NativeResult<()> {
        self.memory.store(bytes, Ordering::Release);
        Err(self.failure(bytes))
    }
}

#[derive(Debug, Default)]
struct SequencedFailureControl {
    polls: AtomicU64,
}

impl OperationControl for SequencedFailureControl {
    fn poll(&self) -> NativeResult<()> {
        let poll = self.polls.fetch_add(1, Ordering::AcqRel);
        if poll == 0 {
            Err(NativeError::new(
                ErrorKind::Timeout,
                "FIRST_TIMEOUT",
                "first operation failure",
            ))
        } else {
            Err(NativeError::new(
                ErrorKind::Invariant,
                "LATER_INVARIANT",
                "later operation failure",
            ))
        }
    }

    fn observe_memory(&self, bytes: u64) -> NativeResult<()> {
        Err(NativeError::new(
            ErrorKind::Resource,
            "LATER_RESOURCE",
            "later memory failure",
        )
        .with_context("limit", "later_limit")
        .with_context("observed", bytes.to_string())
        .with_context("allowed", "0"))
    }
}

fn require_native_error<T>(result: NativeResult<T>) -> NativeResult<NativeError> {
    result
        .err()
        .ok_or_else(|| NativeError::invariant("expected native bridge failure"))
}

fn assert_resource_context(error: &NativeError, limit: &str, observed: &str, allowed: &str) {
    assert_eq!(error.kind, ErrorKind::Resource);
    assert_eq!(error.code, "RESOURCE_LIMIT");
    assert_eq!(error.context.get("limit").map(String::as_str), Some(limit));
    assert_eq!(
        error.context.get("observed").map(String::as_str),
        Some(observed)
    );
    assert_eq!(
        error.context.get("allowed").map(String::as_str),
        Some(allowed)
    );
}

#[test]
fn cancellation_and_timeout_remain_distinct_after_component_round_trips() -> NativeResult<()> {
    let cancellation = FixedFailureControl::new(ErrorKind::Cancelled);
    let bridge = OperationControlBridge::new(&cancellation);
    let component = DatatypeControl::poll(&bridge)
        .err()
        .ok_or_else(|| NativeError::invariant("datatype cancellation was swallowed"))?;
    assert_eq!(component.kind, DatatypeErrorKind::Cancelled);
    let error = require_native_error(bridge.finish_datatype::<()>(Err(component)))?;
    assert_eq!(error.kind, ErrorKind::Cancelled);
    assert_eq!(error.code, "REASONER_INTERRUPTED");
    assert_eq!(cancellation.polls.load(Ordering::Acquire), 1);

    let timeout = FixedFailureControl::new(ErrorKind::Timeout);
    let bridge = OperationControlBridge::new(&timeout);
    let component = RoleControl::poll(&bridge)
        .err()
        .ok_or_else(|| NativeError::invariant("role timeout was swallowed"))?;
    assert_eq!(component.kind, RoleErrorKind::Cancelled);
    let error = require_native_error(bridge.finish_role::<()>(Err(component)))?;
    assert_eq!(error.kind, ErrorKind::Timeout);
    assert_eq!(error.code, "REASONER_TIMEOUT");
    assert_eq!(timeout.polls.load(Ordering::Acquire), 1);
    Ok(())
}

#[test]
fn memory_failure_context_survives_even_if_the_component_returns_success() -> NativeResult<()> {
    let control = FixedFailureControl::new(ErrorKind::Resource);
    let bridge = OperationControlBridge::new(&control);
    let component = BlockingControl::observe_memory(&bridge, 65)
        .err()
        .ok_or_else(|| NativeError::invariant("blocking memory failure was swallowed"))?;
    assert_eq!(component.kind, BlockingErrorKind::Resource);
    assert_eq!(component.limit, Some("operation_control"));

    let error = require_native_error(bridge.finish_blocking(Ok(7_u8)))?;
    assert_eq!(error.kind, ErrorKind::Resource);
    assert_eq!(error.code, "RESOURCE_LIMIT");
    assert_eq!(
        error.context.get("limit").map(String::as_str),
        Some("dynamic_test_memory")
    );
    assert_eq!(
        error.context.get("observed").map(String::as_str),
        Some("65")
    );
    assert_eq!(error.context.get("allowed").map(String::as_str), Some("64"));
    assert_eq!(control.memory.load(Ordering::Acquire), 65);
    Ok(())
}

#[test]
fn invariant_operation_failure_takes_precedence_over_component_output() -> NativeResult<()> {
    let control = FixedFailureControl::new(ErrorKind::Invariant);
    let mut bridge = OperationControlBridge::new(&control);
    let component = ExpansionControl::poll(&mut bridge)
        .err()
        .ok_or_else(|| NativeError::invariant("expansion invariant was swallowed"))?;
    assert_eq!(component.kind, ExpansionErrorKind::Invariant);

    let error = require_native_error(bridge.finish_expansion::<()>(Err(component)))?;
    assert_eq!(error.kind, ErrorKind::Invariant);
    assert_eq!(error.code, "NATIVE_TEST_INVARIANT");
    assert_eq!(
        error.context.get("owner").map(String::as_str),
        Some("test-tableau")
    );
    Ok(())
}

#[test]
fn multiple_component_polls_preserve_and_consume_the_first_failure() -> NativeResult<()> {
    let control = SequencedFailureControl::default();
    let bridge = OperationControlBridge::new(&control);
    let first = DatatypeControl::poll(&bridge)
        .err()
        .ok_or_else(|| NativeError::invariant("first sequenced failure was swallowed"))?;
    assert_eq!(first.kind, DatatypeErrorKind::Cancelled);

    let later = BlockingControl::poll(&bridge)
        .err()
        .ok_or_else(|| NativeError::invariant("later sequenced failure was swallowed"))?;
    assert_eq!(later.kind, BlockingErrorKind::Invariant);

    let error = require_native_error(bridge.finish_blocking::<()>(Err(later)))?;
    assert_eq!(error.kind, ErrorKind::Timeout);
    assert_eq!(error.code, "FIRST_TIMEOUT");
    assert_eq!(error.message, "first operation failure");
    assert_eq!(control.polls.load(Ordering::Acquire), 2);
    Ok(())
}

#[test]
fn component_errors_map_to_stable_native_kinds_codes_and_limits() {
    let datatype = datatype_error_to_native(DatatypeError::resource("digits", 11, 10));
    assert_resource_context(&datatype, "digits", "11", "10");

    let role_resource = role_error_to_native(RoleError::resource("states", 9, 8));
    assert_resource_context(&role_resource, "states", "9", "8");

    let blocking_resource = blocking_error_to_native(BlockingError::resource(
        "candidate limit",
        "candidates",
        7,
        6,
    ));
    assert_resource_context(&blocking_resource, "candidates", "7", "6");

    let expansion_resource =
        expansion_error_to_native(ExpansionError::resource("witness limit", "witnesses", 5, 4));
    assert_resource_context(&expansion_resource, "witnesses", "5", "4");

    let role = role_error_to_native(RoleError::invalid("dangling role"));
    assert_eq!(role.kind, ErrorKind::Wire);
    assert_eq!(role.code, "NATIVE_ROLE_INVALID");

    let blocking = blocking_error_to_native(BlockingError::invariant("stale assignment"));
    assert_eq!(blocking.kind, ErrorKind::Invariant);
    assert_eq!(blocking.code, "NATIVE_BLOCKING_INVARIANT");

    let expansion = expansion_error_to_native(ExpansionError::invalid("malformed obligation"));
    assert_eq!(expansion.kind, ErrorKind::Wire);
    assert_eq!(expansion.code, "NATIVE_EXPANSION_INVALID");

    let cancelled = datatype_error_to_native(DatatypeError::cancelled("stop"));
    assert_eq!(cancelled.kind, ErrorKind::Cancelled);
    assert_eq!(cancelled.code, "NATIVE_DATATYPE_CANCELLED");
}

#[test]
fn one_object_safe_bridge_implements_every_supported_component_control() -> NativeResult<()> {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<OperationControlBridge<'static>>();

    let operation: &dyn OperationControl = &NeverAbort;
    let mut bridge = OperationControlBridge::new(operation);
    assert!(DatatypeControl::poll(&bridge).is_ok());
    assert!(DatatypeControl::observe_memory(&bridge, 1).is_ok());
    assert!(RoleControl::poll(&bridge).is_ok());
    assert!(RoleControl::observe_memory(&bridge, 2).is_ok());
    assert!(BlockingControl::poll(&bridge).is_ok());
    assert!(BlockingControl::observe_memory(&bridge, 3).is_ok());
    assert!(ExpansionControl::poll(&mut bridge).is_ok());
    assert!(ExpansionControl::add_work(&mut bridge, u64::MAX).is_ok());
    bridge.finish_expansion(Ok(()))
}
