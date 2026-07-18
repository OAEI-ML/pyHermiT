//! Lossless operation-control and component-error bridge for the composite tableau.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::sync::OnceLock;

use crate::blocking::{BlockingControl, BlockingError, BlockingErrorKind};
use crate::datatypes::{DatatypeControl, DatatypeError, DatatypeErrorKind};
use crate::error::{ErrorKind, NativeError, NativeResult};
use crate::existentials::{ExpansionControl, ExpansionError, ExpansionErrorKind};
use crate::roles::{RoleControl, RoleError, RoleErrorKind};
use crate::session::OperationControl;

/// Adapts one object-safe session operation control to the component control traits.
///
/// Component cancellation errors cannot encode a session timeout separately.  The first
/// original operation failure is therefore retained by move and takes precedence when the
/// component result is finished.  This also prevents a component from accidentally swallowing
/// an operation failure by returning `Ok` after a failed poll.
pub struct OperationControlBridge<'a> {
    control: &'a dyn OperationControl,
    operation_failure: OnceLock<NativeError>,
}

impl<'a> OperationControlBridge<'a> {
    #[must_use]
    pub const fn new(control: &'a dyn OperationControl) -> Self {
        Self {
            control,
            operation_failure: OnceLock::new(),
        }
    }

    pub fn finish_datatype<T>(self, result: Result<T, DatatypeError>) -> NativeResult<T> {
        self.finish(result, datatype_error_to_native)
    }

    pub fn finish_role<T>(self, result: Result<T, RoleError>) -> NativeResult<T> {
        self.finish(result, role_error_to_native)
    }

    pub fn finish_blocking<T>(self, result: Result<T, BlockingError>) -> NativeResult<T> {
        self.finish(result, blocking_error_to_native)
    }

    pub fn finish_expansion<T>(self, result: Result<T, ExpansionError>) -> NativeResult<T> {
        self.finish(result, expansion_error_to_native)
    }

    fn capture<E>(
        &self,
        result: NativeResult<()>,
        convert: fn(&NativeError) -> E,
    ) -> Result<(), E> {
        match result {
            Ok(()) => Ok(()),
            Err(error) => {
                let component_error = convert(&error);
                let _ = self.operation_failure.set(error);
                Err(component_error)
            }
        }
    }

    fn finish<T, E>(self, result: Result<T, E>, convert: fn(E) -> NativeError) -> NativeResult<T> {
        // Consuming `self` makes recovery of the retained operation error a one-shot action.
        // A second conversion cannot accidentally replay or replace the first failure.
        self.operation_failure
            .into_inner()
            .map_or_else(|| result.map_err(convert), Err)
    }
}

impl DatatypeControl for OperationControlBridge<'_> {
    fn poll(&self) -> Result<(), DatatypeError> {
        self.capture(self.control.poll(), control_to_datatype)
    }

    fn observe_memory(&self, bytes: u64) -> Result<(), DatatypeError> {
        self.capture(self.control.observe_memory(bytes), control_to_datatype)
    }
}

impl RoleControl for OperationControlBridge<'_> {
    fn poll(&self) -> Result<(), RoleError> {
        self.capture(self.control.poll(), control_to_role)
    }

    fn observe_memory(&self, bytes: u64) -> Result<(), RoleError> {
        self.capture(self.control.observe_memory(bytes), control_to_role)
    }
}

impl BlockingControl for OperationControlBridge<'_> {
    fn poll(&self) -> Result<(), BlockingError> {
        self.capture(self.control.poll(), control_to_blocking)
    }

    fn observe_memory(&self, bytes: u64) -> Result<(), BlockingError> {
        self.capture(self.control.observe_memory(bytes), control_to_blocking)
    }
}

impl ExpansionControl for OperationControlBridge<'_> {
    fn poll(&mut self) -> Result<(), ExpansionError> {
        self.capture(self.control.poll(), control_to_expansion)
    }

    fn add_work(&mut self, _amount: u64) -> Result<(), ExpansionError> {
        // `OperationControl` has no work-accounting contract.  Expansion search performs its
        // own bounded accounting and polls separately at each configured interval.
        Ok(())
    }
}

#[must_use]
pub fn datatype_error_to_native(error: DatatypeError) -> NativeError {
    const UNSUPPORTED_PREFIX: &str =
        "opaque or unsupported datatype semantics cannot be evaluated:";
    let unsupported_iri = (error.kind == DatatypeErrorKind::Invalid)
        .then(|| error.message.strip_prefix(UNSUPPORTED_PREFIX))
        .flatten()
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(str::to_owned);
    let (kind, code) = match error.kind {
        DatatypeErrorKind::Invalid if unsupported_iri.is_some() => {
            (ErrorKind::UnsupportedDatatype, "UNSUPPORTED_DATATYPE")
        }
        DatatypeErrorKind::Invalid => (ErrorKind::Wire, "NATIVE_DATATYPE_INVALID"),
        DatatypeErrorKind::Resource => (ErrorKind::Resource, "RESOURCE_LIMIT"),
        DatatypeErrorKind::Cancelled => (ErrorKind::Cancelled, "NATIVE_DATATYPE_CANCELLED"),
    };
    let native = component_error(
        kind,
        code,
        error.message,
        error.limit,
        error.observed,
        error.allowed,
    );
    match unsupported_iri {
        Some(iri) => native.with_context("datatype_iri", iri),
        None => native,
    }
}

#[must_use]
pub fn role_error_to_native(error: RoleError) -> NativeError {
    let (kind, code) = match error.kind {
        RoleErrorKind::Invalid => (ErrorKind::Wire, "NATIVE_ROLE_INVALID"),
        RoleErrorKind::Resource => (ErrorKind::Resource, "RESOURCE_LIMIT"),
        RoleErrorKind::Cancelled => (ErrorKind::Cancelled, "NATIVE_ROLE_CANCELLED"),
    };
    component_error(
        kind,
        code,
        error.message,
        error.limit,
        error.observed,
        error.allowed,
    )
}

#[must_use]
pub fn blocking_error_to_native(error: BlockingError) -> NativeError {
    let (kind, code) = match error.kind {
        BlockingErrorKind::InvalidInput => (ErrorKind::Wire, "NATIVE_BLOCKING_INVALID"),
        BlockingErrorKind::Cancelled => (ErrorKind::Cancelled, "NATIVE_BLOCKING_CANCELLED"),
        BlockingErrorKind::Resource => (ErrorKind::Resource, "RESOURCE_LIMIT"),
        BlockingErrorKind::Invariant => (ErrorKind::Invariant, "NATIVE_BLOCKING_INVARIANT"),
    };
    component_error(
        kind,
        code,
        error.message,
        error.limit,
        error.observed,
        error.allowed,
    )
}

#[must_use]
pub fn expansion_error_to_native(error: ExpansionError) -> NativeError {
    let (kind, code) = match error.kind {
        ExpansionErrorKind::InvalidInput => (ErrorKind::Wire, "NATIVE_EXPANSION_INVALID"),
        ExpansionErrorKind::Cancelled => (ErrorKind::Cancelled, "NATIVE_EXPANSION_CANCELLED"),
        ExpansionErrorKind::Resource => (ErrorKind::Resource, "RESOURCE_LIMIT"),
        ExpansionErrorKind::Invariant => (ErrorKind::Invariant, "NATIVE_EXPANSION_INVARIANT"),
    };
    component_error(
        kind,
        code,
        error.message,
        error.limit,
        error.observed,
        error.allowed,
    )
}

fn component_error(
    kind: ErrorKind,
    code: &'static str,
    message: String,
    limit: Option<&'static str>,
    observed: Option<u64>,
    allowed: Option<u64>,
) -> NativeError {
    let mut error = NativeError::new(kind, code, message);
    if let Some(value) = limit {
        error = error.with_context("limit", value);
    }
    if let Some(value) = observed {
        error = error.with_context("observed", value.to_string());
    }
    if let Some(value) = allowed {
        error = error.with_context("allowed", value.to_string());
    }
    error
}

fn control_to_datatype(error: &NativeError) -> DatatypeError {
    match error.kind {
        ErrorKind::Cancelled | ErrorKind::Timeout => {
            DatatypeError::cancelled(error.message.clone())
        }
        ErrorKind::Resource => {
            let (limit, observed, allowed) = control_resource(error);
            DatatypeError::resource(limit, observed, allowed)
        }
        _ => DatatypeError::invalid(error.message.clone()),
    }
}

fn control_to_role(error: &NativeError) -> RoleError {
    match error.kind {
        ErrorKind::Cancelled | ErrorKind::Timeout => RoleError::cancelled(error.message.clone()),
        ErrorKind::Resource => {
            let (limit, observed, allowed) = control_resource(error);
            RoleError::resource(limit, observed, allowed)
        }
        _ => RoleError::invalid(error.message.clone()),
    }
}

fn control_to_blocking(error: &NativeError) -> BlockingError {
    match error.kind {
        ErrorKind::Cancelled | ErrorKind::Timeout => {
            BlockingError::cancelled(error.message.clone())
        }
        ErrorKind::Resource => {
            let (limit, observed, allowed) = control_resource(error);
            BlockingError::resource(error.message.clone(), limit, observed, allowed)
        }
        ErrorKind::Invariant | ErrorKind::Poisoned => {
            BlockingError::invariant(error.message.clone())
        }
        _ => BlockingError::invalid(error.message.clone()),
    }
}

fn control_to_expansion(error: &NativeError) -> ExpansionError {
    match error.kind {
        ErrorKind::Cancelled | ErrorKind::Timeout => {
            ExpansionError::cancelled(error.message.clone())
        }
        ErrorKind::Resource => {
            let (limit, observed, allowed) = control_resource(error);
            ExpansionError::resource(error.message.clone(), limit, observed, allowed)
        }
        ErrorKind::Invariant | ErrorKind::Poisoned => {
            ExpansionError::invariant(error.message.clone())
        }
        _ => ExpansionError::invalid(error.message.clone()),
    }
}

fn control_resource(error: &NativeError) -> (&'static str, u64, u64) {
    let limit = match error.context.get("limit").map(String::as_str) {
        Some("max_memory_bytes") => "max_memory_bytes",
        Some("max_scheduler_steps") => "max_scheduler_steps",
        Some("max_batch_queries") => "max_batch_queries",
        Some("max_batch_result_bytes") => "max_batch_result_bytes",
        Some("max_event_queue") => "max_event_queue",
        _ => "operation_control",
    };
    let observed = context_u64(error, "observed");
    let allowed = context_u64(error, "allowed");
    (limit, observed, allowed)
}

fn context_u64(error: &NativeError, key: &str) -> u64 {
    error
        .context
        .get(key)
        .and_then(|value| value.parse().ok())
        .unwrap_or_default()
}
