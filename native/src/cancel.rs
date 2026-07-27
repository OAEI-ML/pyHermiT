//! Python-independent cooperative cancellation shared by coarse native operations.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::{Duration, Instant};

use pyo3::prelude::*;

use crate::error::{ErrorKind, NativeError, NativeResult};

#[derive(Debug)]
pub struct CancellationState {
    interrupted: AtomicBool,
    reason: Mutex<Option<String>>,
    deadline_nanos: AtomicU64,
    memory_bytes: AtomicU64,
    max_memory_bytes: AtomicU64,
    poll_count: AtomicU64,
}

impl CancellationState {
    fn new(timeout: Option<f64>, max_memory_bytes: Option<u64>) -> NativeResult<Self> {
        let deadline_nanos = validate_deadline(timeout)?;
        let max_memory_bytes = validate_memory_limit(max_memory_bytes)?;
        Ok(Self {
            interrupted: AtomicBool::new(false),
            reason: Mutex::new(None),
            deadline_nanos: AtomicU64::new(deadline_nanos),
            memory_bytes: AtomicU64::new(0),
            max_memory_bytes: AtomicU64::new(max_memory_bytes),
            poll_count: AtomicU64::new(0),
        })
    }

    pub fn interrupt(&self, reason: Option<String>) -> NativeResult<bool> {
        if reason.as_ref().is_some_and(String::is_empty) {
            return Err(NativeError::wire(
                "cancellation reason must be nonempty when supplied",
            ));
        }
        let mut stored = self
            .reason
            .lock()
            .map_err(|_| NativeError::invariant("cancellation reason mutex is poisoned"))?;
        if self.interrupted.load(Ordering::Acquire) {
            return Ok(false);
        }
        *stored = reason;
        self.interrupted.store(true, Ordering::Release);
        drop(stored);
        Ok(true)
    }

    /// Start a fresh serialized public operation while retaining this shared handle.
    ///
    /// The caller guarantees that the previous operation has returned. Validation completes
    /// before any live state changes, so an invalid reset leaves the old cancellation state
    /// untouched. All fields are then published before the interrupted flag is cleared.
    pub fn reset(&self, timeout: Option<f64>, max_memory_bytes: Option<u64>) -> NativeResult<()> {
        let deadline_nanos = validate_deadline(timeout)?;
        let max_memory_bytes = validate_memory_limit(max_memory_bytes)?;
        let mut reason = self
            .reason
            .lock()
            .map_err(|_| NativeError::invariant("cancellation reason mutex is poisoned"))?;
        *reason = None;
        self.memory_bytes.store(0, Ordering::Release);
        self.max_memory_bytes
            .store(max_memory_bytes, Ordering::Release);
        self.deadline_nanos.store(deadline_nanos, Ordering::Release);
        self.poll_count.store(0, Ordering::Release);
        self.interrupted.store(false, Ordering::Release);
        drop(reason);
        Ok(())
    }

    pub fn observe_memory(&self, amount: u64) {
        self.memory_bytes.fetch_max(amount, Ordering::AcqRel);
    }

    pub fn poll(&self) -> NativeResult<()> {
        let _ = self
            .poll_count
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |count| {
                Some(count.saturating_add(1))
            });
        let deadline_nanos = self.deadline_nanos.load(Ordering::Acquire);
        if deadline_nanos != 0 && monotonic_nanos() >= deadline_nanos {
            return Err(NativeError::new(
                ErrorKind::Timeout,
                "REASONER_TIMEOUT",
                "native reasoning operation exceeded its timeout",
            ));
        }
        if self.interrupted.load(Ordering::Acquire) {
            let reason = self
                .reason
                .lock()
                .map_err(|_| NativeError::invariant("cancellation reason mutex is poisoned"))?
                .clone()
                .unwrap_or_else(|| "native reasoning operation was interrupted".to_owned());
            return Err(NativeError::new(
                ErrorKind::Cancelled,
                "REASONER_INTERRUPTED",
                reason,
            ));
        }
        let observed = self.memory_bytes.load(Ordering::Acquire);
        let allowed = self.max_memory_bytes.load(Ordering::Acquire);
        if allowed != 0 && observed > allowed {
            return Err(NativeError::new(
                ErrorKind::Resource,
                "RESOURCE_LIMIT",
                "native reasoning memory limit exceeded",
            )
            .with_context("limit", "max_memory_bytes")
            .with_context("observed", observed.to_string())
            .with_context("allowed", allowed.to_string()));
        }
        Ok(())
    }

    #[must_use]
    pub fn interrupted(&self) -> bool {
        self.interrupted.load(Ordering::Acquire)
    }

    #[must_use]
    pub fn poll_count(&self) -> u64 {
        self.poll_count.load(Ordering::Acquire)
    }
}

fn validate_deadline(timeout: Option<f64>) -> NativeResult<u64> {
    let Some(value) = timeout else {
        return Ok(0);
    };
    if !value.is_finite() || value <= 0.0 {
        return Err(NativeError::wire(
            "cancellation timeout must be finite and strictly positive",
        ));
    }
    let duration = Duration::try_from_secs_f64(value)
        .map_err(|_| NativeError::wire("cancellation timeout cannot be represented safely"))?;
    let duration_nanos = u64::try_from(duration.as_nanos())
        .ok()
        .filter(|nanos| *nanos != 0)
        .ok_or_else(|| NativeError::wire("cancellation timeout cannot be represented safely"))?;
    monotonic_nanos()
        .checked_add(duration_nanos)
        .filter(|deadline| *deadline != 0)
        .ok_or_else(|| NativeError::wire("cancellation timeout cannot be represented safely"))
}

fn validate_memory_limit(max_memory_bytes: Option<u64>) -> NativeResult<u64> {
    match max_memory_bytes {
        None => Ok(0),
        Some(0) => Err(NativeError::wire(
            "max_memory_bytes must be positive when supplied",
        )),
        Some(value) => Ok(value),
    }
}

fn monotonic_nanos() -> u64 {
    static EPOCH: OnceLock<Instant> = OnceLock::new();
    let elapsed = EPOCH.get_or_init(Instant::now).elapsed().as_nanos();
    u64::try_from(elapsed).unwrap_or(u64::MAX)
}

#[pyclass(module = "pyhermit._native", frozen, skip_from_py_object)]
#[derive(Clone, Debug)]
pub struct CancellationHandle {
    state: Arc<CancellationState>,
}

impl CancellationHandle {
    pub fn from_options(timeout: Option<f64>, max_memory_bytes: Option<u64>) -> NativeResult<Self> {
        Ok(Self {
            state: Arc::new(CancellationState::new(timeout, max_memory_bytes)?),
        })
    }

    #[must_use]
    pub fn state(&self) -> Arc<CancellationState> {
        Arc::clone(&self.state)
    }
}

impl crate::blocking::BlockingControl for CancellationState {
    fn poll(&self) -> Result<(), crate::blocking::BlockingError> {
        Self::poll(self).map_err(cancellation_blocking_error)
    }

    fn observe_memory(&self, bytes: u64) -> Result<(), crate::blocking::BlockingError> {
        Self::observe_memory(self, bytes);
        Self::poll(self).map_err(cancellation_blocking_error)
    }
}

impl crate::roles::RoleControl for CancellationState {
    fn poll(&self) -> Result<(), crate::roles::RoleError> {
        Self::poll(self).map_err(cancellation_role_error)
    }

    fn observe_memory(&self, bytes: u64) -> Result<(), crate::roles::RoleError> {
        Self::observe_memory(self, bytes);
        Self::poll(self).map_err(cancellation_role_error)
    }
}

impl crate::datatypes::DatatypeControl for CancellationState {
    fn poll(&self) -> Result<(), crate::datatypes::DatatypeError> {
        Self::poll(self).map_err(cancellation_datatype_error)
    }

    fn observe_memory(&self, bytes: u64) -> Result<(), crate::datatypes::DatatypeError> {
        Self::observe_memory(self, bytes);
        Self::poll(self).map_err(cancellation_datatype_error)
    }
}

fn cancellation_blocking_error(error: NativeError) -> crate::blocking::BlockingError {
    match error.kind {
        ErrorKind::Cancelled | ErrorKind::Timeout => {
            crate::blocking::BlockingError::cancelled(error.message)
        }
        ErrorKind::Resource => crate::blocking::BlockingError::resource(
            error.message,
            "max_memory_bytes",
            error
                .context
                .get("observed")
                .and_then(|value| value.parse().ok())
                .unwrap_or_default(),
            error
                .context
                .get("allowed")
                .and_then(|value| value.parse().ok())
                .unwrap_or_default(),
        ),
        _ => crate::blocking::BlockingError::invariant(error.message),
    }
}

fn cancellation_role_error(error: NativeError) -> crate::roles::RoleError {
    match error.kind {
        ErrorKind::Cancelled | ErrorKind::Timeout => {
            crate::roles::RoleError::cancelled(error.message)
        }
        ErrorKind::Resource => crate::roles::RoleError::resource(
            "max_memory_bytes",
            error
                .context
                .get("observed")
                .and_then(|value| value.parse().ok())
                .unwrap_or_default(),
            error
                .context
                .get("allowed")
                .and_then(|value| value.parse().ok())
                .unwrap_or_default(),
        ),
        _ => crate::roles::RoleError::invalid(error.message),
    }
}

fn cancellation_datatype_error(error: NativeError) -> crate::datatypes::DatatypeError {
    match error.kind {
        ErrorKind::Cancelled | ErrorKind::Timeout => {
            crate::datatypes::DatatypeError::cancelled(error.message)
        }
        ErrorKind::Resource => crate::datatypes::DatatypeError::resource(
            "max_memory_bytes",
            error
                .context
                .get("observed")
                .and_then(|value| value.parse().ok())
                .unwrap_or_default(),
            error
                .context
                .get("allowed")
                .and_then(|value| value.parse().ok())
                .unwrap_or_default(),
        ),
        _ => crate::datatypes::DatatypeError::invalid(error.message),
    }
}

#[pymethods]
impl CancellationHandle {
    #[new]
    #[pyo3(signature = (timeout=None, max_memory_bytes=None))]
    fn py_new(
        py: Python<'_>,
        timeout: Option<f64>,
        max_memory_bytes: Option<u64>,
    ) -> PyResult<Self> {
        Self::from_options(timeout, max_memory_bytes).map_err(|error| error.into_pyerr(py))
    }

    #[pyo3(signature = (reason=None))]
    fn interrupt(&self, py: Python<'_>, reason: Option<String>) -> PyResult<bool> {
        self.state
            .interrupt(reason)
            .map_err(|error| error.into_pyerr(py))
    }

    fn observe_memory(&self, memory_bytes: u64) {
        self.state.observe_memory(memory_bytes);
    }

    #[pyo3(signature = (timeout=None, max_memory_bytes=None))]
    fn reset(
        &self,
        py: Python<'_>,
        timeout: Option<f64>,
        max_memory_bytes: Option<u64>,
    ) -> PyResult<()> {
        self.state
            .reset(timeout, max_memory_bytes)
            .map_err(|error| error.into_pyerr(py))
    }

    #[getter]
    fn interrupted(&self) -> bool {
        self.state.interrupted()
    }

    #[getter]
    fn _debug_poll_count(&self) -> u64 {
        self.state.poll_count()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interruption_and_resource_limits_are_stable() -> NativeResult<()> {
        let handle = CancellationHandle::from_options(None, Some(8))?;
        handle.state.observe_memory(9);
        assert_eq!(
            handle.state.poll().err().map(|error| error.kind),
            Some(ErrorKind::Resource)
        );

        let handle = CancellationHandle::from_options(None, None)?;
        assert!(handle.state.interrupt(Some("stop".to_owned()))?);
        assert!(!handle.state.interrupt(None)?);
        assert_eq!(
            handle.state.poll().err().map(|error| error.kind),
            Some(ErrorKind::Cancelled)
        );

        handle.state.reset(None, Some(16))?;
        assert!(!handle.state.interrupted());
        handle.state.observe_memory(9);
        handle.state.poll()?;
        handle.state.observe_memory(17);
        assert_eq!(
            handle.state.poll().err().map(|error| error.kind),
            Some(ErrorKind::Resource)
        );
        Ok(())
    }
}
