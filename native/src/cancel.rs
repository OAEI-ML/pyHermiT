//! Python-independent cooperative cancellation shared by coarse native operations.
// SPDX-License-Identifier: LGPL-3.0-or-later

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use pyo3::prelude::*;

use crate::error::{ErrorKind, NativeError, NativeResult};

#[derive(Debug)]
pub struct CancellationState {
    interrupted: AtomicBool,
    reason: Mutex<Option<String>>,
    deadline: Option<Instant>,
    memory_bytes: AtomicU64,
    max_memory_bytes: Option<u64>,
}

impl CancellationState {
    fn new(timeout: Option<f64>, max_memory_bytes: Option<u64>) -> NativeResult<Self> {
        let deadline = match timeout {
            None => None,
            Some(value) if value.is_finite() && value > 0.0 => {
                let duration = Duration::try_from_secs_f64(value).map_err(|_| {
                    NativeError::wire("cancellation timeout cannot be represented safely")
                })?;
                Instant::now().checked_add(duration)
            }
            Some(_) => {
                return Err(NativeError::wire(
                    "cancellation timeout must be finite and strictly positive",
                ));
            }
        };
        if max_memory_bytes == Some(0) {
            return Err(NativeError::wire(
                "max_memory_bytes must be positive when supplied",
            ));
        }
        Ok(Self {
            interrupted: AtomicBool::new(false),
            reason: Mutex::new(None),
            deadline,
            memory_bytes: AtomicU64::new(0),
            max_memory_bytes,
        })
    }

    pub fn interrupt(&self, reason: Option<String>) -> NativeResult<bool> {
        if reason.as_ref().is_some_and(String::is_empty) {
            return Err(NativeError::wire(
                "cancellation reason must be nonempty when supplied",
            ));
        }
        if self
            .interrupted
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return Ok(false);
        }
        let mut stored = self
            .reason
            .lock()
            .map_err(|_| NativeError::invariant("cancellation reason mutex is poisoned"))?;
        *stored = reason;
        drop(stored);
        Ok(true)
    }

    pub fn observe_memory(&self, amount: u64) {
        self.memory_bytes.fetch_max(amount, Ordering::AcqRel);
    }

    pub fn poll(&self) -> NativeResult<()> {
        if self
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
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
        if self
            .max_memory_bytes
            .is_some_and(|allowed| observed > allowed)
        {
            return Err(NativeError::new(
                ErrorKind::Resource,
                "RESOURCE_LIMIT",
                "native reasoning memory limit exceeded",
            )
            .with_context("limit", "max_memory_bytes")
            .with_context("observed", observed.to_string())
            .with_context(
                "allowed",
                self.max_memory_bytes.unwrap_or_default().to_string(),
            ));
        }
        Ok(())
    }

    #[must_use]
    pub fn interrupted(&self) -> bool {
        self.interrupted.load(Ordering::Acquire)
    }
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

    #[getter]
    fn interrupted(&self) -> bool {
        self.state.interrupted()
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
        Ok(())
    }
}
