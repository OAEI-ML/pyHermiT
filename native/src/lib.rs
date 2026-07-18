//! Private `PyO3` boundary for the WPR0 wire/lifecycle/state foundation.
// SPDX-License-Identifier: LGPL-3.0-or-later

#![forbid(unsafe_code)]
// This is an internal crate rather than a public Rust API. The Python contract and wire
// validators are documented externally, and keeping each validator in one place makes its
// ordered hostile-input checks auditable.
#![allow(
    clippy::missing_errors_doc,
    clippy::module_name_repetitions,
    clippy::needless_pass_by_value,
    clippy::option_if_let_else,
    clippy::redundant_pub_crate,
    clippy::too_many_lines
)]

pub mod blocking;
mod branching;
mod cancel;
pub mod datatypes;
pub mod error;
pub mod existentials;
pub mod merging;
pub mod model;
pub mod nominals;
pub mod operation_bridge;
pub mod result_wire;
pub mod roles;
pub mod rules;
pub mod services;
pub mod session;
pub mod store;
pub mod wire;

#[cfg(test)]
mod session_tests;

use std::collections::VecDeque;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use pyo3::prelude::*;
use pyo3::types::{PyBytes, PySequence};

pub use cancel::{CancellationHandle, CancellationState};
use error::{ErrorKind, NativeError, NativeResult};
use model::{
    CoreMetadata, ABI_VERSION, CORE_ADAPTER_PROTOCOL_VERSION, CORE_API_VERSION,
    CORE_MODEL_SCHEMA_VERSION, CORE_WIRE_FORMAT_VERSION, IR_SCHEMA_VERSION,
};
use store::{replay_state_trace, TableauKernel, STATE_TRACE_MAGIC, STATE_TRACE_VERSION};
use wire::{validate_owned, DocumentKind, ValidatedDocument, MAX_WIRE_BYTES};

const EVENT_CAPACITY: usize = 256;
const POLL_STRIDE_MAX: u64 = 1_000_000;
const MAX_STATE_TRACE_BYTES: usize = 64 * 1024 * 1024;

struct SessionOwned {
    ontology: ValidatedDocument,
    // Kept alive beside the ontology so the session owns exactly one validated
    // copy of each caller-supplied document for its complete lifetime.
    _config: ValidatedDocument,
    kernel: TableauKernel,
    events: VecDeque<(String, u64)>,
}

struct SessionControl {
    owner_pid: u32,
    closed: AtomicBool,
    busy: AtomicBool,
    poisoned: AtomicBool,
    cancellation: Arc<CancellationState>,
    owned: Mutex<Option<SessionOwned>>,
}

impl SessionControl {
    fn preflight(&self) -> NativeResult<BusyGuard<'_>> {
        if self.closed.load(Ordering::Acquire) {
            return Err(NativeError::new(
                ErrorKind::Disposed,
                "DISPOSED_REASONER",
                "native session is closed",
            ));
        }
        if std::process::id() != self.owner_pid {
            return Err(NativeError::new(
                ErrorKind::Fork,
                "NATIVE_FORK",
                "native session cannot be reused after fork",
            ));
        }
        if self.poisoned.load(Ordering::Acquire) {
            return Err(NativeError::new(
                ErrorKind::Poisoned,
                "NATIVE_PANIC",
                "native session is poisoned after a contained panic",
            ));
        }
        if self
            .busy
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return Err(NativeError::new(
                ErrorKind::Busy,
                "CONCURRENT_MUTATION",
                "native session already has an active operation",
            ));
        }
        Ok(BusyGuard { busy: &self.busy })
    }

    #[allow(clippy::significant_drop_tightening)]
    fn run<T>(
        &self,
        operation: impl FnOnce(&mut SessionOwned) -> NativeResult<T>,
    ) -> NativeResult<T> {
        let _guard = self.preflight()?;
        let mut slot = self
            .owned
            .lock()
            .map_err(|_| NativeError::invariant("native session mutex is poisoned"))?;
        let owned = slot.as_mut().ok_or_else(|| {
            NativeError::new(
                ErrorKind::Disposed,
                "DISPOSED_REASONER",
                "native session is closed",
            )
        })?;
        // Catch while the guard is still live so unwinding never marks the ownership mutex as
        // poisoned. The explicit session poison bit remains the sole stable lifecycle signal.
        let outcome = catch_unwind(AssertUnwindSafe(|| operation(owned)));
        drop(slot);
        outcome.unwrap_or_else(|_| {
            self.poisoned.store(true, Ordering::Release);
            Err(NativeError::new(
                ErrorKind::Poisoned,
                "NATIVE_PANIC",
                "native panic was contained; the session is poisoned",
            ))
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

#[pyclass(module = "pyhermit._native", frozen)]
struct NativeSession {
    control: Arc<SessionControl>,
}

#[pymethods]
impl NativeSession {
    #[getter]
    fn ontology_fingerprint(&self, py: Python<'_>) -> PyResult<String> {
        self.control
            .run(|owned| {
                let metadata = owned.ontology.metadata.as_ref().ok_or_else(|| {
                    NativeError::invariant("native ontology metadata is unavailable")
                })?;
                Ok(metadata.ontology_fingerprint_hex())
            })
            .map_err(|error| error.into_pyerr(py))
    }

    #[getter]
    fn closed(&self) -> bool {
        self.control.closed.load(Ordering::Acquire)
    }

    #[getter]
    fn poisoned(&self) -> bool {
        self.control.poisoned.load(Ordering::Acquire)
    }

    fn check(&self, py: Python<'_>, _query: Option<&Bound<'_, PyBytes>>) -> PyResult<Vec<u8>> {
        self.unsupported(py, "full_reasoner")
    }

    fn check_many(&self, py: Python<'_>, _queries: &Bound<'_, PySequence>) -> PyResult<Vec<u8>> {
        self.unsupported(py, "full_reasoner")
    }

    fn classify_classes(&self, py: Python<'_>) -> PyResult<Vec<u8>> {
        self.unsupported(py, "classification")
    }

    fn classify_object_properties(&self, py: Python<'_>) -> PyResult<Vec<u8>> {
        self.unsupported(py, "classification")
    }

    fn classify_data_properties(&self, py: Python<'_>) -> PyResult<Vec<u8>> {
        self.unsupported(py, "classification")
    }

    fn realize(&self, py: Python<'_>) -> PyResult<Vec<u8>> {
        self.unsupported(py, "realization")
    }

    fn apply_delta(&self, py: Python<'_>, _delta: &Bound<'_, PyBytes>) -> PyResult<Vec<u8>> {
        self.unsupported(py, "incremental_updates")
    }

    fn reset_query_state(&self, py: Python<'_>) -> PyResult<()> {
        self.control
            .run(|owned| owned.kernel.reset_to_operation_root())
            .map_err(|error| error.into_pyerr(py))
    }

    fn close(&self, py: Python<'_>) -> PyResult<()> {
        if self.control.closed.load(Ordering::Acquire) {
            return Ok(());
        }
        if std::process::id() != self.control.owner_pid {
            return Err(NativeError::new(
                ErrorKind::Fork,
                "NATIVE_FORK",
                "native session cannot be closed through inherited post-fork state",
            )
            .into_pyerr(py));
        }
        if self
            .control
            .busy
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return Err(NativeError::new(
                ErrorKind::Busy,
                "CONCURRENT_MUTATION",
                "cannot close a native session while an operation is active",
            )
            .into_pyerr(py));
        }
        let guard = BusyGuard {
            busy: &self.control.busy,
        };
        let result =
            self.control.owned.lock().map_err(|_| {
                NativeError::invariant("native session mutex is poisoned").into_pyerr(py)
            });
        match result {
            Ok(mut slot) => {
                slot.take();
                self.control.closed.store(true, Ordering::Release);
                drop(guard);
                Ok(())
            }
            Err(error) => Err(error),
        }
    }

    /// WPR0 trace parity hook. It is private test infrastructure, never a semantic check result.
    fn _debug_replay_state_trace(
        &self,
        py: Python<'_>,
        trace: &Bound<'_, PyBytes>,
    ) -> PyResult<Vec<String>> {
        let control = Arc::clone(&self.control);
        let result = control.run(|_owned| {
            let trace = copy_capped_bytes(trace, MAX_STATE_TRACE_BYTES, "state trace")?;
            py.detach(move || replay_state_trace(&trace))
        });
        result.map_err(|error| error.into_pyerr(py))
    }

    /// Deterministic cancellable work used to prove GIL detachment and same-session exclusion.
    #[pyo3(signature = (iterations, poll_stride=4096))]
    fn _debug_long_work(&self, py: Python<'_>, iterations: u64, poll_stride: u64) -> PyResult<u64> {
        if poll_stride == 0 || poll_stride > POLL_STRIDE_MAX {
            return Err(
                NativeError::wire("poll_stride must be between one and one million").into_pyerr(py),
            );
        }
        let control = Arc::clone(&self.control);
        let result = control.run(|owned| {
            py.detach(|| {
                let mut checksum = 0_u64;
                for index in 0..iterations {
                    if index % poll_stride == 0 {
                        control.cancellation.poll()?;
                    }
                    checksum = checksum.rotate_left(7) ^ index.wrapping_mul(0x9e37_79b9);
                }
                control.cancellation.poll()?;
                if owned.events.len() == EVENT_CAPACITY {
                    owned.events.pop_front();
                }
                owned
                    .events
                    .push_back(("debug_work_complete".to_owned(), iterations));
                Ok(checksum)
            })
        });
        result.map_err(|error| error.into_pyerr(py))
    }

    fn _drain_debug_events(&self, py: Python<'_>) -> PyResult<Vec<(String, u64)>> {
        self.control
            .run(|owned| Ok(owned.events.drain(..).collect()))
            .map_err(|error| error.into_pyerr(py))
    }

    /// Containment test: the panic is caught, redacted, and permanently poisons this session.
    #[allow(clippy::panic)]
    fn _debug_inject_panic(&self, py: Python<'_>) -> PyResult<()> {
        self.control
            // A non-string payload also keeps the process panic hook from disclosing an
            // internal diagnostic before `catch_unwind` maps the stable public error.
            .run(|_owned| std::panic::panic_any(()))
            .map_err(|error| error.into_pyerr(py))
    }
}

impl NativeSession {
    fn unsupported<T>(&self, py: Python<'_>, feature: &'static str) -> PyResult<T> {
        self.control
            .run(|_owned| Err(NativeError::feature(feature)))
            .map_err(|error| error.into_pyerr(py))
    }
}

#[pyfunction]
fn self_test(py: Python<'_>) -> PyResult<()> {
    let result = catch_unwind(AssertUnwindSafe(|| {
        if ABI_VERSION != 1 || IR_SCHEMA_VERSION != 1 || STATE_TRACE_VERSION != 1 {
            return Err(NativeError::version(
                "native ABI, IR, or trace schema constant is inconsistent",
            ));
        }
        if STATE_TRACE_MAGIC != "PYHERMIT-STATE-TRACE" {
            return Err(NativeError::invariant("native state-trace magic changed"));
        }
        TableauKernel::new().check_invariants()
    }));
    match result {
        Ok(value) => value.map_err(|error| error.into_pyerr(py)),
        Err(_) => Err(NativeError::new(
            ErrorKind::Poisoned,
            "NATIVE_PANIC",
            "native self-test panic was contained",
        )
        .into_pyerr(py)),
    }
}

#[pyfunction]
fn create_session(
    py: Python<'_>,
    ir: &Bound<'_, PyBytes>,
    config: &Bound<'_, PyBytes>,
    cancellation: PyRef<'_, CancellationHandle>,
) -> PyResult<NativeSession> {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let ontology = validate_owned(
            copy_capped_bytes(ir, MAX_WIRE_BYTES, "ontology wire")?,
            DocumentKind::Ontology,
        )?;
        let metadata = ontology
            .metadata
            .as_ref()
            .ok_or_else(|| NativeError::wire("ontology wire lacks core metadata"))?;
        validate_core_metadata(metadata)?;
        let config = validate_owned(
            copy_capped_bytes(config, MAX_WIRE_BYTES, "configuration wire")?,
            DocumentKind::Config,
        )?;
        Ok(NativeSession {
            control: Arc::new(SessionControl {
                owner_pid: std::process::id(),
                closed: AtomicBool::new(false),
                busy: AtomicBool::new(false),
                poisoned: AtomicBool::new(false),
                cancellation: cancellation.state(),
                owned: Mutex::new(Some(SessionOwned {
                    ontology,
                    _config: config,
                    kernel: TableauKernel::new(),
                    events: VecDeque::with_capacity(EVENT_CAPACITY),
                })),
            }),
        })
    }));
    match result {
        Ok(value) => value.map_err(|error: NativeError| error.into_pyerr(py)),
        Err(_) => Err(NativeError::new(
            ErrorKind::Poisoned,
            "NATIVE_PANIC",
            "native session-construction panic was contained",
        )
        .into_pyerr(py)),
    }
}

fn copy_capped_bytes(
    source: &Bound<'_, PyBytes>,
    maximum: usize,
    label: &'static str,
) -> NativeResult<Vec<u8>> {
    let bytes = source.as_bytes();
    if bytes.len() > maximum {
        return Err(NativeError::new(
            ErrorKind::Resource,
            "NATIVE_INPUT_SIZE_LIMIT",
            format!("{label} exceeds the native input size limit"),
        )
        .with_context("limit", label)
        .with_context("observed", bytes.len().to_string())
        .with_context("allowed", maximum.to_string()));
    }
    Ok(bytes.to_vec())
}

fn validate_core_metadata(metadata: &CoreMetadata) -> NativeResult<()> {
    if metadata.core_api_version != CORE_API_VERSION
        || metadata.core_model_schema_version != CORE_MODEL_SCHEMA_VERSION
        || metadata.core_wire_format_version != CORE_WIRE_FORMAT_VERSION
        || metadata.core_adapter_protocol_version != CORE_ADAPTER_PROTOCOL_VERSION
    {
        return Err(NativeError::new(
            ErrorKind::Version,
            "NATIVE_CORE_VERSION",
            "native session core metadata is incompatible with the compiled core contract",
        )
        .with_context(
            "expected_api",
            format!("{}.{}", CORE_API_VERSION.0, CORE_API_VERSION.1),
        )
        .with_context(
            "observed_api",
            format!(
                "{}.{}",
                metadata.core_api_version.0, metadata.core_api_version.1
            ),
        ));
    }
    Ok(())
}

#[pymodule]
fn _native(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add("__version__", env!("CARGO_PKG_VERSION"))?;
    module.add("ABI_VERSION", ABI_VERSION)?;
    module.add("IR_SCHEMA_VERSION", IR_SCHEMA_VERSION)?;
    module.add("STATE_TRACE_VERSION", STATE_TRACE_VERSION)?;
    module.add(
        "FEATURES",
        (
            "abi3-py310",
            "wire-v1",
            "state-trace-v1",
            "cancellable-mock-work",
        ),
    )?;
    module.add_class::<CancellationHandle>()?;
    module.add_class::<NativeSession>()?;
    module.add_function(wrap_pyfunction!(self_test, module)?)?;
    module.add_function(wrap_pyfunction!(create_session, module)?)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use wire::build_test_document;

    const fn metadata() -> CoreMetadata {
        CoreMetadata {
            ontology_fingerprint: [7; 32],
            structural_fingerprint: [1; 32],
            logical_fingerprint: [2; 32],
            signature_fingerprint: [3; 32],
            core_api_version: CORE_API_VERSION,
            core_model_schema_version: 1,
            core_wire_format_version: CORE_WIRE_FORMAT_VERSION,
            core_adapter_protocol_version: CORE_ADAPTER_PROTOCOL_VERSION,
        }
    }

    #[test]
    fn forced_semantic_calls_never_return_a_placeholder() -> NativeResult<()> {
        let cancellation = CancellationHandle::from_options(None, None)?;
        let session = NativeSession {
            control: Arc::new(SessionControl {
                owner_pid: std::process::id(),
                closed: AtomicBool::new(false),
                busy: AtomicBool::new(false),
                poisoned: AtomicBool::new(false),
                cancellation: cancellation.state(),
                owned: Mutex::new(Some(SessionOwned {
                    ontology: validate_owned(
                        build_test_document(DocumentKind::Ontology, Some(&metadata())),
                        DocumentKind::Ontology,
                    )?,
                    _config: validate_owned(
                        build_test_document(DocumentKind::Config, None),
                        DocumentKind::Config,
                    )?,
                    kernel: TableauKernel::new(),
                    events: VecDeque::new(),
                })),
            }),
        };
        let result: NativeResult<Vec<u8>> = session
            .control
            .run(|_owned| Err(NativeError::feature("full_reasoner")));
        assert_eq!(
            result.err().map(|error| error.kind),
            Some(ErrorKind::Feature)
        );
        Ok(())
    }
}
