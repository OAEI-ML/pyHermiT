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
mod classification_bridge;
mod datatype_tableau;
pub mod datatypes;
pub mod encoded;
pub mod error;
pub mod event_wire;
pub mod existentials;
pub mod input_wire;
pub mod merging;
pub mod model;
pub mod native_tableau;
pub mod nominals;
pub mod operation_bridge;
pub mod program_bridge;
mod realization_bridge;
pub mod result_wire;
pub mod roles;
pub mod rules;
mod service_context;
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
use std::time::{Duration, Instant};

use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyInt, PyMemoryView, PySequence, PySlice, PyString, PyTuple};
use sha2::{Digest, Sha256};

pub use cancel::{CancellationHandle, CancellationState};
use error::{ErrorKind, NativeError, NativeResult};
use event_wire::encode_events;
use input_wire::{
    decode_config, decode_delta, decode_ontology, decode_ontology_metadata, decode_query,
    DecodeLimits, DecodedConfig, DecodedDelta, DecodedOntology, DecodedQuery, InputWireError,
};
use model::{
    ABI_VERSION, CORE_ADAPTER_PROTOCOL_VERSION, CORE_API_VERSION, CORE_MODEL_SCHEMA_VERSION,
    CORE_WIRE_FORMAT_VERSION, IR_SCHEMA_VERSION,
};
use native_tableau::ProductionTableau;
use program_bridge::load_permanent_rule_state;
use result_wire::{
    encode_check, encode_check_many, encode_delta, encode_hierarchy, encode_realization_ids,
    CheckStatistics, CheckWireResult, DeltaWireOutcome,
};
use services::{ClassificationCache, ClassificationDomain, RealizationCache};
use session::{QueryKey, SessionCheckResult, SessionLimits, SessionQuery, SessionScheduler};
use store::{replay_state_trace, TableauKernel, STATE_TRACE_MAGIC, STATE_TRACE_VERSION};

const EVENT_CAPACITY: usize = 256;
const POLL_STRIDE_MAX: u64 = 1_000_000;
const MAX_STATE_TRACE_BYTES: usize = 64 * 1024 * 1024;
const MAX_ENCODED_SESSION_METADATA_BYTES: usize = 4 * 1024;
const MAX_DEFERRED_FINGERPRINT_CONTEXT_BYTES: usize = 128 * 1024;
const MAX_DEFERRED_CACHE_TEMPLATE_BYTES: usize = 64 * 1024;
const DEFERRED_FINGERPRINT_VERSION: u8 = 1;
const LOGICAL_FINGERPRINT_SENTINEL: &str =
    "LLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLL";
const SIGNATURE_FINGERPRINT_SENTINEL: &str =
    "SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS";
const COMPILER_CACHE_DOMAIN: &[u8] = b"pyhermit/compiler-cache/v1\x00";
const HERMIT_COMPATIBILITY_ID: &str = "hermit-37ec30a-v1";
const COMPILER_CACHE_SCHEMA_VERSION: u64 = 1;
const PYTHON_VERSION_SOURCE: &str = include_str!("../../src/pyhermit/_version.py");

struct DeferredFingerprintRequest {
    context: encoded::fingerprints::StructuralContextEvidence,
    structural_mode: encoded::fingerprints::StructuralFingerprintMode,
    compiler_cache_template: Vec<u8>,
}

#[derive(Clone, Copy)]
struct BorrowedPyBytes<'a, 'py> {
    view: &'a Bound<'py, PyAny>,
    len: usize,
}

impl encoded::ByteSource for BorrowedPyBytes<'_, '_> {
    fn len(self) -> usize {
        self.len
    }

    fn byte(self, index: usize) -> Option<u8> {
        self.view.get_item(index).ok()?.extract().ok()
    }
}

struct BorrowedPyBufferLease<'py> {
    view: Bound<'py, PyAny>,
    len: usize,
}

impl<'py> BorrowedPyBufferLease<'py> {
    const fn source(&self) -> BorrowedPyBytes<'_, 'py> {
        BorrowedPyBytes {
            view: &self.view,
            len: self.len,
        }
    }
}

struct RetainedPyByteRange<'py> {
    owner: Bound<'py, PyBytes>,
    start: usize,
    end: usize,
}

impl RetainedPyByteRange<'_> {
    fn source(&self) -> &[u8] {
        &self.owner.as_bytes()[self.start..self.end]
    }
}

struct BorrowedEncodedSliceLease<'py> {
    posting_mode: u8,
    postings: BorrowedPyBufferLease<'py>,
    context_bytes: usize,
    scope_maps: Vec<BorrowedPyBufferLease<'py>>,
    root_kinds: BorrowedPyBufferLease<'py>,
    root_ids: BorrowedPyBufferLease<'py>,
    node_tags: BorrowedPyBufferLease<'py>,
    node_field_offsets: BorrowedPyBufferLease<'py>,
    field_kinds: BorrowedPyBufferLease<'py>,
    field_values: BorrowedPyBufferLease<'py>,
    field_lengths: BorrowedPyBufferLease<'py>,
    item_kinds: BorrowedPyBufferLease<'py>,
    item_values: BorrowedPyBufferLease<'py>,
    item_lengths: BorrowedPyBufferLease<'py>,
    scalar_bytes: BorrowedPyBufferLease<'py>,
}

struct RetainedEncodedSliceLease<'py> {
    posting_mode: u8,
    postings: RetainedPyByteRange<'py>,
    context_bytes: usize,
    scope_maps: Vec<RetainedPyByteRange<'py>>,
    root_kinds: RetainedPyByteRange<'py>,
    root_ids: RetainedPyByteRange<'py>,
    node_tags: RetainedPyByteRange<'py>,
    node_field_offsets: RetainedPyByteRange<'py>,
    field_kinds: RetainedPyByteRange<'py>,
    field_values: RetainedPyByteRange<'py>,
    field_lengths: RetainedPyByteRange<'py>,
    item_kinds: RetainedPyByteRange<'py>,
    item_values: RetainedPyByteRange<'py>,
    item_lengths: RetainedPyByteRange<'py>,
    scalar_bytes: RetainedPyByteRange<'py>,
}

struct EncodedSliceInput<B: encoded::ByteSource> {
    posting_mode: u8,
    postings: B,
    context_bytes: usize,
    scope_maps: Vec<B>,
    columns: encoded::EncodedColumns<B>,
}

struct SessionOwned {
    ontology: Arc<DecodedOntology>,
    // Retained beside the ontology so all effective native configuration is owned
    // and immutable for the complete session lifetime.
    config: DecodedConfig,
    scheduler: SessionScheduler<ProductionTableau>,
    classification: ClassificationCache,
    realization: RealizationCache,
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
    compiler_digest: Option<[u8; 32]>,
    encoded_compiler_gil_released: bool,
}

#[pymethods]
impl NativeSession {
    #[getter]
    fn ontology_fingerprint(&self, py: Python<'_>) -> PyResult<String> {
        self.control
            .run(|owned| Ok(hex_digest(&owned.ontology.metadata.ontology_fingerprint)))
            .map_err(|error| error.into_pyerr(py))
    }

    #[getter]
    fn _debug_source_fingerprints(&self, py: Python<'_>) -> PyResult<(String, String, String)> {
        self.control
            .run(|owned| {
                let metadata = &owned.ontology.metadata;
                Ok((
                    hex_digest(&metadata.structural_fingerprint.digest),
                    hex_digest(&metadata.logical_fingerprint.digest),
                    hex_digest(&metadata.signature_fingerprint.digest),
                ))
            })
            .map_err(|error| error.into_pyerr(py))
    }

    #[getter]
    fn permanent_program_sha256(&self, py: Python<'_>) -> PyResult<String> {
        self.control
            .run(|owned| Ok(hex_digest(&owned.ontology.metadata.program_sha256)))
            .map_err(|error| error.into_pyerr(py))
    }

    #[getter]
    fn compiler_digest(&self, py: Python<'_>) -> PyResult<Option<String>> {
        self.control
            .run(|_owned| Ok(self.compiler_digest.map(|value| hex_digest(&value))))
            .map_err(|error| error.into_pyerr(py))
    }

    #[getter]
    fn encoded_compiler_gil_released(&self, py: Python<'_>) -> PyResult<bool> {
        self.control
            .run(|_owned| Ok(self.encoded_compiler_gil_released))
            .map_err(|error| error.into_pyerr(py))
    }

    fn _encoded_service_context_v1(&self, py: Python<'_>) -> PyResult<Vec<u8>> {
        let control = Arc::clone(&self.control);
        let compiler_digest = self.compiler_digest.ok_or_else(|| {
            NativeError::new(
                ErrorKind::Version,
                "NATIVE_ENCODED_CONTEXT_UNAVAILABLE",
                "native scalar-wire session has no encoded compiler digest",
            )
            .into_pyerr(py)
        })?;
        control
            .run(|owned| {
                py.detach(|| {
                    control.cancellation.poll()?;
                    let encoded = service_context::encode_service_context(
                        owned.ontology.as_ref(),
                        &compiler_digest,
                    )?;
                    control.cancellation.poll()?;
                    Ok(encoded)
                })
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

    fn check(&self, py: Python<'_>, query: Option<&Bound<'_, PyBytes>>) -> PyResult<Vec<u8>> {
        let limits = DecodeLimits::default();
        let query_wire = query
            .map(|value| copy_capped_bytes(value, limits.max_wire_bytes, "query wire"))
            .transpose()
            .map_err(|error| error.into_pyerr(py))?;
        let control = Arc::clone(&self.control);
        let result = control.run(|owned| {
            py.detach(|| {
                control.cancellation.poll()?;
                let decoded = query_wire
                    .map(|wire| decode_session_query(wire, &limits))
                    .transpose()?;
                let started = Instant::now();
                let result = if let Some(query) = decoded.as_ref() {
                    owned
                        .scheduler
                        .check_query(query, control.cancellation.as_ref())?
                } else {
                    owned
                        .scheduler
                        .check_permanent(control.cancellation.as_ref())?
                };
                control.cancellation.poll()?;
                encode_check(check_wire_result(result, started.elapsed()))
            })
        });
        result.map_err(|error| error.into_pyerr(py))
    }

    fn check_many(&self, py: Python<'_>, queries: &Bound<'_, PySequence>) -> PyResult<Vec<u8>> {
        let limits = DecodeLimits::default();
        let count = queries.len()?;
        let mut wires = Vec::new();
        wires.try_reserve_exact(count).map_err(|_| {
            NativeError::new(
                ErrorKind::Resource,
                "NATIVE_INPUT_SIZE_LIMIT",
                "query batch allocation failed",
            )
            .into_pyerr(py)
        })?;
        for index in 0..count {
            let item = queries.get_item(index)?;
            let bytes = item.cast::<PyBytes>().map_err(|_| {
                NativeError::wire("query batch items must be exact bytes").into_pyerr(py)
            })?;
            wires.push(
                copy_capped_bytes(bytes, limits.max_wire_bytes, "query wire")
                    .map_err(|error| error.into_pyerr(py))?,
            );
        }
        let control = Arc::clone(&self.control);
        let result = control.run(|owned| {
            py.detach(|| {
                control.cancellation.poll()?;
                let queries = wires
                    .into_iter()
                    .map(|wire| decode_session_query(wire, &limits))
                    .collect::<NativeResult<Vec<_>>>()?;
                let started = Instant::now();
                let results = owned
                    .scheduler
                    .check_many(&queries, control.cancellation.as_ref())?;
                control.cancellation.poll()?;
                let elapsed = started.elapsed();
                let encoded = results
                    .into_iter()
                    .map(|result| check_wire_result(result, elapsed))
                    .collect::<Vec<_>>();
                encode_check_many(&encoded)
            })
        });
        result.map_err(|error| error.into_pyerr(py))
    }

    fn classify_classes(&self, py: Python<'_>) -> PyResult<Vec<u8>> {
        self.classify(py, ClassificationDomain::Classes)
    }

    fn classify_object_properties(&self, py: Python<'_>) -> PyResult<Vec<u8>> {
        self.classify(py, ClassificationDomain::ObjectProperties)
    }

    fn classify_data_properties(&self, py: Python<'_>) -> PyResult<Vec<u8>> {
        self.classify(py, ClassificationDomain::DataProperties)
    }

    fn realize(&self, py: Python<'_>) -> PyResult<Vec<u8>> {
        let control = Arc::clone(&self.control);
        let result = control.run(|owned| {
            py.detach(|| {
                let realization = realization_bridge::realize_ontology(
                    &owned.ontology,
                    &owned.config,
                    &owned.scheduler,
                    &mut owned.classification,
                    &mut owned.realization,
                    &control.cancellation,
                )?;
                control.cancellation.poll()?;
                encode_realization_ids(realization.as_ref())
            })
        });
        result.map_err(|error| error.into_pyerr(py))
    }

    fn apply_delta(&self, py: Python<'_>, delta: &Bound<'_, PyBytes>) -> PyResult<Vec<u8>> {
        let limits = DecodeLimits::default();
        let wire = copy_capped_bytes(delta, limits.max_wire_bytes, "delta wire")
            .map_err(|error| error.into_pyerr(py))?;
        let control = Arc::clone(&self.control);
        let result = control.run(|owned| {
            py.detach(|| {
                control.cancellation.poll()?;
                let delta = decode_delta(wire, &limits).map_err(map_input_wire_error)?;
                delta
                    .validate_revision(&owned.ontology)
                    .map_err(map_input_wire_error)?;
                control.cancellation.poll()?;
                encode_delta(delta_wire_outcome(&delta))
            })
        });
        result.map_err(|error| error.into_pyerr(py))
    }

    fn reset_query_state(&self, py: Python<'_>) -> PyResult<()> {
        self.control
            .run(|owned| owned.scheduler.reset_query_state())
            .map_err(|error| error.into_pyerr(py))
    }

    fn drain_events(&self, py: Python<'_>) -> PyResult<Vec<u8>> {
        self.control
            .run(|owned| encode_events(&owned.scheduler.drain_events()?))
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
    fn classify(&self, py: Python<'_>, domain: ClassificationDomain) -> PyResult<Vec<u8>> {
        let control = Arc::clone(&self.control);
        let result = control.run(|owned| {
            py.detach(|| {
                let hierarchy = classification_bridge::classify_domain(
                    &owned.ontology,
                    &owned.config,
                    &owned.scheduler,
                    &mut owned.classification,
                    &control.cancellation,
                    domain,
                )?;
                control.cancellation.poll()?;
                encode_hierarchy(hierarchy.as_ref())
            })
        });
        result.map_err(|error| error.into_pyerr(py))
    }
}

fn borrowed_py_bytes<'a, 'py>(
    buffer: &'a Bound<'py, PyAny>,
    name: &str,
) -> NativeResult<BorrowedPyBytes<'a, 'py>> {
    let invalid = |message: &str| {
        NativeError::new(
            ErrorKind::Wire,
            "NATIVE_ENCODED_VIEW_INVALID",
            format!("encoded buffer {name} {message}"),
        )
    };
    if !buffer.is_exact_instance_of::<PyMemoryView>() {
        return Err(invalid("is not an exact memoryview"));
    }
    let readonly = buffer
        .getattr("readonly")
        .and_then(|value| value.extract::<bool>())
        .map_err(|_| invalid("has invalid readonly metadata"))?;
    if !readonly {
        return Err(NativeError::new(
            ErrorKind::Wire,
            "NATIVE_ENCODED_VIEW_INVALID",
            format!("encoded buffer {name} is writable"),
        ));
    }
    let dimensions = buffer
        .getattr("ndim")
        .and_then(|value| value.extract::<usize>())
        .map_err(|_| invalid("has invalid dimensional metadata"))?;
    let item_size = buffer
        .getattr("itemsize")
        .and_then(|value| value.extract::<usize>())
        .map_err(|_| invalid("has invalid item-size metadata"))?;
    let contiguous = buffer
        .getattr("c_contiguous")
        .and_then(|value| value.extract::<bool>())
        .map_err(|_| invalid("has invalid contiguity metadata"))?;
    let format = buffer
        .getattr("format")
        .and_then(|value| value.extract::<String>())
        .map_err(|_| invalid("has invalid format metadata"))?;
    if dimensions != 1 || item_size != 1 || !contiguous || format != "B" {
        return Err(invalid(
            "is not a contiguous one-dimensional unsigned-byte memoryview",
        ));
    }
    let len = buffer
        .getattr("nbytes")
        .and_then(|value| value.extract::<usize>())
        .map_err(|_| invalid("has invalid byte-length metadata"))?;
    if buffer.len().map_err(|_| invalid("has invalid length"))? != len {
        return Err(invalid("has inconsistent byte-length metadata"));
    }
    Ok(BorrowedPyBytes { view: buffer, len })
}

fn borrowed_py_buffer_lease<'py>(
    buffer: Bound<'py, PyAny>,
    name: &str,
) -> NativeResult<BorrowedPyBufferLease<'py>> {
    let len = borrowed_py_bytes(&buffer, name)?.len;
    Ok(BorrowedPyBufferLease { view: buffer, len })
}

fn tuple_buffer_lease<'py>(
    record: &Bound<'py, PyTuple>,
    index: usize,
    name: &'static str,
) -> NativeResult<BorrowedPyBufferLease<'py>> {
    borrowed_py_buffer_lease(tuple_item(record, index, name)?, name)
}

fn prepare_borrowed_encoded_slices<'py>(
    slices: &Bound<'py, PyAny>,
) -> NativeResult<Vec<BorrowedEncodedSliceLease<'py>>> {
    if !slices.is_exact_instance_of::<PyTuple>() {
        return Err(encoded_slice_invalid(
            "encoded slice program is not an exact tuple",
        ));
    }
    let slices = slices
        .cast::<PyTuple>()
        .map_err(|_| encoded_slice_invalid("encoded slice program changed type"))?;
    let max_slices = encoded::named_classes::NamedClassPhaseLimits::default().max_slices;
    if slices.is_empty() {
        return Err(encoded_slice_invalid(
            "encoded slice program requires at least one slice",
        ));
    }
    if slices.len() > max_slices {
        return Err(encoded_validation_error(
            encoded::EncodedValidationError::resource(
                "encoded slice program exceeds its slice limit",
            ),
        ));
    }
    let mut prepared = Vec::new();
    prepared.try_reserve_exact(slices.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "encoded slice lease allocation failed",
        ))
    })?;
    for slice_index in 0..slices.len() {
        let record = tuple_item(slices, slice_index, "record")?;
        if !record.is_exact_instance_of::<PyTuple>() {
            return Err(encoded_slice_invalid(
                "encoded slice record is not an exact tuple",
            ));
        }
        let record = record
            .cast::<PyTuple>()
            .map_err(|_| encoded_slice_invalid("encoded slice record changed type"))?;
        if record.len() != ENCODED_SLICE_RECORD_LEN {
            return Err(encoded_slice_invalid(
                "encoded slice record has the wrong field count",
            ));
        }
        let context_bytes = validate_encoded_slice_context(record)?;
        let posting_mode = tuple_item(record, 0, "posting mode")?;
        if !posting_mode.is_exact_instance_of::<PyInt>() {
            return Err(encoded_slice_invalid(
                "encoded slice posting mode is not an exact integer",
            ));
        }
        let posting_mode = posting_mode
            .extract::<u8>()
            .map_err(|_| encoded_slice_invalid("encoded slice posting mode is outside u8"))?;
        let scope_values = tuple_item(record, 3, "anonymous scope maps")?;
        let scope_values = scope_values.cast::<PyTuple>().map_err(|_| {
            encoded_slice_invalid("encoded slice anonymous scope maps changed type")
        })?;
        let mut scope_maps = Vec::new();
        scope_maps
            .try_reserve_exact(scope_values.len())
            .map_err(|_| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded anonymous-scope lease allocation failed",
                ))
            })?;
        for index in 0..scope_values.len() {
            scope_maps.push(borrowed_py_buffer_lease(
                tuple_item(scope_values, index, "anonymous scope map")?,
                "anonymous scope map",
            )?);
        }
        prepared.push(BorrowedEncodedSliceLease {
            posting_mode,
            postings: tuple_buffer_lease(record, 1, "root postings")?,
            context_bytes,
            scope_maps,
            root_kinds: tuple_buffer_lease(record, 4, "root_kinds")?,
            root_ids: tuple_buffer_lease(record, 5, "root_ids")?,
            node_tags: tuple_buffer_lease(record, 6, "node_tags")?,
            node_field_offsets: tuple_buffer_lease(record, 7, "node_field_offsets")?,
            field_kinds: tuple_buffer_lease(record, 8, "field_kinds")?,
            field_values: tuple_buffer_lease(record, 9, "field_values")?,
            field_lengths: tuple_buffer_lease(record, 10, "field_lengths")?,
            item_kinds: tuple_buffer_lease(record, 11, "item_kinds")?,
            item_values: tuple_buffer_lease(record, 12, "item_values")?,
            item_lengths: tuple_buffer_lease(record, 13, "item_lengths")?,
            scalar_bytes: tuple_buffer_lease(record, 14, "scalar_bytes")?,
        });
    }
    Ok(prepared)
}

fn exact_pybytes_owner<'py>(
    buffer: &BorrowedPyBufferLease<'py>,
) -> NativeResult<Option<Bound<'py, PyBytes>>> {
    let owner = buffer
        .view
        .getattr("obj")
        .map_err(|_| encoded_slice_invalid("encoded memoryview owner is unreadable"))?;
    if !owner.is_exact_instance_of::<PyBytes>() {
        return Ok(None);
    }
    owner
        .cast_into::<PyBytes>()
        .map(Some)
        .map_err(|_| encoded_slice_invalid("encoded memoryview bytes owner changed type"))
}

fn memoryview_matches_pybytes_range(
    buffer: &BorrowedPyBufferLease<'_>,
    owner: &Bound<'_, PyBytes>,
    start: usize,
    end: usize,
) -> NativeResult<bool> {
    let start = isize::try_from(start)
        .map_err(|_| encoded_slice_invalid("encoded retained range start exceeds isize"))?;
    let end = isize::try_from(end)
        .map_err(|_| encoded_slice_invalid("encoded retained range end exceeds isize"))?;
    let owner_view = PyMemoryView::from(owner.as_any())
        .map_err(|_| encoded_slice_invalid("encoded bytes owner cannot provide a memoryview"))?;
    let expected = owner_view
        .get_item(PySlice::new(owner.py(), start, end, 1))
        .map_err(|_| encoded_slice_invalid("encoded retained range is unreadable"))?;
    buffer
        .view
        .eq(expected)
        .map_err(|_| encoded_slice_invalid("encoded retained range comparison failed"))
}

fn retain_individual_pybytes_range<'py>(
    buffer: &BorrowedPyBufferLease<'py>,
) -> NativeResult<Option<RetainedPyByteRange<'py>>> {
    let Some(owner) = exact_pybytes_owner(buffer)? else {
        return Ok(None);
    };
    if owner.as_bytes().len() != buffer.len
        || !memoryview_matches_pybytes_range(buffer, &owner, 0, buffer.len)?
    {
        return Ok(None);
    }
    Ok(Some(RetainedPyByteRange {
        owner,
        start: 0,
        end: buffer.len,
    }))
}

fn retain_encoded_column_ranges<'py>(
    buffers: [&BorrowedPyBufferLease<'py>; 11],
) -> NativeResult<Option<[RetainedPyByteRange<'py>; 11]>> {
    let mut owners = Vec::new();
    owners.try_reserve_exact(buffers.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "encoded retained-owner allocation failed",
        ))
    })?;
    for buffer in buffers {
        let Some(owner) = exact_pybytes_owner(buffer)? else {
            return Ok(None);
        };
        owners.push(owner);
    }

    if owners
        .iter()
        .zip(buffers)
        .all(|(owner, buffer)| owner.as_bytes().len() == buffer.len)
    {
        let mut ranges = Vec::new();
        ranges.try_reserve_exact(buffers.len()).map_err(|_| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded retained-range allocation failed",
            ))
        })?;
        for (owner, buffer) in owners.into_iter().zip(buffers) {
            if !memoryview_matches_pybytes_range(buffer, &owner, 0, buffer.len)? {
                return Ok(None);
            }
            ranges.push(RetainedPyByteRange {
                owner,
                start: 0,
                end: buffer.len,
            });
        }
        return ranges
            .try_into()
            .map(Some)
            .map_err(|_| NativeError::invariant("encoded retained column count changed"));
    }

    let first = &owners[0];
    if !owners.iter().all(|owner| owner.as_any().is(first.as_any())) {
        return Ok(None);
    }
    let total = buffers.iter().try_fold(0_usize, |sum, buffer| {
        sum.checked_add(buffer.len)
            .ok_or_else(|| encoded_slice_invalid("encoded retained column bytes overflowed"))
    })?;
    if first.as_bytes().len() != total {
        return Ok(None);
    }
    let mut ranges = Vec::new();
    ranges.try_reserve_exact(buffers.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "encoded retained-range allocation failed",
        ))
    })?;
    let mut start = 0_usize;
    for (owner, buffer) in owners.into_iter().zip(buffers) {
        let end = start
            .checked_add(buffer.len)
            .ok_or_else(|| encoded_slice_invalid("encoded retained range overflowed"))?;
        if !memoryview_matches_pybytes_range(buffer, &owner, start, end)? {
            return Ok(None);
        }
        ranges.push(RetainedPyByteRange { owner, start, end });
        start = end;
    }
    ranges
        .try_into()
        .map(Some)
        .map_err(|_| NativeError::invariant("encoded retained column count changed"))
}

fn retain_encoded_slice_leases<'py>(
    slices: &[BorrowedEncodedSliceLease<'py>],
) -> NativeResult<Option<Vec<RetainedEncodedSliceLease<'py>>>> {
    let mut retained = Vec::new();
    retained.try_reserve_exact(slices.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "encoded retained-slice allocation failed",
        ))
    })?;
    for slice in slices {
        let Some(postings) = retain_individual_pybytes_range(&slice.postings)? else {
            return Ok(None);
        };
        let mut scope_maps = Vec::new();
        scope_maps
            .try_reserve_exact(slice.scope_maps.len())
            .map_err(|_| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded retained anonymous-scope allocation failed",
                ))
            })?;
        for scope_map in &slice.scope_maps {
            let Some(scope_map) = retain_individual_pybytes_range(scope_map)? else {
                return Ok(None);
            };
            scope_maps.push(scope_map);
        }
        let Some(
            [root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes],
        ) = retain_encoded_column_ranges([
            &slice.root_kinds,
            &slice.root_ids,
            &slice.node_tags,
            &slice.node_field_offsets,
            &slice.field_kinds,
            &slice.field_values,
            &slice.field_lengths,
            &slice.item_kinds,
            &slice.item_values,
            &slice.item_lengths,
            &slice.scalar_bytes,
        ])?
        else {
            return Ok(None);
        };
        retained.push(RetainedEncodedSliceLease {
            posting_mode: slice.posting_mode,
            postings,
            context_bytes: slice.context_bytes,
            scope_maps,
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        });
    }
    Ok(Some(retained))
}

fn borrowed_encoded_slice_inputs<'a, 'py>(
    slices: &'a [BorrowedEncodedSliceLease<'py>],
) -> NativeResult<Vec<EncodedSliceInput<BorrowedPyBytes<'a, 'py>>>> {
    let mut inputs = Vec::new();
    inputs.try_reserve_exact(slices.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "encoded borrowed-input allocation failed",
        ))
    })?;
    for slice in slices {
        let mut scope_maps = Vec::new();
        scope_maps
            .try_reserve_exact(slice.scope_maps.len())
            .map_err(|_| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded borrowed scope-input allocation failed",
                ))
            })?;
        scope_maps.extend(slice.scope_maps.iter().map(BorrowedPyBufferLease::source));
        inputs.push(EncodedSliceInput {
            posting_mode: slice.posting_mode,
            postings: slice.postings.source(),
            context_bytes: slice.context_bytes,
            scope_maps,
            columns: encoded::EncodedColumns {
                root_kinds: slice.root_kinds.source(),
                root_ids: slice.root_ids.source(),
                node_tags: slice.node_tags.source(),
                node_field_offsets: slice.node_field_offsets.source(),
                field_kinds: slice.field_kinds.source(),
                field_values: slice.field_values.source(),
                field_lengths: slice.field_lengths.source(),
                item_kinds: slice.item_kinds.source(),
                item_values: slice.item_values.source(),
                item_lengths: slice.item_lengths.source(),
                scalar_bytes: slice.scalar_bytes.source(),
            },
        });
    }
    Ok(inputs)
}

fn retained_encoded_slice_inputs<'a>(
    slices: &'a [RetainedEncodedSliceLease<'_>],
) -> NativeResult<Vec<EncodedSliceInput<&'a [u8]>>> {
    let mut inputs = Vec::new();
    inputs.try_reserve_exact(slices.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "encoded retained-input allocation failed",
        ))
    })?;
    for slice in slices {
        let mut scope_maps = Vec::new();
        scope_maps
            .try_reserve_exact(slice.scope_maps.len())
            .map_err(|_| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded retained scope-input allocation failed",
                ))
            })?;
        scope_maps.extend(slice.scope_maps.iter().map(RetainedPyByteRange::source));
        inputs.push(EncodedSliceInput {
            posting_mode: slice.posting_mode,
            postings: slice.postings.source(),
            context_bytes: slice.context_bytes,
            scope_maps,
            columns: encoded::EncodedColumns {
                root_kinds: slice.root_kinds.source(),
                root_ids: slice.root_ids.source(),
                node_tags: slice.node_tags.source(),
                node_field_offsets: slice.node_field_offsets.source(),
                field_kinds: slice.field_kinds.source(),
                field_values: slice.field_values.source(),
                field_lengths: slice.field_lengths.source(),
                item_kinds: slice.item_kinds.source(),
                item_values: slice.item_values.source(),
                item_lengths: slice.item_lengths.source(),
                scalar_bytes: slice.scalar_bytes.source(),
            },
        });
    }
    Ok(inputs)
}

fn encoded_logical_fingerprint(value: &Bound<'_, PyAny>) -> NativeResult<[u8; 32]> {
    let borrowed = borrowed_py_bytes(value, "logical fingerprint")?;
    if borrowed.len != 32 {
        return Err(encoded_slice_invalid(
            "encoded logical fingerprint must contain exactly 32 bytes",
        ));
    }
    let mut fingerprint = [0_u8; 32];
    for (index, byte) in fingerprint.iter_mut().enumerate() {
        *byte = encoded::ByteSource::byte(borrowed, index)
            .ok_or_else(|| encoded_slice_invalid("encoded logical fingerprint byte disappeared"))?;
    }
    Ok(fingerprint)
}

fn decode_deferred_fingerprint_request(
    value: Option<&Bound<'_, PyAny>>,
) -> NativeResult<Option<DeferredFingerprintRequest>> {
    let Some(value) = value else {
        return Ok(None);
    };
    if !value.is_exact_instance_of::<PyTuple>() {
        return Err(encoded_slice_invalid(
            "deferred fingerprint request is not an exact tuple",
        ));
    }
    let record = value
        .cast::<PyTuple>()
        .map_err(|_| encoded_slice_invalid("deferred fingerprint request changed type"))?;
    if record.len() != 5 {
        return Err(encoded_slice_invalid(
            "deferred fingerprint request has the wrong field count",
        ));
    }
    let version = tuple_item(record, 0, "deferred fingerprint version")?;
    if !version.is_exact_instance_of::<PyInt>()
        || version
            .extract::<u8>()
            .map_err(|_| encoded_slice_invalid("deferred fingerprint version is outside u8"))?
            != DEFERRED_FINGERPRINT_VERSION
    {
        return Err(encoded_slice_invalid(
            "deferred fingerprint request version is unsupported",
        ));
    }
    let kind = tuple_item(record, 1, "deferred fingerprint context kind")?;
    if !kind.is_exact_instance_of::<PyString>() {
        return Err(encoded_slice_invalid(
            "deferred fingerprint context kind is not an exact string",
        ));
    }
    let kind = kind
        .cast::<PyString>()
        .map_err(|_| encoded_slice_invalid("deferred fingerprint context kind changed type"))?
        .to_str()
        .map_err(|_| encoded_slice_invalid("deferred fingerprint context kind is not UTF-8"))?;
    let kind = match kind {
        "overlay" => encoded::fingerprints::StructuralContextKind::Overlay,
        "composite" => encoded::fingerprints::StructuralContextKind::Composite,
        _ => {
            return Err(encoded_slice_invalid(
                "deferred fingerprint context kind is unsupported",
            ));
        }
    };
    let structural_mode = tuple_item(record, 2, "deferred structural fingerprint mode")?;
    if !structural_mode.is_exact_instance_of::<PyString>() {
        return Err(encoded_slice_invalid(
            "deferred structural fingerprint mode is not an exact string",
        ));
    }
    let structural_mode = structural_mode
        .cast::<PyString>()
        .map_err(|_| encoded_slice_invalid("deferred structural fingerprint mode changed type"))?
        .to_str()
        .map_err(|_| encoded_slice_invalid("deferred structural fingerprint mode is not UTF-8"))?;
    let structural_mode = match structural_mode {
        "effective" => encoded::fingerprints::StructuralFingerprintMode::Effective,
        "overlay-anchor-alias" => {
            encoded::fingerprints::StructuralFingerprintMode::OverlayAnchorAlias
        }
        _ => {
            return Err(encoded_slice_invalid(
                "deferred structural fingerprint mode is unsupported",
            ));
        }
    };
    if structural_mode == encoded::fingerprints::StructuralFingerprintMode::OverlayAnchorAlias
        && kind != encoded::fingerprints::StructuralContextKind::Overlay
    {
        return Err(encoded_slice_invalid(
            "overlay anchor structural alias requires an overlay context",
        ));
    }
    let context = tuple_item(record, 3, "deferred fingerprint context bytes")?;
    if !context.is_exact_instance_of::<PyBytes>() {
        return Err(encoded_slice_invalid(
            "deferred fingerprint context is not exact bytes",
        ));
    }
    let context = context
        .cast::<PyBytes>()
        .map_err(|_| encoded_slice_invalid("deferred fingerprint context changed type"))?;
    let context = copy_capped_bytes(
        context,
        MAX_DEFERRED_FINGERPRINT_CONTEXT_BYTES,
        "deferred fingerprint context",
    )?;
    let context = encoded::fingerprints::StructuralContextEvidence::new(kind, context)
        .map_err(encoded_validation_error)?;
    let template = tuple_item(record, 4, "deferred compiler-cache template")?;
    if !template.is_exact_instance_of::<PyBytes>() {
        return Err(encoded_slice_invalid(
            "deferred compiler-cache template is not exact bytes",
        ));
    }
    let template = template
        .cast::<PyBytes>()
        .map_err(|_| encoded_slice_invalid("deferred compiler-cache template changed type"))?;
    let compiler_cache_template = copy_capped_bytes(
        template,
        MAX_DEFERRED_CACHE_TEMPLATE_BYTES,
        "deferred compiler-cache template",
    )?;
    Ok(Some(DeferredFingerprintRequest {
        context,
        structural_mode,
        compiler_cache_template,
    }))
}

fn encoded_validation_error(error: encoded::EncodedValidationError) -> NativeError {
    let kind = match error.code {
        "NATIVE_ENCODED_VIEW_INVALID" => ErrorKind::Wire,
        "NATIVE_ENCODED_RESOURCE_LIMIT" => ErrorKind::Resource,
        _ => ErrorKind::Invariant,
    };
    let mut mapped = NativeError::new(kind, error.code, error.message);
    for (key, value) in error.context {
        mapped = mapped.with_context(key, value);
    }
    if kind == ErrorKind::Resource && !mapped.context.contains_key("limit") {
        mapped = mapped.with_context("limit", "encoded-structural-validation");
    }
    mapped
}

fn encoded_profile_error(error: encoded::profile::ProfilePhaseError<NativeError>) -> NativeError {
    match error {
        encoded::profile::ProfilePhaseError::Encoded(error) => encoded_validation_error(error),
        encoded::profile::ProfilePhaseError::Control(error) => error,
    }
}

fn encoded_symbol_error(error: encoded::symbols::SymbolPhaseError<NativeError>) -> NativeError {
    match error {
        encoded::symbols::SymbolPhaseError::Encoded(error) => encoded_validation_error(error),
        encoded::symbols::SymbolPhaseError::Control(error) => error,
    }
}

fn encoded_fingerprint_error(
    error: encoded::fingerprints::FingerprintPhaseError<NativeError>,
) -> NativeError {
    match error {
        encoded::fingerprints::FingerprintPhaseError::Encoded(error) => {
            encoded_validation_error(error)
        }
        encoded::fingerprints::FingerprintPhaseError::Control(error) => error,
    }
}

fn encoded_permanent_error(
    error: encoded::permanent_program::PermanentProgramError<NativeError>,
) -> NativeError {
    match error {
        encoded::permanent_program::PermanentProgramError::Encoded(error) => {
            encoded_validation_error(error)
        }
        encoded::permanent_program::PermanentProgramError::Control(error) => error,
    }
}

fn encoded_profile_unsupported_datatype_policy(
    value: &str,
) -> NativeResult<encoded::profile::ProfileUnsupportedDatatypePolicy> {
    match value {
        "error" => Ok(encoded::profile::ProfileUnsupportedDatatypePolicy::Error),
        "ignore_with_warning" => {
            Ok(encoded::profile::ProfileUnsupportedDatatypePolicy::IgnoreWithWarning)
        }
        _ => Err(encoded_slice_invalid(
            "encoded profile unsupported-datatype policy is not recognized",
        )),
    }
}

const fn encoded_profile_policy_from_config(
    value: input_wire::UnsupportedDatatypeChoice,
) -> encoded::profile::ProfileUnsupportedDatatypePolicy {
    match value {
        input_wire::UnsupportedDatatypeChoice::Error => {
            encoded::profile::ProfileUnsupportedDatatypePolicy::Error
        }
        input_wire::UnsupportedDatatypeChoice::IgnoreWithWarning => {
            encoded::profile::ProfileUnsupportedDatatypePolicy::IgnoreWithWarning
        }
    }
}

fn ensure_encoded_profile_conforms(
    conforms: bool,
    issues: &[encoded::profile::ProfileIssue],
) -> NativeResult<()> {
    let error_count = issues
        .iter()
        .filter(|issue| issue.severity == "error")
        .count();
    if conforms {
        if error_count == 0 {
            return Ok(());
        }
        return Err(NativeError::invariant(
            "conforming encoded profile contains error diagnostics",
        ));
    }
    if error_count == 0 {
        return Err(NativeError::invariant(
            "nonconforming encoded profile contains no error diagnostics",
        ));
    }
    let mut rule_ids = issues
        .iter()
        .filter(|issue| issue.severity == "error")
        .map(|issue| issue.rule_id)
        .collect::<Vec<_>>();
    rule_ids.sort_unstable();
    rule_ids.dedup();
    let codes = rule_ids.join(", ");
    Err(NativeError::new(
        ErrorKind::Profile,
        "OWL2DL_PROFILE_VIOLATION",
        format!("ontology is outside OWL 2 DL: {codes}"),
    )
    .with_context("issue_count", error_count.to_string())
    .with_context("rule_ids", codes))
}

#[allow(clippy::too_many_arguments)]
fn borrowed_encoded_columns<'a, 'py>(
    root_kinds: &'a Bound<'py, PyAny>,
    root_ids: &'a Bound<'py, PyAny>,
    node_tags: &'a Bound<'py, PyAny>,
    node_field_offsets: &'a Bound<'py, PyAny>,
    field_kinds: &'a Bound<'py, PyAny>,
    field_values: &'a Bound<'py, PyAny>,
    field_lengths: &'a Bound<'py, PyAny>,
    item_kinds: &'a Bound<'py, PyAny>,
    item_values: &'a Bound<'py, PyAny>,
    item_lengths: &'a Bound<'py, PyAny>,
    scalar_bytes: &'a Bound<'py, PyAny>,
) -> NativeResult<encoded::EncodedColumns<BorrowedPyBytes<'a, 'py>>> {
    Ok(encoded::EncodedColumns {
        root_kinds: borrowed_py_bytes(root_kinds, "root_kinds")?,
        root_ids: borrowed_py_bytes(root_ids, "root_ids")?,
        node_tags: borrowed_py_bytes(node_tags, "node_tags")?,
        node_field_offsets: borrowed_py_bytes(node_field_offsets, "node_field_offsets")?,
        field_kinds: borrowed_py_bytes(field_kinds, "field_kinds")?,
        field_values: borrowed_py_bytes(field_values, "field_values")?,
        field_lengths: borrowed_py_bytes(field_lengths, "field_lengths")?,
        item_kinds: borrowed_py_bytes(item_kinds, "item_kinds")?,
        item_values: borrowed_py_bytes(item_values, "item_values")?,
        item_lengths: borrowed_py_bytes(item_lengths, "item_lengths")?,
        scalar_bytes: borrowed_py_bytes(scalar_bytes, "scalar_bytes")?,
    })
}

#[pyfunction(name = "_validate_encoded_columns_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn validate_encoded_columns_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<()> {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let symbols = encoded::symbols::compile_symbol_phase(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let object_roles = encoded::object_roles::compile_object_role_phase(
            &symbols,
            encoded::object_roles::ObjectRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let data_roles = encoded::data_roles::compile_data_role_phase(
            &symbols,
            encoded::data_roles::DataRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let data_inclusions = encoded::data_inclusions::compile_data_inclusion_phase(
            &model,
            &symbols,
            &data_roles,
            encoded::data_inclusions::DataInclusionPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        encoded::data_role_hierarchy::compile_data_role_hierarchy_phase(
            &data_roles,
            &data_inclusions,
            encoded::data_role_hierarchy::DataRoleHierarchyLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let simple_roles = encoded::simple_roles::compile_simple_role_phase(
            &model,
            &symbols,
            &object_roles,
            encoded::simple_roles::SimpleRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let complex_roles = encoded::complex_roles::compile_complex_role_phase(
            &model,
            &symbols,
            &object_roles,
            encoded::complex_roles::ComplexRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let role_characteristics =
            encoded::role_characteristics::compile_role_characteristic_phase(
                &model,
                &symbols,
                &object_roles,
                &data_roles,
                encoded::role_characteristics::RoleCharacteristicPhaseLimits::default(),
            )
            .map_err(encoded_validation_error)?;
        let hierarchy = encoded::object_role_hierarchy::compile_object_role_hierarchy_phase(
            &object_roles,
            &simple_roles,
            encoded::object_role_hierarchy::ObjectRoleHierarchyLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let role_semantics = encoded::role_semantics::compile_role_semantics_phase(
            &object_roles,
            &simple_roles,
            &complex_roles,
            &hierarchy,
            encoded::role_semantics::RoleSemanticsPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let role_automata = encoded::role_automata::compile_role_automata_phase(
            &object_roles,
            &simple_roles,
            &complex_roles,
            &hierarchy,
            &role_semantics,
            encoded::role_automata::RoleAutomataPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let role_model = encoded::role_model::compile_role_model_phase(
            &object_roles,
            &data_roles,
            &simple_roles,
            &data_inclusions,
            &complex_roles,
            &hierarchy,
            &role_semantics,
            &role_automata,
            encoded::role_model::RoleModelPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        encoded::role_clauses::compile_role_clause_phase(
            &object_roles,
            &data_roles,
            &simple_roles,
            &data_inclusions,
            &complex_roles,
            &role_characteristics,
            &role_model,
            encoded::role_clauses::RoleClausePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        encoded::named_classes::compile_named_class_phase_with_role_domains_scoped(
            &model,
            &symbols,
            &object_roles,
            &data_roles,
            &[],
            encoded::named_classes::NamedClassPhaseLimits::default(),
        )
        .map(drop)
        .map_err(encoded_validation_error)
    }));
    match result {
        Ok(value) => value.map_err(|error| error.into_pyerr(py)),
        Err(_) => Err(NativeError::new(
            ErrorKind::Poisoned,
            "NATIVE_PANIC",
            "native encoded-column validation panic was contained",
        )
        .into_pyerr(py)),
    }
}

#[pyfunction(name = "_validate_encoded_selection_v1")]
#[pyo3(signature = (*, posting_mode, postings, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn validate_encoded_selection_v1(
    py: Python<'_>,
    posting_mode: u8,
    postings: &Bound<'_, PyAny>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<()> {
    contain_encoded_selection(py, || {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let postings = borrowed_py_bytes(postings, "root postings")?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let symbols = encoded::symbols::compile_symbol_phase_selected(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
            posting_mode,
            postings,
        )
        .map_err(encoded_validation_error)?;
        let object_roles = encoded::object_roles::compile_object_role_phase(
            &symbols,
            encoded::object_roles::ObjectRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let data_roles = encoded::data_roles::compile_data_role_phase(
            &symbols,
            encoded::data_roles::DataRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let data_inclusions = encoded::data_inclusions::compile_data_inclusion_phase(
            &model,
            &symbols,
            &data_roles,
            encoded::data_inclusions::DataInclusionPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        encoded::data_role_hierarchy::compile_data_role_hierarchy_phase(
            &data_roles,
            &data_inclusions,
            encoded::data_role_hierarchy::DataRoleHierarchyLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let simple_roles = encoded::simple_roles::compile_simple_role_phase(
            &model,
            &symbols,
            &object_roles,
            encoded::simple_roles::SimpleRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let complex_roles = encoded::complex_roles::compile_complex_role_phase(
            &model,
            &symbols,
            &object_roles,
            encoded::complex_roles::ComplexRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let role_characteristics =
            encoded::role_characteristics::compile_role_characteristic_phase(
                &model,
                &symbols,
                &object_roles,
                &data_roles,
                encoded::role_characteristics::RoleCharacteristicPhaseLimits::default(),
            )
            .map_err(encoded_validation_error)?;
        let hierarchy = encoded::object_role_hierarchy::compile_object_role_hierarchy_phase(
            &object_roles,
            &simple_roles,
            encoded::object_role_hierarchy::ObjectRoleHierarchyLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let role_semantics = encoded::role_semantics::compile_role_semantics_phase(
            &object_roles,
            &simple_roles,
            &complex_roles,
            &hierarchy,
            encoded::role_semantics::RoleSemanticsPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let role_automata = encoded::role_automata::compile_role_automata_phase(
            &object_roles,
            &simple_roles,
            &complex_roles,
            &hierarchy,
            &role_semantics,
            encoded::role_automata::RoleAutomataPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let role_model = encoded::role_model::compile_role_model_phase(
            &object_roles,
            &data_roles,
            &simple_roles,
            &data_inclusions,
            &complex_roles,
            &hierarchy,
            &role_semantics,
            &role_automata,
            encoded::role_model::RoleModelPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        encoded::role_clauses::compile_role_clause_phase(
            &object_roles,
            &data_roles,
            &simple_roles,
            &data_inclusions,
            &complex_roles,
            &role_characteristics,
            &role_model,
            encoded::role_clauses::RoleClausePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        encoded::named_classes::compile_named_class_phase_with_role_domains_scoped(
            &model,
            &symbols,
            &object_roles,
            &data_roles,
            &[],
            encoded::named_classes::NamedClassPhaseLimits::default(),
        )
        .map(drop)
        .map_err(encoded_validation_error)
    })
}

const ENCODED_SLICE_RECORD_LEN: usize = 15;
const ENCODED_SLICE_CONTEXT_DEPTH: usize = 32;
const PROFILE_ONTOLOGY_IDENTITY_CONTEXT_VERSION: u16 = 1;
const PROFILE_ORIGIN_CONTEXT_VERSION: u16 = 1;

fn encoded_slice_invalid(message: impl Into<String>) -> NativeError {
    NativeError::new(ErrorKind::Wire, "NATIVE_ENCODED_VIEW_INVALID", message)
}

fn profile_context_text(
    value: &Bound<'_, PyAny>,
    name: &'static str,
    owned_bytes: &mut usize,
    limit: usize,
) -> NativeResult<Vec<u8>> {
    if !value.is_exact_instance_of::<PyString>() {
        return Err(encoded_slice_invalid(format!(
            "encoded profile ontology identity {name} is not an exact string"
        )));
    }
    let value = value
        .cast::<PyString>()
        .map_err(|_| encoded_slice_invalid("encoded profile ontology identity string changed"))?
        .to_str()
        .map_err(|_| {
            encoded_slice_invalid(format!(
                "encoded profile ontology identity {name} is not UTF-8"
            ))
        })?;
    if value.is_empty() {
        return Err(encoded_slice_invalid(format!(
            "encoded profile ontology identity {name} is empty"
        )));
    }
    *owned_bytes = owned_bytes.checked_add(value.len()).ok_or_else(|| {
        encoded_slice_invalid("encoded profile ontology identity byte count overflowed")
    })?;
    if *owned_bytes > limit {
        return Err(encoded_validation_error(
            encoded::EncodedValidationError::resource(
                "encoded profile ontology identity context exceeds its byte limit",
            ),
        ));
    }
    let mut owned = Vec::new();
    owned.try_reserve_exact(value.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "encoded profile ontology identity string allocation failed",
        ))
    })?;
    owned.extend_from_slice(value.as_bytes());
    Ok(owned)
}

fn profile_context_optional_iri(
    value: &Bound<'_, PyAny>,
    name: &'static str,
    owned_bytes: &mut usize,
    limit: usize,
) -> NativeResult<Option<Vec<u8>>> {
    if value.is_none() {
        Ok(None)
    } else {
        let iri = profile_context_text(value, name, owned_bytes, limit)?;
        let iri_text = std::str::from_utf8(&iri).map_err(|_| {
            encoded_slice_invalid(format!(
                "encoded profile ontology identity {name} is not UTF-8"
            ))
        })?;
        encoded::symbols::validate_iri(iri_text).map_err(|_| {
            encoded_slice_invalid(format!(
                "encoded profile ontology identity {name} violates the core model IRI contract"
            ))
        })?;
        Ok(Some(iri))
    }
}

fn decode_profile_ontology_identity_context(
    value: Option<&Bound<'_, PyAny>>,
    limits: encoded::profile::ProfilePhaseLimits,
    poll: &mut impl FnMut(&'static str) -> NativeResult<()>,
) -> NativeResult<Vec<encoded::profile::ProfileOntologyIdentifier>> {
    let Some(value) = value else {
        return Ok(Vec::new());
    };
    poll("profile-ontology-identity-context-preflight")?;
    if !value.is_exact_instance_of::<PyTuple>() {
        return Err(encoded_slice_invalid(
            "encoded profile ontology identity context is not an exact tuple",
        ));
    }
    let context = value.cast::<PyTuple>().map_err(|_| {
        encoded_slice_invalid("encoded profile ontology identity context changed type")
    })?;
    if context.len() != 2 {
        return Err(encoded_slice_invalid(
            "encoded profile ontology identity context has the wrong field count",
        ));
    }
    let version = tuple_item(context, 0, "ontology identity context version")?;
    if !version.is_exact_instance_of::<PyInt>() {
        return Err(encoded_slice_invalid(
            "encoded profile ontology identity context version is not an exact integer",
        ));
    }
    let version = version.extract::<u16>().map_err(|_| {
        encoded_slice_invalid("encoded profile ontology identity context version exceeds u16")
    })?;
    if version != PROFILE_ONTOLOGY_IDENTITY_CONTEXT_VERSION {
        return Err(encoded_slice_invalid(
            "encoded profile ontology identity context version is unsupported",
        ));
    }
    let documents = tuple_item(context, 1, "ontology identity documents")?;
    if !documents.is_exact_instance_of::<PyTuple>() {
        return Err(encoded_slice_invalid(
            "encoded profile ontology identity documents are not an exact tuple",
        ));
    }
    let documents = documents.cast::<PyTuple>().map_err(|_| {
        encoded_slice_invalid("encoded profile ontology identity documents changed type")
    })?;
    if documents.is_empty() {
        return Err(encoded_slice_invalid(
            "encoded profile ontology identity context has no documents",
        ));
    }
    if documents.len() > limits.max_ontology_documents {
        return Err(encoded_validation_error(
            encoded::EncodedValidationError::resource(
                "encoded profile ontology identity context exceeds its document limit",
            ),
        ));
    }
    let row_bytes = documents
        .len()
        .checked_mul(std::mem::size_of::<
            encoded::profile::ProfileOntologyIdentifier,
        >())
        .ok_or_else(|| {
            encoded_slice_invalid("encoded profile ontology identity row size overflowed")
        })?;
    if row_bytes > limits.max_owned_bytes {
        return Err(encoded_validation_error(
            encoded::EncodedValidationError::resource(
                "encoded profile ontology identity context exceeds its byte limit",
            ),
        ));
    }
    let mut identifiers = Vec::new();
    identifiers
        .try_reserve_exact(documents.len())
        .map_err(|_| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded profile ontology identity row allocation failed",
            ))
        })?;
    let mut owned_bytes = row_bytes;
    for index in 0..documents.len() {
        poll("profile-ontology-identity-context-document")?;
        let row = tuple_item(documents, index, "ontology identity document")?;
        if !row.is_exact_instance_of::<PyTuple>() {
            return Err(encoded_slice_invalid(
                "encoded profile ontology identity document is not an exact tuple",
            ));
        }
        let row = row.cast::<PyTuple>().map_err(|_| {
            encoded_slice_invalid("encoded profile ontology identity document changed type")
        })?;
        if row.len() != 3 {
            return Err(encoded_slice_invalid(
                "encoded profile ontology identity document has the wrong field count",
            ));
        }
        let document_key = profile_context_text(
            &tuple_item(row, 0, "ontology identity document key")?,
            "document key",
            &mut owned_bytes,
            limits.max_owned_bytes,
        )?;
        let ontology_iri = profile_context_optional_iri(
            &tuple_item(row, 1, "ontology identity ontology IRI")?,
            "ontology IRI",
            &mut owned_bytes,
            limits.max_owned_bytes,
        )?;
        let version_iri = profile_context_optional_iri(
            &tuple_item(row, 2, "ontology identity version IRI")?,
            "version IRI",
            &mut owned_bytes,
            limits.max_owned_bytes,
        )?;
        if ontology_iri.is_none() && version_iri.is_some() {
            return Err(encoded_slice_invalid(
                "encoded profile ontology identity version IRI has no ontology IRI",
            ));
        }
        identifiers.push(encoded::profile::ProfileOntologyIdentifier {
            document_key,
            ontology_iri,
            version_iri,
        });
    }
    if identifiers
        .windows(2)
        .any(|pair| pair[0].document_key >= pair[1].document_key)
    {
        return Err(encoded_slice_invalid(
            "encoded profile ontology identity documents are not ordered by unique document key",
        ));
    }
    poll("profile-ontology-identity-context-complete")?;
    Ok(identifiers)
}

fn decode_profile_origin_context(
    value: Option<&Bound<'_, PyAny>>,
    limits: encoded::profile::ProfilePhaseLimits,
    poll: &mut impl FnMut(&'static str) -> NativeResult<()>,
) -> NativeResult<Option<Vec<encoded::profile::ProfileOrigin>>> {
    let Some(value) = value else {
        return Ok(None);
    };
    poll("profile-origin-context-preflight")?;
    if !value.is_exact_instance_of::<PyTuple>() {
        return Err(encoded_slice_invalid(
            "encoded profile origin context is not an exact tuple",
        ));
    }
    let context = value
        .cast::<PyTuple>()
        .map_err(|_| encoded_slice_invalid("encoded profile origin context changed type"))?;
    if context.len() != 2 {
        return Err(encoded_slice_invalid(
            "encoded profile origin context has the wrong field count",
        ));
    }
    let version = tuple_item(context, 0, "profile origin context version")?;
    if !version.is_exact_instance_of::<PyInt>() {
        return Err(encoded_slice_invalid(
            "encoded profile origin context version is not an exact integer",
        ));
    }
    let version = version
        .extract::<u16>()
        .map_err(|_| encoded_slice_invalid("encoded profile origin context version exceeds u16"))?;
    if version != PROFILE_ORIGIN_CONTEXT_VERSION {
        return Err(encoded_slice_invalid(
            "encoded profile origin context version is unsupported",
        ));
    }
    let rows = tuple_item(context, 1, "profile origin rows")?;
    if !rows.is_exact_instance_of::<PyTuple>() {
        return Err(encoded_slice_invalid(
            "encoded profile origin rows are not an exact tuple",
        ));
    }
    let rows = rows
        .cast::<PyTuple>()
        .map_err(|_| encoded_slice_invalid("encoded profile origin rows changed type"))?;
    if rows.len() > limits.max_axioms {
        return Err(encoded_validation_error(
            encoded::EncodedValidationError::resource(
                "encoded profile origin context exceeds its row limit",
            ),
        ));
    }
    let mut owned_bytes = rows
        .len()
        .checked_mul(std::mem::size_of::<encoded::profile::ProfileOrigin>())
        .ok_or_else(|| encoded_slice_invalid("encoded profile origin row size overflowed"))?;
    if owned_bytes > limits.max_owned_bytes {
        return Err(encoded_validation_error(
            encoded::EncodedValidationError::resource(
                "encoded profile origin context exceeds its byte limit",
            ),
        ));
    }
    let mut origins = Vec::new();
    origins.try_reserve_exact(rows.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "encoded profile origin row allocation failed",
        ))
    })?;
    for index in 0..rows.len() {
        poll("profile-origin-context-row")?;
        let row = tuple_item(rows, index, "profile origin row")?;
        if !row.is_exact_instance_of::<PyTuple>() {
            return Err(encoded_slice_invalid(
                "encoded profile origin row is not an exact tuple",
            ));
        }
        let row = row
            .cast::<PyTuple>()
            .map_err(|_| encoded_slice_invalid("encoded profile origin row changed type"))?;
        if row.len() != 2 {
            return Err(encoded_slice_invalid(
                "encoded profile origin row has the wrong field count",
            ));
        }
        let provenance = tuple_item(row, 0, "profile origin provenance")?;
        if !provenance.is_exact_instance_of::<PyBytes>() {
            return Err(encoded_slice_invalid(
                "encoded profile origin provenance is not exact bytes",
            ));
        }
        let provenance = provenance
            .cast::<PyBytes>()
            .map_err(|_| encoded_slice_invalid("encoded profile origin provenance changed type"))?
            .as_bytes();
        let provenance_sha256: [u8; 32] = provenance.try_into().map_err(|_| {
            encoded_slice_invalid("encoded profile origin provenance is not bytes32")
        })?;
        let document_values = tuple_item(row, 1, "profile origin document keys")?;
        if !document_values.is_exact_instance_of::<PyTuple>() {
            return Err(encoded_slice_invalid(
                "encoded profile origin document keys are not an exact tuple",
            ));
        }
        let document_values = document_values.cast::<PyTuple>().map_err(|_| {
            encoded_slice_invalid("encoded profile origin document keys changed type")
        })?;
        if document_values.is_empty() {
            return Err(encoded_slice_invalid(
                "encoded profile origin row has no document keys",
            ));
        }
        owned_bytes = owned_bytes
            .checked_add(
                document_values
                    .len()
                    .checked_mul(std::mem::size_of::<String>())
                    .ok_or_else(|| {
                        encoded_slice_invalid("encoded profile origin document-key size overflowed")
                    })?,
            )
            .ok_or_else(|| encoded_slice_invalid("encoded profile origin ownership overflowed"))?;
        let mut document_keys = Vec::new();
        document_keys
            .try_reserve_exact(document_values.len())
            .map_err(|_| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded profile origin document-key allocation failed",
                ))
            })?;
        for document_index in 0..document_values.len() {
            poll("profile-origin-context-document")?;
            let document_key = tuple_item(
                document_values,
                document_index,
                "profile origin document key",
            )?;
            if !document_key.is_exact_instance_of::<PyString>() {
                return Err(encoded_slice_invalid(
                    "encoded profile origin document key is not an exact string",
                ));
            }
            let document_key = document_key
                .cast::<PyString>()
                .map_err(|_| {
                    encoded_slice_invalid("encoded profile origin document key changed type")
                })?
                .to_str()
                .map_err(|_| {
                    encoded_slice_invalid("encoded profile origin document key is not UTF-8")
                })?;
            if document_key.is_empty() {
                return Err(encoded_slice_invalid(
                    "encoded profile origin document key is empty",
                ));
            }
            owned_bytes = owned_bytes.checked_add(document_key.len()).ok_or_else(|| {
                encoded_slice_invalid("encoded profile origin byte count overflowed")
            })?;
            if owned_bytes > limits.max_owned_bytes {
                return Err(encoded_validation_error(
                    encoded::EncodedValidationError::resource(
                        "encoded profile origin context exceeds its byte limit",
                    ),
                ));
            }
            document_keys.push(document_key.to_owned());
        }
        if document_keys.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(encoded_slice_invalid(
                "encoded profile origin document keys are not sorted unique",
            ));
        }
        origins.push(encoded::profile::ProfileOrigin {
            root_digest_sha256: provenance_sha256,
            document_keys,
        });
    }
    if origins
        .windows(2)
        .any(|pair| pair[0].root_digest_sha256 >= pair[1].root_digest_sha256)
    {
        return Err(encoded_slice_invalid(
            "encoded profile origin rows are not sorted by unique provenance",
        ));
    }
    poll("profile-origin-context-complete")?;
    Ok(Some(origins))
}

fn tuple_item<'py>(
    value: &Bound<'py, PyTuple>,
    index: usize,
    name: &'static str,
) -> NativeResult<Bound<'py, PyAny>> {
    value
        .get_item(index)
        .map_err(|_| encoded_slice_invalid(format!("encoded slice {name} is unreadable")))
}

fn exact_encoded_role_id(value: &Bound<'_, PyAny>, name: &'static str) -> NativeResult<u32> {
    if !value.is_exact_instance_of::<PyInt>() {
        return Err(encoded_slice_invalid(format!(
            "encoded object-role {name} is not an exact integer"
        )));
    }
    value.extract::<u32>().map_err(|_| {
        encoded_slice_invalid(format!(
            "encoded object-role {name} is outside the nonnegative u32 domain"
        ))
    })
}

fn exact_encoded_role_word(value: &Bound<'_, PyAny>) -> NativeResult<Vec<u32>> {
    if !value.is_exact_instance_of::<PyTuple>() {
        return Err(encoded_slice_invalid(
            "encoded object-role word is not an exact tuple",
        ));
    }
    let word = value
        .cast::<PyTuple>()
        .map_err(|_| encoded_slice_invalid("encoded object-role word changed type"))?;
    let limits = encoded::role_automata::RoleAutomataPhaseLimits::default();
    if word.len() > limits.max_word_length {
        return Err(encoded_validation_error(
            encoded::EncodedValidationError::resource(
                "object-role acceptance word exceeds its length limit",
            ),
        ));
    }
    let mut result = Vec::new();
    result.try_reserve_exact(word.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "object-role acceptance word allocation failed",
        ))
    })?;
    for index in 0..word.len() {
        let role_id = tuple_item(word, index, "object-role word item")?;
        result.push(exact_encoded_role_id(&role_id, "word item")?);
    }
    Ok(result)
}

fn validate_encoded_slice_context(record: &Bound<'_, PyTuple>) -> NativeResult<usize> {
    let tokens = tuple_item(record, 2, "member tokens")?;
    if !tokens.is_exact_instance_of::<PyTuple>() {
        return Err(encoded_slice_invalid(
            "encoded slice member tokens are not an exact tuple",
        ));
    }
    let tokens = tokens
        .cast::<PyTuple>()
        .map_err(|_| encoded_slice_invalid("encoded slice member tokens changed type"))?;
    if tokens.len() > ENCODED_SLICE_CONTEXT_DEPTH {
        return Err(encoded_slice_invalid(
            "encoded slice member-token context exceeds its depth limit",
        ));
    }
    for index in 0..tokens.len() {
        let token = tuple_item(tokens, index, "member token")?;
        if !token.is_exact_instance_of::<PyBytes>() {
            return Err(encoded_slice_invalid(
                "encoded slice member token is not exact bytes",
            ));
        }
        let token = token
            .cast::<PyBytes>()
            .map_err(|_| encoded_slice_invalid("encoded slice member token changed type"))?;
        if token.as_bytes().len() != 32 {
            return Err(encoded_slice_invalid(
                "encoded slice member token is not bytes32",
            ));
        }
    }

    let scope_maps = tuple_item(record, 3, "anonymous scope maps")?;
    if !scope_maps.is_exact_instance_of::<PyTuple>() {
        return Err(encoded_slice_invalid(
            "encoded slice anonymous scope maps are not an exact tuple",
        ));
    }
    let scope_maps = scope_maps
        .cast::<PyTuple>()
        .map_err(|_| encoded_slice_invalid("encoded slice anonymous scope maps changed type"))?;
    if scope_maps.len() > ENCODED_SLICE_CONTEXT_DEPTH {
        return Err(encoded_slice_invalid(
            "encoded slice anonymous-scope context exceeds its depth limit",
        ));
    }
    let mut context_bytes = tokens
        .len()
        .checked_mul(32)
        .ok_or_else(|| encoded_slice_invalid("encoded slice member-token byte count overflowed"))?;
    for index in 0..scope_maps.len() {
        let value = tuple_item(scope_maps, index, "anonymous scope map")?;
        let scope_map = borrowed_py_bytes(&value, "anonymous scope map")?;
        context_bytes = context_bytes
            .checked_add(scope_map.len)
            .ok_or_else(|| encoded_slice_invalid("encoded slice context byte count overflowed"))?;
    }
    Ok(context_bytes)
}

fn validate_encoded_scope_map<S: encoded::ByteSource>(scope_map: S) -> NativeResult<()> {
    if scope_map.len() % 64 != 0 {
        return Err(encoded_slice_invalid(
            "encoded anonymous scope map contains a partial row",
        ));
    }
    let mut previous: Option<[u8; 32]> = None;
    for offset in (0..scope_map.len()).step_by(64) {
        let mut source = [0_u8; 32];
        let mut target = [0_u8; 32];
        for index in 0..32 {
            source[index] = scope_map.byte(offset + index).ok_or_else(|| {
                encoded_slice_invalid("encoded anonymous scope source disappeared")
            })?;
            target[index] = scope_map.byte(offset + 32 + index).ok_or_else(|| {
                encoded_slice_invalid("encoded anonymous scope target disappeared")
            })?;
        }
        if previous.is_some_and(|value| value >= source) || source == target {
            return Err(encoded_slice_invalid(
                "encoded anonymous scope sources are not sorted unique or contain identity rows",
            ));
        }
        previous = Some(source);
    }
    Ok(())
}

fn decode_encoded_scope_maps<S: encoded::ByteSource>(
    scope_maps: &[S],
    max_owned_bytes: usize,
) -> NativeResult<(Vec<encoded::role_characteristics::AnonymousScopeMap>, usize)> {
    let requested_outer_bytes = scope_maps
        .len()
        .checked_mul(std::mem::size_of::<
            encoded::role_characteristics::AnonymousScopeMap,
        >())
        .ok_or_else(|| encoded_slice_invalid("anonymous-scope map allocation overflowed"))?;
    let mut requested_owned_bytes = requested_outer_bytes;
    for scope_map in scope_maps {
        validate_encoded_scope_map(*scope_map)?;
        requested_owned_bytes = requested_owned_bytes
            .checked_add(scope_map.len())
            .ok_or_else(|| encoded_slice_invalid("anonymous-scope map bytes overflowed"))?;
    }
    if requested_owned_bytes > max_owned_bytes {
        return Err(encoded_validation_error(
            encoded::EncodedValidationError::resource(
                "anonymous-scope map decoding exceeds the remaining owned-byte limit",
            ),
        ));
    }
    let mut decoded = Vec::new();
    decoded.try_reserve_exact(scope_maps.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "anonymous-scope map collection allocation failed",
        ))
    })?;
    let mut owned_bytes = decoded
        .capacity()
        .checked_mul(std::mem::size_of::<
            encoded::role_characteristics::AnonymousScopeMap,
        >())
        .ok_or_else(|| encoded_slice_invalid("anonymous-scope map capacity overflowed"))?;
    if owned_bytes > max_owned_bytes {
        return Err(encoded_validation_error(
            encoded::EncodedValidationError::resource(
                "anonymous-scope map allocation exceeds the remaining owned-byte limit",
            ),
        ));
    }
    for scope_map in scope_maps {
        let row_count = scope_map.len() / 64;
        let mut rows = Vec::new();
        rows.try_reserve_exact(row_count).map_err(|_| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "anonymous-scope replacement allocation failed",
            ))
        })?;
        let row_bytes = rows
            .capacity()
            .checked_mul(std::mem::size_of::<
                encoded::role_characteristics::AnonymousScopeReplacement,
            >())
            .ok_or_else(|| encoded_slice_invalid("anonymous-scope row capacity overflowed"))?;
        owned_bytes = owned_bytes
            .checked_add(row_bytes)
            .ok_or_else(|| encoded_slice_invalid("anonymous-scope ownership overflowed"))?;
        if owned_bytes > max_owned_bytes {
            return Err(encoded_validation_error(
                encoded::EncodedValidationError::resource(
                    "anonymous-scope map allocation exceeds the remaining owned-byte limit",
                ),
            ));
        }
        for offset in (0..scope_map.len()).step_by(64) {
            let mut source = [0_u8; 32];
            let mut target = [0_u8; 32];
            for byte_index in 0..32 {
                source[byte_index] = encoded::ByteSource::byte(*scope_map, offset + byte_index)
                    .ok_or_else(|| encoded_slice_invalid("anonymous scope source disappeared"))?;
                target[byte_index] =
                    encoded::ByteSource::byte(*scope_map, offset + 32 + byte_index).ok_or_else(
                        || encoded_slice_invalid("anonymous scope target disappeared"),
                    )?;
            }
            rows.push(encoded::role_characteristics::AnonymousScopeReplacement { source, target });
        }
        decoded.push(rows);
    }
    Ok((decoded, owned_bytes))
}

fn compile_encoded_slice_symbol_phases<B: encoded::ByteSource>(
    slices: &[EncodedSliceInput<B>],
    limits: encoded::named_classes::NamedClassPhaseLimits,
    poll: &mut impl FnMut(&'static str) -> NativeResult<()>,
) -> NativeResult<Vec<encoded::symbols::SymbolPhase>> {
    let mut phases = Vec::new();
    phases.try_reserve_exact(slices.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "encoded symbol slice transaction allocation failed",
        ))
    })?;
    let mut catalogs = Vec::new();
    catalogs.try_reserve_exact(slices.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "encoded source declaration catalog allocation failed",
        ))
    })?;
    let mut source_work = 0_u64;
    let mut source_owned = 0_usize;
    let mut context_bytes = 0_usize;
    for slice in slices {
        for scope_map in &slice.scope_maps {
            validate_encoded_scope_map(*scope_map)?;
        }
        context_bytes = context_bytes
            .checked_add(slice.context_bytes)
            .ok_or_else(|| encoded_slice_invalid("encoded slice context bytes overflowed"))?;
        if context_bytes > limits.max_owned_bytes {
            return Err(encoded_validation_error(
                encoded::EncodedValidationError::resource(
                    "encoded slice contexts exceed their byte limit",
                ),
            ));
        }
        let model =
            encoded::model::ValidatedModel::new(slice.columns, encoded::EncodedLimits::default())
                .map_err(encoded_validation_error)?;
        let symbol_limits = encoded::symbols::SymbolPhaseLimits {
            max_owned_bytes: limits
                .max_owned_bytes
                .checked_sub(source_owned)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded slice symbol ownership exceeded its aggregate limit",
                    ))
                })?,
            max_work: limits.max_work.checked_sub(source_work).ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice symbol work exceeded its aggregate limit",
                ))
            })?,
            ..encoded::symbols::SymbolPhaseLimits::default()
        };
        let (phase, catalog) =
            encoded::symbols::compile_symbol_phase_selected_with_catalog_controlled(
                &model,
                symbol_limits,
                slice.posting_mode,
                slice.postings,
                poll,
            )
            .map_err(encoded_symbol_error)?;
        source_work = source_work.checked_add(phase.work).ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded slice symbol work overflowed",
            ))
        })?;
        source_owned = source_owned.checked_add(phase.owned_bytes).ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded slice symbol ownership overflowed",
            ))
        })?;
        phases.push(phase);
        catalogs.push(catalog);
        poll("source-symbol")?;
    }
    let proof_limits = encoded::symbols::SymbolPhaseLimits {
        max_owned_bytes: limits
            .max_owned_bytes
            .checked_sub(source_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice symbols exceeded their aggregate ownership limit",
                ))
            })?,
        max_work: limits.max_work.checked_sub(source_work).ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded slice symbols exceeded their aggregate work limit",
            ))
        })?,
        ..encoded::symbols::SymbolPhaseLimits::default()
    };
    encoded::symbols::install_source_declaration_proof_controlled(
        &mut phases,
        &mut catalogs,
        proof_limits,
        poll,
    )
    .map_err(encoded_symbol_error)?;
    poll("source-declaration-proof")?;
    Ok(phases)
}

fn compile_encoded_slice_program(
    slices: &Bound<'_, PyAny>,
) -> NativeResult<encoded::permanent_program::EncodedSliceProgram> {
    compile_encoded_slice_program_with_namespace(slices, None)
}

fn compile_encoded_slice_program_with_namespace(
    slices: &Bound<'_, PyAny>,
    definition_namespace: Option<[u8; 32]>,
) -> NativeResult<encoded::permanent_program::EncodedSliceProgram> {
    let mut poll = |_phase| Ok(());
    compile_encoded_slice_program_controlled(slices, definition_namespace, &mut poll)
}

fn compile_encoded_slice_program_controlled(
    slices: &Bound<'_, PyAny>,
    definition_namespace: Option<[u8; 32]>,
    poll: &mut impl FnMut(&'static str) -> NativeResult<()>,
) -> NativeResult<encoded::permanent_program::EncodedSliceProgram> {
    let leases = prepare_borrowed_encoded_slices(slices)?;
    let inputs = borrowed_encoded_slice_inputs(&leases)?;
    compile_encoded_slice_program_inputs_controlled(&inputs, definition_namespace, poll)
}

fn compile_encoded_slice_program_inputs_controlled<B: encoded::ByteSource>(
    slices: &[EncodedSliceInput<B>],
    definition_namespace: Option<[u8; 32]>,
    poll: &mut impl FnMut(&'static str) -> NativeResult<()>,
) -> NativeResult<encoded::permanent_program::EncodedSliceProgram> {
    compile_encoded_slice_program_inputs_with_fingerprints_controlled(
        slices,
        definition_namespace,
        None,
        None,
        poll,
    )
    .map(|(program, _fingerprints)| program)
}

fn compile_encoded_slice_program_inputs_with_fingerprints_controlled<B: encoded::ByteSource>(
    slices: &[EncodedSliceInput<B>],
    definition_namespace: Option<[u8; 32]>,
    fingerprint_request: Option<(
        &encoded::fingerprints::StructuralContextEvidence,
        encoded::fingerprints::StructuralFingerprintMode,
    )>,
    max_owned_bytes: Option<usize>,
    poll: &mut impl FnMut(&'static str) -> NativeResult<()>,
) -> NativeResult<(
    encoded::permanent_program::EncodedSliceProgram,
    Option<encoded::fingerprints::ViewFingerprints>,
)> {
    let mut limits = encoded::named_classes::NamedClassPhaseLimits::default();
    if let Some(maximum) = max_owned_bytes {
        limits.max_owned_bytes = maximum;
    }
    if slices.is_empty() {
        return Err(encoded_slice_invalid(
            "encoded slice program requires at least one slice",
        ));
    }
    if slices.len() > limits.max_slices {
        return Err(encoded_validation_error(
            encoded::EncodedValidationError::resource(
                "encoded slice program exceeds its slice limit",
            ),
        ));
    }
    poll("program-preflight")?;
    let symbol_phases = compile_encoded_slice_symbol_phases(slices, limits, poll)?;
    let fingerprints = if let Some((context, structural_mode)) = fingerprint_request {
        if definition_namespace.is_some() {
            return Err(encoded_slice_invalid(
                "encoded deferred fingerprints conflict with an explicit definition namespace",
            ));
        }
        let fingerprint_limits = encoded::fingerprints::FingerprintPhaseLimits {
            max_owned_bytes: limits.max_owned_bytes,
            ..encoded::fingerprints::FingerprintPhaseLimits::default()
        };
        let symbol_headers = symbol_phases
            .capacity()
            .checked_mul(std::mem::size_of::<encoded::symbols::SymbolPhase>())
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded fingerprint symbol headers overflowed",
                ))
            })?;
        let symbol_owned = symbol_phases
            .iter()
            .try_fold(symbol_headers, |total, phase| {
                total.checked_add(phase.owned_bytes).ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded fingerprint retained-symbol ownership overflowed",
                    ))
                })
            })?;
        let mut contributions = Vec::new();
        contributions.try_reserve_exact(slices.len()).map_err(|_| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded fingerprint slice transaction allocation failed",
            ))
        })?;
        let contribution_headers = contributions
            .capacity()
            .checked_mul(std::mem::size_of::<
                encoded::fingerprints::FingerprintContributions,
            >())
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded fingerprint contribution headers overflowed",
                ))
            })?;
        let retained_base = symbol_owned
            .checked_add(contribution_headers)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded fingerprint retained ownership overflowed",
                ))
            })?;
        if retained_base > fingerprint_limits.max_owned_bytes {
            return Err(encoded_validation_error(
                encoded::EncodedValidationError::resource(
                    "encoded fingerprint retained phases exceed the owned-byte limit",
                ),
            ));
        }
        let mut contribution_owned = 0_usize;
        let mut contribution_work = 0_u64;
        for (slice, symbols) in slices.iter().zip(&symbol_phases) {
            let model = encoded::model::ValidatedModel::new(
                slice.columns,
                encoded::EncodedLimits::default(),
            )
            .map_err(encoded_validation_error)?;
            let retained_owned =
                retained_base
                    .checked_add(contribution_owned)
                    .ok_or_else(|| {
                        encoded_validation_error(encoded::EncodedValidationError::resource(
                            "encoded fingerprint contribution ownership overflowed",
                        ))
                    })?;
            let remaining_before_scope = fingerprint_limits
                .max_owned_bytes
                .checked_sub(retained_owned)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded fingerprints exceed the aggregate owned-byte limit",
                    ))
                })?;
            let (scope_maps, scope_owned) =
                decode_encoded_scope_maps(&slice.scope_maps, remaining_before_scope)?;
            let phase_owned_limit =
                remaining_before_scope
                    .checked_sub(scope_owned)
                    .ok_or_else(|| {
                        encoded_validation_error(encoded::EncodedValidationError::resource(
                            "encoded fingerprint scope maps exceed the aggregate owned-byte limit",
                        ))
                    })?;
            let phase_work_limit = fingerprint_limits
                .max_work
                .checked_sub(contribution_work)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded fingerprints exceed the aggregate work limit",
                    ))
                })?;
            let phase_limits = encoded::fingerprints::FingerprintPhaseLimits {
                max_owned_bytes: phase_owned_limit,
                max_work: phase_work_limit,
                ..fingerprint_limits
            };
            let contribution = encoded::fingerprints::compile_fingerprint_contributions_controlled(
                &model,
                &symbols.roots,
                &scope_maps,
                phase_limits,
                poll,
            )
            .map_err(encoded_fingerprint_error)?;
            contribution_owned = contribution_owned
                .checked_add(contribution.owned_bytes())
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded fingerprint contribution ownership overflowed",
                    ))
                })?;
            contribution_work = contribution_work
                .checked_add(contribution.work())
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded fingerprint contribution work overflowed",
                    ))
                })?;
            contributions.push(contribution);
        }
        let merge_owned_limit = fingerprint_limits
            .max_owned_bytes
            .checked_sub(symbol_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded fingerprint symbols exceed the aggregate owned-byte limit",
                ))
            })?;
        let merge_limits = encoded::fingerprints::FingerprintPhaseLimits {
            max_owned_bytes: merge_owned_limit,
            ..fingerprint_limits
        };
        Some(
            encoded::fingerprints::merge_view_fingerprints_controlled(
                contributions,
                context,
                structural_mode,
                merge_limits,
                poll,
            )
            .map_err(encoded_fingerprint_error)?,
        )
    } else {
        None
    };
    let definition_namespace =
        fingerprints.map_or(definition_namespace, |value| Some(value.logical));
    let mut symbol_phases = symbol_phases.into_iter();
    let mut phases = Vec::new();
    phases.try_reserve_exact(slices.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "encoded slice transaction allocation failed",
        ))
    })?;
    let mut object_role_phases = Vec::new();
    object_role_phases
        .try_reserve_exact(slices.len())
        .map_err(|_| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded object-role slice transaction allocation failed",
            ))
        })?;
    let mut data_role_phases = Vec::new();
    data_role_phases
        .try_reserve_exact(slices.len())
        .map_err(|_| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded data-property slice transaction allocation failed",
            ))
        })?;
    let mut data_inclusion_phases = Vec::new();
    data_inclusion_phases
        .try_reserve_exact(slices.len())
        .map_err(|_| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded data-property inclusion slice allocation failed",
            ))
        })?;
    let mut simple_role_phases = Vec::new();
    simple_role_phases
        .try_reserve_exact(slices.len())
        .map_err(|_| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded simple-role slice transaction allocation failed",
            ))
        })?;
    let mut complex_role_phases = Vec::new();
    complex_role_phases
        .try_reserve_exact(slices.len())
        .map_err(|_| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded complex-role slice transaction allocation failed",
            ))
        })?;
    let mut role_characteristic_phases = Vec::new();
    role_characteristic_phases
        .try_reserve_exact(slices.len())
        .map_err(|_| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded role-characteristic slice transaction allocation failed",
            ))
        })?;
    let mut source_work = 0_u64;
    let mut source_owned = 0_usize;
    for slice in slices {
        let model =
            encoded::model::ValidatedModel::new(slice.columns, encoded::EncodedLimits::default())
                .map_err(encoded_validation_error)?;
        let symbols = symbol_phases.next().ok_or_else(|| {
            NativeError::new(
                ErrorKind::Invariant,
                "NATIVE_ENCODED_INVARIANT",
                "encoded symbol prepass ended before its source slices",
            )
        })?;
        let after_symbol_work = source_work.checked_add(symbols.work).ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded slice source work overflowed",
            ))
        })?;
        let after_symbol_owned =
            source_owned
                .checked_add(symbols.owned_bytes)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded slice source ownership overflowed",
                    ))
                })?;
        let object_role_limits = encoded::object_roles::ObjectRolePhaseLimits {
            max_owned_bytes: limits
                .max_owned_bytes
                .checked_sub(after_symbol_owned)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded slice symbol ownership exceeded its aggregate limit",
                    ))
                })?,
            max_work: limits
                .max_work
                .checked_sub(after_symbol_work)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded slice symbol work exceeded its aggregate limit",
                    ))
                })?,
            ..encoded::object_roles::ObjectRolePhaseLimits::default()
        };
        let object_roles =
            encoded::object_roles::compile_object_role_phase(&symbols, object_role_limits)
                .map_err(encoded_validation_error)?;
        poll("source-object-role")?;
        let after_object_role_work = after_symbol_work
            .checked_add(object_roles.work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice object-role work overflowed",
                ))
            })?;
        let after_object_role_owned = after_symbol_owned
            .checked_add(object_roles.owned_bytes)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice object-role ownership overflowed",
                ))
            })?;
        let data_role_limits = encoded::data_roles::DataRolePhaseLimits {
            max_owned_bytes: limits
                .max_owned_bytes
                .checked_sub(after_object_role_owned)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded slice object-role ownership exceeded its aggregate limit",
                    ))
                })?,
            max_work: limits
                .max_work
                .checked_sub(after_object_role_work)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded slice object-role work exceeded its aggregate limit",
                    ))
                })?,
            ..encoded::data_roles::DataRolePhaseLimits::default()
        };
        let data_roles = encoded::data_roles::compile_data_role_phase(&symbols, data_role_limits)
            .map_err(encoded_validation_error)?;
        poll("source-data-role")?;
        let after_data_role_work = after_object_role_work
            .checked_add(data_roles.work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice data-property work overflowed",
                ))
            })?;
        let after_data_role_owned = after_object_role_owned
            .checked_add(data_roles.owned_bytes)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice data-property ownership overflowed",
                ))
            })?;
        let data_inclusion_limits = encoded::data_inclusions::DataInclusionPhaseLimits {
            max_owned_bytes: limits
                .max_owned_bytes
                .checked_sub(after_data_role_owned)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded slice data-property ownership exceeded its aggregate limit",
                    ))
                })?,
            max_work: limits
                .max_work
                .checked_sub(after_data_role_work)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded slice data-property work exceeded its aggregate limit",
                    ))
                })?,
            ..encoded::data_inclusions::DataInclusionPhaseLimits::default()
        };
        let data_inclusions = encoded::data_inclusions::compile_data_inclusion_phase(
            &model,
            &symbols,
            &data_roles,
            data_inclusion_limits,
        )
        .map_err(encoded_validation_error)?;
        poll("source-data-inclusion")?;
        let after_data_inclusion_work = after_data_role_work
            .checked_add(data_inclusions.work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice data-property inclusion work overflowed",
                ))
            })?;
        let after_data_inclusion_owned = after_data_role_owned
            .checked_add(data_inclusions.owned_bytes)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice data-property inclusion ownership overflowed",
                ))
            })?;
        let simple_role_limits = encoded::simple_roles::SimpleRolePhaseLimits {
            max_owned_bytes: limits
                .max_owned_bytes
                .checked_sub(after_data_inclusion_owned)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded slice data-property inclusion ownership exceeded its aggregate limit",
                    ))
                })?,
            max_work: limits
                .max_work
                .checked_sub(after_data_inclusion_work)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded slice data-property inclusion work exceeded its aggregate limit",
                    ))
                })?,
            ..encoded::simple_roles::SimpleRolePhaseLimits::default()
        };
        let simple_roles = encoded::simple_roles::compile_simple_role_phase(
            &model,
            &symbols,
            &object_roles,
            simple_role_limits,
        )
        .map_err(encoded_validation_error)?;
        poll("source-simple-role")?;
        let after_simple_role_work = after_data_inclusion_work
            .checked_add(simple_roles.work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice simple-role work overflowed",
                ))
            })?;
        let after_simple_role_owned = after_data_inclusion_owned
            .checked_add(simple_roles.owned_bytes)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice simple-role ownership overflowed",
                ))
            })?;
        let complex_role_limits = encoded::complex_roles::ComplexRolePhaseLimits {
            max_owned_bytes: limits
                .max_owned_bytes
                .checked_sub(after_simple_role_owned)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded slice simple-role ownership exceeded its aggregate limit",
                    ))
                })?,
            max_work: limits
                .max_work
                .checked_sub(after_simple_role_work)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded slice simple-role work exceeded its aggregate limit",
                    ))
                })?,
            ..encoded::complex_roles::ComplexRolePhaseLimits::default()
        };
        let complex_roles = encoded::complex_roles::compile_complex_role_phase(
            &model,
            &symbols,
            &object_roles,
            complex_role_limits,
        )
        .map_err(encoded_validation_error)?;
        poll("source-complex-role")?;
        let after_complex_role_work = after_simple_role_work
            .checked_add(complex_roles.work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice complex-role work overflowed",
                ))
            })?;
        let after_complex_role_owned = after_simple_role_owned
            .checked_add(complex_roles.owned_bytes)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice complex-role ownership overflowed",
                ))
            })?;
        let remaining_after_complex_owned = limits
            .max_owned_bytes
            .checked_sub(after_complex_role_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice complex-role ownership exceeded its aggregate limit",
                ))
            })?;
        let has_role_characteristics = symbols.roots.iter().any(|root| {
            matches!(
                root.handler,
                encoded::symbols::RootHandler::DisjointObjectProperties
                    | encoded::symbols::RootHandler::IrreflexiveObjectProperty
                    | encoded::symbols::RootHandler::AsymmetricObjectProperty
                    | encoded::symbols::RootHandler::DisjointDataProperties
            )
        });
        let has_named_axiom_provenance = symbols.roots.iter().any(|root| {
            matches!(
                root.handler,
                encoded::symbols::RootHandler::SubClassOf
                    | encoded::symbols::RootHandler::EquivalentClasses
                    | encoded::symbols::RootHandler::DisjointClasses
                    | encoded::symbols::RootHandler::SameIndividual
                    | encoded::symbols::RootHandler::DifferentIndividuals
                    | encoded::symbols::RootHandler::ClassAssertion
                    | encoded::symbols::RootHandler::ObjectPropertyAssertion
                    | encoded::symbols::RootHandler::NegativeObjectPropertyAssertion
                    | encoded::symbols::RootHandler::ObjectPropertyDomain
                    | encoded::symbols::RootHandler::ObjectPropertyRange
                    | encoded::symbols::RootHandler::FunctionalObjectProperty
                    | encoded::symbols::RootHandler::InverseFunctionalObjectProperty
                    | encoded::symbols::RootHandler::ReflexiveObjectProperty
                    | encoded::symbols::RootHandler::DataPropertyDomain
                    | encoded::symbols::RootHandler::DataPropertyRange
                    | encoded::symbols::RootHandler::FunctionalDataProperty
                    | encoded::symbols::RootHandler::DatatypeDefinition
                    | encoded::symbols::RootHandler::HasKey
            )
        });
        let (scope_maps, scope_map_owned) =
            if has_role_characteristics || has_named_axiom_provenance {
                decode_encoded_scope_maps(&slice.scope_maps, remaining_after_complex_owned)?
            } else {
                (Vec::new(), 0)
            };
        let role_characteristic_limits =
            encoded::role_characteristics::RoleCharacteristicPhaseLimits {
                max_owned_bytes: remaining_after_complex_owned
                    .checked_sub(scope_map_owned)
                    .ok_or_else(|| {
                        encoded_validation_error(encoded::EncodedValidationError::resource(
                            "anonymous-scope maps exceeded the role-characteristic ownership limit",
                        ))
                    })?,
                max_work: limits
                    .max_work
                    .checked_sub(after_complex_role_work)
                    .ok_or_else(|| {
                        encoded_validation_error(encoded::EncodedValidationError::resource(
                            "encoded slice complex-role work exceeded its aggregate limit",
                        ))
                    })?,
                ..encoded::role_characteristics::RoleCharacteristicPhaseLimits::default()
            };
        let role_characteristics =
            encoded::role_characteristics::compile_role_characteristic_phase_scoped(
                &model,
                &symbols,
                &object_roles,
                &data_roles,
                if has_role_characteristics {
                    &scope_maps
                } else {
                    &[]
                },
                role_characteristic_limits,
            )
            .map_err(encoded_validation_error)?;
        poll("source-role-characteristic")?;
        let after_role_characteristic_work = after_complex_role_work
            .checked_add(role_characteristics.work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice role-characteristic work overflowed",
                ))
            })?;
        let after_role_characteristic_owned = after_complex_role_owned
            .checked_add(role_characteristics.owned_bytes)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice role-characteristic ownership overflowed",
                ))
            })?;
        let named_limits = encoded::named_classes::NamedClassPhaseLimits {
            max_owned_bytes: limits
                .max_owned_bytes
                .checked_sub(after_role_characteristic_owned)
                .and_then(|remaining| remaining.checked_sub(scope_map_owned))
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "anonymous-scope maps exceeded the named-class ownership limit",
                    ))
                })?,
            max_work: limits
                .max_work
                .checked_sub(after_role_characteristic_work)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded slice role-characteristic work exceeded its aggregate limit",
                    ))
                })?,
            ..limits
        };
        let named_scope_maps = if has_named_axiom_provenance {
            scope_maps.as_slice()
        } else {
            &[]
        };
        let named = match definition_namespace {
            Some(namespace) => encoded::named_classes::compile_named_class_phase_with_role_domains_scoped_and_namespace(
                &model,
                &symbols,
                &object_roles,
                &data_roles,
                named_scope_maps,
                namespace,
                named_limits,
            ),
            None => encoded::named_classes::compile_named_class_phase_with_role_domains_scoped(
                &model,
                &symbols,
                &object_roles,
                &data_roles,
                named_scope_maps,
                named_limits,
            ),
        }
        .map_err(encoded_validation_error)?;
        poll("source-named-class")?;
        drop(scope_maps);
        source_work = after_role_characteristic_work
            .checked_add(named.work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice source work overflowed",
                ))
            })?;
        source_owned = after_role_characteristic_owned
            .checked_add(named.owned_bytes)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded slice source ownership overflowed",
                ))
            })?;
        if source_work > limits.max_work || source_owned > limits.max_owned_bytes {
            return Err(encoded_validation_error(
                encoded::EncodedValidationError::resource(
                    "encoded slice sources exceed their aggregate compilation limit",
                ),
            ));
        }
        phases.push((symbols, named));
        object_role_phases.push(object_roles);
        data_role_phases.push(data_roles);
        data_inclusion_phases.push(data_inclusions);
        simple_role_phases.push(simple_roles);
        complex_role_phases.push(complex_roles);
        role_characteristic_phases.push(role_characteristics);
        poll("source-slice")?;
    }
    if symbol_phases.next().is_some() {
        return Err(NativeError::new(
            ErrorKind::Invariant,
            "NATIVE_ENCODED_INVARIANT",
            "encoded symbol prepass outlived its source slices",
        ));
    }
    let object_role_limits = encoded::object_roles::ObjectRolePhaseLimits {
        max_owned_bytes: limits.max_owned_bytes,
        max_work: limits.max_work,
        ..encoded::object_roles::ObjectRolePhaseLimits::default()
    };
    let object_roles =
        encoded::object_roles::merge_object_role_phases(&object_role_phases, object_role_limits)
            .map_err(encoded_validation_error)?;
    poll("merged-object-role")?;
    let data_role_limits = encoded::data_roles::DataRolePhaseLimits {
        max_owned_bytes: limits
            .max_owned_bytes
            .checked_sub(object_roles.owned_bytes)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded object-role merge ownership exceeded the program limit",
                ))
            })?,
        max_work: limits
            .max_work
            .checked_sub(object_roles.work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded object-role merge work exceeded the program limit",
                ))
            })?,
        ..encoded::data_roles::DataRolePhaseLimits::default()
    };
    let data_roles =
        encoded::data_roles::merge_data_role_phases(&data_role_phases, data_role_limits)
            .map_err(encoded_validation_error)?;
    poll("merged-data-role")?;
    let merged_role_domain_owned = object_roles
        .owned_bytes
        .checked_add(data_roles.owned_bytes)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged role-domain ownership overflowed",
            ))
        })?;
    let merged_role_domain_work =
        object_roles
            .work
            .checked_add(data_roles.work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged role-domain work overflowed",
                ))
            })?;
    let named_limits = encoded::named_classes::NamedClassPhaseLimits {
        max_owned_bytes: limits
            .max_owned_bytes
            .checked_sub(merged_role_domain_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged role domains exceeded the program ownership limit",
                ))
            })?,
        max_work: limits
            .max_work
            .checked_sub(merged_role_domain_work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged role domains exceeded the program work limit",
                ))
            })?,
        ..limits
    };
    let named_classes = encoded::named_classes::merge_named_class_phases_with_role_domains(
        &phases,
        &object_role_phases,
        &object_roles,
        &data_role_phases,
        &data_roles,
        named_limits,
    )
    .map_err(encoded_validation_error)?;
    poll("merged-named-class")?;
    let merged_role_owned = merged_role_domain_owned
        .checked_add(named_classes.owned_bytes)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged role ownership overflowed",
            ))
        })?;
    let merged_role_work = merged_role_domain_work
        .checked_add(named_classes.work)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged role work overflowed",
            ))
        })?;
    let data_inclusion_limits = encoded::data_inclusions::DataInclusionPhaseLimits {
        max_owned_bytes: limits
            .max_owned_bytes
            .checked_sub(merged_role_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged roles exceeded the program ownership limit",
                ))
            })?,
        max_work: limits
            .max_work
            .checked_sub(merged_role_work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged roles exceeded the program work limit",
                ))
            })?,
        ..encoded::data_inclusions::DataInclusionPhaseLimits::default()
    };
    let data_inclusions = encoded::data_inclusions::merge_data_inclusion_phases(
        &data_role_phases,
        &data_inclusion_phases,
        &data_roles,
        data_inclusion_limits,
    )
    .map_err(encoded_validation_error)?;
    poll("merged-data-inclusion")?;
    let merged_role_owned = merged_role_owned
        .checked_add(data_inclusions.owned_bytes)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged data-property inclusion ownership overflowed",
            ))
        })?;
    let merged_role_work = merged_role_work
        .checked_add(data_inclusions.work)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged data-property inclusion work overflowed",
            ))
        })?;
    let data_hierarchy_limits = encoded::data_role_hierarchy::DataRoleHierarchyLimits {
        max_owned_bytes: limits
            .max_owned_bytes
            .checked_sub(merged_role_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged data inclusions exceeded the program ownership limit",
                ))
            })?,
        max_work: limits
            .max_work
            .checked_sub(merged_role_work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged data inclusions exceeded the program work limit",
                ))
            })?,
        ..encoded::data_role_hierarchy::DataRoleHierarchyLimits::default()
    };
    let data_role_hierarchy = encoded::data_role_hierarchy::compile_data_role_hierarchy_phase(
        &data_roles,
        &data_inclusions,
        data_hierarchy_limits,
    )
    .map_err(encoded_validation_error)?;
    poll("merged-data-hierarchy")?;
    let merged_role_owned = merged_role_owned
        .checked_add(data_role_hierarchy.owned_bytes)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged data hierarchy ownership overflowed",
            ))
        })?;
    let merged_role_work = merged_role_work
        .checked_add(data_role_hierarchy.work)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged data hierarchy work overflowed",
            ))
        })?;
    let simple_role_limits = encoded::simple_roles::SimpleRolePhaseLimits {
        max_owned_bytes: limits
            .max_owned_bytes
            .checked_sub(merged_role_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged roles exceeded the program ownership limit",
                ))
            })?,
        max_work: limits
            .max_work
            .checked_sub(merged_role_work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged roles exceeded the program work limit",
                ))
            })?,
        ..encoded::simple_roles::SimpleRolePhaseLimits::default()
    };
    let simple_roles = encoded::simple_roles::merge_simple_role_phases(
        &object_role_phases,
        &simple_role_phases,
        &object_roles,
        simple_role_limits,
    )
    .map_err(encoded_validation_error)?;
    poll("merged-simple-role")?;
    let merged_simple_owned = merged_role_owned
        .checked_add(simple_roles.owned_bytes)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged simple-role ownership overflowed",
            ))
        })?;
    let merged_simple_work = merged_role_work
        .checked_add(simple_roles.work)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged simple-role work overflowed",
            ))
        })?;
    let complex_role_limits = encoded::complex_roles::ComplexRolePhaseLimits {
        max_owned_bytes: limits
            .max_owned_bytes
            .checked_sub(merged_simple_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged simple roles exceeded the program ownership limit",
                ))
            })?,
        max_work: limits
            .max_work
            .checked_sub(merged_simple_work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged simple roles exceeded the program work limit",
                ))
            })?,
        ..encoded::complex_roles::ComplexRolePhaseLimits::default()
    };
    let complex_roles = encoded::complex_roles::merge_complex_role_phases(
        &object_role_phases,
        &complex_role_phases,
        &object_roles,
        complex_role_limits,
    )
    .map_err(encoded_validation_error)?;
    poll("merged-complex-role")?;
    let merged_complex_owned = merged_simple_owned
        .checked_add(complex_roles.owned_bytes)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged complex-role ownership overflowed",
            ))
        })?;
    let merged_complex_work = merged_simple_work
        .checked_add(complex_roles.work)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged complex-role work overflowed",
            ))
        })?;
    let role_characteristic_limits = encoded::role_characteristics::RoleCharacteristicPhaseLimits {
        max_owned_bytes: limits
            .max_owned_bytes
            .checked_sub(merged_complex_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged complex roles exceeded the program ownership limit",
                ))
            })?,
        max_work: limits
            .max_work
            .checked_sub(merged_complex_work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged complex roles exceeded the program work limit",
                ))
            })?,
        ..encoded::role_characteristics::RoleCharacteristicPhaseLimits::default()
    };
    let role_characteristics = encoded::role_characteristics::merge_role_characteristic_phases(
        &object_role_phases,
        &data_role_phases,
        &role_characteristic_phases,
        &object_roles,
        &data_roles,
        role_characteristic_limits,
    )
    .map_err(encoded_validation_error)?;
    poll("merged-role-characteristic")?;
    let merged_characteristic_owned = merged_complex_owned
        .checked_add(role_characteristics.owned_bytes)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged role-characteristic ownership overflowed",
            ))
        })?;
    let merged_characteristic_work = merged_complex_work
        .checked_add(role_characteristics.work)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged role-characteristic work overflowed",
            ))
        })?;
    let hierarchy_limits = encoded::object_role_hierarchy::ObjectRoleHierarchyLimits {
        max_owned_bytes: limits
            .max_owned_bytes
            .checked_sub(merged_characteristic_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged role characteristics exceeded the program ownership limit",
                ))
            })?,
        max_work: limits
            .max_work
            .checked_sub(merged_characteristic_work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged role characteristics exceeded the program work limit",
                ))
            })?,
        ..encoded::object_role_hierarchy::ObjectRoleHierarchyLimits::default()
    };
    let object_role_hierarchy =
        encoded::object_role_hierarchy::compile_object_role_hierarchy_phase(
            &object_roles,
            &simple_roles,
            hierarchy_limits,
        )
        .map_err(encoded_validation_error)?;
    poll("merged-object-role-hierarchy")?;
    let merged_hierarchy_owned = merged_characteristic_owned
        .checked_add(object_role_hierarchy.owned_bytes)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged role-hierarchy ownership overflowed",
            ))
        })?;
    let merged_hierarchy_work = merged_characteristic_work
        .checked_add(object_role_hierarchy.work)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged role-hierarchy work overflowed",
            ))
        })?;
    let semantics_limits = encoded::role_semantics::RoleSemanticsPhaseLimits {
        max_owned_bytes: limits
            .max_owned_bytes
            .checked_sub(merged_hierarchy_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged role hierarchy exceeded the program ownership limit",
                ))
            })?,
        max_work: limits
            .max_work
            .checked_sub(merged_hierarchy_work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged role hierarchy exceeded the program work limit",
                ))
            })?,
        ..encoded::role_semantics::RoleSemanticsPhaseLimits::default()
    };
    let role_semantics = encoded::role_semantics::compile_role_semantics_phase(
        &object_roles,
        &simple_roles,
        &complex_roles,
        &object_role_hierarchy,
        semantics_limits,
    )
    .map_err(encoded_validation_error)?;
    poll("merged-role-semantics")?;
    let merged_semantics_owned = merged_hierarchy_owned
        .checked_add(role_semantics.owned_bytes)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged role-semantics ownership overflowed",
            ))
        })?;
    let merged_semantics_work = merged_hierarchy_work
        .checked_add(role_semantics.work)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged role-semantics work overflowed",
            ))
        })?;
    let automata_limits = encoded::role_automata::RoleAutomataPhaseLimits {
        max_owned_bytes: limits
            .max_owned_bytes
            .checked_sub(merged_semantics_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged role semantics exceeded the program ownership limit",
                ))
            })?,
        max_work: limits
            .max_work
            .checked_sub(merged_semantics_work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged role semantics exceeded the program work limit",
                ))
            })?,
        ..encoded::role_automata::RoleAutomataPhaseLimits::default()
    };
    let role_automata = encoded::role_automata::compile_role_automata_phase(
        &object_roles,
        &simple_roles,
        &complex_roles,
        &object_role_hierarchy,
        &role_semantics,
        automata_limits,
    )
    .map_err(encoded_validation_error)?;
    poll("merged-role-automata")?;
    let merged_automata_owned = merged_semantics_owned
        .checked_add(role_automata.owned_bytes)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged role-automata ownership overflowed",
            ))
        })?;
    let merged_automata_work = merged_semantics_work
        .checked_add(role_automata.work)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged role-automata work overflowed",
            ))
        })?;
    let role_model_limits = encoded::role_model::RoleModelPhaseLimits {
        max_owned_bytes: limits
            .max_owned_bytes
            .checked_sub(merged_automata_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged role automata exceeded the program ownership limit",
                ))
            })?,
        max_work: limits
            .max_work
            .checked_sub(merged_automata_work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged role automata exceeded the program work limit",
                ))
            })?,
        ..encoded::role_model::RoleModelPhaseLimits::default()
    };
    let role_model = encoded::role_model::compile_role_model_phase(
        &object_roles,
        &data_roles,
        &simple_roles,
        &data_inclusions,
        &complex_roles,
        &object_role_hierarchy,
        &role_semantics,
        &role_automata,
        role_model_limits,
    )
    .map_err(encoded_validation_error)?;
    poll("merged-role-model")?;
    let merged_role_model_owned = merged_automata_owned
        .checked_add(role_model.owned_bytes)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged role-model ownership overflowed",
            ))
        })?;
    let merged_role_model_work = merged_automata_work
        .checked_add(role_model.work)
        .ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded merged role-model work overflowed",
            ))
        })?;
    let role_clause_limits = encoded::role_clauses::RoleClausePhaseLimits {
        max_owned_bytes: limits
            .max_owned_bytes
            .checked_sub(merged_role_model_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged role model exceeded the program ownership limit",
                ))
            })?,
        max_work: limits
            .max_work
            .checked_sub(merged_role_model_work)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded merged role model exceeded the program work limit",
                ))
            })?,
        ..encoded::role_clauses::RoleClausePhaseLimits::default()
    };
    let role_clauses = encoded::role_clauses::compile_role_clause_phase(
        &object_roles,
        &data_roles,
        &simple_roles,
        &data_inclusions,
        &complex_roles,
        &role_characteristics,
        &role_model,
        role_clause_limits,
    )
    .map_err(encoded_validation_error)?;
    // Nothing escapes the coarse call before this final publication checkpoint.
    poll("merged-role-clause-publication")?;
    Ok((
        encoded::permanent_program::EncodedSliceProgram {
            named_classes,
            object_roles,
            data_roles,
            data_inclusions,
            data_role_hierarchy,
            simple_roles,
            complex_roles,
            role_characteristics,
            object_role_hierarchy,
            role_semantics,
            role_automata,
            role_model,
            role_clauses,
        },
        fingerprints,
    ))
}

#[pyfunction(name = "_validate_encoded_slices_v1")]
#[pyo3(signature = (*, slices, cancellation=None))]
fn validate_encoded_slices_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
    cancellation: Option<PyRef<'_, CancellationHandle>>,
) -> PyResult<()> {
    let cancellation = cancellation.map(|handle| handle.state());
    contain_encoded_selection(py, || {
        let mut poll = |_phase| match cancellation.as_ref() {
            Some(state) => state.poll(),
            None => Ok(()),
        };
        compile_encoded_slice_program_controlled(slices, None, &mut poll).map(drop)
    })
}

/// Deterministically inject cancellation at each private orchestration checkpoint.
///
/// This is test-only evidence for transactional disposal and is not an encoded compiler
/// capability. Production cancellation uses `CancellationHandle` above.
#[pyfunction(name = "_debug_validate_encoded_slices_cancel_v1")]
#[pyo3(signature = (*, slices, cancel_at_checkpoint))]
fn debug_validate_encoded_slices_cancel_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
    cancel_at_checkpoint: u64,
) -> PyResult<()> {
    contain_encoded_selection(py, || {
        if cancel_at_checkpoint == 0 {
            return Err(encoded_slice_invalid(
                "encoded cancellation checkpoint must be positive",
            ));
        }
        let mut checkpoint = 0_u64;
        let mut poll = |phase: &'static str| {
            checkpoint = checkpoint
                .checked_add(1)
                .ok_or_else(|| NativeError::invariant("encoded checkpoint count overflowed"))?;
            if checkpoint == cancel_at_checkpoint {
                return Err(NativeError::new(
                    ErrorKind::Cancelled,
                    "REASONER_INTERRUPTED",
                    "native encoded compilation was interrupted at a test checkpoint",
                )
                .with_context("checkpoint", checkpoint.to_string())
                .with_context("phase", phase));
            }
            Ok(())
        };
        compile_encoded_slice_program_controlled(slices, None, &mut poll).map(drop)
    })
}

/// Private exact-parity probe for the encoded permanent-program prerequisite.
///
/// This publishes no session and is deliberately absent from `FEATURES`.
#[pyfunction(name = "_encoded_permanent_program_parity_v1")]
#[pyo3(signature = (
    *,
    slices,
    reference_ir,
    logical_fingerprint=None,
    max_owned_bytes=None,
    cancel_at_checkpoint=None
))]
fn encoded_permanent_program_parity_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
    reference_ir: &Bound<'_, PyBytes>,
    logical_fingerprint: Option<&Bound<'_, PyAny>>,
    max_owned_bytes: Option<usize>,
    cancel_at_checkpoint: Option<u64>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        if cancel_at_checkpoint == Some(0) {
            return Err(encoded_slice_invalid(
                "permanent-program cancellation checkpoint must be positive",
            ));
        }
        let namespace = logical_fingerprint
            .map(encoded_logical_fingerprint)
            .transpose()?;
        let limits = DecodeLimits::default();
        let reference = decode_ontology(
            copy_capped_bytes(
                reference_ir,
                limits.max_wire_bytes,
                "permanent-program reference wire",
            )?,
            &limits,
        )
        .map_err(map_input_wire_error)?;
        let mut checkpoint = 0_u64;
        let mut poll = |phase: &'static str| {
            checkpoint = checkpoint.checked_add(1).ok_or_else(|| {
                NativeError::invariant("permanent-program checkpoint count overflowed")
            })?;
            if cancel_at_checkpoint == Some(checkpoint) {
                return Err(NativeError::new(
                    ErrorKind::Cancelled,
                    "REASONER_INTERRUPTED",
                    "native permanent-program assembly was interrupted at a test checkpoint",
                )
                .with_context("checkpoint", checkpoint.to_string())
                .with_context("phase", phase));
            }
            Ok(())
        };
        let phases = compile_encoded_slice_program_controlled(slices, namespace, &mut poll)?;
        let mut assembly_limits = encoded::permanent_program::PermanentProgramLimits::default();
        if let Some(maximum) = max_owned_bytes {
            assembly_limits.max_owned_bytes = maximum;
        }
        let assembled = encoded::permanent_program::assemble_encoded_permanent_program(
            phases,
            assembly_limits,
            &mut poll,
        )
        .map_err(encoded_permanent_error)?;
        let mismatch = permanent_program_mismatch(&assembled.program, &reference.program);
        if let Some(section) = mismatch {
            let semantic_fence = matches!(
                section,
                "ground_disjunctions" | "datatype_model" | "expressivity"
            );
            return Err(NativeError::new(
                ErrorKind::Wire,
                "NATIVE_ENCODED_PARITY_MISMATCH",
                if semantic_fence {
                    "encoded permanent phases cannot exactly represent the reference semantics"
                } else {
                    "encoded permanent-program assembly differs from the scalar reference"
                },
            )
            .with_context("section", section));
        }
        assembled
            .parity_manifest_json()
            .map_err(encoded_validation_error)
    })
}

fn permanent_program_mismatch(
    assembled: &input_wire::DecodedProgram,
    reference: &input_wire::DecodedProgram,
) -> Option<&'static str> {
    [
        (
            assembled.symbol_domains != reference.symbol_domains,
            "symbol_domains",
        ),
        (assembled.predicates != reference.predicates, "predicates"),
        (assembled.clauses != reference.clauses, "clauses"),
        (
            assembled.positive_facts != reference.positive_facts,
            "positive_facts",
        ),
        (
            assembled.negative_facts != reference.negative_facts,
            "negative_facts",
        ),
        (
            assembled.ground_disjunctions != reference.ground_disjunctions,
            "ground_disjunctions",
        ),
        (assembled.role_model != reference.role_model, "role_model"),
        (
            assembled.datatype_model != reference.datatype_model,
            "datatype_model",
        ),
        (
            assembled.expressivity != reference.expressivity,
            "expressivity",
        ),
        (assembled.provenance != reference.provenance, "provenance"),
    ]
    .into_iter()
    .find_map(|(different, section)| different.then_some(section))
}

fn compile_encoded_profile_slices_controlled(
    slices: &Bound<'_, PyAny>,
    unsupported_datatypes: encoded::profile::ProfileUnsupportedDatatypePolicy,
    poll: &mut impl FnMut(&'static str) -> NativeResult<()>,
) -> NativeResult<encoded::profile::ProfilePhase> {
    let leases = prepare_borrowed_encoded_slices(slices)?;
    let inputs = borrowed_encoded_slice_inputs(&leases)?;
    compile_encoded_profile_slice_inputs_controlled(&inputs, unsupported_datatypes, poll)
}

fn compile_encoded_profile_slice_inputs_controlled<B: encoded::ByteSource>(
    slices: &[EncodedSliceInput<B>],
    unsupported_datatypes: encoded::profile::ProfileUnsupportedDatatypePolicy,
    poll: &mut impl FnMut(&'static str) -> NativeResult<()>,
) -> NativeResult<encoded::profile::ProfilePhase> {
    let limits = encoded::profile::ProfilePhaseLimits::default();
    if slices.is_empty() {
        return Err(encoded_slice_invalid(
            "encoded profile slice program requires at least one slice",
        ));
    }
    if slices.len() > limits.max_slices {
        return Err(encoded_validation_error(
            encoded::EncodedValidationError::resource(
                "encoded profile slice program exceeds its slice limit",
            ),
        ));
    }
    poll("profile-program-preflight")?;
    let mut phases = Vec::new();
    phases.try_reserve_exact(slices.len()).map_err(|_| {
        encoded_validation_error(encoded::EncodedValidationError::resource(
            "encoded profile slice transaction allocation failed",
        ))
    })?;
    let mut source_work = 0_u64;
    let mut source_owned = 0_usize;
    let mut context_bytes = 0_usize;
    for slice in slices {
        context_bytes = context_bytes
            .checked_add(slice.context_bytes)
            .ok_or_else(|| encoded_slice_invalid("encoded profile slice context overflowed"))?;
        if context_bytes > limits.max_owned_bytes {
            return Err(encoded_validation_error(
                encoded::EncodedValidationError::resource(
                    "encoded profile slice contexts exceed their byte limit",
                ),
            ));
        }

        let remaining_before_scope = limits
            .max_owned_bytes
            .checked_sub(source_owned)
            .ok_or_else(|| {
                encoded_validation_error(encoded::EncodedValidationError::resource(
                    "encoded profile slice ownership exceeded its aggregate limit",
                ))
            })?;
        let (scope_maps, scope_owned) =
            decode_encoded_scope_maps(&slice.scope_maps, remaining_before_scope)?;
        let phase_owned_limit =
            remaining_before_scope
                .checked_sub(scope_owned)
                .ok_or_else(|| {
                    encoded_validation_error(encoded::EncodedValidationError::resource(
                        "encoded profile scope maps exceed the remaining owned-byte limit",
                    ))
                })?;
        let phase_work_limit = limits.max_work.checked_sub(source_work).ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded profile slice work exceeded its aggregate limit",
            ))
        })?;

        let model =
            encoded::model::ValidatedModel::new(slice.columns, encoded::EncodedLimits::default())
                .map_err(encoded_validation_error)?;
        let phase = encoded::profile::compile_profile_phase_selected_controlled_with_policy(
            &model,
            &scope_maps,
            encoded::profile::ProfilePhaseLimits {
                max_owned_bytes: phase_owned_limit,
                max_work: phase_work_limit,
                ..limits
            },
            slice.posting_mode,
            slice.postings,
            unsupported_datatypes,
            poll,
        )
        .map_err(encoded_profile_error)?;
        source_work = source_work.checked_add(phase.work).ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded profile slice work overflowed",
            ))
        })?;
        source_owned = source_owned.checked_add(phase.owned_bytes).ok_or_else(|| {
            encoded_validation_error(encoded::EncodedValidationError::resource(
                "encoded profile slice ownership overflowed",
            ))
        })?;
        phases.push(phase);
    }
    encoded::profile::merge_profile_phases_controlled_with_policy(
        phases,
        limits,
        unsupported_datatypes,
        poll,
    )
    .map_err(encoded_profile_error)
}

fn compile_encoded_profile_slices_manifest_controlled(
    slices: &Bound<'_, PyAny>,
    unsupported_datatypes: encoded::profile::ProfileUnsupportedDatatypePolicy,
    ontology_identity_context: Option<&Bound<'_, PyAny>>,
    origin_context: Option<&Bound<'_, PyAny>>,
    poll: &mut impl FnMut(&'static str) -> NativeResult<()>,
) -> NativeResult<Vec<u8>> {
    let limits = encoded::profile::ProfilePhaseLimits::default();
    let ontology_identifiers =
        decode_profile_ontology_identity_context(ontology_identity_context, limits, poll)?;
    let origins = decode_profile_origin_context(origin_context, limits, poll)?;
    let phase = compile_encoded_profile_slices_controlled(slices, unsupported_datatypes, poll)?;
    let phase = apply_encoded_profile_contexts_controlled(
        phase,
        &ontology_identifiers,
        origins.as_deref(),
        limits,
        poll,
    )?;
    if origins.is_some() {
        phase
            .canonical_origin_manifest_json()
            .map_err(encoded_validation_error)
    } else {
        phase
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    }
}

fn apply_encoded_profile_contexts_controlled(
    phase: encoded::profile::ProfilePhase,
    ontology_identifiers: &[encoded::profile::ProfileOntologyIdentifier],
    origins: Option<&[encoded::profile::ProfileOrigin]>,
    limits: encoded::profile::ProfilePhaseLimits,
    poll: &mut impl FnMut(&'static str) -> NativeResult<()>,
) -> NativeResult<encoded::profile::ProfilePhase> {
    let phase = if ontology_identifiers.is_empty() {
        phase
    } else {
        encoded::profile::apply_ontology_identity_context_controlled(
            phase,
            ontology_identifiers,
            origins.is_some(),
            limits,
            poll,
        )
        .map_err(encoded_profile_error)?
    };
    Ok(if let Some(origins) = origins {
        encoded::profile::apply_origin_context_controlled(phase, origins, limits, poll)
            .map_err(encoded_profile_error)?
    } else {
        phase
    })
}

#[pyfunction(name = "_encoded_profile_slices_manifest_v1")]
#[pyo3(signature = (*, slices, unsupported_datatypes="error", ontology_identity_context=None, origin_context=None, cancellation=None))]
fn encoded_profile_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
    unsupported_datatypes: &str,
    ontology_identity_context: Option<&Bound<'_, PyAny>>,
    origin_context: Option<&Bound<'_, PyAny>>,
    cancellation: Option<PyRef<'_, CancellationHandle>>,
) -> PyResult<Vec<u8>> {
    let cancellation = cancellation.map(|handle| handle.state());
    contain_encoded_selection(py, || {
        let mut poll = |_phase| match cancellation.as_ref() {
            Some(state) => state.poll(),
            None => Ok(()),
        };
        let unsupported_datatypes =
            encoded_profile_unsupported_datatype_policy(unsupported_datatypes)?;
        compile_encoded_profile_slices_manifest_controlled(
            slices,
            unsupported_datatypes,
            ontology_identity_context,
            origin_context,
            &mut poll,
        )
    })
}

/// Deterministically inject cancellation into the private profile-context transaction.
#[pyfunction(name = "_debug_encoded_profile_context_cancel_v1")]
#[pyo3(signature = (*, slices, ontology_identity_context, cancel_at_checkpoint, origin_context=None))]
fn debug_encoded_profile_context_cancel_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
    ontology_identity_context: &Bound<'_, PyAny>,
    cancel_at_checkpoint: u64,
    origin_context: Option<&Bound<'_, PyAny>>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        if cancel_at_checkpoint == 0 {
            return Err(encoded_slice_invalid(
                "encoded profile cancellation checkpoint must be positive",
            ));
        }
        let mut checkpoint = 0_u64;
        let mut poll = |phase: &'static str| {
            checkpoint = checkpoint.checked_add(1).ok_or_else(|| {
                NativeError::invariant("encoded profile checkpoint count overflowed")
            })?;
            if checkpoint == cancel_at_checkpoint {
                return Err(NativeError::new(
                    ErrorKind::Cancelled,
                    "REASONER_INTERRUPTED",
                    "native encoded profile compilation was interrupted at a test checkpoint",
                )
                .with_context("checkpoint", checkpoint.to_string())
                .with_context("phase", phase));
            }
            Ok(())
        };
        compile_encoded_profile_slices_manifest_controlled(
            slices,
            encoded::profile::ProfileUnsupportedDatatypePolicy::Error,
            Some(ontology_identity_context),
            origin_context,
            &mut poll,
        )
    })
}

#[pyfunction(name = "_encoded_profile_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes, unsupported_datatypes="error", ontology_identity_context=None, origin_context=None, cancellation=None))]
#[allow(clippy::too_many_arguments)]
fn encoded_profile_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
    unsupported_datatypes: &str,
    ontology_identity_context: Option<&Bound<'_, PyAny>>,
    origin_context: Option<&Bound<'_, PyAny>>,
    cancellation: Option<PyRef<'_, CancellationHandle>>,
) -> PyResult<Vec<u8>> {
    let cancellation = cancellation.map(|handle| handle.state());
    contain_encoded_selection(py, || {
        let mut poll = |_phase| match cancellation.as_ref() {
            Some(state) => state.poll(),
            None => Ok(()),
        };
        poll("profile-program-preflight")?;
        let unsupported_datatypes =
            encoded_profile_unsupported_datatype_policy(unsupported_datatypes)?;
        let limits = encoded::profile::ProfilePhaseLimits::default();
        let ontology_identifiers =
            decode_profile_ontology_identity_context(ontology_identity_context, limits, &mut poll)?;
        let origins = decode_profile_origin_context(origin_context, limits, &mut poll)?;
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let phase = encoded::profile::compile_profile_phase_controlled_with_policy(
            &model,
            &[],
            limits,
            unsupported_datatypes,
            &mut poll,
        )
        .map_err(encoded_profile_error)?;
        let phase = if ontology_identifiers.is_empty() {
            phase
        } else {
            encoded::profile::apply_ontology_identity_context_controlled(
                phase,
                &ontology_identifiers,
                origins.is_some(),
                limits,
                &mut poll,
            )
            .map_err(encoded_profile_error)?
        };
        let phase = if let Some(origins) = origins.as_deref() {
            encoded::profile::apply_origin_context_controlled(phase, origins, limits, &mut poll)
                .map_err(encoded_profile_error)?
        } else {
            phase
        };
        if origins.is_some() {
            phase
                .canonical_origin_manifest_json()
                .map_err(encoded_validation_error)
        } else {
            phase
                .canonical_manifest_json()
                .map_err(encoded_validation_error)
        }
    })
}

#[pyfunction(name = "_encoded_named_class_slices_manifest_v1")]
#[pyo3(signature = (*, slices, logical_fingerprint=None))]
fn encoded_named_class_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
    logical_fingerprint: Option<&Bound<'_, PyAny>>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        let namespace = logical_fingerprint
            .map(encoded_logical_fingerprint)
            .transpose()?;
        compile_encoded_slice_program_with_namespace(slices, namespace)?
            .named_classes
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_session_domain_slices_manifest_v1")]
#[pyo3(signature = (*, slices, logical_fingerprint=None))]
fn encoded_session_domain_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
    logical_fingerprint: Option<&Bound<'_, PyAny>>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        let namespace = logical_fingerprint
            .map(encoded_logical_fingerprint)
            .transpose()?;
        compile_encoded_slice_program_with_namespace(slices, namespace)?
            .named_classes
            .canonical_session_domain_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_object_role_slices_manifest_v1")]
#[pyo3(signature = (*, slices))]
fn encoded_object_role_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        compile_encoded_slice_program(slices)?
            .object_roles
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_data_property_slices_manifest_v1")]
#[pyo3(signature = (*, slices))]
fn encoded_data_property_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        compile_encoded_slice_program(slices)?
            .data_roles
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_data_property_inclusions_slices_manifest_v1")]
#[pyo3(signature = (*, slices))]
fn encoded_data_property_inclusions_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        compile_encoded_slice_program(slices)?
            .data_inclusions
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_data_property_hierarchy_slices_manifest_v1")]
#[pyo3(signature = (*, slices))]
fn encoded_data_property_hierarchy_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        compile_encoded_slice_program(slices)?
            .data_role_hierarchy
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_simple_object_role_slices_manifest_v1")]
#[pyo3(signature = (*, slices))]
fn encoded_simple_object_role_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        compile_encoded_slice_program(slices)?
            .simple_roles
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_complex_object_role_slices_manifest_v1")]
#[pyo3(signature = (*, slices))]
fn encoded_complex_object_role_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        compile_encoded_slice_program(slices)?
            .complex_roles
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_role_characteristic_slices_manifest_v1")]
#[pyo3(signature = (*, slices))]
fn encoded_role_characteristic_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        compile_encoded_slice_program(slices)?
            .role_characteristics
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_object_role_hierarchy_slices_manifest_v1")]
#[pyo3(signature = (*, slices))]
fn encoded_object_role_hierarchy_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        compile_encoded_slice_program(slices)?
            .object_role_hierarchy
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_object_role_semantics_slices_manifest_v1")]
#[pyo3(signature = (*, slices))]
fn encoded_object_role_semantics_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        compile_encoded_slice_program(slices)?
            .role_semantics
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_object_role_automata_slices_manifest_v1")]
#[pyo3(signature = (*, slices))]
fn encoded_object_role_automata_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        compile_encoded_slice_program(slices)?
            .role_automata
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_role_model_slices_manifest_v1")]
#[pyo3(signature = (*, slices))]
fn encoded_role_model_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        compile_encoded_slice_program(slices)?
            .role_model
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_role_clause_slices_manifest_v1")]
#[pyo3(signature = (*, slices))]
fn encoded_role_clause_slices_manifest_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        compile_encoded_slice_program(slices)?
            .role_clauses
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_object_role_slices_accepts_v1")]
#[pyo3(signature = (*, slices, target_role_id, word_role_ids))]
fn encoded_object_role_slices_accepts_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
    target_role_id: &Bound<'_, PyAny>,
    word_role_ids: &Bound<'_, PyAny>,
) -> PyResult<bool> {
    contain_encoded_selection(py, || {
        let target_role_id = exact_encoded_role_id(target_role_id, "target role ID")?;
        let word_role_ids = exact_encoded_role_word(word_role_ids)?;
        let program = compile_encoded_slice_program(slices)?;
        program
            .role_automata
            .accepts(
                &program.object_role_hierarchy,
                target_role_id,
                &word_role_ids,
            )
            .map_err(encoded_validation_error)
    })
}

fn contain_encoded_selection<T>(
    py: Python<'_>,
    operation: impl FnOnce() -> NativeResult<T>,
) -> PyResult<T> {
    let result = catch_unwind(AssertUnwindSafe(operation));
    match result {
        Ok(value) => value.map_err(|error| error.into_pyerr(py)),
        Err(_) => Err(NativeError::new(
            ErrorKind::Poisoned,
            "NATIVE_PANIC",
            "native encoded-selection validation panic was contained",
        )
        .into_pyerr(py)),
    }
}

#[pyfunction(name = "_debug_encoded_selection_panic_v1")]
#[allow(clippy::panic)]
fn debug_encoded_selection_panic_v1(py: Python<'_>) -> PyResult<()> {
    contain_encoded_selection(py, || -> NativeResult<()> { std::panic::panic_any(()) })
}

struct EncodedRoleAutomataProgram {
    hierarchy: encoded::object_role_hierarchy::ObjectRoleHierarchyPhase,
    automata: encoded::role_automata::RoleAutomataPhase,
}

fn compile_encoded_role_automata_program<B: encoded::ByteSource>(
    model: &encoded::model::ValidatedModel<B>,
) -> encoded::EncodedResult<EncodedRoleAutomataProgram> {
    let symbols = encoded::symbols::compile_symbol_phase(
        model,
        encoded::symbols::SymbolPhaseLimits::default(),
    )?;
    let roles = encoded::object_roles::compile_object_role_phase(
        &symbols,
        encoded::object_roles::ObjectRolePhaseLimits::default(),
    )?;
    let simple = encoded::simple_roles::compile_simple_role_phase(
        model,
        &symbols,
        &roles,
        encoded::simple_roles::SimpleRolePhaseLimits::default(),
    )?;
    let complex = encoded::complex_roles::compile_complex_role_phase(
        model,
        &symbols,
        &roles,
        encoded::complex_roles::ComplexRolePhaseLimits::default(),
    )?;
    let hierarchy = encoded::object_role_hierarchy::compile_object_role_hierarchy_phase(
        &roles,
        &simple,
        encoded::object_role_hierarchy::ObjectRoleHierarchyLimits::default(),
    )?;
    let semantics = encoded::role_semantics::compile_role_semantics_phase(
        &roles,
        &simple,
        &complex,
        &hierarchy,
        encoded::role_semantics::RoleSemanticsPhaseLimits::default(),
    )?;
    let automata = encoded::role_automata::compile_role_automata_phase(
        &roles,
        &simple,
        &complex,
        &hierarchy,
        &semantics,
        encoded::role_automata::RoleAutomataPhaseLimits::default(),
    )?;
    Ok(EncodedRoleAutomataProgram {
        hierarchy,
        automata,
    })
}

struct EncodedRoleProgram {
    model: encoded::role_model::RoleModelPhase,
    clauses: encoded::role_clauses::RoleClausePhase,
}

fn compile_encoded_role_model_program<B: encoded::ByteSource>(
    model: &encoded::model::ValidatedModel<B>,
) -> encoded::EncodedResult<EncodedRoleProgram> {
    let symbols = encoded::symbols::compile_symbol_phase(
        model,
        encoded::symbols::SymbolPhaseLimits::default(),
    )?;
    let object_roles = encoded::object_roles::compile_object_role_phase(
        &symbols,
        encoded::object_roles::ObjectRolePhaseLimits::default(),
    )?;
    let data_roles = encoded::data_roles::compile_data_role_phase(
        &symbols,
        encoded::data_roles::DataRolePhaseLimits::default(),
    )?;
    let data_inclusions = encoded::data_inclusions::compile_data_inclusion_phase(
        model,
        &symbols,
        &data_roles,
        encoded::data_inclusions::DataInclusionPhaseLimits::default(),
    )?;
    encoded::data_role_hierarchy::compile_data_role_hierarchy_phase(
        &data_roles,
        &data_inclusions,
        encoded::data_role_hierarchy::DataRoleHierarchyLimits::default(),
    )?;
    let simple_roles = encoded::simple_roles::compile_simple_role_phase(
        model,
        &symbols,
        &object_roles,
        encoded::simple_roles::SimpleRolePhaseLimits::default(),
    )?;
    let complex_roles = encoded::complex_roles::compile_complex_role_phase(
        model,
        &symbols,
        &object_roles,
        encoded::complex_roles::ComplexRolePhaseLimits::default(),
    )?;
    let role_characteristics = encoded::role_characteristics::compile_role_characteristic_phase(
        model,
        &symbols,
        &object_roles,
        &data_roles,
        encoded::role_characteristics::RoleCharacteristicPhaseLimits::default(),
    )?;
    let hierarchy = encoded::object_role_hierarchy::compile_object_role_hierarchy_phase(
        &object_roles,
        &simple_roles,
        encoded::object_role_hierarchy::ObjectRoleHierarchyLimits::default(),
    )?;
    let semantics = encoded::role_semantics::compile_role_semantics_phase(
        &object_roles,
        &simple_roles,
        &complex_roles,
        &hierarchy,
        encoded::role_semantics::RoleSemanticsPhaseLimits::default(),
    )?;
    let automata = encoded::role_automata::compile_role_automata_phase(
        &object_roles,
        &simple_roles,
        &complex_roles,
        &hierarchy,
        &semantics,
        encoded::role_automata::RoleAutomataPhaseLimits::default(),
    )?;
    let role_model = encoded::role_model::compile_role_model_phase(
        &object_roles,
        &data_roles,
        &simple_roles,
        &data_inclusions,
        &complex_roles,
        &hierarchy,
        &semantics,
        &automata,
        encoded::role_model::RoleModelPhaseLimits::default(),
    )?;
    let role_clauses = encoded::role_clauses::compile_role_clause_phase(
        &object_roles,
        &data_roles,
        &simple_roles,
        &data_inclusions,
        &complex_roles,
        &role_characteristics,
        &role_model,
        encoded::role_clauses::RoleClausePhaseLimits::default(),
    )?;
    Ok(EncodedRoleProgram {
        model: role_model,
        clauses: role_clauses,
    })
}

#[pyfunction(name = "_encoded_symbol_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_symbol_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let phase = encoded::symbols::compile_symbol_phase(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        phase
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    }));
    match result {
        Ok(value) => value.map_err(|error| error.into_pyerr(py)),
        Err(_) => Err(NativeError::new(
            ErrorKind::Poisoned,
            "NATIVE_PANIC",
            "native encoded-symbol manifest panic was contained",
        )
        .into_pyerr(py)),
    }
}

#[pyfunction(name = "_encoded_object_role_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_object_role_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let symbols = encoded::symbols::compile_symbol_phase(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let phase = encoded::object_roles::compile_object_role_phase(
            &symbols,
            encoded::object_roles::ObjectRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        phase
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    }));
    match result {
        Ok(value) => value.map_err(|error| error.into_pyerr(py)),
        Err(_) => Err(NativeError::new(
            ErrorKind::Poisoned,
            "NATIVE_PANIC",
            "native encoded object-role manifest panic was contained",
        )
        .into_pyerr(py)),
    }
}

#[pyfunction(name = "_encoded_data_property_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_data_property_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let symbols = encoded::symbols::compile_symbol_phase(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let phase = encoded::data_roles::compile_data_role_phase(
            &symbols,
            encoded::data_roles::DataRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        phase
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    }));
    match result {
        Ok(value) => value.map_err(|error| error.into_pyerr(py)),
        Err(_) => Err(NativeError::new(
            ErrorKind::Poisoned,
            "NATIVE_PANIC",
            "native encoded data-property manifest panic was contained",
        )
        .into_pyerr(py)),
    }
}

#[pyfunction(name = "_encoded_data_property_inclusions_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_data_property_inclusions_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let symbols = encoded::symbols::compile_symbol_phase(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let roles = encoded::data_roles::compile_data_role_phase(
            &symbols,
            encoded::data_roles::DataRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        encoded::data_inclusions::compile_data_inclusion_phase(
            &model,
            &symbols,
            &roles,
            encoded::data_inclusions::DataInclusionPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?
        .canonical_manifest_json()
        .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_data_property_hierarchy_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_data_property_hierarchy_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let symbols = encoded::symbols::compile_symbol_phase(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let roles = encoded::data_roles::compile_data_role_phase(
            &symbols,
            encoded::data_roles::DataRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let inclusions = encoded::data_inclusions::compile_data_inclusion_phase(
            &model,
            &symbols,
            &roles,
            encoded::data_inclusions::DataInclusionPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        encoded::data_role_hierarchy::compile_data_role_hierarchy_phase(
            &roles,
            &inclusions,
            encoded::data_role_hierarchy::DataRoleHierarchyLimits::default(),
        )
        .map_err(encoded_validation_error)?
        .canonical_manifest_json()
        .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_simple_object_role_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_simple_object_role_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let symbols = encoded::symbols::compile_symbol_phase(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let roles = encoded::object_roles::compile_object_role_phase(
            &symbols,
            encoded::object_roles::ObjectRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let phase = encoded::simple_roles::compile_simple_role_phase(
            &model,
            &symbols,
            &roles,
            encoded::simple_roles::SimpleRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        phase
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    }));
    match result {
        Ok(value) => value.map_err(|error| error.into_pyerr(py)),
        Err(_) => Err(NativeError::new(
            ErrorKind::Poisoned,
            "NATIVE_PANIC",
            "native encoded simple-role manifest panic was contained",
        )
        .into_pyerr(py)),
    }
}

#[pyfunction(name = "_encoded_complex_object_role_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_complex_object_role_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let symbols = encoded::symbols::compile_symbol_phase(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let roles = encoded::object_roles::compile_object_role_phase(
            &symbols,
            encoded::object_roles::ObjectRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let phase = encoded::complex_roles::compile_complex_role_phase(
            &model,
            &symbols,
            &roles,
            encoded::complex_roles::ComplexRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        phase
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    }));
    match result {
        Ok(value) => value.map_err(|error| error.into_pyerr(py)),
        Err(_) => Err(NativeError::new(
            ErrorKind::Poisoned,
            "NATIVE_PANIC",
            "native encoded complex-role manifest panic was contained",
        )
        .into_pyerr(py)),
    }
}

#[pyfunction(name = "_encoded_object_role_hierarchy_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_object_role_hierarchy_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let symbols = encoded::symbols::compile_symbol_phase(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let roles = encoded::object_roles::compile_object_role_phase(
            &symbols,
            encoded::object_roles::ObjectRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let simple = encoded::simple_roles::compile_simple_role_phase(
            &model,
            &symbols,
            &roles,
            encoded::simple_roles::SimpleRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let phase = encoded::object_role_hierarchy::compile_object_role_hierarchy_phase(
            &roles,
            &simple,
            encoded::object_role_hierarchy::ObjectRoleHierarchyLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        phase
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    }));
    match result {
        Ok(value) => value.map_err(|error| error.into_pyerr(py)),
        Err(_) => Err(NativeError::new(
            ErrorKind::Poisoned,
            "NATIVE_PANIC",
            "native encoded object-role hierarchy manifest panic was contained",
        )
        .into_pyerr(py)),
    }
}

#[pyfunction(name = "_encoded_object_role_semantics_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_object_role_semantics_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let symbols = encoded::symbols::compile_symbol_phase(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let roles = encoded::object_roles::compile_object_role_phase(
            &symbols,
            encoded::object_roles::ObjectRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let simple = encoded::simple_roles::compile_simple_role_phase(
            &model,
            &symbols,
            &roles,
            encoded::simple_roles::SimpleRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let complex = encoded::complex_roles::compile_complex_role_phase(
            &model,
            &symbols,
            &roles,
            encoded::complex_roles::ComplexRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let hierarchy = encoded::object_role_hierarchy::compile_object_role_hierarchy_phase(
            &roles,
            &simple,
            encoded::object_role_hierarchy::ObjectRoleHierarchyLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let phase = encoded::role_semantics::compile_role_semantics_phase(
            &roles,
            &simple,
            &complex,
            &hierarchy,
            encoded::role_semantics::RoleSemanticsPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        phase
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    }));
    match result {
        Ok(value) => value.map_err(|error| error.into_pyerr(py)),
        Err(_) => Err(NativeError::new(
            ErrorKind::Poisoned,
            "NATIVE_PANIC",
            "native encoded object-role semantics manifest panic was contained",
        )
        .into_pyerr(py)),
    }
}

#[pyfunction(name = "_encoded_object_role_automata_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_object_role_automata_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        compile_encoded_role_automata_program(&model)
            .map_err(encoded_validation_error)?
            .automata
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_role_characteristic_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_role_characteristic_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let symbols = encoded::symbols::compile_symbol_phase(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let object_roles = encoded::object_roles::compile_object_role_phase(
            &symbols,
            encoded::object_roles::ObjectRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let data_roles = encoded::data_roles::compile_data_role_phase(
            &symbols,
            encoded::data_roles::DataRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        encoded::role_characteristics::compile_role_characteristic_phase(
            &model,
            &symbols,
            &object_roles,
            &data_roles,
            encoded::role_characteristics::RoleCharacteristicPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?
        .canonical_manifest_json()
        .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_role_model_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_role_model_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        compile_encoded_role_model_program(&model)
            .map_err(encoded_validation_error)?
            .model
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_role_clause_manifest_v1")]
#[pyo3(signature = (*, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_role_clause_manifest_v1(
    py: Python<'_>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    contain_encoded_selection(py, || {
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        compile_encoded_role_model_program(&model)
            .map_err(encoded_validation_error)?
            .clauses
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_object_role_accepts_v1")]
#[pyo3(signature = (*, target_role_id, word_role_ids, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_object_role_accepts_v1(
    py: Python<'_>,
    target_role_id: &Bound<'_, PyAny>,
    word_role_ids: &Bound<'_, PyAny>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<bool> {
    contain_encoded_selection(py, || {
        let target_role_id = exact_encoded_role_id(target_role_id, "target role ID")?;
        let word_role_ids = exact_encoded_role_word(word_role_ids)?;
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let program =
            compile_encoded_role_automata_program(&model).map_err(encoded_validation_error)?;
        program
            .automata
            .accepts(&program.hierarchy, target_role_id, &word_role_ids)
            .map_err(encoded_validation_error)
    })
}

#[pyfunction(name = "_encoded_named_class_manifest_v1")]
#[pyo3(signature = (*, logical_fingerprint, root_kinds, root_ids, node_tags, node_field_offsets, field_kinds, field_values, field_lengths, item_kinds, item_values, item_lengths, scalar_bytes))]
#[allow(clippy::too_many_arguments)]
fn encoded_named_class_manifest_v1(
    py: Python<'_>,
    logical_fingerprint: &Bound<'_, PyAny>,
    root_kinds: &Bound<'_, PyAny>,
    root_ids: &Bound<'_, PyAny>,
    node_tags: &Bound<'_, PyAny>,
    node_field_offsets: &Bound<'_, PyAny>,
    field_kinds: &Bound<'_, PyAny>,
    field_values: &Bound<'_, PyAny>,
    field_lengths: &Bound<'_, PyAny>,
    item_kinds: &Bound<'_, PyAny>,
    item_values: &Bound<'_, PyAny>,
    item_lengths: &Bound<'_, PyAny>,
    scalar_bytes: &Bound<'_, PyAny>,
) -> PyResult<Vec<u8>> {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let definition_namespace = encoded_logical_fingerprint(logical_fingerprint)?;
        let columns = borrowed_encoded_columns(
            root_kinds,
            root_ids,
            node_tags,
            node_field_offsets,
            field_kinds,
            field_values,
            field_lengths,
            item_kinds,
            item_values,
            item_lengths,
            scalar_bytes,
        )?;
        let model = encoded::model::ValidatedModel::new(columns, encoded::EncodedLimits::default())
            .map_err(encoded_validation_error)?;
        let symbols = encoded::symbols::compile_symbol_phase(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let object_roles = encoded::object_roles::compile_object_role_phase(
            &symbols,
            encoded::object_roles::ObjectRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let data_roles = encoded::data_roles::compile_data_role_phase(
            &symbols,
            encoded::data_roles::DataRolePhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        let phase = encoded::named_classes::compile_named_class_phase_with_role_domains_scoped_and_namespace(
            &model,
            &symbols,
            &object_roles,
            &data_roles,
            &[],
            definition_namespace,
            encoded::named_classes::NamedClassPhaseLimits::default(),
        )
        .map_err(encoded_validation_error)?;
        phase
            .canonical_manifest_json()
            .map_err(encoded_validation_error)
    }));
    match result {
        Ok(value) => value.map_err(|error| error.into_pyerr(py)),
        Err(_) => Err(NativeError::new(
            ErrorKind::Poisoned,
            "NATIVE_PANIC",
            "native encoded named-class manifest panic was contained",
        )
        .into_pyerr(py)),
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

fn poll_encoded_session_checkpoint(
    cancellation: &Arc<CancellationState>,
    checkpoint: &mut u64,
    cancel_at_checkpoint: Option<u64>,
    phase: &'static str,
) -> NativeResult<()> {
    cancellation.poll()?;
    *checkpoint = checkpoint
        .checked_add(1)
        .ok_or_else(|| NativeError::invariant("encoded session checkpoint count overflowed"))?;
    if cancel_at_checkpoint == Some(*checkpoint) {
        return Err(NativeError::new(
            ErrorKind::Cancelled,
            "REASONER_INTERRUPTED",
            "native encoded session construction was interrupted at a test checkpoint",
        )
        .with_context("checkpoint", checkpoint.to_string())
        .with_context("phase", phase));
    }
    Ok(())
}

fn validate_deferred_metadata(metadata: &input_wire::OntologyMetadata) -> NativeResult<()> {
    let placeholders_are_zero = metadata
        .ontology_fingerprint
        .iter()
        .chain(&metadata.structural_fingerprint.digest)
        .chain(&metadata.logical_fingerprint.digest)
        .chain(&metadata.signature_fingerprint.digest)
        .all(|byte| *byte == 0);
    if !placeholders_are_zero
        || metadata.structural_fingerprint.schema != 1
        || metadata.logical_fingerprint.schema != 1
        || metadata.signature_fingerprint.schema != 1
        || metadata.program_sha256.iter().any(|byte| *byte != 0)
    {
        return Err(encoded_slice_invalid(
            "versioned deferred metadata does not contain canonical schema-1 placeholders",
        ));
    }
    Ok(())
}

fn deferred_compiler_cache_key(
    template: &[u8],
    metadata: &input_wire::OntologyMetadata,
    config: &DecodedConfig,
) -> NativeResult<[u8; 32]> {
    let expected = serde_json::json!({
        "compatibility_id": HERMIT_COMPATIBILITY_ID,
        "compiler_schema": COMPILER_CACHE_SCHEMA_VERSION,
        "config": {
            "backend": backend_choice_name(config.backend),
            "blocking": blocking_choice_name(config.blocking),
            "buffer_changes": config.buffer_changes,
            "deterministic": config.deterministic,
            "disjunction_learning": config.disjunction_learning,
            "existentials": existential_choice_name(config.existentials),
            "force_quasi_order_classification": config.force_quasi_order_classification,
            "fresh_entities": fresh_entity_choice_name(config.fresh_entities),
            "individual_grouping": individual_grouping_choice_name(config.individual_grouping),
            "max_memory_bytes": config.max_memory_bytes,
            "timeout": config.timeout_seconds,
            "unsupported_datatypes": unsupported_datatype_choice_name(
                config.unsupported_datatypes
            ),
            "workers": config.workers,
        },
        "core": {
            "adapter": metadata.core_adapter_protocol_version,
            "api": [
                metadata.core_api_version.0,
                metadata.core_api_version.1,
            ],
            "model": metadata.core_model_schema_version,
            "package": metadata.core_package_version,
            "wire": [
                metadata.core_wire_format_version.0,
                metadata.core_wire_format_version.1,
            ],
        },
        "logical_fingerprint": LOGICAL_FINGERPRINT_SENTINEL,
        "signature_fingerprint": SIGNATURE_FINGERPRINT_SENTINEL,
    });
    let parsed: serde_json::Value = serde_json::from_slice(template)
        .map_err(|_| encoded_slice_invalid("deferred compiler-cache template is not valid JSON"))?;
    if parsed != expected {
        return Err(encoded_slice_invalid(
            "deferred compiler-cache template disagrees with metadata or configuration",
        ));
    }
    let mut rust_canonical = serde_json::to_vec(&expected)
        .map_err(|_| NativeError::invariant("compiler-cache template serialization failed"))?;
    if let Some(timeout) = config.timeout_seconds {
        let timeout_range = timeout_token_range(&rust_canonical)?;
        rust_canonical.splice(timeout_range, python_float_token(timeout)?.bytes());
    }
    if template != rust_canonical {
        return Err(encoded_slice_invalid(
            "deferred compiler-cache template is not canonical JSON",
        ));
    }

    let mut payload = template.to_vec();
    replace_exact_sentinel(
        &mut payload,
        LOGICAL_FINGERPRINT_SENTINEL.as_bytes(),
        hex_digest(&metadata.logical_fingerprint.digest).as_bytes(),
        "logical",
    )?;
    replace_exact_sentinel(
        &mut payload,
        SIGNATURE_FINGERPRINT_SENTINEL.as_bytes(),
        hex_digest(&metadata.signature_fingerprint.digest).as_bytes(),
        "signature",
    )?;
    let mut hasher = Sha256::new();
    hasher.update(COMPILER_CACHE_DOMAIN);
    hasher.update(payload);
    Ok(hasher.finalize().into())
}

fn timeout_token_range(bytes: &[u8]) -> NativeResult<std::ops::Range<usize>> {
    const NEEDLE: &[u8] = b"\"timeout\":";
    let start = bytes
        .windows(NEEDLE.len())
        .position(|window| window == NEEDLE)
        .ok_or_else(|| encoded_slice_invalid("compiler-cache timeout field is absent"))?;
    if bytes[start + NEEDLE.len()..]
        .windows(NEEDLE.len())
        .any(|window| window == NEEDLE)
    {
        return Err(encoded_slice_invalid(
            "compiler-cache timeout field is duplicated",
        ));
    }
    let value_start = start + NEEDLE.len();
    let relative_end = bytes[value_start..]
        .iter()
        .position(|byte| *byte == b',')
        .ok_or_else(|| encoded_slice_invalid("compiler-cache timeout field is unterminated"))?;
    let value_end = value_start + relative_end;
    if value_end == value_start {
        return Err(encoded_slice_invalid(
            "compiler-cache timeout field is empty",
        ));
    }
    Ok(value_start..value_end)
}

fn python_float_token(value: f64) -> NativeResult<String> {
    if !value.is_finite() || value <= 0.0 {
        return Err(encoded_slice_invalid(
            "compiler-cache timeout is not a finite positive float",
        ));
    }
    let ryu = serde_json::to_string(&value)
        .map_err(|_| NativeError::invariant("compiler-cache timeout serialization failed"))?;
    let (mantissa, explicit_exponent) = match ryu.find(['e', 'E']) {
        Some(index) => {
            let (mantissa, exponent) = ryu.split_at(index);
            let exponent = exponent[1..]
                .parse::<i32>()
                .map_err(|_| NativeError::invariant("serialized timeout exponent is malformed"))?;
            (mantissa, exponent)
        }
        None => (ryu.as_str(), 0),
    };
    let unsigned = mantissa.strip_prefix('-').unwrap_or(mantissa);
    let decimal_index = unsigned.find('.').unwrap_or(unsigned.len());
    let mut digits = unsigned.replace('.', "");
    while digits.len() > 1 && digits.ends_with('0') {
        digits.pop();
    }
    let first_nonzero = digits.find(|character| character != '0').ok_or_else(|| {
        NativeError::invariant("serialized positive timeout has no nonzero digit")
    })?;
    if first_nonzero != 0 {
        digits.drain(..first_nonzero);
    }
    let decimal_exponent = i32::try_from(decimal_index)
        .and_then(|index| i32::try_from(first_nonzero).map(|leading| index - leading - 1))
        .map_err(|_| NativeError::invariant("timeout decimal exponent exceeds i32"))?
        .checked_add(explicit_exponent)
        .ok_or_else(|| NativeError::invariant("timeout decimal exponent overflowed"))?;
    let negative = mantissa.starts_with('-');
    let mut output = String::new();
    if negative {
        output.push('-');
    }
    if !(-4..16).contains(&decimal_exponent) {
        output.push(char::from(digits.as_bytes()[0]));
        if digits.len() > 1 {
            output.push('.');
            output.push_str(&digits[1..]);
        }
        output.push('e');
        output.push(if decimal_exponent < 0 { '-' } else { '+' });
        let magnitude = decimal_exponent.unsigned_abs();
        if magnitude < 10 {
            output.push('0');
        }
        output.push_str(&magnitude.to_string());
        return Ok(output);
    }
    let point = decimal_exponent + 1;
    if point <= 0 {
        output.push_str("0.");
        output.extend(std::iter::repeat_n(
            '0',
            usize::try_from(-point)
                .map_err(|_| NativeError::invariant("timeout zero prefix exceeds usize"))?,
        ));
        output.push_str(&digits);
    } else {
        let point = usize::try_from(point)
            .map_err(|_| NativeError::invariant("timeout decimal point exceeds usize"))?;
        if point >= digits.len() {
            output.push_str(&digits);
            output.extend(std::iter::repeat_n('0', point - digits.len()));
            output.push_str(".0");
        } else {
            output.push_str(&digits[..point]);
            output.push('.');
            output.push_str(&digits[point..]);
        }
    }
    Ok(output)
}

fn replace_exact_sentinel(
    payload: &mut [u8],
    sentinel: &[u8],
    replacement: &[u8],
    name: &'static str,
) -> NativeResult<()> {
    if sentinel.len() != replacement.len() {
        return Err(NativeError::invariant(
            "compiler-cache fingerprint replacement width changed",
        ));
    }
    let mut matches = payload
        .windows(sentinel.len())
        .enumerate()
        .filter_map(|(index, window)| (window == sentinel).then_some(index));
    let index = matches.next().ok_or_else(|| {
        encoded_slice_invalid(format!("deferred compiler-cache {name} sentinel is absent"))
    })?;
    if matches.next().is_some() {
        return Err(encoded_slice_invalid(format!(
            "deferred compiler-cache {name} sentinel is duplicated"
        )));
    }
    payload[index..index + replacement.len()].copy_from_slice(replacement);
    Ok(())
}

const fn backend_choice_name(value: input_wire::BackendChoice) -> &'static str {
    match value {
        input_wire::BackendChoice::Auto => "auto",
        input_wire::BackendChoice::Python => "python",
        input_wire::BackendChoice::Native => "native",
        input_wire::BackendChoice::Verify => "verify",
    }
}

const fn blocking_choice_name(value: input_wire::BlockingChoice) -> &'static str {
    match value {
        input_wire::BlockingChoice::Auto => "auto",
        input_wire::BlockingChoice::Anywhere => "anywhere",
        input_wire::BlockingChoice::ValidatedAnywhere => "validated_anywhere",
        input_wire::BlockingChoice::Ancestor => "ancestor",
    }
}

const fn existential_choice_name(value: input_wire::ExistentialChoice) -> &'static str {
    match value {
        input_wire::ExistentialChoice::Auto => "auto",
        input_wire::ExistentialChoice::CreationOrder => "creation_order",
        input_wire::ExistentialChoice::IndividualReuse => "individual_reuse",
    }
}

const fn fresh_entity_choice_name(value: input_wire::FreshEntityChoice) -> &'static str {
    match value {
        input_wire::FreshEntityChoice::Disallow => "disallow",
        input_wire::FreshEntityChoice::Allow => "allow",
    }
}

const fn individual_grouping_choice_name(
    value: input_wire::IndividualGroupingChoice,
) -> &'static str {
    match value {
        input_wire::IndividualGroupingChoice::BySameAs => "by_same_as",
        input_wire::IndividualGroupingChoice::ByName => "by_name",
    }
}

const fn unsupported_datatype_choice_name(
    value: input_wire::UnsupportedDatatypeChoice,
) -> &'static str {
    match value {
        input_wire::UnsupportedDatatypeChoice::Error => "error",
        input_wire::UnsupportedDatatypeChoice::IgnoreWithWarning => "ignore_with_warning",
    }
}

#[allow(clippy::too_many_arguments)]
fn compile_encoded_session_phases<B: encoded::ByteSource>(
    slices: &[EncodedSliceInput<B>],
    namespace: Option<[u8; 32]>,
    fingerprint_request: Option<(
        &encoded::fingerprints::StructuralContextEvidence,
        encoded::fingerprints::StructuralFingerprintMode,
    )>,
    max_owned_bytes: Option<usize>,
    unsupported_datatypes: encoded::profile::ProfileUnsupportedDatatypePolicy,
    ontology_identifiers: &[encoded::profile::ProfileOntologyIdentifier],
    origins: Option<&[encoded::profile::ProfileOrigin]>,
    validate_profile: bool,
    cancellation_state: &Arc<CancellationState>,
    checkpoint: &mut u64,
    cancel_at_checkpoint: Option<u64>,
) -> NativeResult<(
    encoded::permanent_program::EncodedSliceProgram,
    Option<encoded::fingerprints::ViewFingerprints>,
)> {
    if validate_profile {
        let mut poll = |phase: &'static str| {
            poll_encoded_session_checkpoint(
                cancellation_state,
                checkpoint,
                cancel_at_checkpoint,
                phase,
            )
        };
        let profile = compile_encoded_profile_slice_inputs_controlled(
            slices,
            unsupported_datatypes,
            &mut poll,
        )?;
        let profile = apply_encoded_profile_contexts_controlled(
            profile,
            ontology_identifiers,
            origins,
            encoded::profile::ProfilePhaseLimits::default(),
            &mut poll,
        )?;
        ensure_encoded_profile_conforms(profile.conforms, &profile.issues)?;
    }
    let mut poll = |phase: &'static str| {
        poll_encoded_session_checkpoint(cancellation_state, checkpoint, cancel_at_checkpoint, phase)
    };
    compile_encoded_slice_program_inputs_with_fingerprints_controlled(
        slices,
        namespace,
        fingerprint_request,
        max_owned_bytes,
        &mut poll,
    )
}

#[allow(clippy::too_many_arguments)]
fn finish_encoded_session_construction(
    phases: encoded::permanent_program::EncodedSliceProgram,
    fingerprints: Option<encoded::fingerprints::ViewFingerprints>,
    compiler_cache_template: Option<Vec<u8>>,
    mut metadata: input_wire::OntologyMetadata,
    config: DecodedConfig,
    cancellation_state: Arc<CancellationState>,
    mut checkpoint: u64,
    cancel_at_checkpoint: Option<u64>,
    max_owned_bytes: Option<usize>,
    compiler_gil_released: bool,
) -> NativeResult<NativeSession> {
    match (fingerprints, compiler_cache_template) {
        (Some(fingerprints), Some(template)) => {
            metadata.structural_fingerprint.digest = fingerprints.structural;
            metadata.logical_fingerprint.digest = fingerprints.logical;
            metadata.signature_fingerprint.digest = fingerprints.signature;
            metadata.ontology_fingerprint =
                deferred_compiler_cache_key(&template, &metadata, &config)?;
        }
        (None, None) => {}
        _ => {
            return Err(NativeError::invariant(
                "deferred fingerprint results lost their compiler-cache template",
            ));
        }
    }
    let mut assembly_limits = encoded::permanent_program::PermanentProgramLimits::default();
    if let Some(maximum) = max_owned_bytes {
        assembly_limits.max_owned_bytes = maximum;
    }
    let assembled = {
        let mut poll = |phase: &'static str| {
            poll_encoded_session_checkpoint(
                &cancellation_state,
                &mut checkpoint,
                cancel_at_checkpoint,
                phase,
            )
        };
        let assembled = encoded::permanent_program::assemble_encoded_permanent_program(
            phases,
            assembly_limits,
            &mut poll,
        )
        .map_err(encoded_permanent_error)?;
        poll("encoded-session-publication")?;
        assembled
    };
    let mut poll = |phase: &'static str| {
        poll_encoded_session_checkpoint(
            &cancellation_state,
            &mut checkpoint,
            cancel_at_checkpoint,
            phase,
        )
    };
    let assembled_sha256 = assembled
        .semantic_sha256_controlled(&mut poll)
        .map_err(encoded_permanent_error)?;
    if metadata.program_sha256.iter().all(|byte| *byte == 0) {
        metadata.program_sha256 = assembled_sha256;
    } else if metadata.program_sha256 != assembled_sha256 {
        return Err(NativeError::new(
            ErrorKind::Wire,
            "NATIVE_ENCODED_PARITY_MISMATCH",
            "encoded permanent-program digest differs from its metadata",
        )
        .with_context("section", "program_sha256"));
    }
    let compiler_digest = {
        let mut poll = |phase: &'static str| {
            poll_encoded_session_checkpoint(
                &cancellation_state,
                &mut checkpoint,
                cancel_at_checkpoint,
                phase,
            )
        };
        assembled
            .compiler_sha256_controlled(&metadata, &mut poll)
            .map_err(encoded_permanent_error)?
    };
    let ontology = DecodedOntology {
        metadata,
        program: assembled.program,
        declared_entities: assembled.declared_entities,
        named_individuals: assembled.named_individuals,
    };
    construct_native_session(
        ontology,
        config,
        cancellation_state,
        Some(compiler_digest),
        compiler_gil_released,
    )
}

/// Private direct encoded-program constructor behind the advertised coarse
/// encoded-session capability.
#[pyfunction(name = "_create_encoded_session_v1")]
#[pyo3(signature = (
    *,
    slices,
    metadata,
    config,
    cancellation,
    validate_profile=true,
    deferred_fingerprints=None,
    ontology_identity_context=None,
    origin_context=None,
    max_owned_bytes=None,
    cancel_at_checkpoint=None
))]
#[allow(clippy::too_many_arguments)]
fn create_encoded_session_v1(
    py: Python<'_>,
    slices: &Bound<'_, PyAny>,
    metadata: &Bound<'_, PyBytes>,
    config: &Bound<'_, PyBytes>,
    cancellation: PyRef<'_, CancellationHandle>,
    validate_profile: bool,
    deferred_fingerprints: Option<&Bound<'_, PyAny>>,
    ontology_identity_context: Option<&Bound<'_, PyAny>>,
    origin_context: Option<&Bound<'_, PyAny>>,
    max_owned_bytes: Option<usize>,
    cancel_at_checkpoint: Option<u64>,
) -> PyResult<NativeSession> {
    let result = catch_unwind(AssertUnwindSafe(|| {
        if cancel_at_checkpoint == Some(0) {
            return Err(encoded_slice_invalid(
                "encoded session cancellation checkpoint must be positive",
            ));
        }
        let limits = DecodeLimits::default();
        let metadata = decode_ontology_metadata(&copy_capped_bytes(
            metadata,
            MAX_ENCODED_SESSION_METADATA_BYTES,
            "encoded session metadata",
        )?)
        .map_err(map_input_wire_error)?;
        validate_core_metadata(&metadata)?;
        let config = decode_config(
            copy_capped_bytes(config, limits.max_wire_bytes, "configuration wire")?,
            &limits,
        )
        .map_err(map_input_wire_error)?;
        let deferred_fingerprints = decode_deferred_fingerprint_request(deferred_fingerprints)?;
        if deferred_fingerprints.is_some() {
            validate_deferred_metadata(&metadata)?;
        }
        let cancellation_state = cancellation.state();
        if !validate_profile && (ontology_identity_context.is_some() || origin_context.is_some()) {
            return Err(encoded_slice_invalid(
                "encoded profile contexts require profile validation",
            ));
        }
        let mut checkpoint = 0_u64;
        let (ontology_identifiers, origins) = if validate_profile {
            let mut poll = |phase: &'static str| {
                poll_encoded_session_checkpoint(
                    &cancellation_state,
                    &mut checkpoint,
                    cancel_at_checkpoint,
                    phase,
                )
            };
            (
                decode_profile_ontology_identity_context(
                    ontology_identity_context,
                    encoded::profile::ProfilePhaseLimits::default(),
                    &mut poll,
                )?,
                decode_profile_origin_context(
                    origin_context,
                    encoded::profile::ProfilePhaseLimits::default(),
                    &mut poll,
                )?,
            )
        } else {
            (Vec::new(), None)
        };
        let namespace = deferred_fingerprints
            .is_none()
            .then_some(metadata.logical_fingerprint.digest);
        let unsupported_datatypes =
            encoded_profile_policy_from_config(config.unsupported_datatypes);
        let borrowed_leases = prepare_borrowed_encoded_slices(slices)?;
        if let Some(retained_leases) = retain_encoded_slice_leases(&borrowed_leases)? {
            let retained_inputs = retained_encoded_slice_inputs(&retained_leases)?;
            return py.detach(move || {
                let (phases, fingerprints) = compile_encoded_session_phases(
                    &retained_inputs,
                    namespace,
                    deferred_fingerprints
                        .as_ref()
                        .map(|request| (&request.context, request.structural_mode)),
                    max_owned_bytes,
                    unsupported_datatypes,
                    &ontology_identifiers,
                    origins.as_deref(),
                    validate_profile,
                    &cancellation_state,
                    &mut checkpoint,
                    cancel_at_checkpoint,
                )?;
                finish_encoded_session_construction(
                    phases,
                    fingerprints,
                    deferred_fingerprints.map(|request| request.compiler_cache_template),
                    metadata,
                    config,
                    cancellation_state,
                    checkpoint,
                    cancel_at_checkpoint,
                    max_owned_bytes,
                    true,
                )
            });
        }
        let borrowed_inputs = borrowed_encoded_slice_inputs(&borrowed_leases)?;
        let (phases, fingerprints) = compile_encoded_session_phases(
            &borrowed_inputs,
            namespace,
            deferred_fingerprints
                .as_ref()
                .map(|request| (&request.context, request.structural_mode)),
            max_owned_bytes,
            unsupported_datatypes,
            &ontology_identifiers,
            origins.as_deref(),
            validate_profile,
            &cancellation_state,
            &mut checkpoint,
            cancel_at_checkpoint,
        )?;
        py.detach(move || {
            finish_encoded_session_construction(
                phases,
                fingerprints,
                deferred_fingerprints.map(|request| request.compiler_cache_template),
                metadata,
                config,
                cancellation_state,
                checkpoint,
                cancel_at_checkpoint,
                max_owned_bytes,
                false,
            )
        })
    }));
    match result {
        Ok(value) => value.map_err(|error: NativeError| error.into_pyerr(py)),
        Err(_) => Err(NativeError::new(
            ErrorKind::Poisoned,
            "NATIVE_PANIC",
            "native encoded session-construction panic was contained",
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
    let limits = DecodeLimits::default();
    let copied = catch_unwind(AssertUnwindSafe(|| {
        Ok((
            copy_capped_bytes(ir, limits.max_wire_bytes, "ontology wire")?,
            copy_capped_bytes(config, limits.max_wire_bytes, "configuration wire")?,
        ))
    }));
    let (ontology_wire, config_wire) = match copied {
        Ok(value) => value.map_err(|error: NativeError| error.into_pyerr(py))?,
        Err(_) => {
            return Err(NativeError::new(
                ErrorKind::Poisoned,
                "NATIVE_PANIC",
                "native session input-copy panic was contained",
            )
            .into_pyerr(py));
        }
    };
    let cancellation_state = cancellation.state();
    let result = catch_unwind(AssertUnwindSafe(|| {
        py.detach(move || {
            let (ontology, config) = decode_session_inputs(ontology_wire, config_wire, &limits)?;
            construct_native_session(ontology, config, cancellation_state, None, false)
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

fn construct_native_session(
    ontology: DecodedOntology,
    config: DecodedConfig,
    cancellation_state: Arc<CancellationState>,
    compiler_digest: Option<[u8; 32]>,
    encoded_compiler_gil_released: bool,
) -> NativeResult<NativeSession> {
    // Session construction preserves the WPR0 lifecycle contract: operation timeout and
    // observed-memory failures are surfaced by the first semantic operation, not while the
    // immutable permanent program is being installed.
    let construction_control = CancellationHandle::from_options(None, None)?.state();
    let ontology = Arc::new(ontology);
    let rules = load_permanent_rule_state(
        &ontology,
        Arc::clone(&construction_control),
        config.disjunction_learning,
        config.existentials,
        config.blocking,
    )?;
    let tableau = ProductionTableau::new(
        Arc::clone(&ontology),
        config.clone(),
        Arc::clone(&cancellation_state),
        rules,
    )?;
    let scheduler = SessionScheduler::new(tableau, SessionLimits::default())?;
    Ok(NativeSession {
        compiler_digest,
        encoded_compiler_gil_released,
        control: Arc::new(SessionControl {
            owner_pid: std::process::id(),
            closed: AtomicBool::new(false),
            busy: AtomicBool::new(false),
            poisoned: AtomicBool::new(false),
            cancellation: cancellation_state,
            owned: Mutex::new(Some(SessionOwned {
                ontology,
                config,
                scheduler,
                classification: ClassificationCache::new(),
                realization: RealizationCache::new(),
                events: VecDeque::with_capacity(EVENT_CAPACITY),
            })),
        }),
    })
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

fn decode_session_inputs(
    ontology: Vec<u8>,
    config: Vec<u8>,
    limits: &DecodeLimits,
) -> NativeResult<(DecodedOntology, DecodedConfig)> {
    let ontology = decode_ontology(ontology, limits).map_err(map_input_wire_error)?;
    validate_core_metadata(&ontology.metadata)?;
    let config = decode_config(config, limits).map_err(map_input_wire_error)?;
    Ok((ontology, config))
}

fn decode_session_query(
    wire: Vec<u8>,
    limits: &DecodeLimits,
) -> NativeResult<SessionQuery<DecodedQuery>> {
    let query = decode_query(wire, limits).map_err(map_input_wire_error)?;
    Ok(SessionQuery::new(QueryKey::new(query.query_hash), query))
}

fn delta_wire_outcome(delta: &DecodedDelta) -> DeltaWireOutcome {
    if delta.result_program_sha256 == delta.base_program_sha256
        && delta.fact_additions.is_empty()
        && delta.fact_removals.is_empty()
    {
        DeltaWireOutcome::AppliedIncrementally
    } else {
        DeltaWireOutcome::RebuildRequired
    }
}

fn check_wire_result(result: SessionCheckResult, elapsed: Duration) -> CheckWireResult {
    CheckWireResult {
        satisfiable: result.satisfiable,
        statistics: CheckStatistics {
            elapsed_nanoseconds: u64::try_from(elapsed.as_nanos()).unwrap_or(u64::MAX),
            nodes: 0,
            facts: result.statistics.delta_rows,
            branches: result.statistics.disjunction_actions,
            backtracks: result.statistics.backtracks,
            merges: result.statistics.nominal_actions,
            datatype_checks: result.statistics.datatype_components,
        },
    }
}

fn map_input_wire_error(error: InputWireError) -> NativeError {
    let kind = match error.code {
        "NATIVE_INPUT_VERSION" => ErrorKind::Version,
        "NATIVE_INPUT_RESOURCE_LIMIT" => ErrorKind::Resource,
        _ => ErrorKind::Wire,
    };
    NativeError::new(kind, error.code, error.message)
}

fn validate_core_metadata(metadata: &input_wire::OntologyMetadata) -> NativeResult<()> {
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

fn hex_digest(digest: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}

fn python_package_version() -> Option<&'static str> {
    PYTHON_VERSION_SOURCE.lines().find_map(|line| {
        line.strip_prefix("__version__ = \"")
            .and_then(|value| value.strip_suffix('"'))
            .filter(|value| !value.is_empty())
    })
}

#[pymodule]
fn _native(module: &Bound<'_, PyModule>) -> PyResult<()> {
    let version = python_package_version().ok_or_else(|| {
        pyo3::exceptions::PyRuntimeError::new_err(
            "canonical Python package version source is malformed",
        )
    })?;
    module.add("__version__", version)?;
    module.add("ABI_VERSION", ABI_VERSION)?;
    module.add("IR_SCHEMA_VERSION", IR_SCHEMA_VERSION)?;
    module.add("STATE_TRACE_VERSION", STATE_TRACE_VERSION)?;
    module.add(
        "FEATURES",
        (
            "abi3-py310",
            "cancellable-mock-work",
            "classification",
            "encoded-structural-compiler-v1",
            "full_reasoner",
            "incremental_updates",
            "realization",
            "state-trace-v1",
            "wire-v1",
        ),
    )?;
    module.add_class::<CancellationHandle>()?;
    module.add_class::<NativeSession>()?;
    module.add_function(wrap_pyfunction!(validate_encoded_columns_v1, module)?)?;
    module.add_function(wrap_pyfunction!(validate_encoded_selection_v1, module)?)?;
    module.add_function(wrap_pyfunction!(validate_encoded_slices_v1, module)?)?;
    module.add_function(wrap_pyfunction!(
        debug_validate_encoded_slices_cancel_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_permanent_program_parity_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(debug_encoded_selection_panic_v1, module)?)?;
    module.add_function(wrap_pyfunction!(encoded_profile_manifest_v1, module)?)?;
    module.add_function(wrap_pyfunction!(
        encoded_profile_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        debug_encoded_profile_context_cancel_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(encoded_symbol_manifest_v1, module)?)?;
    module.add_function(wrap_pyfunction!(encoded_object_role_manifest_v1, module)?)?;
    module.add_function(wrap_pyfunction!(
        encoded_object_role_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(encoded_data_property_manifest_v1, module)?)?;
    module.add_function(wrap_pyfunction!(
        encoded_data_property_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_data_property_inclusions_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_data_property_inclusions_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_data_property_hierarchy_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_data_property_hierarchy_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_simple_object_role_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_simple_object_role_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_complex_object_role_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_complex_object_role_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_role_characteristic_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_role_characteristic_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_object_role_hierarchy_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_object_role_hierarchy_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_object_role_semantics_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_object_role_semantics_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_object_role_automata_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_object_role_automata_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(encoded_role_model_manifest_v1, module)?)?;
    module.add_function(wrap_pyfunction!(
        encoded_role_model_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(encoded_role_clause_manifest_v1, module)?)?;
    module.add_function(wrap_pyfunction!(
        encoded_role_clause_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(encoded_object_role_accepts_v1, module)?)?;
    module.add_function(wrap_pyfunction!(
        encoded_object_role_slices_accepts_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(encoded_named_class_manifest_v1, module)?)?;
    module.add_function(wrap_pyfunction!(
        encoded_named_class_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(
        encoded_session_domain_slices_manifest_v1,
        module
    )?)?;
    module.add_function(wrap_pyfunction!(self_test, module)?)?;
    module.add_function(wrap_pyfunction!(create_encoded_session_v1, module)?)?;
    module.add_function(wrap_pyfunction!(create_session, module)?)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use super::*;
    use crate::program_bridge::LoadedRuleState;

    #[test]
    fn native_version_comes_from_the_python_distribution_source() {
        assert_eq!(python_package_version(), Some("0.1.0.dev0"));
    }

    #[test]
    fn compiler_cache_float_tokens_match_cpython_json_boundaries() -> NativeResult<()> {
        let cases = [
            (1e-4, "0.0001"),
            (1e-5, "1e-05"),
            (1e15, "1000000000000000.0"),
            (1e16, "1e+16"),
            (f64::from_bits(1), "5e-324"),
            (f64::MAX, "1.7976931348623157e+308"),
        ];
        for (value, expected) in cases {
            assert_eq!(python_float_token(value)?, expected);
        }
        Ok(())
    }

    #[test]
    fn encoded_profile_gate_matches_the_scalar_error_summary() {
        let issues = [
            encoded::profile::ProfileIssue {
                rule_id: "RULE_B",
                severity: "error",
                message: Cow::Borrowed("second"),
                constructor: None,
                document_keys: Vec::new(),
                provenance_sha256: None,
            },
            encoded::profile::ProfileIssue {
                rule_id: "RULE_A",
                severity: "error",
                message: Cow::Borrowed("first"),
                constructor: None,
                document_keys: Vec::new(),
                provenance_sha256: None,
            },
            encoded::profile::ProfileIssue {
                rule_id: "RULE_A",
                severity: "error",
                message: Cow::Borrowed("duplicate rule"),
                constructor: None,
                document_keys: Vec::new(),
                provenance_sha256: None,
            },
            encoded::profile::ProfileIssue {
                rule_id: "WARNING",
                severity: "warning",
                message: Cow::Borrowed("warning"),
                constructor: None,
                document_keys: Vec::new(),
                provenance_sha256: None,
            },
        ];
        let error = ensure_encoded_profile_conforms(false, &issues)
            .err()
            .unwrap_or_else(|| NativeError::invariant("expected profile rejection"));
        assert_eq!(error.kind, ErrorKind::Profile);
        assert_eq!(error.code, "OWL2DL_PROFILE_VIOLATION");
        assert_eq!(
            error.message,
            "ontology is outside OWL 2 DL: RULE_A, RULE_B"
        );
        assert_eq!(
            error.context.get("issue_count").map(String::as_str),
            Some("3")
        );
        assert_eq!(
            error.context.get("rule_ids").map(String::as_str),
            Some("RULE_A, RULE_B")
        );
        assert!(ensure_encoded_profile_conforms(true, &issues[3..]).is_ok());
    }

    fn decode_hex(value: &str) -> Vec<u8> {
        value
            .as_bytes()
            .chunks_exact(2)
            .filter_map(|pair| {
                let text = std::str::from_utf8(pair).ok()?;
                u8::from_str_radix(text, 16).ok()
            })
            .collect()
    }

    fn golden_document(name: &str) -> Vec<u8> {
        let fixture: serde_json::Value =
            serde_json::from_str(include_str!("../../tests/data/native-input-v1.json"))
                .unwrap_or(serde_json::Value::Null);
        fixture
            .get("documents")
            .and_then(|documents| documents.get(name))
            .and_then(|document| document.get("hex"))
            .and_then(serde_json::Value::as_str)
            .map_or_else(Vec::new, decode_hex)
    }

    fn decoded_session_input() -> NativeResult<(DecodedOntology, DecodedConfig)> {
        decode_session_inputs(
            golden_document("ontology"),
            golden_document("config"),
            &DecodeLimits::default(),
        )
    }

    fn loaded_rule_state(
        ontology: &DecodedOntology,
        config: &DecodedConfig,
        cancellation: &CancellationHandle,
    ) -> NativeResult<LoadedRuleState> {
        load_permanent_rule_state(
            ontology,
            cancellation.state(),
            config.disjunction_learning,
            config.existentials,
            config.blocking,
        )
    }

    #[test]
    fn production_semantic_check_returns_a_compact_native_answer() -> NativeResult<()> {
        let cancellation = CancellationHandle::from_options(None, None)?;
        let (ontology, config) = decoded_session_input()?;
        let ontology = Arc::new(ontology);
        let rules = loaded_rule_state(&ontology, &config, &cancellation)?;
        let tableau =
            ProductionTableau::new(Arc::clone(&ontology), config, cancellation.state(), rules)?;
        let scheduler = SessionScheduler::new(tableau, SessionLimits::default())?;
        let result = scheduler.check_permanent(cancellation.state().as_ref())?;
        let encoded = encode_check(check_wire_result(result, Duration::ZERO))?;
        assert_eq!(&encoded[..8], result_wire::RESULT_MAGIC);
        Ok(())
    }

    #[test]
    fn production_session_input_owns_current_core_wire_records() -> NativeResult<()> {
        let (ontology, config) = decoded_session_input()?;
        assert_eq!(ontology.metadata.core_wire_format_version, (1, 1));
        assert_eq!(ontology.metadata.core_api_version, CORE_API_VERSION);
        assert_eq!(config.backend, input_wire::BackendChoice::Auto);
        assert_eq!(
            hex_digest(&ontology.metadata.ontology_fingerprint).len(),
            64
        );
        Ok(())
    }

    #[test]
    fn production_session_input_rejects_core_wire_minor_drift() -> NativeResult<()> {
        let (mut ontology, _config) = decoded_session_input()?;
        ontology.metadata.core_wire_format_version = (1, 0);
        let error = validate_core_metadata(&ontology.metadata).err();
        assert_eq!(
            error.as_ref().map(|value| value.kind),
            Some(ErrorKind::Version)
        );
        assert_eq!(
            error.as_ref().map(|value| value.code),
            Some("NATIVE_CORE_VERSION")
        );
        Ok(())
    }

    #[test]
    fn decoded_delta_uses_the_same_noop_or_rebuild_contract_as_python() -> NativeResult<()> {
        let limits = DecodeLimits::default();
        let (ontology, _config) = decoded_session_input()?;
        let mut delta =
            decode_delta(golden_document("delta"), &limits).map_err(map_input_wire_error)?;
        delta
            .validate_revision(&ontology)
            .map_err(map_input_wire_error)?;
        assert_eq!(
            delta_wire_outcome(&delta),
            DeltaWireOutcome::RebuildRequired
        );

        delta.result_program_sha256 = delta.base_program_sha256;
        delta.fact_additions.clear();
        delta.fact_removals.clear();
        assert_eq!(
            delta_wire_outcome(&delta),
            DeltaWireOutcome::AppliedIncrementally
        );
        Ok(())
    }
}
