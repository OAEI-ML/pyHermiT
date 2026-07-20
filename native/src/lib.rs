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
use pyo3::types::{PyBytes, PyMemoryView, PySequence};

pub use cancel::{CancellationHandle, CancellationState};
use error::{ErrorKind, NativeError, NativeResult};
use event_wire::encode_events;
use input_wire::{
    decode_config, decode_delta, decode_ontology, decode_query, DecodeLimits, DecodedConfig,
    DecodedDelta, DecodedOntology, DecodedQuery, InputWireError,
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
const PYTHON_VERSION_SOURCE: &str = include_str!("../../src/pyhermit/_version.py");

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

fn encoded_validation_error(error: encoded::EncodedValidationError) -> NativeError {
    let kind = match error.code {
        "NATIVE_ENCODED_VIEW_INVALID" => ErrorKind::Wire,
        "NATIVE_ENCODED_RESOURCE_LIMIT" => ErrorKind::Resource,
        _ => ErrorKind::Invariant,
    };
    let mapped = NativeError::new(kind, error.code, error.message);
    if kind == ErrorKind::Resource {
        mapped.with_context("limit", "encoded-structural-validation")
    } else {
        mapped
    }
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
        encoded::symbols::compile_symbol_phase(
            &model,
            encoded::symbols::SymbolPhaseLimits::default(),
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
    module.add_function(wrap_pyfunction!(encoded_symbol_manifest_v1, module)?)?;
    module.add_function(wrap_pyfunction!(self_test, module)?)?;
    module.add_function(wrap_pyfunction!(create_session, module)?)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program_bridge::LoadedRuleState;

    #[test]
    fn native_version_comes_from_the_python_distribution_source() {
        assert_eq!(python_package_version(), Some("0.1.0.dev0"));
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
