from __future__ import annotations

import math
import os
import threading
from io import BytesIO
from pathlib import Path
from unittest import mock

import pyowl_core
import pyowl_core.model as owl
import pytest

import pyhermit
import pyhermit.facade as facade_module
from pyhermit import (
    ConcurrentMutationError,
    DisposedReasonerError,
    InferenceType,
    OntologyProfileError,
    Reasoner,
    ReasonerConfig,
    ReasonerInterruptedError,
    ReasonerTimeoutError,
)
from pyhermit.encoded_input import (
    ENCODED_BUFFER_WIDTHS,
    ENCODED_DESCRIPTOR_SHA256,
    ENCODED_SCHEMA_NAME,
    ENCODED_SCHEMA_VERSION,
)

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)
_ENCODED_FORBIDDEN_WORK_COUNTERS = {
    "base_flattening_bytes",
    "materialized_scalar_rows",
    "parser_calls",
    "per_row_ffi_calls",
    "resolver_calls",
    "scalar_axiom_materializations",
    "scalar_term_materializations",
    "structural_copy_bytes",
    "wire_decoder_calls",
    "wire_encoder_calls",
}


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test#>) "
        "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>) "
        "Ontology(<urn:test:facade> " + " ".join(body) + ")"
    ).encode()


def config(**options: object) -> ReasonerConfig:
    backend = os.environ.get("PYHERMIT_TEST_BACKEND", "python")
    return ReasonerConfig(backend=backend, **options)  # type: ignore[arg-type]


def test_public_surface_reexports_exact_core_views_and_runs_complete_services() -> None:
    assert pyhermit.OntologySnapshot is pyowl_core.OntologySnapshot
    assert pyhermit.OntologyOverlay is pyowl_core.OntologyOverlay
    assert pyhermit.OntologyComposite is pyowl_core.OntologyComposite
    assert pyhermit.load_snapshot is pyowl_core.load_snapshot
    source = functional(
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:d))",
        "SubClassOf(:A :B)",
        "ClassAssertion(:A :i)",
        "ObjectPropertyAssertion(:p :i :j)",
        'DataPropertyAssertion(:d :i "1"^^xsd:integer)',
    )
    reasoner = Reasoner(source, config=config(), load_options=OPTIONS)
    a = owl.Class(owl.IRI("urn:test#A"))
    b = owl.Class(owl.IRI("urn:test#B"))
    i = owl.NamedIndividual(owl.IRI("urn:test#i"))
    j = owl.NamedIndividual(owl.IRI("urn:test#j"))
    p = owl.ObjectProperty(owl.IRI("urn:test#p"))
    d = owl.DataProperty(owl.IRI("urn:test#d"))
    literal = owl.Literal(
        "1",
        owl.Datatype(owl.IRI("http://www.w3.org/2001/XMLSchema#integer")),
    )

    assert reasoner.backend.name == os.environ.get("PYHERMIT_TEST_BACKEND", "python")
    assert reasoner.is_consistent()
    assert reasoner.is_subclass(a, b)
    assert reasoner.entails(owl.SubClassOf(a, b))
    assert b in set().union(*reasoner.types(i))
    assert j in reasoner.object_property_values(i, p)
    assert literal in reasoner.data_property_values(i, d)
    assert reasoner.class_hierarchy().nodes
    assert reasoner.object_property_hierarchy().nodes
    assert reasoner.data_property_hierarchy().nodes


def test_diagnostics_are_bounded_immutable_and_survive_dispose() -> None:
    reasoner = Reasoner(
        functional("Declaration(Class(:A))"),
        config=config(),
        load_options=OPTIONS,
    )

    diagnostics = reasoner.diagnostics()
    expected_keys = {
        "compiler_cache_schema_version",
        "compiler_digest",
        "consumer_compile_seconds",
        "encoded_buffer_bytes",
        "encoded_buffer_count",
        "encoded_compiler_gil_released",
        "encoded_detached_buffer_count",
        "encoded_indexed_buffer_count",
        "encoded_posting_bytes",
        "encoded_private_ir_bytes",
        "encoded_referenced_view_count",
        "encoded_segment_count",
        "encoded_staging_copy_bytes",
        "encoded_zero_copy_buffers",
        "implementation_version",
        "ingestion_path",
        "ir_schema_version",
    }
    expected_path = "scalar-python" if reasoner.backend.name == "python" else "encoded-native"
    if reasoner.backend.name in {"native", "verify"}:
        expected_keys.add("native_abi_version")
        expected_keys.update(_ENCODED_FORBIDDEN_WORK_COUNTERS)

    assert tuple(diagnostics) == tuple(sorted(expected_keys))
    assert diagnostics["ingestion_path"] == expected_path
    digest = diagnostics["compiler_digest"]
    assert isinstance(digest, str)
    assert len(digest) == 64
    assert set(digest) <= set("0123456789abcdef")
    assert diagnostics["compiler_cache_schema_version"] == pyhermit.COMPILER_CACHE_SCHEMA_VERSION
    assert diagnostics["ir_schema_version"] == pyhermit.COMPILED_IR_SCHEMA_VERSION
    assert diagnostics["implementation_version"] == reasoner.backend.implementation_version
    assert type(diagnostics["consumer_compile_seconds"]) is float
    assert math.isfinite(diagnostics["consumer_compile_seconds"])
    assert diagnostics["consumer_compile_seconds"] >= 0.0
    if reasoner.backend.name in {"native", "verify"}:
        assert diagnostics["native_abi_version"] == pyhermit.NATIVE_ABI_VERSION
        assert all(
            type(diagnostics[name]) is int and diagnostics[name] == 0
            for name in _ENCODED_FORBIDDEN_WORK_COUNTERS
        )
    encoded = {key: value for key, value in diagnostics.items() if key.startswith("encoded_")}
    if reasoner.backend.name == "python":
        assert encoded == {
            "encoded_buffer_bytes": 0,
            "encoded_buffer_count": 0,
            "encoded_compiler_gil_released": False,
            "encoded_detached_buffer_count": 0,
            "encoded_indexed_buffer_count": 0,
            "encoded_posting_bytes": 0,
            "encoded_private_ir_bytes": 0,
            "encoded_referenced_view_count": 0,
            "encoded_segment_count": 0,
            "encoded_staging_copy_bytes": 0,
            "encoded_zero_copy_buffers": 0,
        }
    else:
        assert encoded["encoded_buffer_bytes"] > 0
        assert encoded["encoded_buffer_count"] > 0
        assert encoded["encoded_compiler_gil_released"] is True
        assert (
            encoded["encoded_detached_buffer_count"]
            == encoded["encoded_buffer_count"]
            == encoded["encoded_zero_copy_buffers"]
        )
        assert encoded["encoded_segment_count"] > 0
        assert encoded["encoded_staging_copy_bytes"] == 0
    with pytest.raises(TypeError):
        diagnostics["ingestion_path"] = "encoded-native"  # type: ignore[index]

    reasoner.dispose()
    assert reasoner.diagnostics() == diagnostics


def test_public_encoded_native_handoff_has_complete_zero_forbidden_work_ledger() -> None:
    if not pyhermit.backend_info().native.available:
        pytest.skip("native extension is unavailable")
    snapshot = pyowl_core.load_snapshot(
        functional("Declaration(Class(:A))"),
        options=OPTIONS,
    )

    with Reasoner(snapshot, config=ReasonerConfig(backend="native")) as reasoner:
        diagnostics = reasoner.diagnostics()

    expected_keys = {
        "compiler_cache_schema_version",
        "compiler_digest",
        "consumer_compile_seconds",
        "encoded_buffer_bytes",
        "encoded_buffer_count",
        "encoded_compiler_gil_released",
        "encoded_detached_buffer_count",
        "encoded_indexed_buffer_count",
        "encoded_posting_bytes",
        "encoded_private_ir_bytes",
        "encoded_referenced_view_count",
        "encoded_segment_count",
        "encoded_staging_copy_bytes",
        "encoded_zero_copy_buffers",
        "implementation_version",
        "ingestion_path",
        "ir_schema_version",
        "native_abi_version",
        *_ENCODED_FORBIDDEN_WORK_COUNTERS,
    }
    assert tuple(diagnostics) == tuple(sorted(expected_keys))
    assert diagnostics["ingestion_path"] == "encoded-native"
    assert {
        name: diagnostics[name] for name in sorted(_ENCODED_FORBIDDEN_WORK_COUNTERS)
    } == dict.fromkeys(sorted(_ENCODED_FORBIDDEN_WORK_COUNTERS), 0)
    assert all(type(diagnostics[name]) is int for name in _ENCODED_FORBIDDEN_WORK_COUNTERS)


def test_consumer_compile_seconds_measures_each_successful_compilation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ticks = iter((10.0, 10.25, 20.0, 20.75))
    monkeypatch.setattr(facade_module, "perf_counter", lambda: next(ticks))
    reasoner = Reasoner(
        functional("Declaration(Class(:A))", "Declaration(Class(:B))"),
        config=config(),
        load_options=OPTIONS,
    )

    assert reasoner.diagnostics()["consumer_compile_seconds"] == pytest.approx(0.25)
    reasoner.add_axioms(
        (
            owl.SubClassOf(
                owl.Class(owl.IRI("urn:test#A")),
                owl.Class(owl.IRI("urn:test#B")),
            ),
        )
    )
    reasoner.flush()

    assert reasoner.diagnostics()["consumer_compile_seconds"] == pytest.approx(0.75)


def test_public_compiler_diagnostics_change_only_with_compilation_identity() -> None:
    source = functional("Declaration(Class(:A))", "Declaration(Class(:B))")
    left = Reasoner(source, config=config(), load_options=OPTIONS)
    right = Reasoner(source, config=config(), load_options=OPTIONS)
    original = left.diagnostics()["compiler_digest"]

    assert right.diagnostics()["compiler_digest"] == original
    left.add_axioms(
        (
            owl.SubClassOf(
                owl.Class(owl.IRI("urn:test#A")),
                owl.Class(owl.IRI("urn:test#B")),
            ),
        )
    )
    assert left.diagnostics()["compiler_digest"] == original
    left.flush()
    assert left.diagnostics()["compiler_digest"] != original


def test_public_compiler_digest_is_backend_and_ingestion_path_independent() -> None:
    if not pyhermit.backend_info().native.available:
        pytest.skip("native extension is unavailable")
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )
    reasoners = tuple(
        Reasoner(snapshot, config=ReasonerConfig(backend=backend))
        for backend in ("python", "native", "verify")
    )

    diagnostics = tuple(reasoner.diagnostics() for reasoner in reasoners)

    assert {value["ingestion_path"] for value in diagnostics} == {
        "encoded-native",
        "scalar-python",
    }
    assert len({value["compiler_digest"] for value in diagnostics}) == 1
    assert len({reasoner._runtime.session.ontology_fingerprint for reasoner in reasoners}) == 3
    assert reasoners[2]._runtime.session._scalar_bundle is not None
    expected_handoff = {
        "buffer_widths": dict(ENCODED_BUFFER_WIDTHS),
        "descriptor_sha256": ENCODED_DESCRIPTOR_SHA256.hex(),
        "model_schema": pyowl_core.MODEL_SCHEMA_VERSION,
        "schema_name": ENCODED_SCHEMA_NAME,
        "schema_version": ENCODED_SCHEMA_VERSION,
    }
    assert getattr(reasoners[0].backend, "compiler_handoff", None) is None
    assert reasoners[1].backend.compiler_handoff == expected_handoff
    assert reasoners[2].backend.compiler_handoff == expected_handoff


def test_buffered_updates_are_transactional_zero_copy_and_clear_precompute() -> None:
    reasoner = Reasoner(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "SubClassOf(:A :B)",
        ),
        config=config(),
        load_options=OPTIONS,
    )
    a = owl.Class(owl.IRI("urn:test#A"))
    b = owl.Class(owl.IRI("urn:test#B"))
    c = owl.Class(owl.IRI("urn:test#C"))
    addition = owl.SubClassOf(b, c)
    before = reasoner.ontology
    reasoner.precompute(InferenceType.CLASS_HIERARCHY)
    assert reasoner.is_precomputed(InferenceType.CLASS_HIERARCHY)

    reasoner.add_axioms((addition,))

    assert reasoner.pending_additions() == frozenset((addition,))
    assert reasoner.ontology is before
    assert not reasoner.is_subclass(a, c)
    reasoner.flush()
    assert isinstance(reasoner.ontology, pyowl_core.OntologyOverlay)
    assert reasoner.ontology.base is before
    assert reasoner.is_subclass(a, c)
    assert not reasoner.is_precomputed(InferenceType.CLASS_HIERARCHY)
    assert not reasoner.pending_additions()

    reasoner.remove_axioms((addition,))
    reasoner.flush()
    assert not reasoner.is_subclass(a, c)


def test_failed_flush_keeps_old_revision_and_pending_batch() -> None:
    reasoner = Reasoner(
        functional("Declaration(Class(:A))"),
        config=config(),
        load_options=OPTIONS,
    )
    a = owl.Class(owl.IRI("urn:test#A"))
    missing = owl.Class(owl.IRI("urn:test#Missing"))
    invalid = owl.SubClassOf(a, missing)
    before = reasoner.ontology
    diagnostics_before = reasoner.diagnostics()
    reasoner.add_axioms((invalid,))

    with pytest.raises(OntologyProfileError):
        reasoner.flush()

    assert reasoner.ontology is before
    assert reasoner.diagnostics() == diagnostics_before
    assert reasoner.pending_additions() == frozenset((invalid,))
    assert reasoner.is_consistent()
    reasoner.remove_axioms((invalid,))
    assert not reasoner.pending_additions()


def test_immediate_updates_context_lifecycle_and_disposed_properties() -> None:
    source = functional(
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
    )
    a = owl.Class(owl.IRI("urn:test#A"))
    b = owl.Class(owl.IRI("urn:test#B"))
    with Reasoner(
        source,
        config=config(buffer_changes=False),
        load_options=OPTIONS,
    ) as reasoner:
        reasoner.add_axioms((owl.SubClassOf(a, b),))
        assert reasoner.is_subclass(a, b)
        assert not reasoner.pending_additions()
        retained_view = reasoner.ontology
        retained_backend = reasoner.backend

    reasoner.dispose()
    assert reasoner.ontology is retained_view
    assert reasoner.backend is retained_backend
    assert reasoner.config.buffer_changes is False
    with pytest.raises(DisposedReasonerError):
        reasoner.is_consistent()
    with pytest.raises(DisposedReasonerError):
        reasoner.pending_additions()
    with pytest.raises(DisposedReasonerError):
        reasoner.interrupt()


def test_precompute_status_is_atomic_and_complete_for_tiny_ontology() -> None:
    reasoner = Reasoner(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "ClassAssertion(:A :i)",
            "ObjectPropertyAssertion(:p :i :j)",
        ),
        config=config(),
        load_options=OPTIONS,
    )
    selected = (
        InferenceType.CLASS_HIERARCHY,
        InferenceType.OBJECT_PROPERTY_HIERARCHY,
        InferenceType.SAME_INDIVIDUAL,
    )

    reasoner.precompute(*selected)

    assert reasoner.precomputable() == frozenset(InferenceType)
    assert all(reasoner.is_precomputed(value) for value in selected)
    with pytest.raises(TypeError):
        reasoner.precompute("class_hierarchy")  # type: ignore[arg-type]


def test_callback_reentrancy_fails_without_deadlock_and_reasoner_recovers() -> None:
    holder: dict[str, Reasoner] = {}
    attempted = False

    def progress(_event: object) -> None:
        nonlocal attempted
        if attempted:
            return
        attempted = True
        holder["reasoner"].is_consistent()

    reasoner = Reasoner(
        functional("Declaration(Class(:A))"),
        config=config(progress=progress),
        load_options=OPTIONS,
    )
    holder["reasoner"] = reasoner

    with pytest.raises(ConcurrentMutationError):
        reasoner.is_consistent()
    assert reasoner.is_consistent()


def test_interrupt_targets_only_the_active_operation() -> None:
    started = threading.Event()
    release = threading.Event()
    errors: list[BaseException] = []

    def progress(event: object) -> None:
        if getattr(event, "kind", None) == "reasoning-started":
            started.set()
            assert release.wait(5)

    reasoner = Reasoner(
        functional("Declaration(Class(:A))"),
        config=config(progress=progress),
        load_options=OPTIONS,
    )

    def run() -> None:
        try:
            reasoner.is_consistent()
        except BaseException as error:
            errors.append(error)

    thread = threading.Thread(target=run)
    thread.start()
    assert started.wait(5)
    reasoner.interrupt()
    release.set()
    thread.join(5)

    assert not thread.is_alive()
    assert len(errors) == 1 and isinstance(errors[0], ReasonerInterruptedError)
    assert reasoner.is_consistent()


def test_provider_is_called_once_and_dispose_retains_the_shared_view() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional("Declaration(Class(:A))"),
        options=OPTIONS,
    )

    class Provider:
        def __init__(self) -> None:
            self.calls = 0

        def owl_snapshot(self) -> pyowl_core.OntologyView:
            self.calls += 1
            return snapshot

    provider = Provider()
    reasoner = Reasoner(provider, config=config())

    assert provider.calls == 1
    assert reasoner.ontology is snapshot
    reasoner.dispose()
    assert reasoner.ontology is snapshot
    assert tuple(snapshot.iter_axioms())


def test_path_stream_overlay_and_composite_inputs_retain_core_views(
    tmp_path: Path,
) -> None:
    source = functional("Declaration(Class(:A))")
    ontology_path = tmp_path / "ontology.ofn"
    ontology_path.write_bytes(source)

    path_reasoner = Reasoner(ontology_path, config=config(), load_options=OPTIONS)
    assert path_reasoner.is_consistent()

    stream = BytesIO(source)
    stream_reasoner = Reasoner(
        stream,
        config=config(),
        document_iri="urn:test:stream",
        load_options=OPTIONS,
    )
    assert stream_reasoner.is_consistent()
    stream_reasoner.dispose()
    assert not stream.closed

    snapshot = pyowl_core.load_snapshot(source, options=OPTIONS)
    a = owl.Class(owl.IRI("urn:test#A"))
    b = owl.Class(owl.IRI("urn:test#B"))
    overlay = pyowl_core.apply_delta(
        snapshot,
        pyowl_core.OntologyDelta(
            add_axioms=owl.CanonicalSet((owl.Declaration(b), owl.SubClassOf(a, b))),
        ),
    )
    overlay_reasoner = Reasoner(overlay, config=config())
    assert overlay_reasoner.ontology is overlay
    assert overlay_reasoner.is_subclass(a, b)

    target = pyowl_core.load_snapshot(
        functional("Declaration(Class(:B))"),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(snapshot, target, roles=("source", "target"))
    composite_reasoner = Reasoner(composite, config=config())
    assert composite_reasoner.ontology is composite
    assert composite_reasoner.is_consistent()


def test_timeout_is_per_operation_and_does_not_poison_the_next_query() -> None:
    reasoner = Reasoner(
        functional("Declaration(Class(:A))"),
        config=config(timeout=1.0),
        load_options=OPTIONS,
    )
    with (
        mock.patch("pyhermit.events.time.monotonic", side_effect=[100.0, 102.0]),
        pytest.raises(ReasonerTimeoutError),
    ):
        reasoner.is_consistent()

    assert reasoner.is_consistent()


def test_same_instance_serializes_and_independent_instances_overlap() -> None:
    first_entered = threading.Event()
    release_first = threading.Event()
    first_calls = 0

    def serialized_progress(event: object) -> None:
        nonlocal first_calls
        if getattr(event, "kind", None) != "reasoning-started":
            return
        first_calls += 1
        if first_calls == 1:
            first_entered.set()
            assert release_first.wait(5)

    reasoner = Reasoner(
        functional("Declaration(Class(:A))"),
        config=config(progress=serialized_progress),
        load_options=OPTIONS,
    )
    results: list[bool] = []
    first = threading.Thread(target=lambda: results.append(reasoner.is_consistent()))
    second = threading.Thread(target=lambda: results.append(reasoner.is_consistent()))
    first.start()
    assert first_entered.wait(5)
    second.start()
    assert first_calls == 1
    release_first.set()
    first.join(5)
    second.join(5)
    assert results == [True, True]

    barrier = threading.Barrier(2, timeout=5)

    def overlapping_progress(event: object) -> None:
        if getattr(event, "kind", None) == "reasoning-started":
            barrier.wait()

    left = Reasoner(
        functional("Declaration(Class(:Left))"),
        config=config(progress=overlapping_progress),
        load_options=OPTIONS,
    )
    right = Reasoner(
        functional("Declaration(Class(:Right))"),
        config=config(progress=overlapping_progress),
        load_options=OPTIONS,
    )
    independent: list[bool] = []
    left_thread = threading.Thread(target=lambda: independent.append(left.is_consistent()))
    right_thread = threading.Thread(target=lambda: independent.append(right.is_consistent()))
    left_thread.start()
    right_thread.start()
    left_thread.join(5)
    right_thread.join(5)
    assert independent == [True, True]
