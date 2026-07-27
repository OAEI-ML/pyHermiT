"""Exact native fingerprint parity and lazy-view traversal boundaries."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import sys
from types import ModuleType
from typing import Any

import pyowl_core
import pyowl_core.model as owl
import pytest

import pyhermit._native as native
import pyhermit.facade as facade_module
from pyhermit import Reasoner, ReasonerConfig
from pyhermit.backends.native import NativeBackendFactory
from pyhermit.backends.native_input import (
    encode_config,
    encode_deferred_encoded_session_metadata,
    encode_encoded_session_metadata,
)
from pyhermit.core import (
    CapturedOntology,
    _deferred_capture_eligible,
    capture_compatible_view,
    capture_compatible_view_deferred,
    compiler_cache_key,
)
from pyhermit.encoded_input import (
    ENCODED_NATIVE_FEATURE,
    ENCODED_SCHEMA_NAME,
    ENCODED_SCHEMA_VERSION,
    _deferred_structural_mode,
    _encoded_slice_records,
    negotiate_encoded_input,
)
from pyhermit.exceptions import (
    BackendMismatchError,
    ReasonerInterruptedError,
    ResourceLimitError,
)
from pyhermit.inputs import _capture_ontology_input

_OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)


def _functional(identifier: str, *body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:deferred#>) "
        "Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>) "
        f"Ontology(<urn:test:deferred:{identifier}> "
        + " ".join(body)
        + ")"
    ).encode()


def _snapshot(identifier: str, *body: str) -> pyowl_core.OntologySnapshot:
    return pyowl_core.load_snapshot(
        _functional(identifier, *body),
        options=_OPTIONS,
    )


def _native_factory() -> NativeBackendFactory:
    extension = ModuleType("deferred_fingerprint_test_extension")
    extension.__version__ = native.__version__
    extension.ABI_VERSION = native.ABI_VERSION
    extension.IR_SCHEMA_VERSION = native.IR_SCHEMA_VERSION
    extension.FEATURES = tuple(sorted({*native.FEATURES, ENCODED_NATIVE_FEATURE}))
    extension.CancellationHandle = native.CancellationHandle
    extension.self_test = native.self_test
    extension.create_session = native.create_session
    extension._create_encoded_session_v1 = native._create_encoded_session_v1
    extension._validate_encoded_columns_v1 = native._validate_encoded_columns_v1
    extension._validate_encoded_slices_v1 = native._validate_encoded_slices_v1
    extension._encoded_profile_slices_manifest_v1 = (
        native._encoded_profile_slices_manifest_v1
    )
    return NativeBackendFactory(extension)


def _assert_deferred_parity(
    view: pyowl_core.OntologyOverlay | pyowl_core.OntologyComposite,
    *,
    expected_mode: str = "effective",
    validate_profile: bool = True,
) -> tuple[str, str, str]:
    config = ReasonerConfig()
    eager = capture_compatible_view(view)
    deferred = capture_compatible_view_deferred(view)
    negotiation = negotiate_encoded_input(
        view,
        {ENCODED_SCHEMA_NAME: ENCODED_SCHEMA_VERSION},
    )
    lease = negotiation.lease
    assert lease is not None
    mode = _deferred_structural_mode(lease)
    assert mode == expected_mode
    metadata, request = encode_deferred_encoded_session_metadata(
        deferred,
        config,
        structural_mode=mode,
    )
    session = native._create_encoded_session_v1(
        slices=_encoded_slice_records(lease.root_slices()),
        metadata=metadata,
        config=encode_config(config),
        cancellation=native.CancellationHandle(),
        deferred_fingerprints=request,
        validate_profile=validate_profile,
    )
    expected = (
        eager.structural_fingerprint.hex,
        eager.logical_fingerprint.hex,
        eager.signature_fingerprint.hex,
    )
    try:
        assert session._debug_source_fingerprints == expected
        assert session.ontology_fingerprint == compiler_cache_key(eager, config)
        assert session.permanent_program_sha256 != "0" * 64
    finally:
        session.close()
    return expected


def _patch_overlay_fingerprint_bombs(monkeypatch: pytest.MonkeyPatch) -> None:
    def forbidden(_self: object) -> object:
        raise AssertionError("Python overlay semantic fingerprint traversal occurred")

    for name in (
        "structural_fingerprint",
        "logical_fingerprint",
        "signature_fingerprint",
    ):
        monkeypatch.setattr(pyowl_core.OntologyOverlay, name, property(forbidden))


def _query_expression() -> owl.ObjectSomeValuesFrom:
    return owl.ObjectSomeValuesFrom(
        owl.ObjectProperty(owl.IRI("urn:test:deferred#p")),
        owl.Class(owl.IRI("urn:test:deferred#B")),
    )


def test_overlay_fingerprints_match_annotated_eager_contract() -> None:
    base = _snapshot(
        "overlay",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(AnnotationProperty(:note))",
        'SubClassOf(Annotation(:note "source") :A :B)',
        'AnnotationAssertion(rdfs:label :A "A")',
    )
    overlay = pyowl_core.apply_delta(
        base,
        pyowl_core.OntologyDelta(
            add_axioms=owl.CanonicalSet(
                (
                    owl.SubClassOf(
                        owl.Class(owl.IRI("urn:test:deferred#B")),
                        owl.Class(owl.IRI("urn:test:deferred#C")),
                    ),
                )
            )
        ),
    )

    _assert_deferred_parity(overlay)


def test_zero_delta_overlay_aliases_anchor_structural_fingerprint() -> None:
    base = _snapshot(
        "empty-overlay",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "SubClassOf(:A :B)",
    )
    overlay = pyowl_core.apply_delta(base, pyowl_core.OntologyDelta())

    observed = _assert_deferred_parity(
        overlay,
        expected_mode="overlay-anchor-alias",
    )

    assert observed[0] == base.structural_fingerprint.hex


def test_cyclic_forged_overlay_chain_fails_closed_for_deferred_capture() -> None:
    overlay = pyowl_core.apply_delta(
        _snapshot("cyclic-overlay", "Declaration(Class(:A))"),
        pyowl_core.OntologyDelta(),
    )
    object.__setattr__(overlay, "base", overlay)

    assert not _deferred_capture_eligible(overlay)


def test_composite_parity_is_order_independent_for_annotated_roots() -> None:
    left = _snapshot(
        "left",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        'SubClassOf(Annotation(rdfs:comment "left") :A :B)',
    )
    right = _snapshot(
        "right",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        'SubClassOf(Annotation(rdfs:comment "right") :B :C)',
    )
    forward = pyowl_core.compose_views(left, right, roles=("left", "right"))
    reverse = pyowl_core.compose_views(right, left, roles=("right", "left"))

    assert _assert_deferred_parity(forward) == _assert_deferred_parity(reverse)


def test_logical_fingerprint_deduplicates_differently_annotated_axioms() -> None:
    left = _snapshot(
        "dedup-left",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        'SubClassOf(Annotation(rdfs:comment "left") :A :B)',
    )
    right = _snapshot(
        "dedup-right",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        'SubClassOf(Annotation(rdfs:comment "right") :A :B)',
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    _assert_deferred_parity(composite)


def test_signature_fingerprint_covers_annotation_only_properties() -> None:
    annotation_only = _snapshot(
        "annotation-only",
        "Annotation(:annotation-only <urn:test:deferred#annotation-value>)",
        "Declaration(Class(:A))",
    )
    direct = _snapshot(
        "annotation-peer",
        "Declaration(Class(:B))",
    )
    composite = pyowl_core.compose_views(
        annotation_only,
        direct,
        roles=("annotation", "direct"),
    )

    _assert_deferred_parity(composite, validate_profile=False)


def test_composite_parity_remaps_colliding_anonymous_scopes() -> None:
    sources = tuple(
        _snapshot(
            "anonymous",
            "Declaration(Class(:A))",
            "ClassAssertion(:A _:shared)",
        )
        for _ in range(2)
    )
    composite = pyowl_core.compose_views(
        *sources,
        roles=("first", "second"),
    )

    assert any(cast_map for cast_map in composite._scope_replacements())
    _assert_deferred_parity(composite)


def test_reasoner_initialization_does_not_read_overlay_fingerprints(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    base = _snapshot(
        "init",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
    )
    overlay = pyowl_core.apply_delta(
        base,
        pyowl_core.OntologyDelta(
            add_axioms=owl.CanonicalSet(
                (
                    owl.SubClassOf(
                        owl.Class(owl.IRI("urn:test:deferred#A")),
                        owl.Class(owl.IRI("urn:test:deferred#B")),
                    ),
                )
            )
        ),
    )
    _patch_overlay_fingerprint_bombs(monkeypatch)

    with Reasoner(overlay, config=ReasonerConfig(backend="native")) as reasoner:
        assert reasoner.diagnostics()["ingestion_path"] == "encoded-native"
        assert reasoner.is_consistent()


def test_reasoner_initialization_does_not_read_composite_fingerprints(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    left = _snapshot(
        "composite-bomb-left",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "SubClassOf(:A :B)",
    )
    right = _snapshot(
        "composite-bomb-right",
        "Declaration(Class(:C))",
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    def forbidden(_self: object) -> object:
        raise AssertionError("Python composite semantic fingerprint traversal occurred")

    for name in (
        "structural_fingerprint",
        "logical_fingerprint",
        "signature_fingerprint",
    ):
        monkeypatch.setattr(pyowl_core.OntologyComposite, name, property(forbidden))

    with Reasoner(composite, config=ReasonerConfig(backend="native")) as reasoner:
        assert reasoner.diagnostics()["ingestion_path"] == "encoded-native"
        assert reasoner.is_consistent()


def test_buffered_flush_does_not_read_overlay_fingerprints(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = _snapshot(
        "flush",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "SubClassOf(:A :B)",
    )
    factory = _native_factory()
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)

    with Reasoner(snapshot, config=ReasonerConfig(buffer_changes=True)) as reasoner:
        _patch_overlay_fingerprint_bombs(monkeypatch)
        reasoner.add_axioms(
            (
                owl.SubClassOf(
                    owl.Class(owl.IRI("urn:test:deferred#B")),
                    owl.Class(owl.IRI("urn:test:deferred#C")),
                ),
            )
        )
        reasoner.flush()
        assert reasoner.diagnostics()["ingestion_path"] == "encoded-native"
        assert reasoner.is_consistent()


def test_temporary_encoded_query_does_not_read_overlay_fingerprints(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = _snapshot(
        "query",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "SubClassOf(:A ObjectSomeValuesFrom(:p :B))",
    )
    factory = _native_factory()
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)

    with Reasoner(snapshot) as reasoner:
        _patch_overlay_fingerprint_bombs(monkeypatch)
        assert isinstance(reasoner.is_satisfiable(_query_expression()), bool)


@pytest.mark.parametrize("initial_shape", ("overlay", "composite"))
def test_temporary_query_on_lazy_initial_view_uses_supported_attestation_path(
    monkeypatch: pytest.MonkeyPatch,
    initial_shape: str,
) -> None:
    base = _snapshot(
        f"nested-query-{initial_shape}",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(ObjectProperty(:p))",
        "SubClassOf(:A ObjectSomeValuesFrom(:p :B))",
    )
    if initial_shape == "overlay":
        view: pyowl_core.OntologyView = pyowl_core.apply_delta(
            base,
            pyowl_core.OntologyDelta(),
        )
    else:
        view = pyowl_core.compose_views(
            base,
            _snapshot(
                "nested-query-composite-peer",
                "Declaration(Class(:C))",
            ),
            roles=("base", "peer"),
        )
    factory = _native_factory()
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)

    with Reasoner(view) as reasoner:
        assert isinstance(reasoner.is_satisfiable(_query_expression()), bool)
        assert reasoner.diagnostics()["ingestion_path"] == "encoded-native"


def test_repeated_flush_and_query_do_not_read_overlay_chain_fingerprints(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = _snapshot(
        "repeated-flush",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(Class(:D))",
        "Declaration(ObjectProperty(:p))",
        "SubClassOf(:A ObjectSomeValuesFrom(:p :B))",
    )
    factory = _native_factory()
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)

    with Reasoner(snapshot, config=ReasonerConfig(buffer_changes=True)) as reasoner:
        _patch_overlay_fingerprint_bombs(monkeypatch)
        for sub_name, super_name in (("B", "C"), ("C", "D")):
            reasoner.add_axioms(
                (
                    owl.SubClassOf(
                        owl.Class(owl.IRI(f"urn:test:deferred#{sub_name}")),
                        owl.Class(owl.IRI(f"urn:test:deferred#{super_name}")),
                    ),
                )
            )
            reasoner.flush()
        assert isinstance(reasoner.is_satisfiable(_query_expression()), bool)
        assert reasoner.diagnostics()["ingestion_path"] == "encoded-native"


def test_temporary_query_after_buffered_flush_uses_supported_attestation_path(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = _snapshot(
        "nested-query-flush",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(Class(:C))",
        "Declaration(ObjectProperty(:p))",
        "SubClassOf(:A ObjectSomeValuesFrom(:p :B))",
    )
    factory = _native_factory()
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)

    with Reasoner(snapshot, config=ReasonerConfig(buffer_changes=True)) as reasoner:
        reasoner.add_axioms(
            (
                owl.SubClassOf(
                    owl.Class(owl.IRI("urn:test:deferred#B")),
                    owl.Class(owl.IRI("urn:test:deferred#C")),
                ),
            )
        )
        reasoner.flush()
        assert isinstance(reasoner.is_satisfiable(_query_expression()), bool)
        assert reasoner.diagnostics()["ingestion_path"] == "encoded-native"


def test_nested_lazy_composite_uses_eager_attestation_without_deferred_metadata(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    left = _snapshot(
        "nested-left",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
    )
    right = _snapshot(
        "nested-right",
        "Declaration(Class(:C))",
    )
    overlay = pyowl_core.apply_delta(
        left,
        pyowl_core.OntologyDelta(
            add_axioms=owl.CanonicalSet(
                (
                    owl.SubClassOf(
                        owl.Class(owl.IRI("urn:test:deferred#A")),
                        owl.Class(owl.IRI("urn:test:deferred#B")),
                    ),
                )
            )
        ),
    )
    composite = pyowl_core.compose_views(
        overlay,
        right,
        roles=("overlay", "direct"),
    )
    captured = _capture_ontology_input(composite, defer_fingerprints=True)
    assert isinstance(captured.captured, CapturedOntology)

    factory = _native_factory()
    requests: list[object] = []
    raw_constructor = native._create_encoded_session_v1

    def tracked_constructor(**kwargs: Any) -> object:
        requests.append(kwargs.get("deferred_fingerprints"))
        return raw_constructor(**kwargs)

    factory._create_encoded_session = tracked_constructor
    monkeypatch.setattr(facade_module, "select_backend_factory", lambda _config: factory)

    with Reasoner(composite) as reasoner:
        assert reasoner.diagnostics()["ingestion_path"] == "encoded-native"
        assert reasoner.is_consistent()

    assert requests == [None]


def test_bridged_nested_composite_is_not_deferred() -> None:
    left = _snapshot(
        "bridge-left",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
    )
    right = _snapshot(
        "bridge-right",
        "Declaration(Class(:C))",
    )
    bridge = owl.SubClassOf(
        owl.Class(owl.IRI("urn:test:deferred#B")),
        owl.Class(owl.IRI("urn:test:deferred#C")),
    )
    inner = pyowl_core.compose_views(
        left,
        right,
        roles=("left", "right"),
        delta=pyowl_core.OntologyDelta(add_axioms=owl.CanonicalSet((bridge,))),
    )
    outer = pyowl_core.compose_views(
        inner,
        _snapshot("bridge-outer", "Declaration(Class(:D))"),
        roles=("inner", "outer"),
    )

    captured = _capture_ontology_input(outer, defer_fingerprints=True)

    assert isinstance(captured.captured, CapturedOntology)


@pytest.mark.parametrize(
    "timeout",
    (
        1e-4,
        1e-5,
        1e15,
        1e16,
        float.fromhex("0x0.0000000000001p-1022"),
        sys.float_info.max,
    ),
)
def test_deferred_cache_template_matches_python_float_spelling(timeout: float) -> None:
    base = _snapshot(
        "float-template",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
    )
    overlay = pyowl_core.apply_delta(
        base,
        pyowl_core.OntologyDelta(
            add_axioms=owl.CanonicalSet(
                (
                    owl.SubClassOf(
                        owl.Class(owl.IRI("urn:test:deferred#A")),
                        owl.Class(owl.IRI("urn:test:deferred#B")),
                    ),
                )
            )
        ),
    )
    eager = capture_compatible_view(overlay)
    deferred = capture_compatible_view_deferred(overlay)
    lease = negotiate_encoded_input(
        overlay,
        {ENCODED_SCHEMA_NAME: ENCODED_SCHEMA_VERSION},
    ).lease
    assert lease is not None
    config = ReasonerConfig(timeout=timeout)
    metadata, request = encode_deferred_encoded_session_metadata(
        deferred,
        config,
        structural_mode=_deferred_structural_mode(lease),
    )

    session = native._create_encoded_session_v1(
        slices=_encoded_slice_records(lease.root_slices()),
        metadata=metadata,
        config=encode_config(config),
        cancellation=native.CancellationHandle(),
        deferred_fingerprints=request,
        validate_profile=False,
    )
    try:
        assert session.ontology_fingerprint == compiler_cache_key(eager, config)
    finally:
        session.close()


def test_malformed_deferred_evidence_fails_closed_and_valid_retry_succeeds() -> None:
    base = _snapshot(
        "malformed",
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
    )
    overlay = pyowl_core.apply_delta(base, pyowl_core.OntologyDelta())
    eager = capture_compatible_view(overlay)
    deferred = capture_compatible_view_deferred(overlay)
    lease = negotiate_encoded_input(
        overlay,
        {ENCODED_SCHEMA_NAME: ENCODED_SCHEMA_VERSION},
    ).lease
    assert lease is not None
    config = ReasonerConfig(timeout=1e-5)
    metadata, request = encode_deferred_encoded_session_metadata(
        deferred,
        config,
        structural_mode=_deferred_structural_mode(lease),
    )
    slices = _encoded_slice_records(lease.root_slices())
    config_wire = encode_config(config)

    def construct(
        selected_request: tuple[int, str, str, bytes, bytes],
        *,
        selected_metadata: bytes = metadata,
    ) -> object:
        return native._create_encoded_session_v1(
            slices=slices,
            metadata=selected_metadata,
            config=config_wire,
            cancellation=native.CancellationHandle(),
            deferred_fingerprints=selected_request,
            validate_profile=False,
        )

    with pytest.raises(BackendMismatchError):
        construct((2, *request[1:]))
    alternate_template = request[-1].replace(b"1e-05", b"1e-5")
    assert alternate_template != request[-1]
    with pytest.raises(BackendMismatchError):
        construct((*request[:-1], alternate_template))
    with pytest.raises(BackendMismatchError):
        construct(
            request,
            selected_metadata=encode_encoded_session_metadata(eager, config),
        )

    retry = construct(request)
    retry.close()


def test_fingerprint_cancellation_and_budget_failures_discard_then_retry() -> None:
    sources = tuple(
        _snapshot(
            "budget",
            "Declaration(Class(:A))",
            "ClassAssertion(:A _:shared)",
        )
        for _ in range(2)
    )
    composite = pyowl_core.compose_views(*sources, roles=("first", "second"))
    deferred = capture_compatible_view_deferred(composite)
    lease = negotiate_encoded_input(
        composite,
        {ENCODED_SCHEMA_NAME: ENCODED_SCHEMA_VERSION},
    ).lease
    assert lease is not None
    config = ReasonerConfig()
    metadata, request = encode_deferred_encoded_session_metadata(
        deferred,
        config,
        structural_mode=_deferred_structural_mode(lease),
    )
    slices = _encoded_slice_records(lease.root_slices())
    arguments = {
        "slices": slices,
        "metadata": metadata,
        "config": encode_config(config),
        "deferred_fingerprints": request,
        "validate_profile": False,
    }

    with pytest.raises(ReasonerInterruptedError) as interrupted:
        native._create_encoded_session_v1(
            **arguments,
            cancellation=native.CancellationHandle(),
            cancel_at_checkpoint=13,
        )
    assert interrupted.value.context["phase"].startswith("source-fingerprint")

    with pytest.raises(ResourceLimitError, match="fingerprint"):
        native._create_encoded_session_v1(
            **arguments,
            cancellation=native.CancellationHandle(),
            max_owned_bytes=6_000,
        )

    retry = native._create_encoded_session_v1(
        **arguments,
        cancellation=native.CancellationHandle(),
    )
    try:
        assert retry._debug_source_fingerprints
    finally:
        retry.close()
