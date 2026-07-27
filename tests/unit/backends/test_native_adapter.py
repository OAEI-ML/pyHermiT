"""Strict flat-wire native adapter behavior with a fake private extension."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import hashlib
import json
import struct
import sys
from dataclasses import dataclass
from types import ModuleType, SimpleNamespace

import pyowl_core
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1

from pyhermit import __version__
from pyhermit.backends.native import NativeBackendFactory
from pyhermit.backends.native_events import (
    EVENT_HEADER_LENGTH,
    EVENT_MAGIC,
    EVENT_RECORD_LENGTH,
)
from pyhermit.backends.native_wire import RESULT_HEADER_LENGTH, RESULT_MAGIC, ResultKind
from pyhermit.backends.protocol import CompiledOntology, DeltaOutcome, EntityRef
from pyhermit.config import ReasonerConfig, UnsupportedDatatypePolicy
from pyhermit.encoded_input import (
    ENCODED_BUFFER_WIDTHS,
    ENCODED_NATIVE_FEATURE,
    ENCODED_SCHEMA_NAME,
    ENCODED_SCHEMA_VERSION,
)
from pyhermit.events import CancellationSource, ProgressEvent
from pyhermit.exceptions import BackendMismatchError, BackendPoisonedError, BackendVersionError
from pyhermit.facade import Reasoner
from pyhermit.profile import OWL2DLReport, validate_owl2_dl_view


@dataclass(frozen=True)
class _Fingerprint:
    digest: bytes
    algorithm: str = "sha256"
    schema: int = 1

    @property
    def hex(self) -> str:
        return self.digest.hex()


@dataclass(frozen=True)
class _IR:
    payload: bytes
    schema_version: int = 1

    def canonical_bytes(self) -> bytes:
        return self.payload


class _Handle:
    def __init__(
        self,
        timeout: float | None = None,
        max_memory_bytes: int | None = None,
    ) -> None:
        self.resets = [(timeout, max_memory_bytes)]
        self.interruptions: list[str | None] = []

    @property
    def interrupted(self) -> bool:
        return bool(self.interruptions)

    def interrupt(self, reason: str | None = None) -> bool:
        self.interruptions.append(reason)
        return True

    def reset(
        self,
        timeout: float | None = None,
        max_memory_bytes: int | None = None,
    ) -> None:
        self.resets.append((timeout, max_memory_bytes))


class _Session:
    def __init__(self, fingerprint: str) -> None:
        self.ontology_fingerprint = fingerprint
        self.closed = False
        self.last_query: bytes | None = None
        self.last_queries: tuple[bytes, ...] = ()
        self.last_delta: bytes | None = None
        self.check_document = _check_document(ResultKind.CHECK, (True,))
        self.events_document = _event_document(())

    def check(self, query: bytes | None) -> bytes:
        self.last_query = query
        return self.check_document

    def check_many(self, queries: tuple[bytes, ...]) -> bytes:
        self.last_queries = tuple(queries)
        return _check_document(ResultKind.CHECK_MANY, (True,) * len(queries))

    def classify_classes(self) -> bytes:
        return _hierarchy_document()

    def classify_object_properties(self) -> bytes:
        return _hierarchy_document()

    def classify_data_properties(self) -> bytes:
        return _hierarchy_document()

    def realize(self) -> bytes:
        return _realization_document()

    def apply_delta(self, delta: bytes) -> bytes:
        self.last_delta = delta
        return _document(ResultKind.DELTA, 1, b"\x02" + b"\0" * 7)

    def drain_events(self) -> bytes:
        document = self.events_document
        self.events_document = _event_document(())
        return document

    def reset_query_state(self) -> None:
        return None

    def close(self) -> None:
        self.closed = True


class _EncodedLease:
    def __init__(
        self,
        buffers: dict[str, memoryview],
        local: tuple[_EncodedLease, ...] | None = None,
        root_slices: tuple[object, ...] | None = None,
    ) -> None:
        self.buffers = buffers
        self._local = local
        self._root_slices = root_slices

    def local_leases(self) -> tuple[_EncodedLease, ...]:
        return (self,) if self._local is None else self._local

    def overlay_root_slices(self) -> tuple[object, ...] | None:
        return self._root_slices

    def root_slices(self) -> tuple[object, ...] | None:
        return self._root_slices


def _compiled() -> CompiledOntology:
    fingerprint = _Fingerprint(b"x" * 32)
    ir = _IR(b"ir")
    return CompiledOntology(
        schema_version=1,
        ontology_fingerprint="0" * 64,
        source_structural_fingerprint=fingerprint,
        source_logical_fingerprint=fingerprint,
        source_signature_fingerprint=fingerprint,
        core_package_version="0.1.0.dev0",
        core_api_version=(0, 1),
        core_model_schema_version=1,
        core_wire_format_version=(1, 0),
        core_adapter_protocol_version=1,
        symbols=ir,
        clauses=(),
        positive_facts=(),
        negative_facts=(),
        ground_disjunctions=(),
        role_model=ir,
        datatype_model=ir,
        expressivity=ir,
        declared_entities=(EntityRef("class", "urn:test:A", 0),),
        named_individuals=(0,),
        provenance=ir,
    )


def _extension() -> tuple[ModuleType, list[_Handle], list[_Session]]:
    module = ModuleType("pyhermit._native")
    module.__version__ = __version__
    module.ABI_VERSION = 1
    module.IR_SCHEMA_VERSION = 1
    module.FEATURES = (
        "classification",
        "full_reasoner",
        "incremental_updates",
        "realization",
    )
    handles: list[_Handle] = []
    sessions: list[_Session] = []

    def create_session(_ir: bytes, _config: bytes, handle: _Handle) -> _Session:
        handles.append(handle)
        session = _Session("0" * 64)
        sessions.append(session)
        return session

    module.CancellationHandle = _Handle
    module.create_session = create_session
    module.self_test = lambda: None
    return module, handles, sessions


def _profile_fixture() -> tuple[pyowl_core.OntologyView, OWL2DLReport]:
    options = pyowl_core.LoadOptions(
        imports=pyowl_core.ImportPolicy.IGNORE,
        backend=pyowl_core.BackendPreference.PYTHON,
    )
    snapshot = pyowl_core.load_snapshot(
        (
            b"Prefix(:=<urn:native-profile#>) "
            b"Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>) "
            b"Ontology(<urn:native-profile> "
            b"Declaration(Class(:A)) Declaration(DataProperty(:p)) "
            b"Declaration(DataProperty(:q)) "
            b"SubClassOf(:A DataSomeValuesFrom(:p :q xsd:string)))"
        ),
        document_iri="urn:native-profile:document",
        options=options,
    )
    return snapshot, validate_owl2_dl_view(snapshot)


def _profile_result(report: OWL2DLReport) -> bytes:
    return json.dumps(
        {
            "schema_version": 1,
            "family": "owl2_dl_profile",
            "conforms": report.conforms,
            "axioms_checked": report.axioms_checked,
            "extensions_checked": report.extensions_checked,
            "ordered_rule_ids": [issue.rule_id for issue in report.issues],
            "issues": [
                {
                    "rule_id": issue.rule_id,
                    "severity": issue.severity.value,
                    "message": issue.message,
                    "constructor": issue.constructor,
                    "document_keys": list(issue.document_keys),
                    "provenance_sha256": issue.provenance_sha256,
                }
                for issue in report.issues
            ],
        },
        separators=(",", ":"),
        sort_keys=True,
    ).encode()


def _profile_lease(snapshot: pyowl_core.OntologyView) -> _EncodedLease:
    published = produce_encoded_structural_view_v1(snapshot)
    lease = _EncodedLease(dict(published.buffers))
    lease._root_slices = (
        SimpleNamespace(
            lease=lease,
            posting_mode=0,
            root_ids=memoryview(b""),
            member_tokens=(),
            anonymous_scope_maps=(),
        ),
    )
    return lease


def _install_codec(monkeypatch: pytest.MonkeyPatch) -> None:
    codec = ModuleType("pyhermit.backends.native_input")
    codec.encode_ontology = lambda _value: b"ontology"
    codec.encode_config = lambda _value: b"config"
    codec.encode_query = lambda _value: b"query"
    codec.encode_delta = lambda _value: b"delta"
    monkeypatch.setitem(sys.modules, codec.__name__, codec)


def _document(kind: ResultKind, count: int, payload: bytes) -> bytes:
    encoded = bytearray(RESULT_HEADER_LENGTH)
    encoded.extend(payload)
    struct.pack_into(
        "<8sHHIQII32s",
        encoded,
        0,
        RESULT_MAGIC,
        1,
        kind,
        0,
        len(encoded),
        count,
        0,
        hashlib.sha256(payload).digest(),
    )
    return bytes(encoded)


def _check_document(kind: ResultKind, values: tuple[bool, ...]) -> bytes:
    payload = b"".join(struct.pack("<B7x7Q", int(value), 0, 0, 0, 0, 0, 0, 0) for value in values)
    return _document(kind, len(values), payload)


def _event_record(
    *,
    sequence: int,
    kind: int,
    completed: int = 0,
    query_key: bytes | None = None,
    satisfiable: int = 0,
) -> bytes:
    return struct.pack(
        "<HBBIQQII32sB7xII",
        1,
        1,
        kind,
        int(query_key is not None),
        sequence,
        3,
        completed,
        1,
        bytes(32) if query_key is None else query_key,
        satisfiable,
        0,
        0,
    )


def _event_document(records: tuple[bytes, ...]) -> bytes:
    payload = b"".join(records)
    return (
        struct.pack(
            "<8sHHIQII32s",
            EVENT_MAGIC,
            1,
            EVENT_RECORD_LENGTH,
            0,
            EVENT_HEADER_LENGTH + len(payload),
            len(records),
            0,
            hashlib.sha256(payload).digest(),
        )
        + payload
    )


def _u32s(*values: int) -> bytes:
    return struct.pack(f"<{len(values)}I", *values)


def _hierarchy_document() -> bytes:
    payload = b"".join(
        (
            _u32s(2, 2, 1, 0, 1, 0),
            _u32s(0, 1, 2),
            _u32s(0, 1),
            _u32s(1, 0),
        )
    )
    return _document(ResultKind.HIERARCHY, 2, payload)


def _realization_document() -> bytes:
    payload = b"".join((_u32s(1, 1, 0, 0, 0, 0, 0, 0, 0, 0), _u32s(0, 1), _u32s(0)))
    return _document(ResultKind.REALIZATION, 1, payload)


def test_factory_maps_all_coarse_operations_and_cancellation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_codec(monkeypatch)
    extension, handles, native_sessions = _extension()
    source = CancellationSource()
    session = NativeBackendFactory(extension).create_session(
        _compiled(), ReasonerConfig(), source.token
    )

    assert session.check().satisfiable
    assert session.check_many((object(), object()))[1].satisfiable  # type: ignore[arg-type]
    assert session.classify_classes().nodes == ((0,), (1,))
    assert session.classify_object_properties().edges == ((1, 0),)
    assert session.classify_data_properties().top_node == 0
    assert session.realize().same_as == ((0,),)
    assert session.apply_delta(object()) is DeltaOutcome.REBUILD_REQUIRED  # type: ignore[arg-type]
    assert native_sessions[0].last_delta == b"delta"

    source.begin_operation(timeout=None, max_memory_bytes=256)
    source.interrupt("stop-native")
    assert handles[0].resets[-1] == (None, 256)
    assert handles[0].interruptions == ["stop-native"]
    session.close()


def test_invalid_result_poisoning_is_fail_closed(monkeypatch: pytest.MonkeyPatch) -> None:
    _install_codec(monkeypatch)
    extension, _handles, sessions = _extension()
    session = NativeBackendFactory(extension).create_session(
        _compiled(), ReasonerConfig(), CancellationSource().token
    )
    sessions[0].check_document = b"corrupt"

    with pytest.raises(BackendMismatchError):
        session.check()
    with pytest.raises(BackendPoisonedError):
        session.check()
    session.close()


def test_factory_rejects_an_incomplete_feature_handshake() -> None:
    extension, _handles, _sessions = _extension()
    extension.FEATURES = ("classification",)
    with pytest.raises(BackendVersionError, match="complete reasoner"):
        NativeBackendFactory(extension)


@pytest.mark.parametrize(
    "missing_surface",
    (
        "_create_encoded_session_v1",
        "_validate_encoded_columns_v1",
        "_validate_encoded_slices_v1",
        "_encoded_profile_slices_manifest_v1",
    ),
)
def test_factory_rejects_an_incomplete_encoded_compiler_handshake(
    missing_surface: str,
) -> None:
    extension, _handles, _sessions = _extension()
    extension.FEATURES = tuple(sorted((*extension.FEATURES, ENCODED_NATIVE_FEATURE)))
    extension._create_encoded_session_v1 = lambda **_values: object()
    extension._validate_encoded_columns_v1 = lambda **_values: None
    extension._validate_encoded_slices_v1 = lambda **_values: None
    extension._encoded_profile_slices_manifest_v1 = lambda **_values: b"{}"
    delattr(extension, missing_surface)

    with pytest.raises(
        BackendVersionError,
        match="encoded compiler capability surface is incomplete",
    ) as caught:
        NativeBackendFactory(extension)

    assert caught.value.context["reason"] == "incomplete_features"


def test_factory_rejects_a_package_version_mismatch() -> None:
    extension, _handles, _sessions = _extension()
    extension.__version__ = "0.1.0.other"
    with pytest.raises(BackendVersionError) as caught:
        NativeBackendFactory(extension)
    assert caught.value.context["reason"] == "package_version_mismatch"


def test_encoded_handoff_is_absent_without_requesting_core_buffers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    extension, _handles, _sessions = _extension()
    factory = NativeBackendFactory(extension)

    def unexpected_negotiation(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("encoded input must not be requested without a native validator")

    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        unexpected_negotiation,
    )

    factory._validate_encoded_handoff(object())  # type: ignore[arg-type]


def test_encoded_handoff_preserves_scalar_fallback_when_core_schema_is_absent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    extension, _handles, _sessions = _extension()
    validated = False
    requested: dict[str, int] = {}

    def validate(**_buffers: memoryview) -> None:
        nonlocal validated
        validated = True

    def negotiate(_view: object, schemas: dict[str, int]) -> object:
        requested.update(schemas)
        return SimpleNamespace(lease=None)

    extension._validate_encoded_columns_v1 = validate
    monkeypatch.setattr("pyhermit.backends.native.negotiate_encoded_input", negotiate)

    NativeBackendFactory(extension)._validate_encoded_handoff(object())  # type: ignore[arg-type]

    assert requested == {ENCODED_SCHEMA_NAME: ENCODED_SCHEMA_VERSION}
    assert not validated


def test_encoded_handoff_borrows_the_exact_public_column_ledger(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    extension, _handles, _sessions = _extension()
    buffers = {name: memoryview(bytes([index])) for index, name in enumerate(ENCODED_BUFFER_WIDTHS)}
    received: dict[str, memoryview] = {}

    def validate(**values: memoryview) -> None:
        received.update(values)

    extension._validate_encoded_columns_v1 = validate
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(lease=_EncodedLease(buffers)),
    )
    factory = NativeBackendFactory(extension)

    factory._validate_encoded_handoff(object())  # type: ignore[arg-type]

    assert tuple(received) == tuple(ENCODED_BUFFER_WIDTHS)
    assert all(received[name] is buffers[name] for name in ENCODED_BUFFER_WIDTHS)
    assert ENCODED_NATIVE_FEATURE not in factory.info.complete_features


def test_encoded_handoff_preflights_each_unique_segment_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    extension, _handles, _sessions = _extension()
    top_buffers = {name: memoryview(b"top") for name in ENCODED_BUFFER_WIDTHS}
    source_buffers = {name: memoryview(b"source") for name in ENCODED_BUFFER_WIDTHS}
    source = _EncodedLease(source_buffers)
    top = _EncodedLease(top_buffers)
    top._local = (top, source)
    observed: list[memoryview] = []

    def validate(**buffers: memoryview) -> None:
        observed.append(buffers["scalar_bytes"])

    extension._validate_encoded_columns_v1 = validate
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(lease=top),
    )

    NativeBackendFactory(extension)._validate_encoded_handoff(object())  # type: ignore[arg-type]

    assert observed == [top_buffers["scalar_bytes"], source_buffers["scalar_bytes"]]


def test_encoded_handoff_reuses_overlay_sources_with_exact_root_selections(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    extension, _handles, _sessions = _extension()
    base_buffers = {name: memoryview(b"base") for name in ENCODED_BUFFER_WIDTHS}
    delta_buffers = {name: memoryview(b"delta") for name in ENCODED_BUFFER_WIDTHS}
    base = _EncodedLease(base_buffers)
    postings = memoryview(b"\x01\x00\x00\x00")
    delta_postings = memoryview(b"")
    delta = _EncodedLease(delta_buffers)
    delta._root_slices = (
        SimpleNamespace(lease=base, posting_mode=2, root_ids=postings),
        SimpleNamespace(lease=delta, posting_mode=0, root_ids=delta_postings),
    )
    observed: list[tuple[int, memoryview, dict[str, memoryview]]] = []

    def unexpected_columns(**_buffers: memoryview) -> None:
        raise AssertionError("overlay handoff must use the selection-aware validator")

    def validate_selection(
        *, posting_mode: int, postings: memoryview, **buffers: memoryview
    ) -> None:
        observed.append((posting_mode, postings, buffers))

    extension._validate_encoded_columns_v1 = unexpected_columns
    extension._validate_encoded_selection_v1 = validate_selection
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(lease=delta),
    )

    NativeBackendFactory(extension)._validate_encoded_handoff(object())  # type: ignore[arg-type]

    assert [(mode, selected) for mode, selected, _buffers in observed] == [
        (2, postings),
        (0, delta_postings),
    ]
    assert observed[0][1] is postings
    assert observed[1][1] is delta_postings
    assert all(
        observed[0][2][name] is base_buffers[name] and observed[1][2][name] is delta_buffers[name]
        for name in ENCODED_BUFFER_WIDTHS
    )


def test_encoded_handoff_submits_one_contextual_multi_slice_transaction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    extension, _handles, _sessions = _extension()
    base_buffers = {name: memoryview(b"base") for name in ENCODED_BUFFER_WIDTHS}
    delta_buffers = {name: memoryview(b"delta") for name in ENCODED_BUFFER_WIDTHS}
    base = _EncodedLease(base_buffers)
    delta = _EncodedLease(delta_buffers)
    postings = memoryview(b"\x01\x00\x00\x00")
    token = b"t" * 32
    scope_map = memoryview(b"a" * 32 + b"b" * 32)
    delta._root_slices = (
        SimpleNamespace(
            lease=base,
            posting_mode=1,
            root_ids=postings,
            member_tokens=(token,),
            anonymous_scope_maps=(scope_map,),
        ),
        SimpleNamespace(
            lease=delta,
            posting_mode=0,
            root_ids=memoryview(b""),
            member_tokens=(),
            anonymous_scope_maps=(),
        ),
    )
    observed: list[tuple[tuple[object, ...], ...]] = []

    def unexpected_columns(**_buffers: memoryview) -> None:
        raise AssertionError("multi-slice handoff must use one owned transaction")

    def unexpected_selection(**_fields: object) -> None:
        raise AssertionError("multi-slice handoff must not publish independent fragments")

    def validate_slices(*, slices: tuple[tuple[object, ...], ...]) -> None:
        observed.append(slices)

    extension._validate_encoded_columns_v1 = unexpected_columns
    extension._validate_encoded_selection_v1 = unexpected_selection
    extension._validate_encoded_slices_v1 = validate_slices
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(lease=delta),
    )

    NativeBackendFactory(extension)._validate_encoded_handoff(object())  # type: ignore[arg-type]

    assert len(observed) == 1
    records = observed[0]
    assert len(records) == 2
    assert records[0][:4] == (1, postings, (token,), (scope_map,))
    assert records[1][:4] == (0, delta._root_slices[1].root_ids, (), ())
    assert records[0][4] is base_buffers["root_kinds"]
    assert records[0][-1] is base_buffers["scalar_bytes"]
    assert records[1][4] is delta_buffers["root_kinds"]
    assert records[1][-1] is delta_buffers["scalar_bytes"]


def test_encoded_handoff_is_fail_closed_after_advertised_input_is_observed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    extension, _handles, _sessions = _extension()
    failure = BackendMismatchError("hostile encoded columns")

    def reject(**_buffers: memoryview) -> None:
        raise failure

    extension._validate_encoded_columns_v1 = reject
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(
            lease=_EncodedLease({name: memoryview(b"") for name in ENCODED_BUFFER_WIDTHS})
        ),
    )

    with pytest.raises(BackendMismatchError) as caught:
        NativeBackendFactory(extension)._validate_encoded_handoff(object())  # type: ignore[arg-type]

    assert caught.value is failure


def test_encoded_handoff_rejects_a_non_none_native_result(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    extension, _handles, _sessions = _extension()
    extension._validate_encoded_columns_v1 = lambda **_buffers: object()
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(
            lease=_EncodedLease({name: memoryview(b"") for name in ENCODED_BUFFER_WIDTHS})
        ),
    )

    with pytest.raises(BackendMismatchError) as caught:
        NativeBackendFactory(extension)._validate_encoded_handoff(object())  # type: ignore[arg-type]

    assert caught.value.context["reason"] == "encoded_validator_result_invalid"


def test_profile_handoff_is_absent_without_requesting_core_buffers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    extension, _handles, _sessions = _extension()
    factory = NativeBackendFactory(extension)

    def unexpected_negotiation(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("encoded input must not be requested without a profile compiler")

    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        unexpected_negotiation,
    )

    factory._validate_encoded_profile_handoff(  # type: ignore[arg-type]
        object(),
        object(),
        object(),
    )


def test_profile_handoff_supplies_full_context_and_matches_scalar_report(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    extension, _handles, _sessions = _extension()
    snapshot, report = _profile_fixture()
    received: dict[str, object] = {}

    def compile_profile(**values: object) -> bytes:
        received.update(values)
        return _profile_result(report)

    extension._encoded_profile_slices_manifest_v1 = compile_profile
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(lease=_profile_lease(snapshot)),
    )

    NativeBackendFactory(extension)._validate_encoded_profile_handoff(
        snapshot,
        report,
        UnsupportedDatatypePolicy.ERROR,
    )

    assert received["unsupported_datatypes"] == "error"
    slices = received["slices"]
    assert isinstance(slices, tuple) and len(slices) == 1
    assert len(slices[0]) == 15
    identity_version, identity_rows = received["ontology_identity_context"]  # type: ignore[misc]
    assert identity_version == 1
    assert len(identity_rows) == 1
    assert identity_rows[0][1:] == ("urn:native-profile", None)
    origin_version, origin_rows = received["origin_context"]  # type: ignore[misc]
    assert origin_version == 1
    assert origin_rows
    assert all(
        document_keys == (identity_rows[0][0],) for _provenance, document_keys in origin_rows
    )


@pytest.mark.parametrize("compiler_fails", (False, True), ids=("success", "failure"))
def test_profile_handoff_binds_and_detaches_operation_cancellation(
    monkeypatch: pytest.MonkeyPatch,
    compiler_fails: bool,
) -> None:
    extension, _handles, _sessions = _extension()
    snapshot, report = _profile_fixture()
    handles: list[_Handle] = []
    received: dict[str, object] = {}
    failure = RuntimeError("profile compiler failed")

    class TrackingHandle(_Handle):
        def __init__(
            self,
            timeout: float | None = None,
            max_memory_bytes: int | None = None,
        ) -> None:
            super().__init__(timeout, max_memory_bytes)
            handles.append(self)

    def compile_profile(**values: object) -> bytes:
        received.update(values)
        if compiler_fails:
            raise failure
        return _profile_result(report)

    extension.CancellationHandle = TrackingHandle
    extension._encoded_profile_slices_manifest_v1 = compile_profile
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(lease=_profile_lease(snapshot)),
    )
    source = CancellationSource()
    source.begin_operation(timeout=60.0, max_memory_bytes=4_096)
    factory = NativeBackendFactory(extension)

    if compiler_fails:
        with pytest.raises(RuntimeError) as caught:
            factory._validate_encoded_profile_handoff(
                snapshot,
                report,
                UnsupportedDatatypePolicy.ERROR,
                source.token,
                max_memory_bytes=4_096,
            )
        assert caught.value is failure
    else:
        factory._validate_encoded_profile_handoff(
            snapshot,
            report,
            UnsupportedDatatypePolicy.ERROR,
            source.token,
            max_memory_bytes=4_096,
        )

    assert len(handles) == 1
    assert received["cancellation"] is handles[0]
    timeout, memory_limit = handles[0].resets[0]
    assert timeout is not None and 0 < timeout <= 60.0
    assert memory_limit == 4_096
    assert source.interrupt("after-profile") is True
    assert handles[0].interruptions == []


def test_profile_handoff_rejects_native_scalar_manifest_drift(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    extension, _handles, _sessions = _extension()
    snapshot, report = _profile_fixture()
    extension._encoded_profile_slices_manifest_v1 = lambda **_values: b"{}"
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(lease=_profile_lease(snapshot)),
    )

    with pytest.raises(BackendMismatchError) as caught:
        NativeBackendFactory(extension)._validate_encoded_profile_handoff(
            snapshot,
            report,
            UnsupportedDatatypePolicy.ERROR,
        )

    assert caught.value.context["reason"] == "encoded_profile_manifest_mismatch"


def test_profile_handoff_rejects_duplicate_json_keys(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    extension, _handles, _sessions = _extension()
    snapshot, report = _profile_fixture()
    result = _profile_result(report)
    expected = b'"schema_version":1'
    assert result.count(expected) == 1
    extension._encoded_profile_slices_manifest_v1 = lambda **_values: result.replace(
        expected,
        b'"schema_version":2,"schema_version":1',
        1,
    )
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(lease=_profile_lease(snapshot)),
    )

    with pytest.raises(BackendMismatchError) as caught:
        NativeBackendFactory(extension)._validate_encoded_profile_handoff(
            snapshot,
            report,
            UnsupportedDatatypePolicy.ERROR,
        )

    assert caught.value.context["reason"] == "encoded_profile_manifest_invalid"


@pytest.mark.parametrize(
    "encoding_case",
    ["utf-16", "utf-8-bom", "invalid-utf-8"],
)
def test_profile_handoff_rejects_noncanonical_json_encoding(
    monkeypatch: pytest.MonkeyPatch,
    encoding_case: str,
) -> None:
    extension, _handles, _sessions = _extension()
    snapshot, report = _profile_fixture()
    result = _profile_result(report)
    if encoding_case == "utf-16":
        result = result.decode("utf-8").encode("utf-16")
    elif encoding_case == "utf-8-bom":
        result = b"\xef\xbb\xbf" + result
    else:
        result = b"\xff" + result
    extension._encoded_profile_slices_manifest_v1 = lambda **_values: result
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(lease=_profile_lease(snapshot)),
    )

    with pytest.raises(BackendMismatchError) as caught:
        NativeBackendFactory(extension)._validate_encoded_profile_handoff(
            snapshot,
            report,
            UnsupportedDatatypePolicy.ERROR,
        )

    assert caught.value.context["reason"] == "encoded_profile_manifest_invalid"


@pytest.mark.parametrize(
    "schema_version",
    [True, 1.0],
    ids=["bool-for-int", "float-for-int"],
)
def test_profile_handoff_rejects_json_scalar_type_coercion(
    monkeypatch: pytest.MonkeyPatch,
    schema_version: object,
) -> None:
    extension, _handles, _sessions = _extension()
    snapshot, report = _profile_fixture()
    manifest = json.loads(_profile_result(report))
    assert manifest["schema_version"] == schema_version
    assert type(manifest["schema_version"]) is not type(schema_version)
    manifest["schema_version"] = schema_version
    extension._encoded_profile_slices_manifest_v1 = lambda **_values: json.dumps(
        manifest,
        separators=(",", ":"),
        sort_keys=True,
    ).encode()
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(lease=_profile_lease(snapshot)),
    )

    with pytest.raises(BackendMismatchError) as caught:
        NativeBackendFactory(extension)._validate_encoded_profile_handoff(
            snapshot,
            report,
            UnsupportedDatatypePolicy.ERROR,
        )

    assert caught.value.context["reason"] == "encoded_profile_manifest_mismatch"


def test_facade_binds_profile_validation_to_the_active_operation() -> None:
    snapshot, report = _profile_fixture()
    reasoner = object.__new__(Reasoner)
    reasoner._config = ReasonerConfig(max_memory_bytes=8_192)
    reasoner._cancellation = CancellationSource()
    reasoner._cancellation.begin_operation(timeout=60.0, max_memory_bytes=8_192)
    received: dict[str, object] = {}

    def validate(
        view: object,
        profile: object,
        unsupported_datatypes: object,
        cancellation: object,
        *,
        max_memory_bytes: object,
    ) -> None:
        received.update(
            {
                "view": view,
                "profile": profile,
                "unsupported_datatypes": unsupported_datatypes,
                "cancellation": cancellation,
                "max_memory_bytes": max_memory_bytes,
            }
        )

    reasoner._factory = SimpleNamespace(_validate_encoded_profile_handoff=validate)
    validator = reasoner._encoded_profile_validator()
    assert validator is not None

    validator(snapshot, report, UnsupportedDatatypePolicy.ERROR)

    assert received == {
        "view": snapshot,
        "profile": report,
        "unsupported_datatypes": UnsupportedDatatypePolicy.ERROR,
        "cancellation": reasoner._cancellation.token,
        "max_memory_bytes": 8_192,
    }


def test_facade_runs_the_encoded_gate_before_scalar_compilation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    reasoner = object.__new__(Reasoner)
    reasoner._config = ReasonerConfig()
    observed_view = object()
    failure = BackendMismatchError("hostile encoded columns")

    def reject(view: object) -> None:
        assert view is observed_view
        raise failure

    def unexpected_compile(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("scalar compilation must not run after encoded rejection")

    reasoner._factory = SimpleNamespace(_validate_encoded_handoff=reject)
    monkeypatch.setattr("pyhermit.facade.compile_captured_bundle", unexpected_compile)

    with pytest.raises(BackendMismatchError) as caught:
        reasoner._compile_runtime(SimpleNamespace(view=observed_view))  # type: ignore[arg-type]

    assert caught.value is failure


def test_facade_reaches_scalar_compilation_when_the_private_gate_is_absent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    reasoner = object.__new__(Reasoner)
    reasoner._config = ReasonerConfig()
    reasoner._factory = SimpleNamespace()
    reached_scalar = RuntimeError("scalar compilation reached")

    def stop_at_scalar(*_args: object, **_kwargs: object) -> object:
        raise reached_scalar

    monkeypatch.setattr("pyhermit.facade.compile_captured_bundle", stop_at_scalar)

    with pytest.raises(RuntimeError) as caught:
        reasoner._compile_runtime(  # type: ignore[arg-type]
            SimpleNamespace(view=object(), captured=object())
        )

    assert caught.value is reached_scalar


def test_events_are_validated_and_callbacks_run_after_native_return(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_codec(monkeypatch)
    extension, _handles, sessions = _extension()
    events: list[ProgressEvent] = []
    session = NativeBackendFactory(extension).create_session(
        _compiled(), ReasonerConfig(progress=events.append), CancellationSource().token
    )
    sessions[0].events_document = _event_document(
        (
            _event_record(sequence=1, kind=1),
            _event_record(
                sequence=2,
                kind=2,
                completed=1,
                query_key=bytes([4]) * 32,
                satisfiable=2,
            ),
            _event_record(sequence=3, kind=4, completed=1),
        )
    )

    assert session.check().satisfiable
    assert [event.kind for event in events] == [
        "reasoning-started",
        "reasoning-progress",
        "reasoning-completed",
    ]
    assert events[0].elapsed_seconds == 0.0
    assert events[1].details["query_hash"] == "04" * 32


def test_malformed_event_drain_poisons_and_callback_error_cancels(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_codec(monkeypatch)
    extension, _handles, sessions = _extension()
    session = NativeBackendFactory(extension).create_session(
        _compiled(), ReasonerConfig(), CancellationSource().token
    )
    sessions[0].events_document = b"corrupt"
    with pytest.raises(BackendMismatchError):
        session.check()
    with pytest.raises(BackendPoisonedError):
        session.check()
    session.close()

    source = CancellationSource()

    def fail(_event: object) -> None:
        raise RuntimeError("callback failed")

    callback_session = NativeBackendFactory(extension).create_session(
        _compiled(), ReasonerConfig(progress=fail), source.token
    )
    sessions[-1].events_document = _event_document((_event_record(sequence=1, kind=1),))
    with pytest.raises(RuntimeError, match="callback failed"):
        callback_session.check()
    assert source.token.interrupted
    source.begin_operation()
    assert callback_session.check().satisfiable
    callback_session.close()
