"""Strict flat-wire native adapter behavior with a fake private extension."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import hashlib
import struct
import sys
from dataclasses import dataclass
from types import ModuleType

import pytest

from pyhermit.backends.native import NativeBackendFactory
from pyhermit.backends.native_events import (
    EVENT_HEADER_LENGTH,
    EVENT_MAGIC,
    EVENT_RECORD_LENGTH,
)
from pyhermit.backends.native_wire import RESULT_HEADER_LENGTH, RESULT_MAGIC, ResultKind
from pyhermit.backends.protocol import CompiledOntology, DeltaOutcome, EntityRef
from pyhermit.config import ReasonerConfig
from pyhermit.events import CancellationSource, ProgressEvent
from pyhermit.exceptions import BackendMismatchError, BackendPoisonedError, BackendVersionError


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
    module.__version__ = "0.1.0-test"
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
    payload = b"".join(
        struct.pack("<B7x7Q", int(value), 0, 0, 0, 0, 0, 0, 0) for value in values
    )
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
    return struct.pack(
        "<8sHHIQII32s",
        EVENT_MAGIC,
        1,
        EVENT_RECORD_LENGTH,
        0,
        EVENT_HEADER_LENGTH + len(payload),
        len(records),
        0,
        hashlib.sha256(payload).digest(),
    ) + payload


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
