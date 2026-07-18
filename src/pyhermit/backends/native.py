"""Strict adapter for the private complete Rust backend.

SPDX-License-Identifier: LGPL-3.0-or-later

This module is imported only after :mod:`pyhermit.backends.dispatch` has established that the
extension advertises the complete WPR4 feature handshake. Native failures are never replayed in
Python. All inputs cross once as flat bytes and every returned byte buffer is validated before it
becomes a backend-neutral contract value.
"""

from __future__ import annotations

import importlib
import time
from collections.abc import Callable, Sequence
from contextlib import suppress
from types import ModuleType
from typing import NoReturn, Protocol, TypeVar, cast

from pyhermit._version import __version__
from pyhermit.backends.native_events import NativeSessionEvent, decode_events
from pyhermit.backends.native_wire import (
    decode_check,
    decode_check_many,
    decode_delta,
    decode_hierarchy,
    decode_realization,
)
from pyhermit.backends.protocol import (
    COMPILED_IR_SCHEMA_VERSION,
    BackendInfo,
    CheckResult,
    CompiledDelta,
    CompiledOntology,
    CompiledQuery,
    DeltaOutcome,
    HierarchyIds,
    RealizationIds,
)
from pyhermit.backends.verify import VerifyBackendFactory
from pyhermit.config import ReasonerConfig
from pyhermit.core import current_core_versions
from pyhermit.events import CancellationToken, ProgressCallback, ProgressEvent
from pyhermit.exceptions import (
    BackendMismatchError,
    BackendPoisonedError,
    BackendVersionError,
    DisposedReasonerError,
)

_REQUIRED_FEATURES = frozenset(
    {"classification", "full_reasoner", "incremental_updates", "realization"}
)
_SESSION_METHODS = (
    "apply_delta",
    "check",
    "check_many",
    "classify_classes",
    "classify_data_properties",
    "classify_object_properties",
    "close",
    "drain_events",
    "realize",
    "reset_query_state",
)
_T = TypeVar("_T")


class _CancellationHandle(Protocol):
    @property
    def interrupted(self) -> bool: ...

    def interrupt(self, reason: str | None = None) -> object: ...

    def reset(
        self,
        timeout: float | None = None,
        max_memory_bytes: int | None = None,
    ) -> None: ...


class _ExtensionSession(Protocol):
    @property
    def ontology_fingerprint(self) -> str: ...

    def check(self, query: bytes | None) -> bytes: ...

    def check_many(self, queries: Sequence[bytes]) -> bytes: ...

    def classify_classes(self) -> bytes: ...

    def classify_object_properties(self) -> bytes: ...

    def classify_data_properties(self) -> bytes: ...

    def realize(self) -> bytes: ...

    def apply_delta(self, delta: bytes) -> bytes: ...

    def drain_events(self) -> bytes: ...

    def reset_query_state(self) -> None: ...

    def close(self) -> None: ...


class _InputCodec(Protocol):
    def encode_ontology(self, ontology: CompiledOntology) -> bytes: ...

    def encode_config(self, config: ReasonerConfig) -> bytes: ...

    def encode_query(self, query: CompiledQuery) -> bytes: ...

    def encode_delta(self, delta: CompiledDelta) -> bytes: ...


class NativeBackendFactory:
    """Validate extension metadata and create one retained coarse native session."""

    __slots__ = ("_create_session", "_handle_type", "_info")

    def __init__(self, module: ModuleType) -> None:
        if not isinstance(module, ModuleType):
            raise TypeError("module must be the imported pyhermit._native extension")
        implementation = getattr(module, "__version__", None)
        abi = getattr(module, "ABI_VERSION", None)
        schema = getattr(module, "IR_SCHEMA_VERSION", None)
        features = getattr(module, "FEATURES", None)
        handle_type = getattr(module, "CancellationHandle", None)
        create_session = getattr(module, "create_session", None)
        self_test = getattr(module, "self_test", None)
        if not isinstance(implementation, str) or not implementation:
            _version_error("native implementation version is invalid", "metadata_invalid")
        if implementation != __version__:
            _version_error(
                "native implementation version does not match the Python package",
                "package_version_mismatch",
            )
        if abi != 1:
            _version_error("native ABI does not match the Python adapter", "abi_mismatch")
        if schema != COMPILED_IR_SCHEMA_VERSION:
            _version_error("native IR schema does not match the Python adapter", "schema_mismatch")
        if (
            not isinstance(features, tuple)
            or not all(isinstance(value, str) and value for value in features)
            or tuple(sorted(set(features))) != features
        ):
            _version_error("native feature metadata is invalid", "metadata_invalid")
        if not _REQUIRED_FEATURES.issubset(features):
            _version_error("native extension is not a complete reasoner", "incomplete_features")
        if (
            not isinstance(handle_type, type)
            or not callable(create_session)
            or not callable(self_test)
        ):
            _version_error("native extension surface is incomplete", "metadata_invalid")
        try:
            self_test()
        except Exception as error:
            raise BackendVersionError(
                "native extension self-test failed",
                context={"reason": "self_test_failed"},
            ) from error
        core = current_core_versions()
        self._handle_type = handle_type
        self._create_session = create_session
        self._info = BackendInfo(
            name="native",
            package_version=__version__,
            ir_schema_version=COMPILED_IR_SCHEMA_VERSION,
            implementation_version=implementation,
            core_package_version=core.package_version,
            core_api_version=core.api_version,
            core_model_schema_version=core.model_schema_version,
            core_wire_format_version=core.wire_format_version,
            core_adapter_protocol_version=core.adapter_protocol_version,
            complete_features=frozenset(features),
            accelerated=True,
        )

    @property
    def info(self) -> BackendInfo:
        return self._info

    def create_session(
        self,
        ontology: CompiledOntology,
        config: ReasonerConfig,
        cancellation: CancellationToken,
    ) -> NativeBackendSession:
        if not isinstance(ontology, CompiledOntology):
            raise TypeError("ontology must be CompiledOntology")
        if not isinstance(config, ReasonerConfig):
            raise TypeError("config must be ReasonerConfig")
        if not isinstance(cancellation, CancellationToken):
            raise TypeError("cancellation must be CancellationToken")
        cancellation.check()
        codec = _load_input_codec()
        ontology_wire = codec.encode_ontology(ontology)
        config_wire = codec.encode_config(config)
        _require_bytes(ontology_wire, "encoded ontology")
        _require_bytes(config_wire, "encoded configuration")
        cancellation.check()
        remaining = cancellation.remaining_seconds
        if remaining is not None and remaining <= 0:
            cancellation.check()
        handle_value = self._handle_type(
            timeout=remaining,
            max_memory_bytes=config.max_memory_bytes,
        )
        handle = cast(_CancellationHandle, handle_value)
        observer_id = cancellation._attach(handle)
        try:
            cancellation.check()
            native_value = self._create_session(ontology_wire, config_wire, handle_value)
            native = _require_native_session(native_value)
            adapter = NativeBackendSession(
                native,
                codec,
                cancellation,
                observer_id,
                ontology.ontology_fingerprint,
                config.progress,
            )
            cancellation.check()
            return adapter
        except BaseException:
            cancellation._detach(observer_id)
            close = getattr(locals().get("native_value"), "close", None)
            if callable(close):
                with suppress(Exception):
                    close()
            raise


class NativeBackendSession:
    """Backend-neutral validation/mapping shell around one Rust-owned session."""

    __slots__ = (
        "_cancellation",
        "_closed",
        "_codec",
        "_expected_fingerprint",
        "_native",
        "_observer_id",
        "_poisoned",
        "_progress",
    )

    def __init__(
        self,
        native: _ExtensionSession,
        codec: _InputCodec,
        cancellation: CancellationToken,
        observer_id: int,
        expected_fingerprint: str,
        progress: ProgressCallback | None,
    ) -> None:
        self._native = native
        self._codec = codec
        self._cancellation = cancellation
        self._observer_id = observer_id
        self._expected_fingerprint = expected_fingerprint
        self._progress = progress
        self._closed = False
        self._poisoned = False
        _ = self.ontology_fingerprint

    @property
    def ontology_fingerprint(self) -> str:
        self._require_usable()
        actual = self._native.ontology_fingerprint
        if type(actual) is not str or actual != self._expected_fingerprint:
            self._poisoned = True
            raise BackendMismatchError(
                "native session is bound to a different compiled ontology",
                context={"reason": "ontology_fingerprint_mismatch"},
            )
        return actual

    def check(self, query: CompiledQuery | None = None) -> CheckResult:
        self._begin_call()
        encoded = None if query is None else self._codec.encode_query(query)
        if encoded is not None:
            _require_bytes(encoded, "encoded query")
        return self._invoke(decode_check, lambda: self._native.check(encoded))

    def check_many(self, queries: object) -> tuple[CheckResult, ...]:
        self._begin_call()
        if isinstance(queries, (str, bytes)) or not isinstance(queries, Sequence):
            raise TypeError("queries must be a sequence of compiled queries")
        values = tuple(queries)
        encoded = tuple(self._codec.encode_query(cast(CompiledQuery, value)) for value in values)
        for value in encoded:
            _require_bytes(value, "encoded query")
        result = self._invoke(
            decode_check_many,
            lambda: self._native.check_many(encoded),
        )
        if len(result) != len(values):
            self._poisoned = True
            raise BackendMismatchError(
                "native batch result cardinality differs from its query batch",
                context={"reason": "batch_cardinality_mismatch"},
            )
        return result

    def classify_classes(self) -> HierarchyIds:
        return self._invoke(decode_hierarchy, self._native.classify_classes)

    def classify_object_properties(self) -> HierarchyIds:
        return self._invoke(decode_hierarchy, self._native.classify_object_properties)

    def classify_data_properties(self) -> HierarchyIds:
        return self._invoke(decode_hierarchy, self._native.classify_data_properties)

    def realize(self) -> RealizationIds:
        return self._invoke(decode_realization, self._native.realize)

    def apply_delta(self, delta: CompiledDelta) -> DeltaOutcome:
        self._begin_call()
        encoded = self._codec.encode_delta(delta)
        _require_bytes(encoded, "encoded delta")
        return self._invoke(decode_delta, lambda: self._native.apply_delta(encoded))

    def reset_query_state(self) -> None:
        self._begin_call()
        started = time.perf_counter()
        try:
            self._native.reset_query_state()
        except BaseException:
            with suppress(Exception):
                self._drain_events(started)
            raise
        self._drain_events(started)
        self._cancellation.check()

    def close(self) -> None:
        if self._closed:
            return
        self._native.close()
        self._cancellation._detach(self._observer_id)
        self._closed = True

    def _begin_call(self) -> None:
        self._require_usable()
        self._cancellation.check()

    def _decode(self, decoder: Callable[[bytes], _T], encoded: bytes) -> _T:
        try:
            value = decoder(encoded)
            self._cancellation.check()
            return value
        except (BackendMismatchError, TypeError):
            self._poisoned = True
            raise

    def _invoke(self, decoder: Callable[[bytes], _T], call: Callable[[], bytes]) -> _T:
        self._begin_call()
        started = time.perf_counter()
        try:
            value = self._decode(decoder, call())
        except BaseException:
            # Preserve the operation's public error.  A poisoned/panicking scheduler may
            # legitimately reject a subsequent drain, and that must not disguise the cause.
            with suppress(Exception):
                self._drain_events(started)
            raise
        self._drain_events(started)
        self._cancellation.check()
        return value

    def _drain_events(self, started: float) -> None:
        try:
            events = decode_events(self._native.drain_events())
        except (BackendMismatchError, TypeError):
            self._poisoned = True
            raise
        callback = self._progress
        if callback is None:
            return
        elapsed = max(0.0, time.perf_counter() - started)
        for event in events:
            progress = _progress_event(event, elapsed)
            try:
                callback(progress)
            except BaseException:
                # Cancellation propagation is best-effort here: the user's original callback
                # exception is the public error and must never be replaced by an observer fault.
                with suppress(Exception):
                    self._cancellation._interrupt("native progress callback raised")
                raise

    def _require_usable(self) -> None:
        if self._closed:
            raise DisposedReasonerError("native backend session is closed")
        if self._poisoned:
            raise BackendPoisonedError(
                "native backend adapter is poisoned after an invalid native result",
                code="NATIVE_RESULT_POISONED",
            )


def _load_input_codec() -> _InputCodec:
    module = importlib.import_module("pyhermit.backends.native_input")
    for name in ("encode_config", "encode_delta", "encode_ontology", "encode_query"):
        if not callable(getattr(module, name, None)):
            raise BackendVersionError(
                "native input codec surface is incomplete",
                context={"reason": "input_codec_invalid"},
            )
    return cast(_InputCodec, module)


def _require_native_session(value: object) -> _ExtensionSession:
    if not all(callable(getattr(value, name, None)) for name in _SESSION_METHODS) or not hasattr(
        value, "ontology_fingerprint"
    ):
        raise BackendVersionError(
            "native create_session returned an incompatible object",
            context={"reason": "session_surface_invalid"},
        )
    return cast(_ExtensionSession, value)


def _require_bytes(value: object, label: str) -> None:
    if type(value) is not bytes:
        raise BackendMismatchError(
            f"{label} must be exact bytes",
            context={"reason": "input_codec_invalid"},
        )


def _progress_event(event: NativeSessionEvent, elapsed: float) -> ProgressEvent:
    kinds = {
        "operation_started": "reasoning-started",
        "check_completed": "reasoning-progress",
        "query_state_reset": "query-state-reset",
        "operation_completed": "reasoning-completed",
        "operation_aborted": "reasoning-aborted",
    }
    details: dict[str, str | int | bool | None] = {
        "error_code": event.error_code,
        "native_sequence": event.sequence,
        "operation": event.operation,
        "query_hash": None if event.query_key is None else event.query_key.hex(),
        "satisfiable": event.satisfiable,
    }
    return ProgressEvent(
        version=1,
        operation_id=f"native-{event.operation.replace('_', '-')}-{event.operation_id}",
        kind=kinds[event.kind],
        completed=event.completed,
        total=event.total,
        elapsed_seconds=0.0 if event.kind == "operation_started" else elapsed,
        details=details,
    )


def _version_error(message: str, reason: str) -> NoReturn:
    raise BackendVersionError(message, context={"reason": reason})


__all__ = ["NativeBackendFactory", "NativeBackendSession", "VerifyBackendFactory"]
