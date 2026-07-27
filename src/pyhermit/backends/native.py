"""Strict adapter for the private complete Rust backend.

SPDX-License-Identifier: LGPL-3.0-or-later

This module is imported only after :mod:`pyhermit.backends.dispatch` has established that the
extension advertises the complete WPR4 feature handshake. Native failures are never replayed in
Python. All inputs cross once as flat bytes and every returned byte buffer is validated before it
becomes a backend-neutral contract value.
"""

from __future__ import annotations

import importlib
import json
import time
from collections.abc import Callable, Iterable, Mapping, Sequence
from contextlib import suppress
from types import MappingProxyType, ModuleType
from typing import NoReturn, Protocol, TypeVar, cast

from pyowl_core import Entity, OntologyView

from pyhermit._version import __version__
from pyhermit.backends.native_context import NativeServiceContext, decode_service_context
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
from pyhermit.config import ReasonerConfig, UnsupportedDatatypePolicy
from pyhermit.core import CapturedOntology, compiler_cache_key, current_core_versions
from pyhermit.encoded_input import (
    ENCODED_BUFFER_WIDTHS,
    ENCODED_NATIVE_FEATURE,
    ENCODED_SCHEMA_NAME,
    ENCODED_SCHEMA_VERSION,
    _encoded_profile_contexts,
    _encoded_slice_records,
    negotiate_encoded_input,
)
from pyhermit.events import CancellationToken, ProgressCallback, ProgressEvent
from pyhermit.exceptions import (
    BackendMismatchError,
    BackendPoisonedError,
    BackendVersionError,
    DisposedReasonerError,
)
from pyhermit.profile import OWL2DLReport

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


class _EncodedSegmentLease(Protocol):
    root_ids: memoryview
    anonymous_scope_map: memoryview


class _EncodedCompilerLease(Protocol):
    buffers: Mapping[str, memoryview]
    segments: tuple[_EncodedSegmentLease, ...]

    def local_leases(self) -> tuple[_EncodedCompilerLease, ...]: ...


def _encoded_ingestion_counters(lease: object) -> Mapping[str, bool | int]:
    """Freeze the shared zero-copy ledger for one negotiated compiler handoff."""

    compiler_lease = cast(_EncodedCompilerLease, lease)
    local_leases = compiler_lease.local_leases()
    buffer_count = sum(len(value.buffers) for value in local_leases)
    buffer_bytes = sum(buffer.nbytes for value in local_leases for buffer in value.buffers.values())
    segments = tuple(
        segment for value in local_leases for segment in getattr(value, "segments", ())
    )
    posting_bytes = sum(segment.root_ids.nbytes for segment in segments)
    staging_copy_bytes = sum(segment.anonymous_scope_map.nbytes for segment in segments)
    sidecar_count = sum(
        int(segment.root_ids.nbytes != 0) + int(segment.anonymous_scope_map.nbytes != 0)
        for segment in segments
    )
    return MappingProxyType(
        {
            "encoded_buffer_bytes": buffer_bytes,
            "encoded_buffer_count": buffer_count,
            "encoded_compiler_gil_released": False,
            "encoded_detached_buffer_count": buffer_count + sidecar_count,
            "encoded_indexed_buffer_count": 0,
            "encoded_posting_bytes": posting_bytes,
            "encoded_private_ir_bytes": 0,
            "encoded_referenced_view_count": max(0, len(local_leases) - 1),
            "encoded_segment_count": len(segments),
            "encoded_staging_copy_bytes": staging_copy_bytes,
            "encoded_zero_copy_buffers": buffer_count,
        }
    )


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

    @property
    def permanent_program_sha256(self) -> str: ...

    @property
    def compiler_digest(self) -> str | None: ...

    def check(self, query: bytes | None) -> bytes: ...

    def _encoded_service_context_v1(self) -> bytes: ...

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
    def encode_encoded_session_metadata(
        self,
        captured: CapturedOntology,
        config: ReasonerConfig,
    ) -> bytes: ...

    def encode_ontology(self, ontology: CompiledOntology) -> bytes: ...

    def encode_ontology_metadata(self, ontology: CompiledOntology) -> bytes: ...

    def encode_config(self, config: ReasonerConfig) -> bytes: ...

    def encode_query(self, query: CompiledQuery) -> bytes: ...

    def encode_delta(self, delta: CompiledDelta) -> bytes: ...


def _profile_manifest(profile: OWL2DLReport) -> dict[str, object]:
    issues = profile.issues
    return {
        "schema_version": 1,
        "family": "owl2_dl_profile",
        "conforms": profile.conforms,
        "axioms_checked": profile.axioms_checked,
        "extensions_checked": profile.extensions_checked,
        "ordered_rule_ids": [issue.rule_id for issue in issues],
        "issues": [
            {
                "rule_id": issue.rule_id,
                "severity": issue.severity.value,
                "message": issue.message,
                "constructor": issue.constructor,
                "document_keys": list(issue.document_keys),
                "provenance_sha256": issue.provenance_sha256,
            }
            for issue in issues
        ],
    }


def _json_values_are_exact(actual: object, expected: object) -> bool:
    """Compare decoded JSON without Python's bool/int/float coercions."""

    if type(actual) is not type(expected):
        return False
    if type(expected) is dict:
        actual_mapping = cast(dict[object, object], actual)
        expected_mapping = cast(dict[object, object], expected)
        return actual_mapping.keys() == expected_mapping.keys() and all(
            _json_values_are_exact(actual_mapping[key], value)
            for key, value in expected_mapping.items()
        )
    if type(expected) is list:
        actual_values = cast(list[object], actual)
        expected_values = cast(list[object], expected)
        return len(actual_values) == len(expected_values) and all(
            _json_values_are_exact(actual_item, expected_item)
            for actual_item, expected_item in zip(actual_values, expected_values, strict=True)
        )
    return actual == expected


def _reject_duplicate_json_keys(
    pairs: list[tuple[str, object]],
) -> dict[str, object]:
    """Build one JSON object while rejecting ambiguous duplicate names."""

    values: dict[str, object] = {}
    for key, value in pairs:
        if key in values:
            raise ValueError(f"duplicate JSON object key: {key}")
        values[key] = value
    return values


class NativeBackendFactory:
    """Validate extension metadata and create one retained coarse native session."""

    __slots__ = (
        "_create_encoded_session",
        "_create_session",
        "_handle_type",
        "_info",
        "_profile_encoded_slices",
        "_validate_encoded",
        "_validate_encoded_selection",
        "_validate_encoded_slices",
    )

    def __init__(self, module: ModuleType) -> None:
        if not isinstance(module, ModuleType):
            raise TypeError("module must be the imported pyhermit._native extension")
        implementation = getattr(module, "__version__", None)
        abi = getattr(module, "ABI_VERSION", None)
        schema = getattr(module, "IR_SCHEMA_VERSION", None)
        features = getattr(module, "FEATURES", None)
        handle_type = getattr(module, "CancellationHandle", None)
        create_session = getattr(module, "create_session", None)
        create_encoded_session = getattr(module, "_create_encoded_session_v1", None)
        self_test = getattr(module, "self_test", None)
        validate_encoded = getattr(module, "_validate_encoded_columns_v1", None)
        validate_encoded_selection = getattr(module, "_validate_encoded_selection_v1", None)
        validate_encoded_slices = getattr(module, "_validate_encoded_slices_v1", None)
        profile_encoded_slices = getattr(module, "_encoded_profile_slices_manifest_v1", None)
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
        if validate_encoded is not None and not callable(validate_encoded):
            _version_error("native encoded validator is invalid", "metadata_invalid")
        if create_encoded_session is not None and not callable(create_encoded_session):
            _version_error("native encoded session constructor is invalid", "metadata_invalid")
        if validate_encoded_selection is not None and not callable(validate_encoded_selection):
            _version_error("native encoded selection validator is invalid", "metadata_invalid")
        if validate_encoded_slices is not None and not callable(validate_encoded_slices):
            _version_error("native encoded slice validator is invalid", "metadata_invalid")
        if profile_encoded_slices is not None and not callable(profile_encoded_slices):
            _version_error("native encoded profile compiler is invalid", "metadata_invalid")
        if ENCODED_NATIVE_FEATURE in features and not all(
            callable(surface)
            for surface in (
                create_encoded_session,
                validate_encoded,
                validate_encoded_slices,
                profile_encoded_slices,
            )
        ):
            _version_error(
                "native encoded compiler capability surface is incomplete",
                "incomplete_features",
            )
        try:
            self_test()
        except Exception as error:
            raise BackendVersionError(
                "native extension self-test failed",
                context={"reason": "self_test_failed"},
            ) from error
        core = current_core_versions()
        self._handle_type = handle_type
        self._create_encoded_session = create_encoded_session
        self._create_session = create_session
        self._validate_encoded = validate_encoded
        self._validate_encoded_selection = validate_encoded_selection
        self._validate_encoded_slices = validate_encoded_slices
        self._profile_encoded_slices = profile_encoded_slices
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

    def _validate_encoded_handoff(self, view: OntologyView) -> None:
        """Privately preflight borrowed columns and the named class/ABox fragment."""

        validator = self._validate_encoded
        if validator is None:
            return
        negotiation = negotiate_encoded_input(
            view,
            {ENCODED_SCHEMA_NAME: ENCODED_SCHEMA_VERSION},
        )
        lease = negotiation.lease
        if lease is None:
            return
        planner = getattr(lease, "root_slices", None)
        root_slices = planner() if callable(planner) else lease.overlay_root_slices()
        slice_validator = self._validate_encoded_slices
        if slice_validator is not None and root_slices is not None:
            result = slice_validator(slices=_encoded_slice_records(root_slices))
            if result is not None:
                raise BackendMismatchError(
                    "native encoded validator returned an incompatible result",
                    context={"reason": "encoded_validator_result_invalid"},
                )
            return
        selection_validator = self._validate_encoded_selection
        if selection_validator is not None and root_slices is not None:
            for root_slice in root_slices:
                result = selection_validator(
                    posting_mode=root_slice.posting_mode,
                    postings=root_slice.root_ids,
                    **{name: root_slice.lease.buffers[name] for name in ENCODED_BUFFER_WIDTHS},
                )
                if result is not None:
                    raise BackendMismatchError(
                        "native encoded validator returned an incompatible result",
                        context={"reason": "encoded_validator_result_invalid"},
                    )
            return
        for local in lease.local_leases():
            result = validator(**{name: local.buffers[name] for name in ENCODED_BUFFER_WIDTHS})
            if result is not None:
                raise BackendMismatchError(
                    "native encoded validator returned an incompatible result",
                    context={"reason": "encoded_validator_result_invalid"},
                )

    def _validate_encoded_profile_handoff(
        self,
        view: OntologyView,
        profile: OWL2DLReport,
        unsupported_datatypes: UnsupportedDatatypePolicy,
        cancellation: CancellationToken | None = None,
        *,
        max_memory_bytes: int | None = None,
    ) -> None:
        """Compare the full origin-bearing native and scalar profile manifests."""

        profile_compiler = self._profile_encoded_slices
        if profile_compiler is None:
            return
        if not isinstance(profile, OWL2DLReport):
            raise TypeError("profile must be OWL2DLReport")
        if not isinstance(unsupported_datatypes, UnsupportedDatatypePolicy):
            raise TypeError("unsupported_datatypes must be UnsupportedDatatypePolicy")
        if cancellation is not None and not isinstance(cancellation, CancellationToken):
            raise TypeError("cancellation must be CancellationToken or None")
        if max_memory_bytes is not None:
            if isinstance(max_memory_bytes, bool) or not isinstance(max_memory_bytes, int):
                raise TypeError("max_memory_bytes must be a positive integer or None")
            if max_memory_bytes <= 0:
                raise ValueError("max_memory_bytes must be a positive integer or None")
        negotiation = negotiate_encoded_input(
            view,
            {ENCODED_SCHEMA_NAME: ENCODED_SCHEMA_VERSION},
        )
        lease = negotiation.lease
        if lease is None:
            return
        planner = getattr(lease, "root_slices", None)
        root_slices = planner() if callable(planner) else lease.overlay_root_slices()
        if root_slices is None:
            raise BackendMismatchError(
                "native encoded profile compiler received no root-slice plan",
                context={"reason": "encoded_profile_slices_missing"},
            )
        contexts = _encoded_profile_contexts(view)
        handle_value: object | None = None
        observer_id: int | None = None
        if cancellation is not None:
            cancellation.check()
            remaining = cancellation.remaining_seconds
            if remaining is not None and remaining <= 0:
                cancellation.check()
            handle_value = self._handle_type(
                timeout=remaining,
                max_memory_bytes=max_memory_bytes,
            )
            observer_id = cancellation._attach(cast(_CancellationHandle, handle_value))
        try:
            result = profile_compiler(
                slices=_encoded_slice_records(root_slices),
                unsupported_datatypes=unsupported_datatypes.value,
                ontology_identity_context=contexts.ontology_identity_context,
                origin_context=contexts.origin_context,
                cancellation=handle_value,
            )
            if cancellation is not None:
                cancellation.check()
        finally:
            if cancellation is not None and observer_id is not None:
                cancellation._detach(observer_id)
        if type(result) is not bytes:
            raise BackendMismatchError(
                "native encoded profile compiler returned an incompatible result",
                context={"reason": "encoded_profile_manifest_invalid"},
            )
        try:
            encoded = result.decode("utf-8", errors="strict")
            actual = json.loads(
                encoded,
                object_pairs_hook=_reject_duplicate_json_keys,
            )
        except (ValueError, RecursionError) as error:
            raise BackendMismatchError(
                "native encoded profile compiler returned malformed JSON",
                context={"reason": "encoded_profile_manifest_invalid"},
            ) from error
        expected = _profile_manifest(profile)
        if not _json_values_are_exact(actual, expected):
            raise BackendMismatchError(
                "native encoded profile manifest differs from scalar validation",
                context={"reason": "encoded_profile_manifest_mismatch"},
            )

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
        return self._construct_adapter_session(
            ontology.ontology_fingerprint,
            config,
            cancellation,
            codec,
            lambda handle: self._create_session(ontology_wire, config_wire, handle),
        )

    def _encoded_session_request(
        self,
        view: OntologyView,
    ) -> (
        tuple[
            Callable[..., object],
            tuple[tuple[object, ...], ...],
            Mapping[str, bool | int],
        ]
        | None
    ):
        """Resolve one negotiated direct-session request without consuming it."""

        if ENCODED_NATIVE_FEATURE not in self._info.complete_features:
            return None
        constructor = self._create_encoded_session
        if constructor is None:
            raise BackendVersionError(
                "native encoded session capability has no constructor",
                context={"reason": "encoded_session_constructor_missing"},
            )
        if not isinstance(view, OntologyView):
            raise TypeError("view must be OntologyView")
        negotiation = negotiate_encoded_input(
            view,
            {ENCODED_SCHEMA_NAME: ENCODED_SCHEMA_VERSION},
        )
        lease = negotiation.lease
        if lease is None:
            return None
        planner = getattr(lease, "root_slices", None)
        root_slices = planner() if callable(planner) else lease.overlay_root_slices()
        if root_slices is None:
            raise BackendMismatchError(
                "native encoded session constructor received no root-slice plan",
                context={"reason": "encoded_session_slices_missing"},
            )
        return (
            constructor,
            _encoded_slice_records(root_slices),
            _encoded_ingestion_counters(lease),
        )

    def _create_encoded_session_handoff(
        self,
        view: OntologyView,
        ontology: CompiledOntology,
        config: ReasonerConfig,
        cancellation: CancellationToken,
    ) -> NativeBackendSession | None:
        """Create a session without handing the proportional private IR to Rust."""

        if ENCODED_NATIVE_FEATURE not in self._info.complete_features:
            return None
        if not isinstance(view, OntologyView):
            raise TypeError("view must be OntologyView")
        if not isinstance(ontology, CompiledOntology):
            raise TypeError("ontology must be CompiledOntology")
        if not isinstance(config, ReasonerConfig):
            raise TypeError("config must be ReasonerConfig")
        if not isinstance(cancellation, CancellationToken):
            raise TypeError("cancellation must be CancellationToken")
        cancellation.check()
        request = self._encoded_session_request(view)
        if request is None:
            return None
        constructor, slices, ingestion_counters = request
        codec = _load_input_codec()
        metadata_encoder = getattr(codec, "encode_ontology_metadata", None)
        if not callable(metadata_encoder):
            raise BackendVersionError(
                "native metadata codec surface is incomplete",
                context={"reason": "input_codec_invalid"},
            )
        metadata = metadata_encoder(ontology)
        config_wire = codec.encode_config(config)
        _require_bytes(metadata, "encoded ontology metadata")
        _require_bytes(config_wire, "encoded configuration")
        return self._construct_adapter_session(
            ontology.ontology_fingerprint,
            config,
            cancellation,
            codec,
            lambda handle: constructor(
                slices=slices,
                metadata=metadata,
                config=config_wire,
                cancellation=handle,
            ),
            ingestion_counters=ingestion_counters,
        )

    def _create_encoded_lifecycle_handoff(
        self,
        captured: CapturedOntology,
        config: ReasonerConfig,
        cancellation: CancellationToken,
        *,
        validate_profile: bool = True,
    ) -> NativeBackendSession | None:
        """Publish a direct native session before any Python program is constructed."""

        if ENCODED_NATIVE_FEATURE not in self._info.complete_features:
            return None
        if not isinstance(captured, CapturedOntology):
            raise TypeError("captured must be CapturedOntology")
        if not isinstance(config, ReasonerConfig):
            raise TypeError("config must be ReasonerConfig")
        if not isinstance(cancellation, CancellationToken):
            raise TypeError("cancellation must be CancellationToken")
        if not isinstance(validate_profile, bool):
            raise TypeError("validate_profile must be bool")
        cancellation.check()
        request = self._encoded_session_request(captured.view)
        if request is None:
            return None
        constructor, slices, ingestion_counters = request
        codec = _load_input_codec()
        metadata_encoder = getattr(codec, "encode_encoded_session_metadata", None)
        if not callable(metadata_encoder):
            raise BackendVersionError(
                "native encoded-session metadata codec surface is incomplete",
                context={"reason": "input_codec_invalid"},
            )
        metadata = metadata_encoder(captured, config)
        config_wire = codec.encode_config(config)
        _require_bytes(metadata, "encoded ontology metadata")
        _require_bytes(config_wire, "encoded configuration")
        return self._construct_adapter_session(
            compiler_cache_key(captured, config),
            config,
            cancellation,
            codec,
            lambda handle: constructor(
                slices=slices,
                metadata=metadata,
                config=config_wire,
                cancellation=handle,
                validate_profile=validate_profile,
            ),
            ingestion_counters=ingestion_counters,
        )

    def _construct_adapter_session(
        self,
        expected_fingerprint: str,
        config: ReasonerConfig,
        cancellation: CancellationToken,
        codec: _InputCodec,
        invoke: Callable[[object], object],
        *,
        ingestion_counters: Mapping[str, bool | int] | None = None,
    ) -> NativeBackendSession:
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
            native_value = invoke(handle_value)
            native = _require_native_session(native_value)
            adapter = NativeBackendSession(
                native,
                codec,
                cancellation,
                observer_id,
                expected_fingerprint,
                config.progress,
                ingestion_counters,
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
        "_ingestion_counters",
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
        ingestion_counters: Mapping[str, bool | int] | None = None,
    ) -> None:
        self._native = native
        self._codec = codec
        self._cancellation = cancellation
        self._observer_id = observer_id
        self._expected_fingerprint = expected_fingerprint
        self._progress = progress
        self._ingestion_counters = MappingProxyType(dict(ingestion_counters or {}))
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

    @property
    def permanent_program_sha256(self) -> str:
        self._require_usable()
        actual = self._native.permanent_program_sha256
        if type(actual) is not str or len(actual) != 64:
            self._poisoned = True
            raise BackendMismatchError(
                "native session returned an invalid permanent-program digest",
                context={"reason": "program_fingerprint_invalid"},
            )
        try:
            decoded = bytes.fromhex(actual)
        except ValueError:
            decoded = b""
        if len(decoded) != 32 or decoded.hex() != actual:
            self._poisoned = True
            raise BackendMismatchError(
                "native session returned an invalid permanent-program digest",
                context={"reason": "program_fingerprint_invalid"},
            )
        return actual

    @property
    def compiler_digest(self) -> str:
        self._require_usable()
        actual = self._native.compiler_digest
        if type(actual) is not str or len(actual) != 64:
            self._poisoned = True
            raise BackendMismatchError(
                "native session returned an invalid compiler digest",
                context={"reason": "compiler_digest_invalid"},
            )
        try:
            decoded = bytes.fromhex(actual)
        except ValueError:
            decoded = b""
        if len(decoded) != 32 or decoded.hex() != actual:
            self._poisoned = True
            raise BackendMismatchError(
                "native session returned an invalid compiler digest",
                context={"reason": "compiler_digest_invalid"},
            )
        return actual

    @property
    def ingestion_counters(self) -> Mapping[str, bool | int]:
        """Return the immutable ledger captured for this session's input path."""

        return self._ingestion_counters

    def _encoded_service_context(
        self,
        signature: Iterable[Entity],
    ) -> NativeServiceContext:
        self._begin_call()
        exporter = getattr(self._native, "_encoded_service_context_v1", None)
        if not callable(exporter):
            raise BackendVersionError(
                "native encoded service-context surface is incomplete",
                context={"reason": "session_surface_invalid"},
            )
        try:
            encoded = exporter()
            _require_bytes(encoded, "encoded service context")
            context = decode_service_context(
                encoded,
                query_scope_digest=self.ontology_fingerprint,
                signature=signature,
            )
            if context.permanent_program_sha256 != self.permanent_program_sha256:
                raise BackendMismatchError(
                    "native service context is bound to a different permanent program",
                    context={"reason": "program_fingerprint_mismatch"},
                )
            if context.compiler_digest != self.compiler_digest:
                raise BackendMismatchError(
                    "native service context is bound to a different compiler manifest",
                    context={"reason": "compiler_digest_mismatch"},
                )
            self._cancellation.check()
            return context
        except (BackendMismatchError, TypeError, ValueError):
            self._poisoned = True
            raise

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
    for name in (
        "encode_config",
        "encode_delta",
        "encode_ontology",
        "encode_query",
    ):
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
