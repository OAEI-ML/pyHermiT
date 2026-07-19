"""Negotiated public pyowl-core input for the successor native compiler.

This module deliberately treats structural columns as opaque buffers.  It
validates the public envelope and retains every owner needed by a future coarse
Rust call, but it does not import ``pyowl_core._native`` or interpret schema-
local identifiers in Python.
"""

from __future__ import annotations

import hashlib
from collections.abc import Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Any

import pyowl_core as owl

ENCODED_SCHEMA_NAME = "pyowl-core/structural-columns"
ENCODED_SCHEMA_VERSION = 1
ENCODED_NATIVE_FEATURE = "encoded-structural-compiler-v1"


@dataclass(frozen=True, slots=True, eq=False)
class EncodedStructuralLease:
    """Validated encoded envelope and the exact public owner that keeps it alive."""

    encoded_view: object
    owner: owl.OntologyView
    schema_name: str
    schema_version: int
    model_schema: int
    scope: owl.AxiomScope
    descriptor: bytes
    descriptor_digest: bytes
    buffers: Mapping[str, memoryview]
    segments: tuple[object, ...]
    structural_fingerprint: owl.Fingerprint

    @property
    def buffer_count(self) -> int:
        return len(self.buffers)

    @property
    def buffer_bytes(self) -> int:
        return sum(buffer.nbytes for buffer in self.buffers.values())


@dataclass(frozen=True, slots=True)
class EncodedInputNegotiation:
    """Capability result made before any encoded buffer is consumed."""

    lease: EncodedStructuralLease | None
    core_schema_version: int | None
    native_schema_version: int | None
    reason: str | None

    def __post_init__(self) -> None:
        if self.lease is None:
            if not isinstance(self.reason, str) or not self.reason:
                raise ValueError("an unavailable encoded input requires a reason")
        elif self.reason is not None:
            raise ValueError("an available encoded input cannot contain a fallback reason")
        for name in ("core_schema_version", "native_schema_version"):
            value = getattr(self, name)
            if value is not None and (type(value) is not int or value < 1):
                raise ValueError(f"{name} must be a positive integer or None")

    @property
    def available(self) -> bool:
        return self.lease is not None


def negotiate_encoded_input(
    view: owl.OntologyView,
    native_schemas: Mapping[str, int],
    *,
    scope: owl.AxiomScope = owl.AxiomScope.CLOSURE,
) -> EncodedInputNegotiation:
    """Acquire structural columns only when core and native schemas overlap.

    Capability absence is a scalar compatibility result.  Once the core
    advertises the selected schema, acquisition and envelope defects fail
    closed so callers cannot fall back after observing malformed native input.
    """

    if not isinstance(view, owl.OntologyView):
        raise TypeError("view must implement pyowl_core.OntologyView")
    if not isinstance(native_schemas, Mapping):
        raise TypeError("native_schemas must be a mapping")
    if not isinstance(scope, owl.AxiomScope):
        raise TypeError("scope must be pyowl_core.AxiomScope")
    supported = _schema_version(native_schemas, "native")
    capabilities = view.capabilities
    if not isinstance(capabilities, owl.CoreCapabilities):
        raise _compatibility_error("core view capabilities have the wrong public type")
    core_schemas = capabilities.encoded_view_schemas
    advertised = _schema_version(core_schemas, "core")
    if supported is None:
        return EncodedInputNegotiation(
            lease=None,
            core_schema_version=advertised,
            native_schema_version=None,
            reason="native extension does not advertise the structural compiler schema",
        )
    if supported < ENCODED_SCHEMA_VERSION:
        return EncodedInputNegotiation(
            lease=None,
            core_schema_version=advertised,
            native_schema_version=supported,
            reason="native structural compiler schema is older than the required version",
        )
    if advertised is None:
        return EncodedInputNegotiation(
            lease=None,
            core_schema_version=None,
            native_schema_version=supported,
            reason="core view does not advertise structural columns",
        )
    if advertised < ENCODED_SCHEMA_VERSION:
        return EncodedInputNegotiation(
            lease=None,
            core_schema_version=advertised,
            native_schema_version=supported,
            reason="core structural schema is older than the required version",
        )

    encoded_type = getattr(owl, "EncodedStructuralView", None)
    if not isinstance(encoded_type, type):
        raise _compatibility_error(
            "core advertises structural columns but exports no EncodedStructuralView"
        )
    try:
        encoded: Any = view.view(
            encoded_type,
            schema_version=ENCODED_SCHEMA_VERSION,
            scope=scope,
        )
    except (MemoryError, KeyboardInterrupt, SystemExit):
        raise
    except Exception as error:
        raise _compatibility_error(
            "core advertised structural columns but publication failed: "
            f"{type(error).__name__}: {error}"
        ) from error
    if not isinstance(encoded, encoded_type):
        raise _protocol_error("encoded view has the wrong exact public type")
    lease = _validate_encoded_view(view, encoded, scope)
    return EncodedInputNegotiation(
        lease=lease,
        core_schema_version=advertised,
        native_schema_version=supported,
        reason=None,
    )


def _validate_encoded_view(
    owner: owl.OntologyView,
    encoded: object,
    scope: owl.AxiomScope,
) -> EncodedStructuralLease:
    schema_name = _required_attribute(encoded, "schema_name")
    if schema_name != ENCODED_SCHEMA_NAME:
        raise _protocol_error("encoded view schema name is incompatible")
    schema_version = _positive_integer(encoded, "schema_version")
    if schema_version != ENCODED_SCHEMA_VERSION:
        raise _protocol_error("encoded view schema version is incompatible")
    model_schema = _positive_integer(encoded, "model_schema")
    if model_schema != owner.capabilities.model_schema:
        raise _protocol_error("encoded view model schema diverges from its owner")
    if _required_attribute(encoded, "owner") is not owner:
        raise _protocol_error("encoded view did not retain the exact requested owner")

    descriptor = _required_attribute(encoded, "descriptor")
    if type(descriptor) is not bytes or not descriptor:
        raise _protocol_error("encoded descriptor must be nonempty exact bytes")
    authoritative_digest = hashlib.sha256(descriptor).digest()
    descriptor_digest = getattr(encoded, "descriptor_digest", authoritative_digest)
    if type(descriptor_digest) is not bytes or descriptor_digest != authoritative_digest:
        raise _protocol_error("encoded descriptor digest does not match its bytes")

    fingerprint = _required_attribute(encoded, "structural_fingerprint")
    if type(fingerprint) is not owl.Fingerprint or fingerprint != owner.structural_fingerprint:
        raise _protocol_error("encoded structural fingerprint diverges from its owner")
    encoded_scope = _required_attribute(encoded, "scope")
    if encoded_scope is not scope:
        raise _protocol_error("encoded view scope diverges from the request")

    raw_buffers = _required_attribute(encoded, "buffers")
    if not isinstance(raw_buffers, Mapping) or not raw_buffers:
        raise _protocol_error("encoded buffers must be a nonempty mapping")
    buffers: dict[str, memoryview] = {}
    for name, value in raw_buffers.items():
        if type(name) is not str or not name:
            raise _protocol_error("encoded buffer names must be nonempty exact strings")
        buffers[name] = _readonly_bytes(name, value)

    raw_segments = _required_attribute(encoded, "segments")
    if type(raw_segments) is not tuple:
        raise _protocol_error("encoded segments must be an exact tuple")
    return EncodedStructuralLease(
        encoded_view=encoded,
        owner=owner,
        schema_name=schema_name,
        schema_version=schema_version,
        model_schema=model_schema,
        scope=scope,
        descriptor=descriptor,
        descriptor_digest=descriptor_digest,
        buffers=MappingProxyType(dict(sorted(buffers.items()))),
        segments=raw_segments,
        structural_fingerprint=fingerprint,
    )


def _readonly_bytes(name: str, value: object) -> memoryview:
    try:
        result = memoryview(value)  # type: ignore[arg-type]
    except TypeError as error:
        raise _protocol_error(f"encoded buffer {name!r} has no buffer protocol") from error
    if not result.readonly:
        result.release()
        raise _protocol_error(f"encoded buffer {name!r} is writable")
    if not result.c_contiguous:
        result.release()
        raise _protocol_error(f"encoded buffer {name!r} is not C-contiguous")
    try:
        if result.ndim != 1 or result.itemsize != 1 or result.format != "B":
            result = result.cast("B")
    except (TypeError, ValueError) as error:
        result.release()
        raise _protocol_error(f"encoded buffer {name!r} cannot be viewed as bytes") from error
    return result


def _schema_version(values: Mapping[str, int], owner: str) -> int | None:
    value = values.get(ENCODED_SCHEMA_NAME)
    if value is None:
        return None
    if type(value) is not int or value < 1:
        raise _protocol_error(f"{owner} structural schema version is invalid")
    return value


def _positive_integer(value: object, name: str) -> int:
    selected = _required_attribute(value, name)
    if type(selected) is not int or selected < 1:
        raise _protocol_error(f"{name} must be a positive exact integer")
    return selected


def _required_attribute(value: object, name: str) -> Any:
    try:
        return getattr(value, name)
    except AttributeError as error:
        raise _protocol_error(f"encoded view is missing {name}") from error


def _compatibility_error(message: str) -> owl.AdapterCompatibilityError:
    diagnostic = owl.Diagnostic(
        code="ADAPTER_COMPATIBILITY",
        severity=owl.Severity.ERROR,
        message=message,
        details={
            "consumer": "pyhermit",
            "encoded_schema": ENCODED_SCHEMA_NAME,
            "required_schema_version": ENCODED_SCHEMA_VERSION,
        },
    )
    return owl.AdapterCompatibilityError(message, diagnostic=diagnostic)


def _protocol_error(message: str) -> owl.BackendProtocolError:
    return owl.BackendProtocolError(message)


__all__ = [
    "ENCODED_NATIVE_FEATURE",
    "ENCODED_SCHEMA_NAME",
    "ENCODED_SCHEMA_VERSION",
    "EncodedInputNegotiation",
    "EncodedStructuralLease",
    "negotiate_encoded_input",
]
