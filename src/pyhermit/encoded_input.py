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
from typing import Any, cast

import pyowl_core as owl

ENCODED_SCHEMA_NAME = "pyowl-core/structural-columns"
ENCODED_SCHEMA_VERSION = 1
ENCODED_NATIVE_FEATURE = "encoded-structural-compiler-v1"
ENCODED_DESCRIPTOR_SHA256 = bytes.fromhex(
    "9ad29db6a7e616f65cea2957bc5ba8d1f9b99ef0eb1fe1432c09be25786267b5"
)
ENCODED_BUFFER_WIDTHS: Mapping[str, int] = MappingProxyType(
    {
        "field_kinds": 1,
        "field_lengths": 8,
        "field_values": 8,
        "item_kinds": 1,
        "item_lengths": 8,
        "item_values": 8,
        "node_field_offsets": 8,
        "node_tags": 2,
        "root_ids": 4,
        "root_kinds": 1,
        "scalar_bytes": 1,
    }
)
_SEGMENT_DIRECT = 1
_SEGMENT_OVERLAY_BASE = 2
_SEGMENT_OVERLAY_DELTA = 3
_SEGMENT_COMPOSITE_MEMBER = 4
_SEGMENT_COMPOSITE_BRIDGE = 5
_POSTINGS_ALL = 0
_POSTINGS_INCLUDE = 1
_POSTINGS_EXCLUDE = 2
_MAX_SEGMENT_DEPTH = 32
_MAX_COMPOSITE_MEMBERS = 1_024
_MAX_ENCODED_VIEWS = _MAX_COMPOSITE_MEMBERS * (_MAX_SEGMENT_DEPTH + 1) + 1


@dataclass(frozen=True, slots=True, eq=False)
class EncodedStructuralSegmentLease:
    """Validated segment metadata retaining its source view and borrowed sidecars."""

    segment: object
    role: int
    owner: owl.OntologyView
    source: EncodedStructuralLease | None
    posting_mode: int
    root_ids: memoryview
    anonymous_scope_map: memoryview
    member_token: bytes | None


@dataclass(frozen=True, slots=True, eq=False)
class EncodedStructuralLease:
    """Validated encoded envelope and the exact public owner that keeps it alive."""

    encoded_view: object
    owner: owl.OntologyView
    schema_name: str
    schema_version: int
    model_schema: int
    scope: owl.AxiomScope
    document_key: str | None
    descriptor: bytes
    descriptor_digest: bytes
    buffers: Mapping[str, memoryview]
    segments: tuple[EncodedStructuralSegmentLease, ...]
    structural_fingerprint: owl.Fingerprint

    @property
    def buffer_count(self) -> int:
        return len(self.buffers)

    @property
    def buffer_bytes(self) -> int:
        return sum(buffer.nbytes for buffer in self.buffers.values())

    def local_leases(self) -> tuple[EncodedStructuralLease, ...]:
        """Return each unique local column owner once in deterministic depth-first order."""

        ordered: list[EncodedStructuralLease] = []
        pending = [self]
        seen: set[int] = set()
        while pending:
            current = pending.pop()
            identity = id(current.encoded_view)
            if identity in seen:
                continue
            seen.add(identity)
            ordered.append(current)
            pending.extend(
                segment.source
                for segment in reversed(current.segments)
                if segment.source is not None
            )
        return tuple(ordered)


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
    lease = _validate_encoded_view(
        view,
        encoded,
        scope,
        document_key=None,
        active=frozenset(),
        validated={},
    )
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
    *,
    document_key: str | None,
    active: frozenset[int],
    validated: dict[int, EncodedStructuralLease],
) -> EncodedStructuralLease:
    identity = id(encoded)
    if identity in active:
        raise _protocol_error("encoded structural segment graph is cyclic")
    existing = validated.get(identity)
    if existing is not None:
        if (
            existing.owner is not owner
            or existing.scope is not scope
            or existing.document_key != document_key
        ):
            raise _protocol_error("encoded structural view is reused with incompatible ownership")
        return existing
    if len(active) >= _MAX_SEGMENT_DEPTH:
        raise _protocol_error("encoded structural segment graph exceeds the supported depth")
    if len(validated) >= _MAX_ENCODED_VIEWS:
        raise _protocol_error("encoded structural segment graph exceeds the supported view count")
    active = active | {identity}

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
    if authoritative_digest != ENCODED_DESCRIPTOR_SHA256:
        raise _protocol_error(
            "encoded descriptor does not match the frozen pyowl-core structural-columns v1 ledger"
        )

    fingerprint = _required_attribute(encoded, "structural_fingerprint")
    if type(fingerprint) is not owl.Fingerprint:
        raise _protocol_error("encoded structural fingerprint must be an exact Fingerprint")
    if fingerprint.schema != 1:
        raise _protocol_error("encoded structural fingerprint schema is incompatible")
    encoded_scope = _required_attribute(encoded, "scope")
    if encoded_scope is not scope:
        raise _protocol_error("encoded view scope diverges from the request")
    encoded_document_key = _required_attribute(encoded, "document_key")
    if encoded_document_key != document_key:
        raise _protocol_error("encoded view document selection diverges from the request")
    _validate_selection(encoded_scope, encoded_document_key)

    raw_buffers = _required_attribute(encoded, "buffers")
    if not isinstance(raw_buffers, Mapping) or not raw_buffers:
        raise _protocol_error("encoded buffers must be a nonempty mapping")
    buffers: dict[str, memoryview] = {}
    for name, value in raw_buffers.items():
        if type(name) is not str or not name:
            raise _protocol_error("encoded buffer names must be nonempty exact strings")
        buffers[name] = _readonly_bytes(name, value)
    if set(buffers) != set(ENCODED_BUFFER_WIDTHS):
        missing = sorted(set(ENCODED_BUFFER_WIDTHS) - set(buffers))
        extra = sorted(set(buffers) - set(ENCODED_BUFFER_WIDTHS))
        raise _protocol_error(
            f"encoded schema 1 buffer set differs (missing={missing!r}, extra={extra!r})"
        )
    for name, width in ENCODED_BUFFER_WIDTHS.items():
        if buffers[name].nbytes % width:
            raise _protocol_error(
                f"encoded buffer {name!r} length is not divisible by its {width}-byte scalar width"
            )

    raw_segments = _required_attribute(encoded, "segments")
    if type(raw_segments) is not tuple:
        raise _protocol_error("encoded segments must be an exact tuple")
    segments = _validate_segments(
        raw_segments,
        owner=owner,
        local_root_count=buffers["root_ids"].nbytes // 4,
        active=active,
        validated=validated,
    )
    if fingerprint != _encoded_fingerprint(buffers, segments, descriptor):
        raise _protocol_error("encoded structural fingerprint does not cover its publication")
    lease = EncodedStructuralLease(
        encoded_view=encoded,
        owner=owner,
        schema_name=schema_name,
        schema_version=schema_version,
        model_schema=model_schema,
        scope=scope,
        document_key=document_key,
        descriptor=descriptor,
        descriptor_digest=descriptor_digest,
        buffers=MappingProxyType(dict(sorted(buffers.items()))),
        segments=segments,
        structural_fingerprint=fingerprint,
    )
    validated[identity] = lease
    return lease


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


def _validate_segments(
    raw_segments: tuple[object, ...],
    *,
    owner: owl.OntologyView,
    local_root_count: int,
    active: frozenset[int],
    validated: dict[int, EncodedStructuralLease],
) -> tuple[EncodedStructuralSegmentLease, ...]:
    if not raw_segments:
        raise _protocol_error("encoded structural segment table must not be empty")
    if len(raw_segments) > _MAX_COMPOSITE_MEMBERS + 1:
        raise _protocol_error("encoded structural segment table exceeds the supported size")
    segments: list[EncodedStructuralSegmentLease] = []
    for raw_segment in raw_segments:
        (
            role,
            segment_owner,
            source,
            posting_mode,
            raw_root_ids,
            raw_scope_map,
            member_token,
        ) = _segment_attributes(raw_segment)
        if type(role) is not int or role not in {
            _SEGMENT_DIRECT,
            _SEGMENT_OVERLAY_BASE,
            _SEGMENT_OVERLAY_DELTA,
            _SEGMENT_COMPOSITE_MEMBER,
            _SEGMENT_COMPOSITE_BRIDGE,
        }:
            raise _protocol_error("encoded structural segment role is invalid")
        try:
            owner_is_view = isinstance(segment_owner, owl.OntologyView)
        except Exception as error:
            raise _protocol_error("encoded structural segment owner is hostile") from error
        if not owner_is_view:
            raise _protocol_error("encoded structural segment owner is invalid")
        selected_owner = cast(owl.OntologyView, segment_owner)
        if type(posting_mode) is not int or posting_mode not in {
            _POSTINGS_ALL,
            _POSTINGS_INCLUDE,
            _POSTINGS_EXCLUDE,
        }:
            raise _protocol_error("encoded structural posting mode is invalid")
        root_ids = _readonly_bytes("segment root_ids", raw_root_ids)
        anonymous_scope_map = _readonly_bytes("segment anonymous_scope_map", raw_scope_map)
        if root_ids.nbytes % 4:
            raise _protocol_error("encoded structural segment postings contain a partial u32")
        if anonymous_scope_map.nbytes % 64:
            raise _protocol_error("encoded structural anonymous scope map contains a partial row")

        source_lease: EncodedStructuralLease | None = None
        if source is None:
            if segment_owner is not owner:
                raise _protocol_error("local encoded structural segment retained the wrong owner")
            referenced_root_count = local_root_count
        else:
            encoded_type = getattr(owl, "EncodedStructuralView", None)
            if not isinstance(encoded_type, type) or not isinstance(source, encoded_type):
                raise _protocol_error("encoded structural segment source has the wrong public type")
            source_scope = _required_attribute(source, "scope")
            source_document_key = _required_attribute(source, "document_key")
            _validate_selection(source_scope, source_document_key)
            source_lease = _validate_encoded_view(
                selected_owner,
                source,
                source_scope,
                document_key=source_document_key,
                active=active,
                validated=validated,
            )
            referenced_root_count = source_lease.buffers["root_ids"].nbytes // 4

        previous_root_id = 0
        for offset in range(0, root_ids.nbytes, 4):
            root_id = int.from_bytes(root_ids[offset : offset + 4], "little")
            if root_id <= previous_root_id or root_id > referenced_root_count:
                raise _protocol_error(
                    "encoded structural segment postings are not sorted unique in-range IDs"
                )
            previous_root_id = root_id
        if posting_mode == _POSTINGS_ALL and root_ids.nbytes:
            raise _protocol_error("ALL encoded segment mode requires empty postings")
        if posting_mode in {_POSTINGS_INCLUDE, _POSTINGS_EXCLUDE} and not root_ids.nbytes:
            raise _protocol_error("INCLUDE and EXCLUDE encoded segment modes require postings")

        previous_scope: bytes | None = None
        for offset in range(0, anonymous_scope_map.nbytes, 64):
            current_scope = bytes(anonymous_scope_map[offset : offset + 32])
            target_scope = bytes(anonymous_scope_map[offset + 32 : offset + 64])
            if (
                previous_scope is not None and current_scope <= previous_scope
            ) or current_scope == target_scope:
                raise _protocol_error(
                    "encoded anonymous scope sources are not sorted unique or contain identity rows"
                )
            previous_scope = current_scope
        if role == _SEGMENT_COMPOSITE_MEMBER:
            if type(member_token) is not bytes or len(member_token) != 32:
                raise _protocol_error("encoded composite member requires an exact bytes32 token")
        elif member_token is not None:
            raise _protocol_error("only encoded composite members may carry tokens")

        segments.append(
            EncodedStructuralSegmentLease(
                segment=raw_segment,
                role=role,
                owner=selected_owner,
                source=source_lease,
                posting_mode=posting_mode,
                root_ids=root_ids,
                anonymous_scope_map=anonymous_scope_map,
                member_token=member_token,
            )
        )
    result = tuple(segments)
    _validate_segment_family(result, owner, local_root_count)
    return result


def _segment_attributes(segment: object) -> tuple[object, ...]:
    try:
        return tuple(
            getattr(segment, name)
            for name in (
                "role",
                "owner",
                "source",
                "posting_mode",
                "root_ids",
                "anonymous_scope_map",
                "member_token",
            )
        )
    except (MemoryError, KeyboardInterrupt, SystemExit):
        raise
    except Exception as error:
        raise _protocol_error("encoded structural segment attributes are not readable") from error


def _validate_segment_family(
    segments: tuple[EncodedStructuralSegmentLease, ...],
    owner: owl.OntologyView,
    local_root_count: int,
) -> None:
    roles = tuple(segment.role for segment in segments)
    if roles == (_SEGMENT_DIRECT,):
        direct = segments[0]
        if (
            direct.owner is not owner
            or direct.source is not None
            or direct.posting_mode != _POSTINGS_ALL
            or direct.root_ids.nbytes
            or direct.anonymous_scope_map.nbytes
            or direct.member_token is not None
        ):
            raise _protocol_error("direct encoded segment metadata is not canonical")
        return
    if roles in {
        (_SEGMENT_OVERLAY_BASE,),
        (_SEGMENT_OVERLAY_BASE, _SEGMENT_OVERLAY_DELTA),
    }:
        base = segments[0]
        if (
            base.source is None
            or base.owner is not base.source.owner
            or base.posting_mode not in {_POSTINGS_ALL, _POSTINGS_EXCLUDE}
            or base.member_token is not None
        ):
            raise _protocol_error("encoded overlay base segment metadata is invalid")
        if len(segments) == 1:
            if local_root_count:
                raise _protocol_error("encoded overlay without a delta has local roots")
        else:
            delta = segments[1]
            if (
                delta.owner is not owner
                or delta.source is not None
                or delta.posting_mode != _POSTINGS_ALL
                or delta.anonymous_scope_map.nbytes
                or delta.member_token is not None
                or not local_root_count
            ):
                raise _protocol_error("encoded overlay delta segment metadata is invalid")
        return

    bridge_count = roles.count(_SEGMENT_COMPOSITE_BRIDGE)
    member_count = roles.count(_SEGMENT_COMPOSITE_MEMBER)
    if member_count < 2 or member_count > _MAX_COMPOSITE_MEMBERS or bridge_count > 1:
        raise _protocol_error("encoded composite segment family is invalid")
    expected = (_SEGMENT_COMPOSITE_MEMBER,) * member_count + (
        (_SEGMENT_COMPOSITE_BRIDGE,) if bridge_count else ()
    )
    if roles != expected:
        raise _protocol_error("encoded composite segments are not in canonical role order")
    tokens: list[bytes] = []
    for member in segments[:member_count]:
        if (
            member.source is None
            or member.owner is not member.source.owner
            or member.posting_mode
            not in {
                _POSTINGS_ALL,
                _POSTINGS_INCLUDE,
                _POSTINGS_EXCLUDE,
            }
            or member.member_token is None
        ):
            raise _protocol_error("encoded composite member metadata is invalid")
        tokens.append(member.member_token)
    if tokens != sorted(set(tokens)):
        raise _protocol_error("encoded composite member tokens collide or are unordered")
    if bridge_count:
        bridge = segments[-1]
        if (
            bridge.owner is not owner
            or bridge.source is not None
            or bridge.posting_mode != _POSTINGS_ALL
            or bridge.anonymous_scope_map.nbytes
            or bridge.member_token is not None
            or not local_root_count
        ):
            raise _protocol_error("encoded composite bridge metadata is invalid")
    elif local_root_count:
        raise _protocol_error("encoded composite without a bridge has local roots")


def _encoded_fingerprint(
    buffers: Mapping[str, memoryview],
    segments: tuple[EncodedStructuralSegmentLease, ...],
    descriptor: bytes,
) -> owl.Fingerprint:
    names = (
        "root_kinds",
        "root_ids",
        "node_tags",
        "node_field_offsets",
        "field_kinds",
        "field_values",
        "field_lengths",
        "item_kinds",
        "item_values",
        "item_lengths",
        "scalar_bytes",
    )
    hasher = hashlib.sha256()
    hasher.update(b"pyowl-core:encoded-structural-view:v1\x00")
    hasher.update(_frame(descriptor))
    for name in names:
        hasher.update(_frame(name.encode("ascii")))
        value = buffers[name]
        hasher.update(value.nbytes.to_bytes(8, "little"))
        hasher.update(value)
    hasher.update(len(segments).to_bytes(8, "little"))
    for segment in segments:
        hasher.update(bytes((segment.role, segment.posting_mode)))
        if segment.source is None:
            hasher.update(b"\x00")
        else:
            hasher.update(b"\x01")
            source_fingerprint = segment.source.structural_fingerprint
            hasher.update(source_fingerprint.schema.to_bytes(4, "little"))
            hasher.update(source_fingerprint.digest)
        if segment.member_token is None:
            hasher.update(b"\x00")
        else:
            hasher.update(b"\x01" + segment.member_token)
        hasher.update(segment.root_ids.nbytes.to_bytes(8, "little"))
        hasher.update(segment.root_ids)
        hasher.update(segment.anonymous_scope_map.nbytes.to_bytes(8, "little"))
        hasher.update(segment.anonymous_scope_map)
    return owl.Fingerprint("sha256", 1, hasher.digest())


def _frame(value: bytes) -> bytes:
    return _encode_varint(len(value)) + value


def _encode_varint(value: int) -> bytes:
    output = bytearray()
    while value >= 0x80:
        output.append((value & 0x7F) | 0x80)
        value >>= 7
    output.append(value)
    return bytes(output)


def _validate_selection(scope: object, document_key: object) -> None:
    if not isinstance(scope, owl.AxiomScope):
        raise _protocol_error("encoded structural scope is invalid")
    if scope is owl.AxiomScope.DOCUMENT:
        if type(document_key) is not str or not document_key:
            raise _protocol_error("encoded document scope requires a document key")
    elif document_key is not None:
        raise _protocol_error("encoded document key is invalid outside document scope")


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
    "ENCODED_BUFFER_WIDTHS",
    "ENCODED_DESCRIPTOR_SHA256",
    "ENCODED_NATIVE_FEATURE",
    "ENCODED_SCHEMA_NAME",
    "ENCODED_SCHEMA_VERSION",
    "EncodedInputNegotiation",
    "EncodedStructuralLease",
    "EncodedStructuralSegmentLease",
    "negotiate_encoded_input",
]
