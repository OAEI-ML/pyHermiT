"""Exact pyowl-core aliases, compatibility guards, and capture metadata.

SPDX-License-Identifier: LGPL-3.0-or-later

No OWL value is wrapped or subclassed here.  Input coercion itself belongs to WP02;
this leaf validates a view that has already crossed the one-call core boundary.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Iterable
from dataclasses import dataclass
from typing import Generic, TypeVar

import pyowl_core as _core
from pyowl_core import (
    ADAPTER_PROTOCOL_VERSION,
    API_VERSION,
    MODEL_SCHEMA_VERSION,
    WIRE_FORMAT_VERSION,
    AdapterCompatibilityError,
    CoreCapabilities,
    Diagnostic,
    DocumentInput,
    Fingerprint,
    ImportPolicy,
    ImportResolver,
    LoadOptions,
    OntologyComposite,
    OntologyDelta,
    OntologyDocument,
    OntologyInput,
    OntologyOverlay,
    OntologySnapshot,
    OntologyView,
    OptionConflictError,
    ParseLimits,
    Severity,
    SnapshotProvider,
    StructuralContext,
    StructuralContextKind,
    apply_delta,
    compose_views,
    load_snapshot,
)

from .config import ReasonerConfig
from .exceptions import ResourceLimitError

EXPECTED_API_VERSION = (0, 2)
EXPECTED_MODEL_SCHEMA_VERSION = 2
EXPECTED_WIRE_MAJOR = 1
MINIMUM_WIRE_MINOR = 2
EXPECTED_ADAPTER_PROTOCOL_VERSION = 1
COMPILER_CACHE_SCHEMA_VERSION = 1
HERMIT_COMPATIBILITY_ID = "hermit-37ec30a-v1"
GENERATED_IRI_NAMESPACE = "urn:pyhermit:generated:v1:"
_SEMVER = re.compile(r"^(\d+)\.(\d+)\.(\d+)(?:[.+-].*)?$")
_REQUIRED_VIEW_FEATURES = frozenset(
    {
        "document-boundaries",
        "document-scoped-anonymous",
        "import-manifest",
        "ontology-identity-index",
        "owl2-structural",
    }
)
_U32_CAPACITY = 1 << 32
_LOGICAL_FINGERPRINT_SENTINEL = "L" * 64
_SIGNATURE_FINGERPRINT_SENTINEL = "S" * 64


@dataclass(frozen=True, slots=True)
class CoreVersionInfo:
    package_version: str
    api_version: tuple[int, int]
    model_schema_version: int
    wire_format_version: tuple[int, int]
    adapter_protocol_version: int

    def __post_init__(self) -> None:
        if not isinstance(self.package_version, str) or not self.package_version:
            raise ValueError("package_version must be a nonempty string")
        for name in ("api_version", "wire_format_version"):
            value = getattr(self, name)
            if (
                not isinstance(value, tuple)
                or len(value) != 2
                or not all(
                    isinstance(item, int) and not isinstance(item, bool) and item >= 0
                    for item in value
                )
            ):
                raise TypeError(f"{name} must be a pair of nonnegative integers")
        for name in ("model_schema_version", "adapter_protocol_version"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 1:
                raise ValueError(f"{name} must be a positive integer")


def current_core_versions() -> CoreVersionInfo:
    return CoreVersionInfo(
        package_version=_core.__version__,
        api_version=API_VERSION,
        model_schema_version=MODEL_SCHEMA_VERSION,
        wire_format_version=WIRE_FORMAT_VERSION,
        adapter_protocol_version=ADAPTER_PROTOCOL_VERSION,
    )


def _compatibility_error(field: str, expected: str, actual: str) -> AdapterCompatibilityError:
    message = f"incompatible pyowl-core {field}: expected {expected}, got {actual}"
    diagnostic = Diagnostic(
        code="ADAPTER_COMPATIBILITY",
        severity=Severity.ERROR,
        message=message,
        details={"actual": actual, "expected": expected, "field": field},
    )
    return AdapterCompatibilityError(message, diagnostic=diagnostic)


def require_core_compatibility(
    actual: CoreVersionInfo | None = None,
) -> CoreVersionInfo:
    """Fail before profile/backend work when the shared contract line is incompatible."""

    versions = actual or current_core_versions()
    match = _SEMVER.fullmatch(versions.package_version)
    if match is None:
        raise _compatibility_error(
            "package_version", ">=0.2,<0.3 semantic version", versions.package_version
        )
    major, minor, _patch = (int(value) for value in match.groups())
    if (major, minor) != (0, 2):
        raise _compatibility_error("package_version", ">=0.2,<0.3", versions.package_version)
    if versions.api_version != EXPECTED_API_VERSION:
        raise _compatibility_error(
            "API_VERSION", str(EXPECTED_API_VERSION), str(versions.api_version)
        )
    if versions.model_schema_version != EXPECTED_MODEL_SCHEMA_VERSION:
        raise _compatibility_error(
            "MODEL_SCHEMA_VERSION",
            str(EXPECTED_MODEL_SCHEMA_VERSION),
            str(versions.model_schema_version),
        )
    wire_major, wire_minor = versions.wire_format_version
    if wire_major != EXPECTED_WIRE_MAJOR or wire_minor < MINIMUM_WIRE_MINOR:
        raise _compatibility_error(
            "WIRE_FORMAT_VERSION",
            f"({EXPECTED_WIRE_MAJOR}, >= {MINIMUM_WIRE_MINOR})",
            str(versions.wire_format_version),
        )
    if versions.adapter_protocol_version != EXPECTED_ADAPTER_PROTOCOL_VERSION:
        raise _compatibility_error(
            "ADAPTER_PROTOCOL_VERSION",
            str(EXPECTED_ADAPTER_PROTOCOL_VERSION),
            str(versions.adapter_protocol_version),
        )
    return versions


@dataclass(frozen=True, slots=True, eq=False)
class CapturedOntology:
    """One strong view reference plus immutable version/fingerprint metadata."""

    view: OntologyView
    structural_fingerprint: Fingerprint
    logical_fingerprint: Fingerprint
    signature_fingerprint: Fingerprint
    core_package_version: str
    core_api_version: tuple[int, int]
    core_model_schema_version: int
    core_wire_format_version: tuple[int, int]
    core_adapter_protocol_version: int


@dataclass(frozen=True, slots=True, eq=False)
class DeferredCapturedOntology:
    """Retained lazy view identity for one exact encoded-native attempt."""

    view: OntologyView
    structural_context_kind: StructuralContextKind
    structural_context_bytes: bytes
    core_package_version: str
    core_api_version: tuple[int, int]
    core_model_schema_version: int
    core_wire_format_version: tuple[int, int]
    core_adapter_protocol_version: int


def capture_compatible_view(view: OntologyView) -> CapturedOntology:
    """Validate and retain an already-coerced core view by exact identity."""

    versions = require_core_compatibility()
    if not isinstance(view, OntologyView):
        raise _compatibility_error("OntologyView", "runtime protocol", type(view).__name__)
    capabilities = view.capabilities
    _require_view_capabilities(capabilities)
    for name in (
        "structural_fingerprint",
        "logical_fingerprint",
        "signature_fingerprint",
    ):
        value = getattr(view, name)
        if not isinstance(value, Fingerprint):
            raise _compatibility_error(name, "pyowl_core.Fingerprint", type(value).__name__)
    return CapturedOntology(
        view=view,
        structural_fingerprint=view.structural_fingerprint,
        logical_fingerprint=view.logical_fingerprint,
        signature_fingerprint=view.signature_fingerprint,
        core_package_version=versions.package_version,
        core_api_version=versions.api_version,
        core_model_schema_version=versions.model_schema_version,
        core_wire_format_version=versions.wire_format_version,
        core_adapter_protocol_version=versions.adapter_protocol_version,
    )


def capture_compatible_view_deferred(view: OntologyView) -> DeferredCapturedOntology:
    """Capture authoritative lazy-view context without reading semantic fingerprints.

    This internal seam is intentionally limited to the two public core view
    shapes whose effective fingerprints are lazy. Generic capture remains eager,
    and direct/mapped snapshots retain their existing attestation contract.
    """

    versions = require_core_compatibility()
    if not isinstance(view, OntologyView):
        raise _compatibility_error("OntologyView", "runtime protocol", type(view).__name__)
    _require_view_capabilities(view.capabilities)
    expected_kind: StructuralContextKind
    if isinstance(view, OntologyOverlay):
        expected_kind = StructuralContextKind.OVERLAY
    elif isinstance(view, OntologyComposite):
        expected_kind = StructuralContextKind.COMPOSITE
    else:
        raise TypeError("deferred capture requires OntologyOverlay or OntologyComposite")
    if not _deferred_capture_eligible(view):
        raise _compatibility_error(
            "deferred view shape",
            "top-level overlay/composite with direct or mapped sources",
            type(view).__name__,
        )
    context = view.structural_context
    if not isinstance(context, StructuralContext) or context.kind is not expected_kind:
        raise _compatibility_error(
            "structural_context",
            f"pyowl_core.StructuralContext[{expected_kind.value}]",
            type(context).__name__,
        )
    canonical = context.canonical_bytes()
    if type(canonical) is not bytes or not canonical:
        raise _compatibility_error(
            "structural_context.canonical_bytes",
            "nonempty exact bytes",
            type(canonical).__name__,
        )
    return DeferredCapturedOntology(
        view=view,
        structural_context_kind=context.kind,
        structural_context_bytes=canonical,
        core_package_version=versions.package_version,
        core_api_version=versions.api_version,
        core_model_schema_version=versions.model_schema_version,
        core_wire_format_version=versions.wire_format_version,
        core_adapter_protocol_version=versions.adapter_protocol_version,
    )


def _deferred_capture_eligible(view: OntologyView) -> bool:
    """Defer only bounded lazy shapes rooted directly in snapshots."""

    if isinstance(view, OntologyOverlay):
        maximum_depth = view.depth
        if type(maximum_depth) is not int or maximum_depth <= 0:
            return False
        seen: set[int] = set()
        base: OntologyView = view
        while isinstance(base, OntologyOverlay):
            identity = id(base)
            if identity in seen or len(seen) >= maximum_depth:
                return False
            seen.add(identity)
            base = base.base
        return isinstance(base, OntologySnapshot)
    if isinstance(view, OntologyComposite):
        return all(isinstance(member.view, OntologySnapshot) for member in view.provenance_tree)
    return False


def materialize_deferred_capture(captured: DeferredCapturedOntology) -> CapturedOntology:
    """Resolve the eager scalar contract after an encoded capability miss."""

    if not isinstance(captured, DeferredCapturedOntology):
        raise TypeError("captured must be DeferredCapturedOntology")
    eager = capture_compatible_view(captured.view)
    frozen_versions = (
        captured.core_package_version,
        captured.core_api_version,
        captured.core_model_schema_version,
        captured.core_wire_format_version,
        captured.core_adapter_protocol_version,
    )
    eager_versions = (
        eager.core_package_version,
        eager.core_api_version,
        eager.core_model_schema_version,
        eager.core_wire_format_version,
        eager.core_adapter_protocol_version,
    )
    if eager_versions != frozen_versions:
        raise _compatibility_error(
            "core versions",
            repr(frozen_versions),
            repr(eager_versions),
        )
    return eager


def _require_view_capabilities(capabilities: CoreCapabilities) -> None:
    if not isinstance(capabilities, CoreCapabilities):
        raise _compatibility_error(
            "capabilities", "pyowl_core.CoreCapabilities", type(capabilities).__name__
        )
    checks = (
        ("adapter_protocol", EXPECTED_ADAPTER_PROTOCOL_VERSION, capabilities.adapter_protocol),
        ("model_schema", EXPECTED_MODEL_SCHEMA_VERSION, capabilities.model_schema),
        ("wire_major", EXPECTED_WIRE_MAJOR, capabilities.wire_format[0]),
    )
    for name, expected, actual in checks:
        if actual != expected:
            raise _compatibility_error(name, str(expected), str(actual))
    missing = sorted(_REQUIRED_VIEW_FEATURES - capabilities.features)
    if missing:
        raise _compatibility_error(
            "features", ",".join(sorted(_REQUIRED_VIEW_FEATURES)), f"missing:{','.join(missing)}"
        )


def compiler_cache_key(
    captured: CapturedOntology,
    config: ReasonerConfig,
    *,
    compiler_schema: int = COMPILER_CACHE_SCHEMA_VERSION,
    compatibility_id: str = HERMIT_COMPATIBILITY_ID,
) -> str:
    """Domain-separated semantic compilation/session key.

    Structural fingerprint, source paths, syntax, serialized OWL, callbacks, and Python
    hashes are intentionally absent.
    """

    if not isinstance(captured, CapturedOntology):
        raise TypeError("captured must be CapturedOntology")
    if not isinstance(config, ReasonerConfig):
        raise TypeError("config must be ReasonerConfig")
    if (
        isinstance(compiler_schema, bool)
        or not isinstance(compiler_schema, int)
        or compiler_schema < 1
    ):
        raise ValueError("compiler_schema must be a positive integer")
    if not isinstance(compatibility_id, str) or not compatibility_id:
        raise ValueError("compatibility_id must be a nonempty string")
    encoded = _compiler_cache_payload(
        captured,
        config,
        logical_fingerprint=captured.logical_fingerprint.hex,
        signature_fingerprint=captured.signature_fingerprint.hex,
        compiler_schema=compiler_schema,
        compatibility_id=compatibility_id,
    )
    return hashlib.sha256(b"pyhermit/compiler-cache/v1\0" + encoded).hexdigest()


def deferred_compiler_cache_template(
    captured: DeferredCapturedOntology,
    config: ReasonerConfig,
) -> bytes:
    """Return Python-canonical JSON with fixed-width native fingerprint slots."""

    if not isinstance(captured, DeferredCapturedOntology):
        raise TypeError("captured must be DeferredCapturedOntology")
    if not isinstance(config, ReasonerConfig):
        raise TypeError("config must be ReasonerConfig")
    return _compiler_cache_payload(
        captured,
        config,
        logical_fingerprint=_LOGICAL_FINGERPRINT_SENTINEL,
        signature_fingerprint=_SIGNATURE_FINGERPRINT_SENTINEL,
        compiler_schema=COMPILER_CACHE_SCHEMA_VERSION,
        compatibility_id=HERMIT_COMPATIBILITY_ID,
    )


def _compiler_cache_payload(
    captured: CapturedOntology | DeferredCapturedOntology,
    config: ReasonerConfig,
    *,
    logical_fingerprint: str,
    signature_fingerprint: str,
    compiler_schema: int,
    compatibility_id: str,
) -> bytes:
    payload = {
        "compatibility_id": compatibility_id,
        "compiler_schema": compiler_schema,
        "config": config.as_dict(),
        "core": {
            "adapter": captured.core_adapter_protocol_version,
            "api": captured.core_api_version,
            "model": captured.core_model_schema_version,
            "package": captured.core_package_version,
            "wire": captured.core_wire_format_version,
        },
        "logical_fingerprint": logical_fingerprint,
        "signature_fingerprint": signature_fingerprint,
    }
    return json.dumps(
        payload,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")


def generated_symbol_iri(
    logical_fingerprint: Fingerprint,
    expression_key: bytes,
    polarity: str,
    *,
    query_hash: bytes | None = None,
) -> str:
    """Create a deterministic private definition IRI independent of traversal order."""

    if not isinstance(logical_fingerprint, Fingerprint):
        raise TypeError("logical_fingerprint must be pyowl_core.Fingerprint")
    if not isinstance(expression_key, bytes):
        raise TypeError("expression_key must be bytes")
    if not isinstance(polarity, str) or polarity not in {"negative", "both", "positive"}:
        raise ValueError("polarity must be negative, both, or positive")
    if query_hash is not None and (not isinstance(query_hash, bytes) or len(query_hash) != 32):
        raise ValueError("query_hash must be exactly 32 bytes or None")
    digest = hashlib.sha256()
    digest.update(b"pyhermit/generated-name/v1\0")
    digest.update(logical_fingerprint.digest)
    digest.update(len(expression_key).to_bytes(8, "big"))
    digest.update(expression_key)
    digest.update(polarity.encode("ascii"))
    digest.update(query_hash or b"")
    scope = "query" if query_hash is not None else "ontology"
    return f"{GENERATED_IRI_NAMESPACE}{scope}:{polarity}:{digest.hexdigest()}"


T = TypeVar("T")


@dataclass(frozen=True, slots=True)
class DenseId(Generic[T]):
    identifier: int
    canonical_key: bytes
    value: T


def validate_dense_id_capacity(count: int) -> None:
    if isinstance(count, bool) or not isinstance(count, int) or count < 0:
        raise ValueError("ID count must be a nonnegative integer")
    if count > _U32_CAPACITY:
        raise ResourceLimitError(
            "compiled ID domain exceeds u32 capacity",
            limit="u32-domain-count",
            observed=count,
            allowed=_U32_CAPACITY,
        )


def assign_dense_ids(values: Iterable[tuple[bytes, T]]) -> tuple[DenseId[T], ...]:
    """Assign IDs from canonical keys, never input/hash-table order."""

    materialized = tuple(values)
    validate_dense_id_capacity(len(materialized))
    if not all(isinstance(key, bytes) for key, _value in materialized):
        raise TypeError("dense ID canonical keys must be bytes")
    ordered = tuple(sorted(materialized, key=lambda item: item[0]))
    keys = tuple(key for key, _value in ordered)
    if len(keys) != len(set(keys)):
        raise ValueError("dense ID canonical keys must be unique")
    return tuple(DenseId(index, key, value) for index, (key, value) in enumerate(ordered))


__all__ = [
    "ADAPTER_PROTOCOL_VERSION",
    "API_VERSION",
    "COMPILER_CACHE_SCHEMA_VERSION",
    "EXPECTED_ADAPTER_PROTOCOL_VERSION",
    "EXPECTED_API_VERSION",
    "EXPECTED_MODEL_SCHEMA_VERSION",
    "EXPECTED_WIRE_MAJOR",
    "GENERATED_IRI_NAMESPACE",
    "HERMIT_COMPATIBILITY_ID",
    "MINIMUM_WIRE_MINOR",
    "MODEL_SCHEMA_VERSION",
    "WIRE_FORMAT_VERSION",
    "AdapterCompatibilityError",
    "CapturedOntology",
    "CoreVersionInfo",
    "DenseId",
    "DocumentInput",
    "Fingerprint",
    "ImportPolicy",
    "ImportResolver",
    "LoadOptions",
    "OntologyComposite",
    "OntologyDelta",
    "OntologyDocument",
    "OntologyInput",
    "OntologyOverlay",
    "OntologySnapshot",
    "OntologyView",
    "OptionConflictError",
    "ParseLimits",
    "SnapshotProvider",
    "apply_delta",
    "assign_dense_ids",
    "capture_compatible_view",
    "compiler_cache_key",
    "compose_views",
    "current_core_versions",
    "generated_symbol_iri",
    "load_snapshot",
    "require_core_compatibility",
    "validate_dense_id_capacity",
]
