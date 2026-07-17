"""Frozen whole-session backend, compiled-metadata, and result contracts.

SPDX-License-Identifier: LGPL-3.0-or-later

This module owns only backend-neutral control-plane values.  The complete atom,
clause, role, datatype, and symbol implementations are supplied by their later work
packages and satisfy :class:`CanonicalIR`; this file does not create a second OWL
model or a provisional reasoning engine.
"""

from __future__ import annotations

import hashlib
import json
import math
import re
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from enum import Enum
from typing import Generic, Literal, Protocol, TypeVar, cast, runtime_checkable

from pyhermit.config import ReasonerConfig
from pyhermit.events import CancellationToken
from pyhermit.exceptions import ResourceLimitError

U32_MAX = (1 << 32) - 1
COMPILED_IR_SCHEMA_VERSION = 1
_HEX_256 = re.compile(r"^[0-9a-f]{64}$")


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class DeltaOutcome(_StringEnum):
    APPLIED_INCREMENTALLY = "applied_incrementally"
    REBUILD_REQUIRED = "rebuild_required"


class DeltaKind(_StringEnum):
    ASSERTION_ONLY = "assertion_only"
    DECLARATION_ONLY = "declaration_only"
    REBUILD = "rebuild"


@runtime_checkable
class FingerprintLike(Protocol):
    algorithm: str
    schema: int
    digest: bytes

    @property
    def hex(self) -> str: ...


@runtime_checkable
class CanonicalIR(Protocol):
    """Minimal contract implemented by later private-IR records."""

    @property
    def schema_version(self) -> int: ...

    def canonical_bytes(self) -> bytes: ...


def _validate_u32(value: int, name: str) -> None:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an unsigned 32-bit integer")
    if value < 0 or value > U32_MAX:
        raise ResourceLimitError(
            f"{name} exceeds the unsigned 32-bit IR limit",
            limit="u32",
            observed=value,
            allowed=U32_MAX,
        )


def _validate_version(value: tuple[int, int], name: str) -> None:
    if (
        not isinstance(value, tuple)
        or len(value) != 2
        or not all(
            isinstance(item, int) and not isinstance(item, bool) and item >= 0 for item in value
        )
    ):
        raise TypeError(f"{name} must be a pair of nonnegative integers")


def _validate_hex_fingerprint(value: str, name: str) -> None:
    if not isinstance(value, str) or _HEX_256.fullmatch(value) is None:
        raise ValueError(f"{name} must be a lowercase SHA-256 hex digest")


def _ir_digest(value: CanonicalIR) -> str:
    payload = value.canonical_bytes()
    if not isinstance(payload, bytes):
        raise TypeError("CanonicalIR.canonical_bytes() must return bytes")
    return hashlib.sha256(payload).hexdigest()


@dataclass(frozen=True, slots=True, order=True)
class EntityRef:
    kind: str
    iri: str
    entity_id: int

    def __post_init__(self) -> None:
        if not isinstance(self.kind, str) or not self.kind:
            raise ValueError("entity kind must be a nonempty string")
        if not isinstance(self.iri, str) or not self.iri:
            raise ValueError("entity IRI must be a nonempty string")
        _validate_u32(self.entity_id, "entity_id")


@dataclass(frozen=True, slots=True)
class CompiledOntology:
    """Immutable metadata envelope around the complete private HermiT IR."""

    schema_version: int
    ontology_fingerprint: str
    source_structural_fingerprint: FingerprintLike
    source_logical_fingerprint: FingerprintLike
    source_signature_fingerprint: FingerprintLike
    core_package_version: str
    core_api_version: tuple[int, int]
    core_model_schema_version: int
    core_wire_format_version: tuple[int, int]
    core_adapter_protocol_version: int
    symbols: CanonicalIR
    clauses: tuple[CanonicalIR, ...]
    positive_facts: tuple[CanonicalIR, ...]
    negative_facts: tuple[CanonicalIR, ...]
    ground_disjunctions: tuple[CanonicalIR, ...]
    role_model: CanonicalIR
    datatype_model: CanonicalIR
    expressivity: CanonicalIR
    declared_entities: tuple[EntityRef, ...]
    named_individuals: tuple[int, ...]
    provenance: CanonicalIR

    def __post_init__(self) -> None:
        if self.schema_version != COMPILED_IR_SCHEMA_VERSION:
            raise ValueError(
                f"compiled IR schema must be {COMPILED_IR_SCHEMA_VERSION}, "
                f"got {self.schema_version}"
            )
        _validate_hex_fingerprint(self.ontology_fingerprint, "ontology_fingerprint")
        fingerprints = (
            self.source_structural_fingerprint,
            self.source_logical_fingerprint,
            self.source_signature_fingerprint,
        )
        for fingerprint in fingerprints:
            if not isinstance(fingerprint, FingerprintLike):
                raise TypeError("source fingerprints must implement FingerprintLike")
            if fingerprint.algorithm != "sha256" or len(fingerprint.digest) != 32:
                raise ValueError("source fingerprints must be 32-byte SHA-256 values")
        if not isinstance(self.core_package_version, str) or not self.core_package_version:
            raise ValueError("core_package_version must be a nonempty string")
        _validate_version(self.core_api_version, "core_api_version")
        _validate_version(self.core_wire_format_version, "core_wire_format_version")
        for name in ("core_model_schema_version", "core_adapter_protocol_version"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 1:
                raise ValueError(f"{name} must be a positive integer")

        singular = (
            self.symbols,
            self.role_model,
            self.datatype_model,
            self.expressivity,
            self.provenance,
        )
        collections = (
            self.clauses,
            self.positive_facts,
            self.negative_facts,
            self.ground_disjunctions,
        )
        if not all(isinstance(item, CanonicalIR) for item in singular):
            raise TypeError("compiled IR components must implement CanonicalIR")
        for values in collections:
            if not isinstance(values, tuple) or not all(
                isinstance(item, CanonicalIR) for item in values
            ):
                raise TypeError("compiled IR collections must be tuples of CanonicalIR values")
            digests = tuple(_ir_digest(item) for item in values)
            if digests != tuple(sorted(digests)) or len(digests) != len(set(digests)):
                raise ValueError("compiled IR collections must be canonically sorted and unique")

        entities = tuple(self.declared_entities)
        if not all(isinstance(item, EntityRef) for item in entities):
            raise TypeError("declared_entities must contain EntityRef values")
        if entities != tuple(sorted(entities, key=lambda item: (item.kind, item.iri))):
            raise ValueError("declared_entities must be canonically sorted")
        if len({(item.kind, item.iri) for item in entities}) != len(entities):
            raise ValueError("declared_entities must be unique by kind and IRI")
        named = tuple(self.named_individuals)
        for item in named:
            _validate_u32(item, "named_individual_id")
        if named != tuple(sorted(set(named))):
            raise ValueError("named_individuals must be sorted and unique")
        object.__setattr__(self, "declared_entities", entities)
        object.__setattr__(self, "named_individuals", named)

    def canonical_manifest(self) -> dict[str, object]:
        """Canonical diagnostic manifest without backend pointers or OWL text."""

        return {
            "components": {
                "clauses": [_ir_digest(item) for item in self.clauses],
                "datatype_model": _ir_digest(self.datatype_model),
                "expressivity": _ir_digest(self.expressivity),
                "ground_disjunctions": [
                    _ir_digest(item) for item in self.ground_disjunctions
                ],
                "negative_facts": [_ir_digest(item) for item in self.negative_facts],
                "positive_facts": [_ir_digest(item) for item in self.positive_facts],
                "provenance": _ir_digest(self.provenance),
                "role_model": _ir_digest(self.role_model),
                "symbols": _ir_digest(self.symbols),
            },
            "core": {
                "adapter_protocol": self.core_adapter_protocol_version,
                "api": list(self.core_api_version),
                "model_schema": self.core_model_schema_version,
                "package": self.core_package_version,
                "wire": list(self.core_wire_format_version),
            },
            "declared_entities": [
                {"id": item.entity_id, "iri": item.iri, "kind": item.kind}
                for item in self.declared_entities
            ],
            "fingerprints": {
                "logical": self.source_logical_fingerprint.hex,
                "ontology": self.ontology_fingerprint,
                "signature": self.source_signature_fingerprint.hex,
                "structural": self.source_structural_fingerprint.hex,
            },
            "named_individuals": list(self.named_individuals),
            "schema_version": self.schema_version,
        }

    def canonical_json(self) -> str:
        return json.dumps(
            self.canonical_manifest(),
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        )


@dataclass(frozen=True, slots=True)
class CompiledQuery:
    schema_version: int
    ontology_fingerprint: str
    query_fingerprint: str
    first_local_id: int
    clauses: tuple[CanonicalIR, ...] = ()
    positive_facts: tuple[CanonicalIR, ...] = ()
    negative_facts: tuple[CanonicalIR, ...] = ()
    interpretation: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if self.schema_version != COMPILED_IR_SCHEMA_VERSION:
            raise ValueError("compiled query schema mismatch")
        _validate_hex_fingerprint(self.ontology_fingerprint, "ontology_fingerprint")
        _validate_hex_fingerprint(self.query_fingerprint, "query_fingerprint")
        _validate_u32(self.first_local_id, "first_local_id")
        for name in ("clauses", "positive_facts", "negative_facts"):
            values = getattr(self, name)
            if not isinstance(values, tuple) or not all(
                isinstance(item, CanonicalIR) for item in values
            ):
                raise TypeError(f"{name} must be a tuple of CanonicalIR values")
        if not all(isinstance(item, str) and item for item in self.interpretation):
            raise TypeError("interpretation must contain nonempty strings")


@dataclass(frozen=True, slots=True)
class CompiledDelta:
    schema_version: int
    base_ontology_fingerprint: str
    result_ontology_fingerprint: str
    kind: DeltaKind
    additions: tuple[CanonicalIR, ...] = ()
    removals: tuple[CanonicalIR, ...] = ()

    def __post_init__(self) -> None:
        if self.schema_version != COMPILED_IR_SCHEMA_VERSION:
            raise ValueError("compiled delta schema mismatch")
        _validate_hex_fingerprint(self.base_ontology_fingerprint, "base_ontology_fingerprint")
        _validate_hex_fingerprint(
            self.result_ontology_fingerprint, "result_ontology_fingerprint"
        )
        if not isinstance(self.kind, DeltaKind):
            raise TypeError("kind must be DeltaKind")
        for name in ("additions", "removals"):
            values = getattr(self, name)
            if not isinstance(values, tuple) or not all(
                isinstance(item, CanonicalIR) for item in values
            ):
                raise TypeError(f"{name} must be a tuple of CanonicalIR values")


@dataclass(frozen=True, slots=True)
class ReasoningStatistics:
    elapsed_seconds: float = 0.0
    nodes: int = 0
    facts: int = 0
    branches: int = 0
    backtracks: int = 0
    merges: int = 0
    datatype_checks: int = 0

    def __post_init__(self) -> None:
        if isinstance(self.elapsed_seconds, bool) or not isinstance(
            self.elapsed_seconds, (int, float)
        ):
            raise TypeError("elapsed_seconds must be a finite nonnegative number")
        elapsed = float(self.elapsed_seconds)
        if not math.isfinite(elapsed) or elapsed < 0:
            raise ValueError("elapsed_seconds must be a finite nonnegative number")
        object.__setattr__(self, "elapsed_seconds", elapsed)
        for name in ("nodes", "facts", "branches", "backtracks", "merges", "datatype_checks"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")


@dataclass(frozen=True, slots=True)
class CheckResult:
    satisfiable: bool
    statistics: ReasoningStatistics = field(default_factory=ReasoningStatistics, compare=False)

    def __post_init__(self) -> None:
        if not isinstance(self.satisfiable, bool):
            raise TypeError("satisfiable must be bool")
        if not isinstance(self.statistics, ReasoningStatistics):
            raise TypeError("statistics must be ReasoningStatistics")


def _reachable(edges: set[tuple[int, int]], start: int, target: int, skip: tuple[int, int]) -> bool:
    frontier = [start]
    seen = {start}
    while frontier:
        current = frontier.pop()
        for child, parent in edges:
            if (child, parent) == skip or child != current:
                continue
            if parent == target:
                return True
            if parent in seen:
                continue
            seen.add(parent)
            frontier.append(parent)
    return False


@dataclass(frozen=True, slots=True)
class HierarchyIds:
    """Validated finite DAG over compiled IDs; edges point subordinate to superior."""

    nodes: tuple[tuple[int, ...], ...]
    edges: tuple[tuple[int, int], ...]
    top_node: int
    bottom_node: int

    def __post_init__(self) -> None:
        nodes = tuple(tuple(node) for node in self.nodes)
        if not nodes or any(not node for node in nodes):
            raise ValueError("hierarchy nodes must be nonempty and contain nonempty members")
        all_members: set[int] = set()
        for node in nodes:
            for member in node:
                _validate_u32(member, "hierarchy member")
            if node != tuple(sorted(set(node))):
                raise ValueError("hierarchy node members must be sorted and unique")
            if all_members.intersection(node):
                raise ValueError("hierarchy nodes must partition their members")
            all_members.update(node)
        if nodes != tuple(sorted(nodes)):
            raise ValueError("hierarchy nodes must be sorted by their member tuples")
        for name in ("top_node", "bottom_node"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or not 0 <= value < len(nodes):
                raise ValueError(f"{name} must reference a hierarchy node")
        edges = tuple(self.edges)
        if edges != tuple(sorted(set(edges))):
            raise ValueError("hierarchy edges must be sorted and unique")
        edge_set = set(edges)
        for child, parent in edges:
            if not 0 <= child < len(nodes) or not 0 <= parent < len(nodes):
                raise ValueError("hierarchy edge references an absent node")
            if child == parent:
                raise ValueError("hierarchy edges cannot be reflexive")
        for edge in edges:
            if _reachable(edge_set, edge[0], edge[1], edge):
                raise ValueError("hierarchy edges must be a transitive reduction")
        for start in range(len(nodes)):
            if _reachable(edge_set, start, start, (-1, -1)):
                raise ValueError("hierarchy must be acyclic")
        object.__setattr__(self, "nodes", nodes)
        object.__setattr__(self, "edges", edges)


T = TypeVar("T")


@dataclass(frozen=True, slots=True)
class Hierarchy(Generic[T]):
    nodes: tuple[frozenset[T], ...]
    edges: frozenset[tuple[int, int]]
    top_node: int
    bottom_node: int

    def __post_init__(self) -> None:
        nodes = tuple(frozenset(node) for node in self.nodes)
        if not nodes or any(not node for node in nodes):
            raise ValueError("hierarchy nodes must be nonempty")
        seen: set[T] = set()
        for node in nodes:
            if seen.intersection(node):
                raise ValueError("hierarchy nodes must partition their members")
            seen.update(node)
        if not 0 <= self.top_node < len(nodes) or not 0 <= self.bottom_node < len(nodes):
            raise ValueError("top and bottom must reference hierarchy nodes")
        edges = frozenset(self.edges)
        if any(
            child == parent
            or not 0 <= child < len(nodes)
            or not 0 <= parent < len(nodes)
            for child, parent in edges
        ):
            raise ValueError("invalid public hierarchy edge")
        object.__setattr__(self, "nodes", nodes)
        object.__setattr__(self, "edges", edges)

    def ancestors(self, node: int) -> frozenset[int]:
        return self._closure(node, upward=True)

    def descendants(self, node: int) -> frozenset[int]:
        return self._closure(node, upward=False)

    def _closure(self, node: int, *, upward: bool) -> frozenset[int]:
        if isinstance(node, bool) or not isinstance(node, int) or not 0 <= node < len(self.nodes):
            raise IndexError("hierarchy node index out of range")
        reached: set[int] = set()
        frontier = [node]
        while frontier:
            current = frontier.pop()
            for child, parent in self.edges:
                if upward and child == current:
                    candidate = parent
                elif not upward and parent == current:
                    candidate = child
                else:
                    candidate = None
                if candidate is not None and candidate not in reached:
                    reached.add(candidate)
                    frontier.append(candidate)
        return frozenset(reached)


@dataclass(frozen=True, slots=True)
class RealizationIds:
    same_as: tuple[tuple[int, ...], ...]
    direct_types: tuple[tuple[int, tuple[int, ...]], ...] = ()
    object_targets: tuple[tuple[int, int, tuple[int, ...]], ...] = ()
    data_targets: tuple[tuple[int, int, tuple[int, ...]], ...] = ()
    different_from: tuple[tuple[int, int], ...] = ()

    def __post_init__(self) -> None:
        groups = tuple(tuple(group) for group in self.same_as)
        members: set[int] = set()
        for group in groups:
            if not group or group != tuple(sorted(set(group))):
                raise ValueError("same-as groups must be nonempty, sorted, and unique")
            for member in group:
                _validate_u32(member, "individual_id")
            if members.intersection(group):
                raise ValueError("same-as groups must partition individuals")
            members.update(group)
        if groups != tuple(sorted(groups)):
            raise ValueError("same-as groups must be sorted")
        for group_id, types in self.direct_types:
            _validate_u32(group_id, "same_as_group_id")
            if group_id >= len(groups):
                raise ValueError("direct type references an absent same-as group")
            if types != tuple(sorted(set(types))):
                raise ValueError("direct type IDs must be sorted and unique")
            for value in types:
                _validate_u32(value, "class_node_id")
        for rows, value_name in (
            (self.object_targets, "object_target_id"),
            (self.data_targets, "source_literal_id"),
        ):
            for subject, prop, targets in rows:
                _validate_u32(subject, "same_as_group_id")
                _validate_u32(prop, "property_id")
                if subject >= len(groups):
                    raise ValueError("property answer references an absent same-as group")
                if targets != tuple(sorted(set(targets))):
                    raise ValueError("property targets must be sorted and unique")
                for target in targets:
                    _validate_u32(target, value_name)
        for left, right in self.different_from:
            _validate_u32(left, "different_from_left")
            _validate_u32(right, "different_from_right")
            if left >= right or right >= len(groups):
                raise ValueError("different-from pairs must be canonical valid group IDs")
        object.__setattr__(self, "same_as", groups)


@dataclass(frozen=True, slots=True)
class BackendInfo:
    name: Literal["python", "native", "verify"]
    package_version: str
    ir_schema_version: int
    implementation_version: str
    core_package_version: str
    core_api_version: tuple[int, int]
    core_model_schema_version: int
    core_wire_format_version: tuple[int, int]
    core_adapter_protocol_version: int
    complete_features: frozenset[str]
    accelerated: bool

    def __post_init__(self) -> None:
        if self.name not in ("python", "native", "verify"):
            raise ValueError("invalid backend name")
        for name in ("package_version", "implementation_version", "core_package_version"):
            if not isinstance(getattr(self, name), str) or not getattr(self, name):
                raise ValueError(f"{name} must be a nonempty string")
        if self.ir_schema_version != COMPILED_IR_SCHEMA_VERSION:
            raise ValueError("backend IR schema does not match the Python contract")
        _validate_version(self.core_api_version, "core_api_version")
        _validate_version(self.core_wire_format_version, "core_wire_format_version")
        features = frozenset(self.complete_features)
        if not all(isinstance(item, str) and item for item in features):
            raise TypeError("complete_features must contain nonempty strings")
        if not isinstance(self.accelerated, bool):
            raise TypeError("accelerated must be bool")
        object.__setattr__(self, "complete_features", features)


@dataclass(frozen=True, slots=True)
class BackendAvailability:
    name: Literal["python", "native"]
    available: bool
    implementation_version: str | None
    ir_schema_version: int | None
    reason: str | None

    def __post_init__(self) -> None:
        if self.name not in ("python", "native"):
            raise ValueError("availability name must be python or native")
        if not isinstance(self.available, bool):
            raise TypeError("available must be bool")
        if self.implementation_version is not None and (
            not isinstance(self.implementation_version, str) or not self.implementation_version
        ):
            raise ValueError("implementation_version must be nonempty or None")
        if self.ir_schema_version is not None and (
            isinstance(self.ir_schema_version, bool)
            or not isinstance(self.ir_schema_version, int)
            or self.ir_schema_version < 1
        ):
            raise ValueError("ir_schema_version must be positive or None")
        if self.reason is not None and (not isinstance(self.reason, str) or not self.reason):
            raise ValueError("reason must be nonempty or None")
        if self.available and self.reason is not None:
            raise ValueError("an available backend cannot have an unavailability reason")


@dataclass(frozen=True, slots=True)
class BackendStatus:
    environment_request: str | None
    default_selection: Literal["python", "native"]
    python: BackendAvailability
    native: BackendAvailability
    core_package_version: str
    core_api_version: tuple[int, int]

    def __post_init__(self) -> None:
        if self.environment_request is not None and not isinstance(self.environment_request, str):
            raise TypeError("environment_request must be str or None")
        if self.default_selection not in ("python", "native"):
            raise ValueError("default_selection must be python or native")
        if self.python.name != "python" or self.native.name != "native":
            raise ValueError("backend availability records are in the wrong slots")
        if not isinstance(self.core_package_version, str) or not self.core_package_version:
            raise ValueError("core_package_version must be nonempty")
        _validate_version(self.core_api_version, "core_api_version")


class BackendSession(Protocol):
    @property
    def ontology_fingerprint(self) -> str: ...

    def check(self, query: CompiledQuery | None = None) -> CheckResult: ...

    def check_many(self, queries: Sequence[CompiledQuery]) -> tuple[CheckResult, ...]: ...

    def classify_classes(self) -> HierarchyIds: ...

    def classify_object_properties(self) -> HierarchyIds: ...

    def classify_data_properties(self) -> HierarchyIds: ...

    def realize(self) -> RealizationIds: ...

    def apply_delta(self, delta: CompiledDelta) -> DeltaOutcome: ...

    def reset_query_state(self) -> None: ...

    def close(self) -> None: ...


class BackendFactory(Protocol):
    @property
    def info(self) -> BackendInfo: ...

    def create_session(
        self,
        ontology: CompiledOntology,
        config: ReasonerConfig,
        cancellation: CancellationToken,
    ) -> BackendSession: ...


def canonical_backend_json(value: BackendInfo | BackendAvailability | BackendStatus) -> str:
    """Stable JSON for diagnostics and Python/native fixture comparison."""

    if isinstance(value, BackendInfo):
        payload: Mapping[str, object] = {
            "accelerated": value.accelerated,
            "complete_features": sorted(value.complete_features),
            "core_adapter_protocol_version": value.core_adapter_protocol_version,
            "core_api_version": list(value.core_api_version),
            "core_model_schema_version": value.core_model_schema_version,
            "core_package_version": value.core_package_version,
            "core_wire_format_version": list(value.core_wire_format_version),
            "implementation_version": value.implementation_version,
            "ir_schema_version": value.ir_schema_version,
            "name": value.name,
            "package_version": value.package_version,
        }
    elif isinstance(value, BackendAvailability):
        payload = {
            "available": value.available,
            "implementation_version": value.implementation_version,
            "ir_schema_version": value.ir_schema_version,
            "name": value.name,
            "reason": value.reason,
        }
    elif isinstance(value, BackendStatus):
        payload = {
            "core_api_version": list(value.core_api_version),
            "core_package_version": value.core_package_version,
            "default_selection": value.default_selection,
            "environment_request": value.environment_request,
            "native": json.loads(canonical_backend_json(value.native)),
            "python": json.loads(canonical_backend_json(value.python)),
        }
    else:
        raise TypeError("unsupported backend diagnostic value")
    return json.dumps(payload, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


__all__ = [
    "COMPILED_IR_SCHEMA_VERSION",
    "U32_MAX",
    "BackendAvailability",
    "BackendFactory",
    "BackendInfo",
    "BackendSession",
    "BackendStatus",
    "CanonicalIR",
    "CheckResult",
    "CompiledDelta",
    "CompiledOntology",
    "CompiledQuery",
    "DeltaKind",
    "DeltaOutcome",
    "EntityRef",
    "FingerprintLike",
    "Hierarchy",
    "HierarchyIds",
    "RealizationIds",
    "ReasoningStatistics",
    "canonical_backend_json",
]
