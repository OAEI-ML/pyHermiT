"""Exact mixed-family OWL data-domain algebra.

SPDX-License-Identifier: LGPL-3.0-or-later

Family-local ranges are efficient semantic primitives, but OWL data ranges combine
overlapping numeric/string/date-time datatypes with disjoint primitive families.  This
module compiles the canonical semantic payload into bounded disjunctive normal form and
decides containment, emptiness, finite enumeration, and cardinality lower bounds over
the complete data domain.  No tableau or backend state is imported.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from enum import Enum
from functools import lru_cache
from typing import NoReturn, TypeAlias, cast

from pyhermit.events import CancellationToken
from pyhermit.exceptions import ResourceLimitError, UnsupportedDatatypeError

from .binary import XSD_BASE64_BINARY, XSD_HEX_BINARY
from .facets import FacetRestriction, restrict_datatype
from .ieee_ranges import IEEERange
from .literals import (
    NUMERIC_DATATYPES,
    RDFS_LITERAL,
    XSD_BOOLEAN,
    XSD_DOUBLE,
    XSD_FLOAT,
)
from .model import (
    BinaryIdentity,
    BinaryKind,
    BooleanComparison,
    BooleanIdentity,
    CompiledLiteral,
    DataIdentity,
    DatatypeLimits,
    DateTimeIdentity,
    IEEEFormat,
    IEEEIdentity,
    NumericComparison,
    NumericDomain,
    NumericIdentity,
    StringIdentity,
    URIIdentity,
    XMLIdentity,
)
from .nonnumeric_ranges import BinaryRange, StringRange, URIRange, XMLRange
from .ranges import BooleanRange, NumericRange, range_for_datatype
from .semantic import (
    DataRangePayloadKind,
    DataRangeSemanticPayload,
    DatatypeDefinitionSemanticPayload,
    DatatypeSemanticModelPayload,
    LiteralSemanticPayload,
    TaggedSemanticValue,
    data_identity_from_tagged,
)
from .temporal import XSD_DATE_TIME, XSD_DATE_TIME_STAMP
from .temporal_ranges import DateTimeRange
from .textual import RDF_PLAIN_LITERAL, STRING_DATATYPES, XSD_ANY_URI
from .xml_literal import RDF_XML_LITERAL


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class DataValueFamily(_StringEnum):
    """Disjoint partitions of the OWL data domain used by exact algebra."""

    NUMERIC = "numeric"
    BOOLEAN = "boolean"
    FLOAT = "float"
    DOUBLE = "double"
    STRING = "string"
    HEX_BINARY = "hex-binary"
    BASE64_BINARY = "base64-binary"
    URI = "uri"
    XML = "xml"
    DATE_TIME = "date-time"


_FAMILIES = tuple(DataValueFamily)
_FamilyRange: TypeAlias = (
    NumericRange
    | BooleanRange
    | IEEERange
    | StringRange
    | BinaryRange
    | URIRange
    | XMLRange
    | DateTimeRange
)


@dataclass(frozen=True, slots=True)
class _SignedAtom:
    payload: DataRangeSemanticPayload
    positive: bool

    def __post_init__(self) -> None:
        if not isinstance(self.payload, DataRangeSemanticPayload):
            raise TypeError("atom payload must be DataRangeSemanticPayload")
        if self.payload.kind not in {
            DataRangePayloadKind.DATATYPE,
            DataRangePayloadKind.RESTRICTION,
            DataRangePayloadKind.ENUMERATION,
        }:
            raise ValueError("mixed-domain atoms must be datatype, restriction, or enumeration")
        if not isinstance(self.positive, bool):
            raise TypeError("atom polarity must be bool")


_Clause: TypeAlias = tuple[_SignedAtom, ...]
_DNF: TypeAlias = tuple[_Clause, ...]


@dataclass(frozen=True, slots=True)
class DataDomainRange:
    """Canonical union of exact mixed-family conjunctions."""

    _clauses: _DNF

    def __post_init__(self) -> None:
        clauses = tuple(tuple(clause) for clause in self._clauses)
        if not all(all(isinstance(atom, _SignedAtom) for atom in clause) for clause in clauses):
            raise TypeError("clauses must contain signed data-domain atoms")
        normalized = _normalize_dnf(clauses, DatatypeLimits(), None)
        object.__setattr__(self, "_clauses", normalized)

    @classmethod
    def all(cls) -> DataDomainRange:
        return cls(((),))

    @classmethod
    def empty(cls) -> DataDomainRange:
        return cls(())

    @classmethod
    def enumeration(
        cls,
        values: Iterable[CompiledLiteral | LiteralSemanticPayload],
    ) -> DataDomainRange:
        payloads: list[LiteralSemanticPayload] = []
        for value in values:
            if isinstance(value, CompiledLiteral):
                payloads.append(LiteralSemanticPayload.from_compiled(value))
            elif isinstance(value, LiteralSemanticPayload):
                payloads.append(value)
            else:
                raise TypeError("enumeration values must be compiled or semantic literals")
        if not payloads:
            return cls.empty()
        payload = DataRangeSemanticPayload(
            DataRangePayloadKind.ENUMERATION,
            values=tuple(payloads),
        )
        return cls(((_SignedAtom(payload, True),),))

    @classmethod
    def from_payload(
        cls,
        payload: DataRangeSemanticPayload,
        *,
        definitions: Iterable[DatatypeDefinitionSemanticPayload] = (),
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> DataDomainRange:
        selected = _controls(limits, cancellation)
        if not isinstance(payload, DataRangeSemanticPayload):
            raise TypeError("payload must be DataRangeSemanticPayload")
        try:
            definition_items = tuple(definitions)
        except TypeError as error:
            raise TypeError("definitions must be semantic datatype definitions") from error
        if not all(
            isinstance(value, DatatypeDefinitionSemanticPayload) for value in definition_items
        ):
            raise TypeError("definitions must contain DatatypeDefinitionSemanticPayload values")
        names = {value.datatype_iri: value.data_range for value in definition_items}
        context = _DNFContext(names, selected, cancellation)
        return cls(context.compile(payload, negated=False, depth=1))

    @classmethod
    def from_model(
        cls,
        model: DatatypeSemanticModelPayload,
        data_range_id: int,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> DataDomainRange:
        if not isinstance(model, DatatypeSemanticModelPayload):
            raise TypeError("model must be DatatypeSemanticModelPayload")
        if isinstance(data_range_id, bool) or not isinstance(data_range_id, int):
            raise TypeError("data_range_id must be int")
        if data_range_id < 0 or data_range_id >= len(model.data_ranges):
            raise ValueError("data_range_id is dangling")
        return cls.from_payload(
            model.data_ranges[data_range_id],
            definitions=model.definitions,
            limits=limits,
            cancellation=cancellation,
        )

    def contains(
        self,
        value: CompiledLiteral,
        *,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        if not isinstance(value, CompiledLiteral):
            raise TypeError("value must be CompiledLiteral")
        if cancellation is not None and not isinstance(cancellation, CancellationToken):
            raise TypeError("cancellation must be CancellationToken or None")
        for clause in self._clauses:
            if cancellation is not None:
                cancellation.add_work(1)
                cancellation.check()
            if all(_atom_contains(atom.payload, value) is atom.positive for atom in clause):
                return True
        return False

    def intersection(
        self,
        other: DataDomainRange,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> DataDomainRange:
        if not isinstance(other, DataDomainRange):
            raise TypeError("other must be DataDomainRange")
        selected = _controls(limits, cancellation)
        return DataDomainRange(_and_dnf(self._clauses, other._clauses, selected, cancellation))

    def union(
        self,
        other: DataDomainRange,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> DataDomainRange:
        if not isinstance(other, DataDomainRange):
            raise TypeError("other must be DataDomainRange")
        selected = _controls(limits, cancellation)
        return DataDomainRange(
            _normalize_dnf(self._clauses + other._clauses, selected, cancellation)
        )

    def complement(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> DataDomainRange:
        selected = _controls(limits, cancellation)
        return DataDomainRange(_not_dnf(self._clauses, selected, cancellation))

    def is_empty_exact(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        return not self.cardinality_at_least(1, limits=limits, cancellation=cancellation)

    def cardinality_at_least(
        self,
        minimum: int,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        if isinstance(minimum, bool) or not isinstance(minimum, int):
            raise TypeError("minimum must be int")
        if minimum < 0:
            raise ValueError("minimum must be nonnegative")
        if minimum == 0:
            return True
        selected = _controls(limits, cancellation)
        for clause in self._clauses:
            if _clause_cardinality_at_least(
                clause,
                minimum,
                selected,
                cancellation,
            ):
                return True
        identities: set[DataIdentity] = set()
        for clause in self._clauses:
            for identity in _enumerate_clause(clause, selected, cancellation):
                identities.add(identity)
                if len(identities) >= minimum:
                    return True
        return False

    def finite_cardinality(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> int | None:
        selected = _controls(limits, cancellation)
        counts = tuple(
            _clause_cardinality(clause, selected, cancellation) for clause in self._clauses
        )
        if any(value is None for value in counts):
            return None
        integer_counts = cast(tuple[int, ...], counts)
        if len(integer_counts) == 1:
            return integer_counts[0]
        upper = sum(integer_counts)
        if upper > selected.max_enumeration_values:
            return None
        return len(self.enumerate_identities(limits=selected, cancellation=cancellation))

    def enumerate_identities(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> tuple[DataIdentity, ...]:
        selected = _controls(limits, cancellation)
        counts = tuple(
            _clause_cardinality(clause, selected, cancellation) for clause in self._clauses
        )
        if any(value is None for value in counts):
            raise ValueError("cannot enumerate an infinite data-domain range")
        total = sum(cast(tuple[int, ...], counts))
        if total > selected.max_enumeration_values:
            raise ResourceLimitError(
                "data-domain enumeration exceeds the configured value limit",
                limit="max_enumeration_values",
                observed=total,
                allowed=selected.max_enumeration_values,
            )
        identities = {
            identity
            for clause in self._clauses
            for identity in _enumerate_clause(clause, selected, cancellation)
        }
        return tuple(sorted(identities, key=lambda value: repr(value.as_tagged())))


class _DNFContext:
    __slots__ = ("cancellation", "definitions", "limits", "nodes")

    def __init__(
        self,
        definitions: Mapping[str, DataRangeSemanticPayload],
        limits: DatatypeLimits,
        cancellation: CancellationToken | None,
    ) -> None:
        self.definitions = definitions
        self.limits = limits
        self.cancellation = cancellation
        self.nodes = 0

    def compile(
        self,
        payload: DataRangeSemanticPayload,
        *,
        negated: bool,
        depth: int,
    ) -> _DNF:
        self.nodes += 1
        if depth > self.limits.max_data_range_depth:
            raise ResourceLimitError(
                "mixed data-domain compilation exceeds the depth limit",
                limit="max_data_range_depth",
                observed=depth,
                allowed=self.limits.max_data_range_depth,
            )
        if self.nodes > self.limits.max_data_range_nodes:
            raise ResourceLimitError(
                "mixed data-domain compilation exceeds the node limit",
                limit="max_data_range_nodes",
                observed=self.nodes,
                allowed=self.limits.max_data_range_nodes,
            )
        _poll(self.cancellation, self.nodes, self.limits.cancellation_poll_stride)
        if payload.kind is DataRangePayloadKind.OPAQUE:
            _unsupported(cast(str, payload.datatype_iri))
        if payload.kind is DataRangePayloadKind.DATATYPE:
            definition = self.definitions.get(cast(str, payload.datatype_iri))
            if definition is not None:
                return self.compile(definition, negated=negated, depth=depth + 1)
            return _atom_dnf(payload, not negated, self.limits, self.cancellation)
        if payload.kind in {
            DataRangePayloadKind.RESTRICTION,
            DataRangePayloadKind.ENUMERATION,
        }:
            return _atom_dnf(payload, not negated, self.limits, self.cancellation)
        if payload.kind is DataRangePayloadKind.COMPLEMENT:
            return self.compile(
                payload.operands[0],
                negated=not negated,
                depth=depth + 1,
            )
        intersection = payload.kind is DataRangePayloadKind.INTERSECTION
        combine_with_and = intersection != negated
        result: _DNF = ((),) if combine_with_and else ()
        for operand in payload.operands:
            compiled = self.compile(
                operand,
                negated=negated,
                depth=depth + 1,
            )
            result = (
                _and_dnf(result, compiled, self.limits, self.cancellation)
                if combine_with_and
                else _normalize_dnf(result + compiled, self.limits, self.cancellation)
            )
        return result


def _atom_dnf(
    payload: DataRangeSemanticPayload,
    positive: bool,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> _DNF:
    clause = _merge_clause((), (_SignedAtom(payload, positive),))
    return () if clause is None else _normalize_dnf((clause,), limits, cancellation)


def _and_dnf(
    left: _DNF,
    right: _DNF,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> _DNF:
    if not left or not right:
        return ()
    clauses: list[_Clause] = []
    for first in left:
        for second in right:
            merged = _merge_clause(first, second)
            if merged is not None:
                clauses.append(merged)
                if len(clauses) > limits.max_data_range_nodes:
                    raise ResourceLimitError(
                        "mixed data-domain DNF exceeds the configured clause limit",
                        limit="max_data_range_nodes",
                        observed=len(clauses),
                        allowed=limits.max_data_range_nodes,
                    )
            _poll(cancellation, len(clauses), limits.cancellation_poll_stride)
    return _normalize_dnf(tuple(clauses), limits, cancellation)


def _not_dnf(
    value: _DNF,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> _DNF:
    if not value:
        return ((),)
    result: _DNF = ((),)
    for clause in value:
        if not clause:
            return ()
        alternatives: _DNF = tuple(
            (_SignedAtom(atom.payload, not atom.positive),) for atom in clause
        )
        result = _and_dnf(result, alternatives, limits, cancellation)
    return result


def _merge_clause(left: _Clause, right: _Clause) -> _Clause | None:
    selected: dict[DataRangeSemanticPayload, bool] = {}
    for atom in (*left, *right):
        if _is_universal(atom.payload):
            if not atom.positive:
                return None
            continue
        prior = selected.get(atom.payload)
        if prior is not None and prior is not atom.positive:
            return None
        selected[atom.payload] = atom.positive
    return tuple(
        sorted(
            (_SignedAtom(payload, polarity) for payload, polarity in selected.items()),
            key=_atom_key,
        )
    )


def _normalize_dnf(
    clauses: _DNF,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> _DNF:
    unique = tuple(dict.fromkeys(clauses))
    if () in unique:
        return ((),)
    retained: list[_Clause] = []
    for clause in sorted(unique, key=_clause_key):
        atoms = frozenset(clause)
        if any(frozenset(prior) <= atoms for prior in retained):
            continue
        retained = [prior for prior in retained if not atoms < frozenset(prior)]
        retained.append(clause)
        if len(retained) > limits.max_data_range_nodes:
            raise ResourceLimitError(
                "mixed data-domain DNF exceeds the configured clause limit",
                limit="max_data_range_nodes",
                observed=len(retained),
                allowed=limits.max_data_range_nodes,
            )
        _poll(cancellation, len(retained), limits.cancellation_poll_stride)
    return tuple(sorted(retained, key=_clause_key))


def _atom_key(atom: _SignedAtom) -> tuple[bytes, bool]:
    return (atom.payload.canonical_bytes(), not atom.positive)


def _clause_key(clause: _Clause) -> tuple[tuple[bytes, bool], ...]:
    return tuple(_atom_key(atom) for atom in clause)


def _is_universal(payload: DataRangeSemanticPayload) -> bool:
    return payload.kind is DataRangePayloadKind.DATATYPE and payload.datatype_iri == RDFS_LITERAL


@dataclass(frozen=True, slots=True)
class _FamilySubset:
    family: DataValueFamily
    base: _FamilyRange
    numeric_exclusions: tuple[NumericRange, ...]
    finite_exclusions: frozenset[DataIdentity]

    def cardinality(
        self,
        limits: DatatypeLimits,
        cancellation: CancellationToken | None,
    ) -> int | None:
        if _range_empty(self.base, limits, cancellation):
            return 0
        cardinality = _range_cardinality(self.base, limits, cancellation)
        if cardinality is None:
            # A proper nested numeric domain cannot cover a non-singleton member of
            # its broader dense OWL domain; finite explicit exclusions cannot either.
            return None
        if cardinality > limits.max_enumeration_values and self.numeric_exclusions:
            return None
        if self.numeric_exclusions:
            values = _range_enumerate(self.base, limits, cancellation)
            retained = {
                identity
                for identity in values
                if not any(
                    exclusion.contains(_identity_numeric_comparison(identity))
                    for exclusion in self.numeric_exclusions
                )
                and identity not in self.finite_exclusions
            }
            return len(retained)
        removed = sum(
            1
            for identity in self.finite_exclusions
            if _identity_family(identity) is self.family and _range_contains(self.base, identity)
        )
        return cardinality - removed

    def cardinality_up_to(
        self,
        maximum: int,
        limits: DatatypeLimits,
        cancellation: CancellationToken | None,
    ) -> int:
        if maximum == 0 or _range_empty(self.base, limits, cancellation):
            return 0
        if self.numeric_exclusions:
            cardinality = _range_cardinality(self.base, limits, cancellation)
            if cardinality is None:
                return maximum
            values = _range_enumerate(self.base, limits, cancellation)
            retained = sum(
                not any(
                    exclusion.contains(_identity_numeric_comparison(identity))
                    for exclusion in self.numeric_exclusions
                )
                and identity not in self.finite_exclusions
                for identity in values
            )
            return min(retained, maximum)
        exclusion_bound = len(self.finite_exclusions)
        base_count = _range_cardinality_up_to(
            self.base,
            maximum + exclusion_bound,
            limits,
            cancellation,
        )
        if base_count == maximum + exclusion_bound:
            return maximum
        removed = sum(
            1
            for identity in self.finite_exclusions
            if _identity_family(identity) is self.family and _range_contains(self.base, identity)
        )
        return min(base_count - removed, maximum)

    def contains(self, identity: DataIdentity) -> bool:
        if _identity_family(identity) is not self.family:
            return False
        if identity in self.finite_exclusions:
            return False
        if not _range_contains(self.base, identity):
            return False
        return not any(
            exclusion.contains(_identity_numeric_comparison(identity))
            for exclusion in self.numeric_exclusions
        )

    def enumerate(
        self,
        limits: DatatypeLimits,
        cancellation: CancellationToken | None,
    ) -> tuple[DataIdentity, ...]:
        cardinality = self.cardinality(limits, cancellation)
        if cardinality is None:
            raise ValueError("cannot enumerate an infinite family subset")
        if cardinality > limits.max_enumeration_values:
            raise ResourceLimitError(
                "family enumeration exceeds the configured value limit",
                limit="max_enumeration_values",
                observed=cardinality,
                allowed=limits.max_enumeration_values,
            )
        return tuple(
            identity
            for identity in _range_enumerate(self.base, limits, cancellation)
            if self.contains(identity)
        )


def _clause_cardinality(
    clause: _Clause,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> int | None:
    explicit = _explicit_candidates(clause)
    if explicit is not None:
        return len(explicit)
    subsets = _clause_family_subsets(clause)
    total = 0
    for subset in subsets:
        cardinality = subset.cardinality(limits, cancellation)
        if cardinality is None:
            return None
        total += cardinality
    return total


def _clause_cardinality_at_least(
    clause: _Clause,
    minimum: int,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> bool:
    explicit = _explicit_candidates(clause)
    if explicit is not None:
        return len(explicit) >= minimum
    total = 0
    for subset in _clause_family_subsets(clause):
        total += subset.cardinality_up_to(minimum - total, limits, cancellation)
        if total >= minimum:
            return True
    return False


def _enumerate_clause(
    clause: _Clause,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> tuple[DataIdentity, ...]:
    explicit = _explicit_candidates(clause)
    if explicit is not None:
        return explicit
    output: list[DataIdentity] = []
    for subset in _clause_family_subsets(clause):
        output.extend(subset.enumerate(limits, cancellation))
    return tuple(output)


def _explicit_candidates(clause: _Clause) -> tuple[DataIdentity, ...] | None:
    positives = [
        atom.payload
        for atom in clause
        if atom.positive and atom.payload.kind is DataRangePayloadKind.ENUMERATION
    ]
    if not positives:
        return None
    candidates = {value.data_identity: value for value in positives[0].values}
    for payload in positives[1:]:
        retained_keys = {value.data_identity for value in payload.values}
        candidates = {key: value for key, value in candidates.items() if key in retained_keys}
    retained: list[DataIdentity] = []
    for tagged, value in candidates.items():
        compiled = value.to_compiled()
        if all(_atom_contains(atom.payload, compiled) is atom.positive for atom in clause):
            retained.append(data_identity_from_tagged(tagged))
    return tuple(sorted(set(retained), key=lambda item: repr(item.as_tagged())))


def _clause_family_subsets(clause: _Clause) -> tuple[_FamilySubset, ...]:
    positive_families = {
        _payload_family(atom.payload)
        for atom in clause
        if atom.positive and atom.payload.kind is not DataRangePayloadKind.ENUMERATION
    }
    if len(positive_families) > 1:
        return ()
    families = tuple(positive_families) if positive_families else _FAMILIES
    negative_values = frozenset(
        data_identity_from_tagged(value.data_identity)
        for atom in clause
        if not atom.positive and atom.payload.kind is DataRangePayloadKind.ENUMERATION
        for value in atom.payload.values
    )
    output: list[_FamilySubset] = []
    for family in families:
        positive_ranges = tuple(
            _atom_range(atom.payload)
            for atom in clause
            if atom.positive
            and atom.payload.kind is not DataRangePayloadKind.ENUMERATION
            and _payload_family(atom.payload) is family
        )
        negative_ranges = tuple(
            _atom_range(atom.payload)
            for atom in clause
            if not atom.positive
            and atom.payload.kind is not DataRangePayloadKind.ENUMERATION
            and _payload_family(atom.payload) is family
        )
        base = _family_universe(family)
        for value in positive_ranges:
            base = _range_intersection(base, value)
        numeric_exclusions: list[NumericRange] = []
        for value in negative_ranges:
            if (
                family is DataValueFamily.NUMERIC
                and isinstance(base, NumericRange)
                and isinstance(value, NumericRange)
                and value.domain < base.domain
            ):
                numeric_exclusions.append(value)
            else:
                base = _range_intersection(base, _range_complement(value))
        exclusions = frozenset(
            value for value in negative_values if _identity_family(value) is family
        )
        output.append(_FamilySubset(family, base, tuple(numeric_exclusions), exclusions))
    return tuple(output)


def _payload_family(payload: DataRangeSemanticPayload) -> DataValueFamily:
    iri = cast(str, payload.datatype_iri)
    if iri in NUMERIC_DATATYPES:
        return DataValueFamily.NUMERIC
    if iri == XSD_BOOLEAN:
        return DataValueFamily.BOOLEAN
    if iri == XSD_FLOAT:
        return DataValueFamily.FLOAT
    if iri == XSD_DOUBLE:
        return DataValueFamily.DOUBLE
    if iri in STRING_DATATYPES:
        return DataValueFamily.STRING
    if iri == XSD_HEX_BINARY:
        return DataValueFamily.HEX_BINARY
    if iri == XSD_BASE64_BINARY:
        return DataValueFamily.BASE64_BINARY
    if iri == XSD_ANY_URI:
        return DataValueFamily.URI
    if iri == RDF_XML_LITERAL:
        return DataValueFamily.XML
    if iri in {XSD_DATE_TIME, XSD_DATE_TIME_STAMP}:
        return DataValueFamily.DATE_TIME
    _unsupported(iri)


def _identity_family(value: DataIdentity) -> DataValueFamily:
    if isinstance(value, NumericIdentity):
        return DataValueFamily.NUMERIC
    if isinstance(value, BooleanIdentity):
        return DataValueFamily.BOOLEAN
    if isinstance(value, IEEEIdentity):
        return (
            DataValueFamily.FLOAT if value.format is IEEEFormat.FLOAT32 else DataValueFamily.DOUBLE
        )
    if isinstance(value, StringIdentity):
        return DataValueFamily.STRING
    if isinstance(value, BinaryIdentity):
        return (
            DataValueFamily.HEX_BINARY
            if value.kind is BinaryKind.HEX
            else DataValueFamily.BASE64_BINARY
        )
    if isinstance(value, URIIdentity):
        return DataValueFamily.URI
    if isinstance(value, XMLIdentity):
        return DataValueFamily.XML
    if isinstance(value, DateTimeIdentity):
        return DataValueFamily.DATE_TIME
    raise AssertionError("closed DataIdentity family dispatch is incomplete")


@lru_cache(maxsize=4096)
def _atom_range(payload: DataRangeSemanticPayload) -> _FamilyRange:
    iri = cast(str, payload.datatype_iri)
    if payload.kind is DataRangePayloadKind.DATATYPE:
        value = range_for_datatype(iri)
    elif payload.kind is DataRangePayloadKind.RESTRICTION:
        value = restrict_datatype(
            iri,
            tuple(
                FacetRestriction(item.facet_iri, item.value.to_compiled())
                for item in payload.facets
            ),
        )
    else:
        raise TypeError("only datatype and restriction payloads have family ranges")
    if isinstance(value, StringRange):
        universe = StringRange.all(RDF_PLAIN_LITERAL)
        return StringRange(
            RDF_PLAIN_LITERAL,
            universe.universe_without_language,
            universe.universe_with_language,
            value.without_language,
            value.with_language,
        )
    if isinstance(value, DateTimeRange):
        return DateTimeRange(value.zoned, value.unzoned, True)
    if isinstance(
        value,
        (
            NumericRange,
            BooleanRange,
            IEEERange,
            BinaryRange,
            URIRange,
            XMLRange,
        ),
    ):
        return value
    raise AssertionError("rdfs:Literal should have been simplified before family algebra")


def _atom_contains(payload: DataRangeSemanticPayload, value: CompiledLiteral) -> bool:
    if payload.kind is DataRangePayloadKind.ENUMERATION:
        tagged = cast(TaggedSemanticValue, value.data_identity.as_tagged())
        return any(item.data_identity == tagged for item in payload.values)
    return _range_contains(_atom_range(payload), value.data_identity)


def _family_universe(family: DataValueFamily) -> _FamilyRange:
    if family is DataValueFamily.NUMERIC:
        return NumericRange.all(NumericDomain.REAL)
    if family is DataValueFamily.BOOLEAN:
        return BooleanRange.all()
    if family is DataValueFamily.FLOAT:
        return IEEERange.all(IEEEFormat.FLOAT32)
    if family is DataValueFamily.DOUBLE:
        return IEEERange.all(IEEEFormat.FLOAT64)
    if family is DataValueFamily.STRING:
        return StringRange.all(RDF_PLAIN_LITERAL)
    if family is DataValueFamily.HEX_BINARY:
        return BinaryRange.all(BinaryKind.HEX)
    if family is DataValueFamily.BASE64_BINARY:
        return BinaryRange.all(BinaryKind.BASE64)
    if family is DataValueFamily.URI:
        return URIRange.all()
    if family is DataValueFamily.XML:
        return XMLRange.all()
    return DateTimeRange.all()


def _range_intersection(left: _FamilyRange, right: _FamilyRange) -> _FamilyRange:
    if isinstance(left, NumericRange) and isinstance(right, NumericRange):
        return left.intersection(right)
    if isinstance(left, BooleanRange) and isinstance(right, BooleanRange):
        return left.intersection(right)
    if isinstance(left, IEEERange) and isinstance(right, IEEERange):
        return left.intersection(right)
    if isinstance(left, StringRange) and isinstance(right, StringRange):
        return left.intersection(right)
    if isinstance(left, BinaryRange) and isinstance(right, BinaryRange):
        return left.intersection(right)
    if isinstance(left, URIRange) and isinstance(right, URIRange):
        return left.intersection(right)
    if isinstance(left, XMLRange) and isinstance(right, XMLRange):
        return left.intersection(right)
    if isinstance(left, DateTimeRange) and isinstance(right, DateTimeRange):
        return left.intersection(right)
    raise TypeError("family range intersection requires one canonical family")


def _range_complement(value: _FamilyRange) -> _FamilyRange:
    return value.complement()


def _range_empty(
    value: _FamilyRange,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> bool:
    if isinstance(value, (StringRange, URIRange)):
        return value.is_empty_exact(limits=limits, cancellation=cancellation)
    return value.is_empty_exact()


def _range_cardinality(
    value: _FamilyRange,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> int | None:
    if isinstance(value, (StringRange, URIRange)):
        return value.finite_cardinality(limits=limits, cancellation=cancellation)
    return value.finite_cardinality()


def _range_cardinality_up_to(
    value: _FamilyRange,
    maximum: int,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> int:
    if isinstance(value, (BinaryRange, StringRange, URIRange)):
        return value.cardinality_up_to(
            maximum,
            limits=limits,
            cancellation=cancellation,
        )
    cardinality = _range_cardinality(value, limits, cancellation)
    return maximum if cardinality is None else min(cardinality, maximum)


def _range_contains(value: _FamilyRange, identity: DataIdentity) -> bool:
    if isinstance(value, NumericRange):
        return isinstance(identity, NumericIdentity) and value.contains(
            NumericComparison(identity.numerator, identity.denominator)
        )
    if isinstance(value, BooleanRange):
        return isinstance(identity, BooleanIdentity) and value.contains(
            BooleanComparison(identity.value)
        )
    if isinstance(value, IEEERange):
        return isinstance(identity, IEEEIdentity) and value.contains(identity)
    if isinstance(value, StringRange):
        return isinstance(identity, StringIdentity) and value.contains(identity)
    if isinstance(value, BinaryRange):
        return isinstance(identity, BinaryIdentity) and value.contains(identity)
    if isinstance(value, URIRange):
        return isinstance(identity, URIIdentity) and value.contains(identity)
    if isinstance(value, XMLRange):
        return isinstance(identity, XMLIdentity) and value.contains(identity)
    return isinstance(identity, DateTimeIdentity) and value.contains(identity)


def _range_enumerate(
    value: _FamilyRange,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> tuple[DataIdentity, ...]:
    if isinstance(value, NumericRange):
        return tuple(
            NumericIdentity(item.numerator, item.denominator)
            for item in value.enumerate_values(limits=limits, cancellation=cancellation)
        )
    if isinstance(value, BooleanRange):
        return tuple(
            BooleanIdentity(item.value)
            for item in value.enumerate_values(cancellation=cancellation)
        )
    if isinstance(value, IEEERange):
        return value.enumerate_values(limits=limits, cancellation=cancellation)
    if isinstance(value, BinaryRange):
        return value.enumerate_values(limits=limits, cancellation=cancellation)
    if isinstance(value, StringRange):
        return value.enumerate_values(limits=limits, cancellation=cancellation)
    if isinstance(value, URIRange):
        return value.enumerate_values(limits=limits, cancellation=cancellation)
    if isinstance(value, DateTimeRange):
        return tuple(
            DateTimeIdentity(
                item.local_numerator,
                item.local_denominator,
                item.timezone_offset_minutes,
            )
            for item in value.enumerate_values(limits=limits, cancellation=cancellation)
        )
    if _range_empty(value, limits, cancellation):
        return ()
    raise ValueError("nonempty string/URI/XML family range is infinite")


def _identity_numeric_comparison(value: DataIdentity) -> NumericComparison:
    if not isinstance(value, NumericIdentity):
        raise TypeError("numeric exclusion requires NumericIdentity")
    return NumericComparison(value.numerator, value.denominator)


def _controls(
    limits: DatatypeLimits | None,
    cancellation: CancellationToken | None,
) -> DatatypeLimits:
    selected = limits or DatatypeLimits()
    if not isinstance(selected, DatatypeLimits):
        raise TypeError("limits must be DatatypeLimits or None")
    if cancellation is not None and not isinstance(cancellation, CancellationToken):
        raise TypeError("cancellation must be CancellationToken or None")
    if cancellation is not None:
        cancellation.check()
    return selected


def _poll(
    cancellation: CancellationToken | None,
    work: int,
    stride: int,
) -> None:
    if cancellation is not None and work and work % stride == 0:
        cancellation.add_work(stride)
        cancellation.check()


def _unsupported(datatype_iri: str) -> NoReturn:
    raise UnsupportedDatatypeError(
        "opaque datatype semantics cannot be evaluated",
        context={"datatype_iri": datatype_iri},
    )


__all__ = ["DataDomainRange", "DataValueFamily"]
