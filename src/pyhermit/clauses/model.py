"""Validated immutable DL-clause intermediate representation.

The records in this module are the language-neutral boundary shared by the Python
and optional native tableaux.  They intentionally contain no public OWL objects or
backend pointers.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, fields
from enum import Enum
from typing import TypeAlias, TypeVar, cast

from pyhermit.backends.protocol import COMPILED_IR_SCHEMA_VERSION, U32_MAX
from pyhermit.exceptions import ResourceLimitError

_SHA256 = re.compile(r"[0-9a-f]{64}\Z")
_RecordT = TypeVar("_RecordT", bound="CanonicalRecord")
_EMPTY_DATATYPE_SEMANTIC_JSON = (
    '{"data_ranges":[],"definitions":[],"record":"datatype_semantic_model","schema_version":1}'
)


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class TermSort(_StringEnum):
    OBJECT = "object"
    DATA = "data"


class SymbolKind(_StringEnum):
    ENTITY = "entity"
    CLASS_EXPRESSION = "class_expression"
    DATA_RANGE = "data_range"
    OBJECT_ROLE = "object_role"
    DATA_PROPERTY = "data_property"
    INDIVIDUAL = "individual"
    SOURCE_LITERAL = "source_literal"
    DATA_VALUE = "data_value"


class PredicateKind(_StringEnum):
    CONCEPT = "concept"
    NEGATED_CONCEPT = "negated_concept"
    NOMINAL = "nominal"
    NEGATED_NOMINAL = "negated_nominal"
    OBJECT_ROLE = "object_role"
    NEGATED_OBJECT_ROLE = "negated_object_role"
    DATA_ROLE = "data_role"
    NEGATED_DATA_ROLE = "negated_data_role"
    DATA_RANGE = "data_range"
    NEGATED_DATA_RANGE = "negated_data_range"
    EQUALITY = "equality"
    INEQUALITY = "inequality"
    AT_LEAST_OBJECT = "at_least_object"
    AT_LEAST_DATA = "at_least_data"
    ANNOTATED_EQUALITY = "annotated_equality"
    AUTOMATON_STATE = "automaton_state"
    DISJOINT_GUARD = "disjoint_guard"
    ORDERING_GUARD = "ordering_guard"
    NAMED_INDIVIDUAL = "named_individual"


class DeltaCompatibility(_StringEnum):
    ASSERTION_ONLY = "assertion_only"
    DECLARATION_ONLY = "declaration_only"
    REBUILD_REQUIRED = "rebuild_required"
    REJECTED = "rejected"


def _u32(value: int, name: str) -> None:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an unsigned 32-bit integer")
    if value < 0 or value > U32_MAX:
        raise ResourceLimitError(
            f"{name} exceeds the unsigned 32-bit IR limit",
            limit="u32",
            observed=value,
            allowed=U32_MAX,
        )


def _canonical_json(payload: object) -> str:
    return json.dumps(payload, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


class CanonicalRecord:
    """Small implementation shared by all schema records."""

    schema_version: int

    def to_payload(self) -> dict[str, object]:
        return _record_payload(self)

    def canonical_bytes(self) -> bytes:
        return _canonical_json(self.to_payload()).encode("utf-8")


@dataclass(frozen=True, slots=True, order=True)
class Variable(CanonicalRecord):
    index: int
    sort: TermSort
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.index, "variable index")
        if not isinstance(self.sort, TermSort):
            raise TypeError("variable sort must be TermSort")


@dataclass(frozen=True, slots=True, order=True)
class IndividualTerm(CanonicalRecord):
    individual_id: int
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.individual_id, "individual_id")


@dataclass(frozen=True, slots=True, order=True)
class DataConstant(CanonicalRecord):
    source_literal_id: int
    data_identity_id: int
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.source_literal_id, "source_literal_id")
        _u32(self.data_identity_id, "data_identity_id")


Term: TypeAlias = Variable | IndividualTerm | DataConstant
GroundTerm: TypeAlias = IndividualTerm | DataConstant


def term_sort(term: Term) -> TermSort:
    if isinstance(term, (Variable,)):
        return term.sort
    if isinstance(term, IndividualTerm):
        return TermSort.OBJECT
    if isinstance(term, DataConstant):
        return TermSort.DATA
    raise TypeError("term must be a compiled Term")


def _term_order_key(term: Term) -> tuple[str, int, int]:
    if isinstance(term, Variable):
        return (f"0:{term.sort.value}", term.index, 0)
    if isinstance(term, IndividualTerm):
        return ("1:object", term.individual_id, 0)
    return ("2:data", term.data_identity_id, term.source_literal_id)


@dataclass(frozen=True, slots=True, order=True)
class SymbolValue(CanonicalRecord):
    identifier: int
    key_hex: str
    display: str
    generated: bool = False
    query_local: bool = False
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.identifier, "symbol identifier")
        if not isinstance(self.key_hex, str) or not self.key_hex:
            raise ValueError("symbol key_hex must be nonempty")
        try:
            decoded_key = bytes.fromhex(self.key_hex)
        except ValueError as error:
            raise ValueError("symbol key_hex must contain hexadecimal bytes") from error
        if decoded_key.hex() != self.key_hex:
            raise ValueError("symbol key_hex must be canonical lowercase hexadecimal")
        if not isinstance(self.display, str) or not self.display:
            raise ValueError("symbol display must be nonempty")
        if not isinstance(self.generated, bool) or not isinstance(self.query_local, bool):
            raise TypeError("symbol generated/query_local flags must be bool")


@dataclass(frozen=True, slots=True)
class SymbolDomain(CanonicalRecord):
    kind: SymbolKind
    values: tuple[SymbolValue, ...]
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        if not isinstance(self.kind, SymbolKind):
            raise TypeError("symbol domain kind must be SymbolKind")
        values = tuple(self.values)
        if not all(isinstance(value, SymbolValue) for value in values):
            raise TypeError("symbol domain values must contain SymbolValue")
        if tuple(value.identifier for value in values) != tuple(range(len(values))):
            raise ValueError("symbol identifiers must be dense and ordered")
        keys = tuple(value.key_hex for value in values)
        if len(keys) != len(set(keys)):
            raise ValueError("symbol values must have unique canonical keys")
        object.__setattr__(self, "values", values)

    def value(self, identifier: int) -> SymbolValue:
        _u32(identifier, "symbol identifier")
        try:
            return self.values[identifier]
        except IndexError as error:
            raise ValueError("symbol identifier is dangling") from error


@dataclass(frozen=True, slots=True)
class SymbolTable(CanonicalRecord):
    domains: tuple[SymbolDomain, ...]
    predicates: PredicateRegistry | None = None
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        domains = tuple(self.domains)
        if not all(isinstance(value, SymbolDomain) for value in domains):
            raise TypeError("domains must contain SymbolDomain values")
        kinds = tuple(value.kind.value for value in domains)
        if kinds != tuple(sorted(kinds)) or len(kinds) != len(set(kinds)):
            raise ValueError("symbol domains must be uniquely sorted by kind")
        if self.predicates is not None and not isinstance(self.predicates, PredicateRegistry):
            raise TypeError("symbol-table predicates must be PredicateRegistry or None")
        object.__setattr__(self, "domains", domains)

    def domain(self, kind: SymbolKind) -> SymbolDomain:
        for value in self.domains:
            if value.kind is kind:
                return value
        raise ValueError(f"missing symbol domain {kind.value}")


_UNARY_KINDS = frozenset(
    {
        PredicateKind.CONCEPT,
        PredicateKind.NEGATED_CONCEPT,
        PredicateKind.NOMINAL,
        PredicateKind.NEGATED_NOMINAL,
        PredicateKind.AT_LEAST_OBJECT,
        PredicateKind.AT_LEAST_DATA,
        PredicateKind.AUTOMATON_STATE,
        PredicateKind.DISJOINT_GUARD,
        PredicateKind.NAMED_INDIVIDUAL,
    }
)
_BINARY_KINDS = frozenset(
    {
        PredicateKind.OBJECT_ROLE,
        PredicateKind.NEGATED_OBJECT_ROLE,
        PredicateKind.DATA_ROLE,
        PredicateKind.NEGATED_DATA_ROLE,
        PredicateKind.EQUALITY,
        PredicateKind.INEQUALITY,
        PredicateKind.ORDERING_GUARD,
    }
)
_DATA_RANGE_KINDS = frozenset({PredicateKind.DATA_RANGE, PredicateKind.NEGATED_DATA_RANGE})
_NEGATIVE_FACT_KINDS = frozenset(
    {
        PredicateKind.NEGATED_CONCEPT,
        PredicateKind.NEGATED_NOMINAL,
        PredicateKind.NEGATED_OBJECT_ROLE,
        PredicateKind.NEGATED_DATA_ROLE,
        PredicateKind.NEGATED_DATA_RANGE,
    }
)


@dataclass(frozen=True, slots=True, order=True)
class Predicate(CanonicalRecord):
    predicate_id: int
    kind: PredicateKind
    argument_sorts: tuple[TermSort, ...]
    symbol_id: int | None = None
    role_id: int | None = None
    cardinality: int | None = None
    filler_predicate_id: int | None = None
    annotation: tuple[int, ...] = ()
    internal_key: str | None = None
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.predicate_id, "predicate_id")
        if not isinstance(self.kind, PredicateKind):
            raise TypeError("predicate kind must be PredicateKind")
        sorts = tuple(self.argument_sorts)
        if not all(isinstance(value, TermSort) for value in sorts):
            raise TypeError("predicate argument sorts must contain TermSort")
        expected_arity = (
            len(sorts)
            if self.kind in _DATA_RANGE_KINDS
            else (
                3
                if self.kind is PredicateKind.ANNOTATED_EQUALITY
                else (1 if self.kind in _UNARY_KINDS else 2)
            )
        )
        if self.kind not in _UNARY_KINDS | _BINARY_KINDS | _DATA_RANGE_KINDS | {
            PredicateKind.ANNOTATED_EQUALITY
        }:
            raise ValueError(f"unclassified predicate kind {self.kind.value}")
        if len(sorts) != expected_arity:
            raise ValueError(f"{self.kind.value} predicate must have arity {expected_arity}")
        for name in ("symbol_id", "role_id", "cardinality", "filler_predicate_id"):
            value = getattr(self, name)
            if value is not None:
                _u32(value, name)
        annotation = tuple(self.annotation)
        for value in annotation:
            _u32(value, "predicate annotation")
        if self.internal_key is not None and (
            not isinstance(self.internal_key, str) or not self.internal_key
        ):
            raise ValueError("internal_key must be a nonempty string or None")
        _validate_predicate_shape(self)
        object.__setattr__(self, "argument_sorts", sorts)
        object.__setattr__(self, "annotation", annotation)

    def identity_payload(self) -> dict[str, object]:
        payload = self.to_payload()
        payload.pop("predicate_id")
        return payload


def _validate_predicate_shape(predicate: Predicate) -> None:
    kind = predicate.kind
    concept_kinds = {
        PredicateKind.CONCEPT,
        PredicateKind.NEGATED_CONCEPT,
        PredicateKind.NOMINAL,
        PredicateKind.NEGATED_NOMINAL,
    }
    object_unary = {
        PredicateKind.CONCEPT,
        PredicateKind.NEGATED_CONCEPT,
        PredicateKind.NOMINAL,
        PredicateKind.NEGATED_NOMINAL,
        PredicateKind.AT_LEAST_OBJECT,
        PredicateKind.AT_LEAST_DATA,
        PredicateKind.AUTOMATON_STATE,
        PredicateKind.DISJOINT_GUARD,
        PredicateKind.NAMED_INDIVIDUAL,
    }
    if kind in object_unary and predicate.argument_sorts != (TermSort.OBJECT,):
        raise ValueError(f"{kind.value} requires one object argument")
    if kind in _DATA_RANGE_KINDS and (
        not predicate.argument_sorts
        or any(value is not TermSort.DATA for value in predicate.argument_sorts)
    ):
        raise ValueError(f"{kind.value} requires one or more data arguments")
    if kind in {PredicateKind.OBJECT_ROLE, PredicateKind.NEGATED_OBJECT_ROLE} and (
        predicate.argument_sorts != (TermSort.OBJECT, TermSort.OBJECT)
    ):
        raise ValueError(f"{kind.value} requires two object arguments")
    if kind in {PredicateKind.DATA_ROLE, PredicateKind.NEGATED_DATA_ROLE} and (
        predicate.argument_sorts != (TermSort.OBJECT, TermSort.DATA)
    ):
        raise ValueError(f"{kind.value} requires object/data arguments")
    if (
        kind in {PredicateKind.EQUALITY, PredicateKind.INEQUALITY, PredicateKind.ORDERING_GUARD}
        and predicate.argument_sorts[0] is not predicate.argument_sorts[1]
    ):
        raise ValueError(f"{kind.value} cannot mix object and data arguments")
    if kind is PredicateKind.ANNOTATED_EQUALITY and predicate.argument_sorts != (
        TermSort.OBJECT,
        TermSort.OBJECT,
        TermSort.OBJECT,
    ):
        raise ValueError("annotated equality requires three object arguments")
    cardinality_kinds = {
        PredicateKind.AT_LEAST_OBJECT,
        PredicateKind.AT_LEAST_DATA,
        PredicateKind.ANNOTATED_EQUALITY,
    }
    if kind in cardinality_kinds:
        if predicate.cardinality is None or predicate.cardinality < 1:
            raise ValueError("cardinality predicates require a positive cardinality")
        if predicate.role_id is None or predicate.filler_predicate_id is None:
            raise ValueError("cardinality predicates require role and filler predicate IDs")
    elif predicate.cardinality is not None or predicate.filler_predicate_id is not None:
        raise ValueError("cardinality/filler fields are reserved for cardinality predicates")
    if (
        kind
        in {
            PredicateKind.OBJECT_ROLE,
            PredicateKind.NEGATED_OBJECT_ROLE,
            PredicateKind.DATA_ROLE,
            PredicateKind.NEGATED_DATA_ROLE,
        }
        and predicate.role_id is None
    ):
        raise ValueError("role predicates require role_id")
    if kind in concept_kinds | _DATA_RANGE_KINDS and predicate.symbol_id is None:
        raise ValueError("concept/nominal/data-range predicates require symbol_id")
    if kind not in concept_kinds | _DATA_RANGE_KINDS and predicate.symbol_id is not None:
        raise ValueError("symbol_id is reserved for concept/nominal/data-range predicates")
    if (
        kind
        not in cardinality_kinds
        | {
            PredicateKind.OBJECT_ROLE,
            PredicateKind.NEGATED_OBJECT_ROLE,
            PredicateKind.DATA_ROLE,
            PredicateKind.NEGATED_DATA_ROLE,
        }
        and predicate.role_id is not None
    ):
        raise ValueError("role_id is not valid for this predicate kind")

    annotation_kinds = {
        PredicateKind.NOMINAL,
        PredicateKind.NEGATED_NOMINAL,
        PredicateKind.AT_LEAST_DATA,
        PredicateKind.AUTOMATON_STATE,
        PredicateKind.DISJOINT_GUARD,
    }
    if kind not in annotation_kinds and predicate.annotation:
        raise ValueError("annotation is not valid for this predicate kind")
    if kind in {PredicateKind.NOMINAL, PredicateKind.NEGATED_NOMINAL} and (
        not predicate.annotation or predicate.annotation != tuple(sorted(set(predicate.annotation)))
    ):
        raise ValueError("nominal annotations must be nonempty, sorted, and unique")
    if kind is PredicateKind.AT_LEAST_DATA and (
        not predicate.annotation
        or predicate.annotation[0] != predicate.role_id
        or len(predicate.annotation) != len(set(predicate.annotation))
    ):
        raise ValueError("data at-least annotations must list unique role IDs")
    if kind is PredicateKind.AUTOMATON_STATE and len(predicate.annotation) != 2:
        raise ValueError("automaton-state annotations require component and state IDs")
    if kind is PredicateKind.DISJOINT_GUARD and len(predicate.annotation) != 1:
        raise ValueError("disjoint guards require one sequence annotation")

    internal_kinds = {
        PredicateKind.AUTOMATON_STATE,
        PredicateKind.DISJOINT_GUARD,
        PredicateKind.ORDERING_GUARD,
        PredicateKind.NAMED_INDIVIDUAL,
    }
    if kind in internal_kinds and predicate.internal_key is None:
        raise ValueError(f"{kind.value} requires an internal key")
    if kind not in internal_kinds and predicate.internal_key is not None:
        raise ValueError("internal_key is reserved for internal strategy predicates")
    if kind is PredicateKind.ORDERING_GUARD and predicate.internal_key != (
        f"canonical-{predicate.argument_sorts[0].value}-order"
    ):
        raise ValueError("ordering guard internal key must identify its canonical term sort")


@dataclass(frozen=True, slots=True)
class PredicateRegistry(CanonicalRecord):
    predicates: tuple[Predicate, ...]
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        values = tuple(self.predicates)
        if not all(isinstance(value, Predicate) for value in values):
            raise TypeError("predicates must contain Predicate values")
        if tuple(value.predicate_id for value in values) != tuple(range(len(values))):
            raise ValueError("predicate IDs must be dense and ordered")
        keys = tuple(_canonical_json(value.identity_payload()) for value in values)
        if len(keys) != len(set(keys)):
            raise ValueError("predicates must have unique structural identities")
        for predicate in values:
            if predicate.filler_predicate_id is not None:
                if predicate.filler_predicate_id >= len(values):
                    raise ValueError("cardinality filler predicate ID is dangling")
                if predicate.filler_predicate_id == predicate.predicate_id:
                    raise ValueError("cardinality predicates cannot be their own filler")
                filler = values[predicate.filler_predicate_id]
                if predicate.kind in {
                    PredicateKind.AT_LEAST_OBJECT,
                    PredicateKind.ANNOTATED_EQUALITY,
                } and filler.kind not in {
                    PredicateKind.CONCEPT,
                    PredicateKind.NEGATED_CONCEPT,
                    PredicateKind.NOMINAL,
                    PredicateKind.NEGATED_NOMINAL,
                }:
                    raise ValueError("object-cardinality filler must be an object concept literal")
                if predicate.kind is PredicateKind.AT_LEAST_DATA and (
                    filler.kind not in {PredicateKind.DATA_RANGE, PredicateKind.NEGATED_DATA_RANGE}
                    or filler.argument_sorts != (TermSort.DATA,) * len(predicate.annotation)
                ):
                    raise ValueError("data at-least filler must be a matching data-range literal")
        object.__setattr__(self, "predicates", values)

    def predicate(self, predicate_id: int) -> Predicate:
        _u32(predicate_id, "predicate_id")
        try:
            return self.predicates[predicate_id]
        except IndexError as error:
            raise ValueError("predicate ID is dangling") from error


@dataclass(frozen=True, slots=True)
class Atom(CanonicalRecord):
    predicate_id: int
    arguments: tuple[Term, ...]
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.predicate_id, "atom predicate_id")
        arguments = tuple(self.arguments)
        if not all(
            isinstance(value, (Variable, IndividualTerm, DataConstant)) for value in arguments
        ):
            raise TypeError("atom arguments must contain compiled terms")
        object.__setattr__(self, "arguments", arguments)


@dataclass(frozen=True, slots=True)
class GroundAtom(CanonicalRecord):
    predicate_id: int
    arguments: tuple[GroundTerm, ...]
    provenance_ids: tuple[int, ...]
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.predicate_id, "ground atom predicate_id")
        arguments = tuple(self.arguments)
        if not all(isinstance(value, (IndividualTerm, DataConstant)) for value in arguments):
            raise TypeError("ground atom arguments cannot contain variables")
        provenance = _sorted_u32(self.provenance_ids, "ground atom provenance")
        if not provenance:
            raise ValueError("ground facts require provenance")
        object.__setattr__(self, "arguments", arguments)
        object.__setattr__(self, "provenance_ids", provenance)


@dataclass(frozen=True, slots=True, order=True)
class DeltaFactIR(CanonicalRecord):
    """Applicable fact identity independent of revision-local provenance IDs."""

    predicate_id: int
    arguments: tuple[GroundTerm, ...]
    negative: bool
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.predicate_id, "delta fact predicate_id")
        arguments = tuple(self.arguments)
        if not all(isinstance(value, (IndividualTerm, DataConstant)) for value in arguments):
            raise TypeError("delta fact arguments cannot contain variables")
        if not isinstance(self.negative, bool):
            raise TypeError("delta fact negative flag must be bool")
        object.__setattr__(self, "arguments", arguments)


@dataclass(frozen=True, slots=True)
class DLClause(CanonicalRecord):
    clause_id: int
    body: tuple[Atom, ...]
    head: tuple[Atom, ...]
    provenance_ids: tuple[int, ...]
    join_order: tuple[int, ...]
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.clause_id, "clause_id")
        body = tuple(self.body)
        head = tuple(self.head)
        if not all(isinstance(value, Atom) for value in body + head):
            raise TypeError("clause body/head must contain Atom values")
        if tuple(value.canonical_bytes() for value in body) != tuple(
            sorted(value.canonical_bytes() for value in body)
        ) or len(set(body)) != len(body):
            raise ValueError("clause body atoms must be canonically sorted and unique")
        if tuple(value.canonical_bytes() for value in head) != tuple(
            sorted(value.canonical_bytes() for value in head)
        ) or len(set(head)) != len(head):
            raise ValueError("clause head atoms must be canonically sorted and unique")
        provenance = _sorted_u32(self.provenance_ids, "clause provenance")
        if not provenance:
            raise ValueError("clauses require provenance")
        join_order = tuple(self.join_order)
        for value in join_order:
            _u32(value, "join-order index")
        if tuple(sorted(join_order)) != tuple(range(len(body))):
            raise ValueError("join_order must be a permutation of the canonical body")
        object.__setattr__(self, "body", body)
        object.__setattr__(self, "head", head)
        object.__setattr__(self, "provenance_ids", provenance)
        object.__setattr__(self, "join_order", join_order)

    def identity_payload(self) -> dict[str, object]:
        payload = self.to_payload()
        payload.pop("clause_id")
        payload.pop("provenance_ids")
        return payload


@dataclass(frozen=True, slots=True)
class GroundDisjunctionIR(CanonicalRecord):
    disjunction_id: int
    disjuncts: tuple[GroundAtom, ...]
    provenance_ids: tuple[int, ...]
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.disjunction_id, "ground disjunction ID")
        disjuncts = tuple(self.disjuncts)
        if len(disjuncts) < 2 or not all(isinstance(value, GroundAtom) for value in disjuncts):
            raise ValueError("ground disjunctions require at least two ground atoms")
        keys = tuple(value.canonical_bytes() for value in disjuncts)
        if keys != tuple(sorted(keys)) or len(keys) != len(set(keys)):
            raise ValueError("ground disjuncts must be canonically sorted and unique")
        provenance = _sorted_u32(self.provenance_ids, "ground disjunction provenance")
        if not provenance:
            raise ValueError("ground disjunctions require provenance")
        object.__setattr__(self, "disjuncts", disjuncts)
        object.__setattr__(self, "provenance_ids", provenance)


@dataclass(frozen=True, slots=True, order=True)
class ProvenanceEntry(CanonicalRecord):
    provenance_id: int
    source_sha256: tuple[str, ...]
    generated: bool = False
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.provenance_id, "provenance_id")
        values = tuple(sorted(set(self.source_sha256)))
        if not values or any(_SHA256.fullmatch(value) is None for value in values):
            raise ValueError("source_sha256 must contain lowercase SHA-256 digests")
        if not isinstance(self.generated, bool):
            raise TypeError("generated must be bool")
        object.__setattr__(self, "source_sha256", values)


@dataclass(frozen=True, slots=True)
class ProvenanceTable(CanonicalRecord):
    entries: tuple[ProvenanceEntry, ...]
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        entries = tuple(self.entries)
        if not all(isinstance(value, ProvenanceEntry) for value in entries):
            raise TypeError("provenance entries must contain ProvenanceEntry")
        if tuple(value.provenance_id for value in entries) != tuple(range(len(entries))):
            raise ValueError("provenance IDs must be dense and ordered")
        keys = tuple((value.source_sha256, value.generated) for value in entries)
        if keys != tuple(sorted(keys)) or len(keys) != len(set(keys)):
            raise ValueError("provenance entries must be uniquely sorted")
        object.__setattr__(self, "entries", entries)


@dataclass(frozen=True, slots=True, order=True)
class RoleTransitionIR(CanonicalRecord):
    source_state: int
    target_state: int
    role_id: int | None
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.source_state, "automaton source state")
        _u32(self.target_state, "automaton target state")
        if self.role_id is not None:
            _u32(self.role_id, "automaton role_id")


@dataclass(frozen=True, slots=True)
class RoleAutomatonIR(CanonicalRecord):
    component_id: int
    state_count: int
    initial_state: int
    final_states: tuple[int, ...]
    transitions: tuple[RoleTransitionIR, ...]
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.component_id, "role component_id")
        _u32(self.state_count, "automaton state_count")
        _u32(self.initial_state, "automaton initial_state")
        if self.state_count < 1 or self.initial_state >= self.state_count:
            raise ValueError("automaton has invalid state bounds")
        finals = _sorted_u32(self.final_states, "automaton final state")
        if not finals or any(value >= self.state_count for value in finals):
            raise ValueError("automaton final states are invalid")
        transitions = tuple(self.transitions)
        if not all(isinstance(value, RoleTransitionIR) for value in transitions):
            raise TypeError("automaton transitions must contain RoleTransitionIR")
        keys = tuple(value.canonical_bytes() for value in transitions)
        if keys != tuple(sorted(keys)) or len(keys) != len(set(keys)):
            raise ValueError("automaton transitions must be sorted and unique")
        if any(
            value.source_state >= self.state_count or value.target_state >= self.state_count
            for value in transitions
        ):
            raise ValueError("automaton transition references an absent state")
        object.__setattr__(self, "final_states", finals)
        object.__setattr__(self, "transitions", transitions)


@dataclass(frozen=True, slots=True)
class RoleModelIR(CanonicalRecord):
    object_role_count: int
    data_property_count: int
    inverse_role_ids: tuple[int, ...]
    simple_inclusions: tuple[tuple[int, int], ...]
    data_inclusions: tuple[tuple[int, int], ...]
    complex_inclusions: tuple[tuple[tuple[int, ...], int], ...]
    non_simple_components: tuple[int, ...]
    automata: tuple[RoleAutomatonIR, ...]
    top_object_role_id: int
    bottom_object_role_id: int
    top_data_property_id: int
    bottom_data_property_id: int
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        for name in ("object_role_count", "data_property_count"):
            _u32(getattr(self, name), name)
        if self.object_role_count < 1 or self.data_property_count < 1:
            raise ValueError("role models must retain built-in roles")
        inverse = tuple(self.inverse_role_ids)
        for value in inverse:
            _u32(value, "inverse role ID")
        if len(inverse) != self.object_role_count or any(
            value >= self.object_role_count for value in inverse
        ):
            raise ValueError("inverse role map is incomplete or dangling")
        if any(inverse[inverse[index]] != index for index in range(len(inverse))):
            raise ValueError("inverse role map must be an involution")
        for name, limit in (
            ("top_object_role_id", self.object_role_count),
            ("bottom_object_role_id", self.object_role_count),
            ("top_data_property_id", self.data_property_count),
            ("bottom_data_property_id", self.data_property_count),
        ):
            value = getattr(self, name)
            _u32(value, name)
            if value >= limit:
                raise ValueError(f"{name} is dangling")
        _validate_pairs(self.simple_inclusions, self.object_role_count, "object role inclusion")
        _validate_pairs(self.data_inclusions, self.data_property_count, "data role inclusion")
        chains = tuple(self.complex_inclusions)
        if chains != tuple(sorted(set(chains))):
            raise ValueError("complex role inclusions must be sorted and unique")
        for chain, target in chains:
            _u32(target, "complex role target ID")
            for value in chain:
                _u32(value, "complex role chain ID")
            if (
                len(chain) < 2
                or target >= self.object_role_count
                or any(value >= self.object_role_count for value in chain)
            ):
                raise ValueError("complex role inclusion is malformed")
        components = _sorted_u32(self.non_simple_components, "non-simple component")
        automata = tuple(self.automata)
        if not all(isinstance(value, RoleAutomatonIR) for value in automata):
            raise TypeError("automata must contain RoleAutomatonIR")
        automaton_components = tuple(value.component_id for value in automata)
        if automaton_components != tuple(sorted(set(automaton_components))):
            raise ValueError("role automata must be uniquely sorted by component")
        if any(value >= self.object_role_count for value in automaton_components):
            raise ValueError("role automaton has a dangling component ID")
        if any(value >= self.object_role_count for value in components):
            raise ValueError("non-simple component ID is dangling")
        object.__setattr__(self, "inverse_role_ids", inverse)
        object.__setattr__(self, "simple_inclusions", tuple(self.simple_inclusions))
        object.__setattr__(self, "data_inclusions", tuple(self.data_inclusions))
        object.__setattr__(self, "complex_inclusions", chains)
        object.__setattr__(self, "non_simple_components", components)
        object.__setattr__(self, "automata", automata)


@dataclass(frozen=True, slots=True, order=True)
class LiteralIdentityIR(CanonicalRecord):
    source_literal_id: int
    data_identity_id: int
    comparison_key: str
    semantic_payload_json: str
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        _u32(self.source_literal_id, "source_literal_id")
        _u32(self.data_identity_id, "data_identity_id")
        if not isinstance(self.comparison_key, str) or not self.comparison_key:
            raise ValueError("comparison_key must be nonempty")
        if not isinstance(self.semantic_payload_json, str) or not self.semantic_payload_json:
            raise ValueError("semantic_payload_json must be a nonempty canonical JSON record")
        from pyhermit.datatypes import decode_literal_semantic_payload

        decode_literal_semantic_payload(self.semantic_payload_json.encode("utf-8"))


@dataclass(frozen=True, slots=True)
class DatatypeModelIR(CanonicalRecord):
    literal_identities: tuple[LiteralIdentityIR, ...] = ()
    datatype_definitions: tuple[tuple[int, int], ...] = ()
    unknown_datatype_ids: tuple[int, ...] = ()
    semantic_payload_json: str = _EMPTY_DATATYPE_SEMANTIC_JSON
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        identities = tuple(self.literal_identities)
        if not all(isinstance(value, LiteralIdentityIR) for value in identities):
            raise TypeError("literal_identities must contain LiteralIdentityIR")
        if tuple(value.source_literal_id for value in identities) != tuple(range(len(identities))):
            raise ValueError("literal identities must cover source literal IDs densely")
        definitions = tuple(self.datatype_definitions)
        if definitions != tuple(sorted(set(definitions))):
            raise ValueError("datatype definitions must be sorted and unique")
        for datatype_id, range_id in definitions:
            _u32(datatype_id, "datatype definition ID")
            _u32(range_id, "datatype definition range ID")
        unknown = _sorted_u32(self.unknown_datatype_ids, "unknown datatype ID")
        if not isinstance(self.semantic_payload_json, str) or not self.semantic_payload_json:
            raise ValueError("semantic_payload_json must be a nonempty canonical JSON record")
        from pyhermit.datatypes import decode_datatype_semantic_model

        decode_datatype_semantic_model(self.semantic_payload_json.encode("utf-8"))
        object.__setattr__(self, "literal_identities", identities)
        object.__setattr__(self, "datatype_definitions", definitions)
        object.__setattr__(self, "unknown_datatype_ids", unknown)


@dataclass(frozen=True, slots=True)
class Expressivity(CanonicalRecord):
    inverse_roles: bool = False
    nominals: bool = False
    datatypes: bool = False
    unknown_datatypes: bool = False
    complex_roles: bool = False
    number_restrictions: bool = False
    keys: bool = False
    non_horn: bool = False
    bottom_properties: bool = False
    abox: bool = False
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        for value in fields(self):
            if value.name == "schema_version":
                continue
            if not isinstance(getattr(self, value.name), bool):
                raise TypeError(f"expressivity {value.name} must be bool")


@dataclass(frozen=True, slots=True)
class ClauseProgram(CanonicalRecord):
    symbols: SymbolTable
    predicates: PredicateRegistry
    clauses: tuple[DLClause, ...]
    positive_facts: tuple[GroundAtom, ...]
    negative_facts: tuple[GroundAtom, ...]
    ground_disjunctions: tuple[GroundDisjunctionIR, ...]
    role_model: RoleModelIR
    datatype_model: DatatypeModelIR
    expressivity: Expressivity
    provenance: ProvenanceTable
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        if not isinstance(self.symbols, SymbolTable):
            raise TypeError("symbols must be SymbolTable")
        if not isinstance(self.predicates, PredicateRegistry):
            raise TypeError("predicates must be PredicateRegistry")
        if self.symbols.predicates is not self.predicates:
            raise ValueError("symbol table and program must share one predicate registry")
        if not isinstance(self.role_model, RoleModelIR):
            raise TypeError("role_model must be RoleModelIR")
        if not isinstance(self.datatype_model, DatatypeModelIR):
            raise TypeError("datatype_model must be DatatypeModelIR")
        if not isinstance(self.expressivity, Expressivity):
            raise TypeError("expressivity must be Expressivity")
        if not isinstance(self.provenance, ProvenanceTable):
            raise TypeError("provenance must be ProvenanceTable")
        clauses = tuple(self.clauses)
        positives = tuple(self.positive_facts)
        negatives = tuple(self.negative_facts)
        disjunctions = tuple(self.ground_disjunctions)
        if tuple(value.clause_id for value in clauses) != tuple(range(len(clauses))):
            raise ValueError("clause IDs must be dense and ordered")
        if tuple(value.disjunction_id for value in disjunctions) != tuple(range(len(disjunctions))):
            raise ValueError("ground disjunction IDs must be dense and ordered")
        _validate_program(self.predicates, clauses, positives, negatives, disjunctions)
        _validate_cross_references(
            self.symbols,
            self.predicates,
            clauses,
            positives,
            negatives,
            disjunctions,
            self.role_model,
            self.datatype_model,
            self.expressivity,
            self.provenance,
        )
        object.__setattr__(self, "clauses", clauses)
        object.__setattr__(self, "positive_facts", positives)
        object.__setattr__(self, "negative_facts", negatives)
        object.__setattr__(self, "ground_disjunctions", disjunctions)

    def canonical_json(self) -> str:
        return _canonical_json(self.to_payload())

    @classmethod
    def from_canonical_json(cls, encoded: str) -> ClauseProgram:
        if not isinstance(encoded, str):
            raise TypeError("encoded clause program must be str")
        try:
            payload: object = json.loads(encoded)
        except json.JSONDecodeError as error:
            raise ValueError("invalid clause-program JSON") from error
        value = _decode_record(payload)
        if not isinstance(value, cls):
            raise ValueError("canonical JSON does not contain a ClauseProgram")
        if value.canonical_json() != encoded:
            raise ValueError("clause-program JSON is not canonical")
        return value


@dataclass(frozen=True, slots=True)
class CompiledQuery(CanonicalRecord):
    permanent_program_sha256: str
    query_hash: str
    first_local_predicate_id: int
    first_local_symbols: tuple[tuple[str, int], ...]
    requires_rebuild: bool
    program: ClauseProgram | None
    reason: str | None = None
    interpretation: tuple[str, ...] = ()
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        for value, name in (
            (self.permanent_program_sha256, "permanent_program_sha256"),
            (self.query_hash, "query_hash"),
        ):
            if not isinstance(value, str) or _SHA256.fullmatch(value) is None:
                raise ValueError(f"{name} must be a lowercase SHA-256 digest")
        _u32(self.first_local_predicate_id, "first_local_predicate_id")
        symbols = tuple(self.first_local_symbols)
        if symbols != tuple(sorted(symbols)) or len({kind for kind, _count in symbols}) != len(
            symbols
        ):
            raise ValueError("first_local_symbols must be uniquely sorted by domain")
        expected_domains = tuple(sorted(value.value for value in SymbolKind))
        if tuple(kind for kind, _identifier in symbols) != expected_domains:
            raise ValueError("first_local_symbols must contain exactly every symbol domain")
        for kind, identifier in symbols:
            SymbolKind(kind)
            _u32(identifier, "first local symbol identifier")
        if not isinstance(self.requires_rebuild, bool):
            raise TypeError("requires_rebuild must be bool")
        if self.program is not None and not isinstance(self.program, ClauseProgram):
            raise TypeError("program must be ClauseProgram or None")
        if not self.requires_rebuild and self.program is None:
            raise ValueError("incremental query compilation requires a program")
        if self.requires_rebuild and self.program is not None:
            raise ValueError("rebuild-required query compilation cannot carry an overlay program")
        if self.program is not None:
            if self.first_local_predicate_id > len(self.program.predicates.predicates):
                raise ValueError("first_local_predicate_id exceeds the overlay predicate domain")
            for kind_text, cutoff in symbols:
                domain = self.program.symbols.domain(SymbolKind(kind_text))
                if cutoff > len(domain.values):
                    raise ValueError("first local symbol boundary exceeds its overlay domain")
                if any(value.query_local for value in domain.values[:cutoff]) or any(
                    not value.query_local for value in domain.values[cutoff:]
                ):
                    raise ValueError("query-local symbol flags do not match their domain boundary")
        if self.reason is not None and (not isinstance(self.reason, str) or not self.reason):
            raise ValueError("reason must be a nonempty string or None")
        interpretation = tuple(self.interpretation)
        if not all(isinstance(value, str) and value for value in interpretation):
            raise TypeError("query interpretation must contain nonempty strings")
        object.__setattr__(self, "first_local_symbols", symbols)
        object.__setattr__(self, "interpretation", interpretation)

    def canonical_json(self) -> str:
        return _canonical_json(self.to_payload())

    @classmethod
    def from_canonical_json(cls, encoded: str) -> CompiledQuery:
        value = _decode_canonical_text(encoded)
        if not isinstance(value, cls):
            raise ValueError("canonical JSON does not contain a CompiledQuery")
        if value.canonical_json() != encoded:
            raise ValueError("compiled-query JSON is not canonical")
        return value


@dataclass(frozen=True, slots=True)
class CompiledDelta(CanonicalRecord):
    base_program_sha256: str
    result_program_sha256: str
    compatibility: DeltaCompatibility
    addition_sha256: tuple[str, ...]
    removal_sha256: tuple[str, ...]
    fact_additions: tuple[DeltaFactIR, ...] = ()
    fact_removals: tuple[DeltaFactIR, ...] = ()
    reasons: tuple[str, ...] = ()
    schema_version: int = COMPILED_IR_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _validate_schema(self.schema_version)
        for value, name in (
            (self.base_program_sha256, "base_program_sha256"),
            (self.result_program_sha256, "result_program_sha256"),
        ):
            if not isinstance(value, str) or _SHA256.fullmatch(value) is None:
                raise ValueError(f"{name} must be a lowercase SHA-256 digest")
        if not isinstance(self.compatibility, DeltaCompatibility):
            raise TypeError("compatibility must be DeltaCompatibility")
        additions = _digests(self.addition_sha256, "addition_sha256")
        removals = _digests(self.removal_sha256, "removal_sha256")
        fact_additions = tuple(self.fact_additions)
        fact_removals = tuple(self.fact_removals)
        for values, name in (
            (fact_additions, "fact additions"),
            (fact_removals, "fact removals"),
        ):
            if not all(isinstance(value, DeltaFactIR) for value in values):
                raise TypeError(f"{name} must contain DeltaFactIR values")
            encoded = tuple(value.canonical_bytes() for value in values)
            if encoded != tuple(sorted(set(encoded))):
                raise ValueError(f"{name} must be canonically sorted and unique")
        if set(fact_additions).intersection(fact_removals):
            raise ValueError("one fact identity cannot be both added and removed")
        if self.compatibility is not DeltaCompatibility.ASSERTION_ONLY and (
            fact_additions or fact_removals
        ):
            raise ValueError("only assertion-compatible deltas can carry applicable fact rows")
        reasons = tuple(sorted(set(self.reasons)))
        if any(not isinstance(value, str) or not value for value in reasons):
            raise ValueError("delta reasons must be nonempty strings")
        object.__setattr__(self, "addition_sha256", additions)
        object.__setattr__(self, "removal_sha256", removals)
        object.__setattr__(self, "fact_additions", fact_additions)
        object.__setattr__(self, "fact_removals", fact_removals)
        object.__setattr__(self, "reasons", reasons)

    def canonical_json(self) -> str:
        return _canonical_json(self.to_payload())

    @classmethod
    def from_canonical_json(cls, encoded: str) -> CompiledDelta:
        value = _decode_canonical_text(encoded)
        if not isinstance(value, cls):
            raise ValueError("canonical JSON does not contain a CompiledDelta")
        if value.canonical_json() != encoded:
            raise ValueError("compiled-delta JSON is not canonical")
        return value


@dataclass(frozen=True, slots=True)
class CompilationLimits:
    max_symbols_per_domain: int = 4_000_000_000
    max_predicates: int = 4_000_000_000
    max_clauses: int = 4_000_000_000
    max_atoms: int = 4_000_000_000

    def __post_init__(self) -> None:
        for value in fields(self):
            observed = getattr(self, value.name)
            if isinstance(observed, bool) or not isinstance(observed, int) or observed < 1:
                raise ValueError(f"{value.name} must be a positive integer")
            if observed > U32_MAX:
                raise ValueError(f"{value.name} cannot exceed the u32 wire maximum")


def _validate_program(
    registry: PredicateRegistry,
    clauses: tuple[DLClause, ...],
    positives: tuple[GroundAtom, ...],
    negatives: tuple[GroundAtom, ...],
    disjunctions: tuple[GroundDisjunctionIR, ...],
) -> None:
    clause_keys = tuple(_canonical_json(value.identity_payload()) for value in clauses)
    if clause_keys != tuple(sorted(clause_keys)) or len(clause_keys) != len(set(clause_keys)):
        raise ValueError("clauses must be uniquely sorted by semantic identity")
    for clause in clauses:
        for atom in clause.body + clause.head:
            _validate_atom(atom, registry)
        first_occurrence: list[int] = []
        variable_sorts: dict[int, TermSort] = {}
        for atom in clause.body + clause.head:
            for argument in atom.arguments:
                if not isinstance(argument, Variable):
                    continue
                known_sort = variable_sorts.get(argument.index)
                if known_sort is not None and known_sort is not argument.sort:
                    raise ValueError("one variable ID cannot have both object and data sorts")
                if known_sort is None:
                    variable_sorts[argument.index] = argument.sort
                    first_occurrence.append(argument.index)
        if first_occurrence != list(range(len(first_occurrence))):
            raise ValueError("clause variables must follow canonical first-occurrence numbering")
        body_variables = {
            (argument.index, argument.sort)
            for atom in clause.body
            for argument in atom.arguments
            if isinstance(argument, Variable)
            and registry.predicate(atom.predicate_id).kind is not PredicateKind.ORDERING_GUARD
        }
        head_variables = {
            (argument.index, argument.sort)
            for atom in clause.head
            for argument in atom.arguments
            if isinstance(argument, Variable)
        }
        if not head_variables <= body_variables:
            raise ValueError("head variables must be range-restricted by the body")
        if set(clause.body).intersection(clause.head):
            raise ValueError("tautological clauses must be removed")
        for atom in clause.head:
            if registry.predicate(atom.predicate_id).kind is PredicateKind.ORDERING_GUARD:
                raise ValueError("ordering guards cannot occur in clause heads")
    for collection, negative in ((positives, False), (negatives, True)):
        keys = tuple(value.canonical_bytes() for value in collection)
        if keys != tuple(sorted(keys)) or len(keys) != len(set(keys)):
            raise ValueError("ground fact collections must be sorted and unique")
        for fact in collection:
            _validate_ground_atom(fact, registry)
            predicate_is_negative = (
                registry.predicate(fact.predicate_id).kind in _NEGATIVE_FACT_KINDS
            )
            if predicate_is_negative is not negative:
                raise ValueError("ground fact is stored in the wrong polarity partition")
    if set(positives).intersection(negatives):
        raise ValueError("a ground fact cannot be stored as both positive and negative")
    for disjunction in disjunctions:
        for fact in disjunction.disjuncts:
            _validate_ground_atom(fact, registry)


def _validate_cross_references(
    symbols: SymbolTable,
    registry: PredicateRegistry,
    clauses: tuple[DLClause, ...],
    positives: tuple[GroundAtom, ...],
    negatives: tuple[GroundAtom, ...],
    disjunctions: tuple[GroundDisjunctionIR, ...],
    roles: RoleModelIR,
    datatypes: DatatypeModelIR,
    expressivity: Expressivity,
    provenance: ProvenanceTable,
) -> None:
    class_count = len(symbols.domain(SymbolKind.CLASS_EXPRESSION).values)
    data_range_count = len(symbols.domain(SymbolKind.DATA_RANGE).values)
    individual_count = len(symbols.domain(SymbolKind.INDIVIDUAL).values)
    literal_count = len(symbols.domain(SymbolKind.SOURCE_LITERAL).values)
    data_value_count = len(symbols.domain(SymbolKind.DATA_VALUE).values)
    for predicate in registry.predicates:
        if predicate.kind in {
            PredicateKind.CONCEPT,
            PredicateKind.NEGATED_CONCEPT,
            PredicateKind.NOMINAL,
            PredicateKind.NEGATED_NOMINAL,
        } and (predicate.symbol_id is None or predicate.symbol_id >= class_count):
            raise ValueError("concept/nominal predicate has a dangling class-expression ID")
        if predicate.kind in {
            PredicateKind.DATA_RANGE,
            PredicateKind.NEGATED_DATA_RANGE,
        } and (predicate.symbol_id is None or predicate.symbol_id >= data_range_count):
            raise ValueError("data-range predicate has a dangling data-range ID")
        if predicate.kind in {
            PredicateKind.OBJECT_ROLE,
            PredicateKind.NEGATED_OBJECT_ROLE,
            PredicateKind.AT_LEAST_OBJECT,
            PredicateKind.ANNOTATED_EQUALITY,
        } and (predicate.role_id is None or predicate.role_id >= roles.object_role_count):
            raise ValueError("object-role predicate has a dangling role ID")
        if predicate.kind in {
            PredicateKind.DATA_ROLE,
            PredicateKind.NEGATED_DATA_ROLE,
            PredicateKind.AT_LEAST_DATA,
        } and (predicate.role_id is None or predicate.role_id >= roles.data_property_count):
            raise ValueError("data-role predicate has a dangling property ID")
        if predicate.kind in {PredicateKind.NOMINAL, PredicateKind.NEGATED_NOMINAL} and any(
            value >= individual_count for value in predicate.annotation
        ):
            raise ValueError("nominal predicate has a dangling individual ID")
        if predicate.kind is PredicateKind.AT_LEAST_DATA and any(
            value >= roles.data_property_count for value in predicate.annotation
        ):
            raise ValueError("data at-least predicate has a dangling property tuple")
    if len(datatypes.literal_identities) != literal_count:
        raise ValueError("datatype model does not cover the source literal domain")
    from pyhermit.datatypes import decode_datatype_semantic_model

    semantic_datatypes = decode_datatype_semantic_model(
        datatypes.semantic_payload_json.encode("utf-8")
    )
    if len(semantic_datatypes.data_ranges) != data_range_count:
        raise ValueError("datatype semantic payload does not cover the dense data-range domain")
    provenance_count = len(provenance.entries)

    def validate_term_reference(argument: Term) -> None:
        if isinstance(argument, IndividualTerm) and argument.individual_id >= individual_count:
            raise ValueError("compiled atom has a dangling individual ID")
        if isinstance(argument, DataConstant) and (
            argument.source_literal_id >= literal_count
            or argument.data_identity_id >= data_value_count
        ):
            raise ValueError("compiled atom has a dangling literal/data identity ID")
        if isinstance(argument, DataConstant) and (
            datatypes.literal_identities[argument.source_literal_id].data_identity_id
            != argument.data_identity_id
        ):
            raise ValueError("compiled data constant mismatches its source literal identity")

    for clause in clauses:
        _validate_provenance_ids(clause.provenance_ids, provenance_count)
        for atom in clause.body + clause.head:
            for argument in atom.arguments:
                validate_term_reference(argument)
    for fact in positives + negatives:
        _validate_provenance_ids(fact.provenance_ids, provenance_count)
        for argument in fact.arguments:
            validate_term_reference(argument)
    for disjunction in disjunctions:
        _validate_provenance_ids(disjunction.provenance_ids, provenance_count)
        for fact in disjunction.disjuncts:
            _validate_provenance_ids(fact.provenance_ids, provenance_count)
            if fact.provenance_ids != disjunction.provenance_ids:
                raise ValueError("ground disjunct provenance must match its disjunction")
            for argument in fact.arguments:
                validate_term_reference(argument)
    if any(value.data_identity_id >= data_value_count for value in datatypes.literal_identities):
        raise ValueError("datatype model has a dangling data identity ID")
    if any(
        left >= data_range_count or right >= data_range_count
        for left, right in datatypes.datatype_definitions
    ):
        raise ValueError("datatype model has a dangling datatype-definition ID")
    if any(value >= data_range_count for value in datatypes.unknown_datatype_ids):
        raise ValueError("datatype model has a dangling unknown-datatype ID")
    for automaton in roles.automata:
        if automaton.component_id >= roles.object_role_count:
            raise ValueError("role automaton has a dangling component ID")
        if any(
            transition.role_id is not None and transition.role_id >= roles.object_role_count
            for transition in automaton.transitions
        ):
            raise ValueError("role automaton transition has a dangling role ID")
    automata_by_component = {value.component_id: value for value in roles.automata}
    for predicate in registry.predicates:
        if predicate.kind is not PredicateKind.AUTOMATON_STATE:
            continue
        component_id, state_id = predicate.annotation
        referenced_automaton = automata_by_component.get(component_id)
        if referenced_automaton is None or state_id >= referenced_automaton.state_count:
            raise ValueError("automaton-state predicate references an absent role automaton state")
    observed_non_horn = bool(disjunctions) or any(len(value.head) > 1 for value in clauses)
    observed_nominals = any(
        value.kind in {PredicateKind.NOMINAL, PredicateKind.NEGATED_NOMINAL}
        for value in registry.predicates
    )
    observed_datatypes = bool(
        datatypes.literal_identities
        or datatypes.datatype_definitions
        or datatypes.unknown_datatype_ids
    ) or any(
        value.kind
        in {
            PredicateKind.DATA_RANGE,
            PredicateKind.NEGATED_DATA_RANGE,
            PredicateKind.AT_LEAST_DATA,
        }
        or (
            value.kind in {PredicateKind.DATA_ROLE, PredicateKind.NEGATED_DATA_ROLE}
            and value.role_id != roles.bottom_data_property_id
        )
        for value in registry.predicates
    )
    observed_complex_roles = bool(roles.complex_inclusions or roles.automata)
    observed_cardinality = any(
        value.kind
        in {
            PredicateKind.AT_LEAST_OBJECT,
            PredicateKind.AT_LEAST_DATA,
            PredicateKind.ANNOTATED_EQUALITY,
        }
        for value in registry.predicates
    )
    observed_keys = any(
        any(
            registry.predicate(atom.predicate_id).kind is PredicateKind.NAMED_INDIVIDUAL
            for atom in clause.body
        )
        and any(
            registry.predicate(atom.predicate_id).kind is PredicateKind.ORDERING_GUARD
            for atom in clause.body
        )
        and any(
            registry.predicate(atom.predicate_id).kind is PredicateKind.EQUALITY
            for atom in clause.head
        )
        for clause in clauses
    )
    if observed_non_horn and not expressivity.non_horn:
        raise ValueError("expressivity incorrectly marks a non-Horn program as Horn")
    if observed_nominals and not expressivity.nominals:
        raise ValueError("expressivity omits compiled nominals")
    if observed_datatypes and not expressivity.datatypes:
        raise ValueError("expressivity omits compiled datatype constraints")
    if datatypes.unknown_datatype_ids and not expressivity.unknown_datatypes:
        raise ValueError("expressivity omits unknown datatype restrictions")
    if observed_complex_roles and not expressivity.complex_roles:
        raise ValueError("expressivity omits complex role clauses or automata")
    if observed_cardinality and not expressivity.number_restrictions:
        raise ValueError("expressivity omits compiled number restrictions")
    if observed_keys and not expressivity.keys:
        raise ValueError("expressivity omits compiled keys")


def _validate_provenance_ids(values: tuple[int, ...], count: int) -> None:
    if any(value >= count for value in values):
        raise ValueError("compiled rule has a dangling provenance ID")


def _validate_atom(atom: Atom, registry: PredicateRegistry) -> None:
    predicate = registry.predicate(atom.predicate_id)
    if len(atom.arguments) != len(predicate.argument_sorts):
        raise ValueError("atom arity does not match its predicate")
    if tuple(term_sort(value) for value in atom.arguments) != predicate.argument_sorts:
        raise ValueError("atom argument sorts do not match its predicate")
    if predicate.kind in {PredicateKind.EQUALITY, PredicateKind.INEQUALITY} and (
        _term_order_key(atom.arguments[1]) < _term_order_key(atom.arguments[0])
    ):
        raise ValueError("equality/inequality arguments must be canonically ordered")
    if predicate.kind is PredicateKind.ORDERING_GUARD and (
        _term_order_key(atom.arguments[0]) >= _term_order_key(atom.arguments[1])
    ):
        raise ValueError("ordering-guard arguments must be in strict canonical order")
    if predicate.kind is PredicateKind.ANNOTATED_EQUALITY and (
        _term_order_key(atom.arguments[1]) < _term_order_key(atom.arguments[0])
    ):
        raise ValueError("annotated-equality pair arguments must be canonically ordered")


def _validate_ground_atom(atom: GroundAtom, registry: PredicateRegistry) -> None:
    predicate = registry.predicate(atom.predicate_id)
    if len(atom.arguments) != len(predicate.argument_sorts):
        raise ValueError("ground atom arity does not match its predicate")
    if tuple(term_sort(value) for value in atom.arguments) != predicate.argument_sorts:
        raise ValueError("ground atom argument sorts do not match its predicate")
    if predicate.kind in {PredicateKind.EQUALITY, PredicateKind.INEQUALITY} and (
        _term_order_key(atom.arguments[1]) < _term_order_key(atom.arguments[0])
    ):
        raise ValueError("ground equality/inequality arguments must be canonically ordered")
    if predicate.kind in {
        PredicateKind.AT_LEAST_OBJECT,
        PredicateKind.AT_LEAST_DATA,
        PredicateKind.AUTOMATON_STATE,
        PredicateKind.DISJOINT_GUARD,
        PredicateKind.ORDERING_GUARD,
    }:
        raise ValueError("internal strategy predicates cannot be public ground facts")


def _record_payload(value: CanonicalRecord) -> dict[str, object]:
    payload: dict[str, object] = {"type": type(value).__name__}
    for field in fields(value):  # type: ignore[arg-type]
        payload[field.name] = _payload_value(getattr(value, field.name))
    return payload


def _payload_value(value: object) -> object:
    if isinstance(value, _StringEnum):
        return value.value
    if isinstance(value, CanonicalRecord):
        return value.to_payload()
    if isinstance(value, tuple):
        return [_payload_value(item) for item in value]
    if isinstance(value, (str, int, bool)) or value is None:
        return value
    raise TypeError(f"unsupported canonical payload value {type(value).__name__}")


def _validate_schema(value: int) -> None:
    if value != COMPILED_IR_SCHEMA_VERSION:
        raise ValueError(f"compiled IR schema must be {COMPILED_IR_SCHEMA_VERSION}, got {value}")


def _sorted_u32(values: tuple[int, ...], name: str) -> tuple[int, ...]:
    result = tuple(values)
    for value in result:
        _u32(value, name)
    if result != tuple(sorted(set(result))):
        raise ValueError(f"{name} values must be sorted and unique")
    return result


def _digests(values: tuple[str, ...], name: str) -> tuple[str, ...]:
    result = tuple(sorted(set(values)))
    if any(not isinstance(value, str) or _SHA256.fullmatch(value) is None for value in result):
        raise ValueError(f"{name} must contain lowercase SHA-256 digests")
    return result


def _validate_pairs(values: tuple[tuple[int, int], ...], limit: int, name: str) -> None:
    pairs = tuple(values)
    if pairs != tuple(sorted(set(pairs))):
        raise ValueError(f"{name} values must be sorted and unique")
    for left, right in pairs:
        _u32(left, f"{name} left ID")
        _u32(right, f"{name} right ID")
        if left >= limit or right >= limit:
            raise ValueError(f"{name} contains a dangling ID")


def _decode_record(value: object) -> CanonicalRecord:
    payload = _mapping(value)
    record_type = _text(payload.pop("type"), "type")
    schema = _integer(payload.pop("schema_version"), "schema_version")
    if record_type == "Variable":
        _exact(payload, {"index", "sort"}, record_type)
        return Variable(
            _integer(payload["index"], "index"),
            TermSort(_text(payload["sort"], "sort")),
            schema,
        )
    if record_type == "IndividualTerm":
        _exact(payload, {"individual_id"}, record_type)
        return IndividualTerm(_integer(payload["individual_id"], "individual_id"), schema)
    if record_type == "DataConstant":
        _exact(payload, {"data_identity_id", "source_literal_id"}, record_type)
        return DataConstant(
            _integer(payload["source_literal_id"], "source_literal_id"),
            _integer(payload["data_identity_id"], "data_identity_id"),
            schema,
        )
    if record_type == "SymbolValue":
        _exact(
            payload,
            {"display", "generated", "identifier", "key_hex", "query_local"},
            record_type,
        )
        return SymbolValue(
            _integer(payload["identifier"], "identifier"),
            _text(payload["key_hex"], "key_hex"),
            _text(payload["display"], "display"),
            _boolean(payload["generated"], "generated"),
            _boolean(payload["query_local"], "query_local"),
            schema,
        )
    if record_type == "SymbolDomain":
        _exact(payload, {"kind", "values"}, record_type)
        values = _records(payload["values"], SymbolValue, "values")
        return SymbolDomain(
            SymbolKind(_text(payload["kind"], "kind")),
            values,
            schema,
        )
    if record_type == "SymbolTable":
        _exact(payload, {"domains", "predicates"}, record_type)
        domains = _records(payload["domains"], SymbolDomain, "domains")
        predicates_value = payload["predicates"]
        predicates = None
        if predicates_value is not None:
            decoded = _decode_record(predicates_value)
            if not isinstance(decoded, PredicateRegistry):
                raise TypeError("predicates must decode to PredicateRegistry")
            predicates = decoded
        return SymbolTable(domains, predicates, schema)
    if record_type == "Predicate":
        _exact(
            payload,
            {
                "annotation",
                "argument_sorts",
                "cardinality",
                "filler_predicate_id",
                "internal_key",
                "kind",
                "predicate_id",
                "role_id",
                "symbol_id",
            },
            record_type,
        )
        return Predicate(
            predicate_id=_integer(payload["predicate_id"], "predicate_id"),
            kind=PredicateKind(_text(payload["kind"], "kind")),
            argument_sorts=tuple(
                TermSort(_text(item, "argument sort"))
                for item in _sequence(payload["argument_sorts"], "argument_sorts")
            ),
            symbol_id=_optional_integer(payload["symbol_id"], "symbol_id"),
            role_id=_optional_integer(payload["role_id"], "role_id"),
            cardinality=_optional_integer(payload["cardinality"], "cardinality"),
            filler_predicate_id=_optional_integer(
                payload["filler_predicate_id"],
                "filler_predicate_id",
            ),
            annotation=tuple(
                _integer(item, "annotation")
                for item in _sequence(payload["annotation"], "annotation")
            ),
            internal_key=_optional_text(payload["internal_key"], "internal_key"),
            schema_version=schema,
        )
    if record_type == "PredicateRegistry":
        _exact(payload, {"predicates"}, record_type)
        return PredicateRegistry(
            _records(payload["predicates"], Predicate, "predicates"),
            schema,
        )
    if record_type == "Atom":
        _exact(payload, {"arguments", "predicate_id"}, record_type)
        arguments = _terms(payload["arguments"], ground=False)
        return Atom(
            _integer(payload["predicate_id"], "predicate_id"),
            arguments,
            schema,
        )
    if record_type == "GroundAtom":
        _exact(payload, {"arguments", "predicate_id", "provenance_ids"}, record_type)
        arguments = _terms(payload["arguments"], ground=True)
        return GroundAtom(
            _integer(payload["predicate_id"], "predicate_id"),
            cast(tuple[GroundTerm, ...], arguments),
            _integers(payload["provenance_ids"], "provenance_ids"),
            schema,
        )
    if record_type == "DeltaFactIR":
        _exact(payload, {"arguments", "negative", "predicate_id"}, record_type)
        arguments = _terms(payload["arguments"], ground=True)
        return DeltaFactIR(
            _integer(payload["predicate_id"], "predicate_id"),
            cast(tuple[GroundTerm, ...], arguments),
            _boolean(payload["negative"], "negative"),
            schema,
        )
    if record_type == "DLClause":
        _exact(
            payload,
            {"body", "clause_id", "head", "join_order", "provenance_ids"},
            record_type,
        )
        return DLClause(
            _integer(payload["clause_id"], "clause_id"),
            _records(payload["body"], Atom, "body"),
            _records(payload["head"], Atom, "head"),
            _integers(payload["provenance_ids"], "provenance_ids"),
            _integers(payload["join_order"], "join_order"),
            schema,
        )
    if record_type == "GroundDisjunctionIR":
        _exact(
            payload,
            {"disjunction_id", "disjuncts", "provenance_ids"},
            record_type,
        )
        return GroundDisjunctionIR(
            _integer(payload["disjunction_id"], "disjunction_id"),
            _records(payload["disjuncts"], GroundAtom, "disjuncts"),
            _integers(payload["provenance_ids"], "provenance_ids"),
            schema,
        )
    if record_type == "ProvenanceEntry":
        _exact(payload, {"generated", "provenance_id", "source_sha256"}, record_type)
        return ProvenanceEntry(
            _integer(payload["provenance_id"], "provenance_id"),
            tuple(
                _text(item, "source_sha256")
                for item in _sequence(payload["source_sha256"], "source_sha256")
            ),
            _boolean(payload["generated"], "generated"),
            schema,
        )
    if record_type == "ProvenanceTable":
        _exact(payload, {"entries"}, record_type)
        return ProvenanceTable(
            _records(payload["entries"], ProvenanceEntry, "entries"),
            schema,
        )
    if record_type == "RoleTransitionIR":
        _exact(payload, {"role_id", "source_state", "target_state"}, record_type)
        return RoleTransitionIR(
            _integer(payload["source_state"], "source_state"),
            _integer(payload["target_state"], "target_state"),
            _optional_integer(payload["role_id"], "role_id"),
            schema,
        )
    if record_type == "RoleAutomatonIR":
        _exact(
            payload,
            {"component_id", "final_states", "initial_state", "state_count", "transitions"},
            record_type,
        )
        return RoleAutomatonIR(
            _integer(payload["component_id"], "component_id"),
            _integer(payload["state_count"], "state_count"),
            _integer(payload["initial_state"], "initial_state"),
            _integers(payload["final_states"], "final_states"),
            _records(payload["transitions"], RoleTransitionIR, "transitions"),
            schema,
        )
    if record_type == "RoleModelIR":
        return _decode_role_model(payload, schema)
    if record_type == "LiteralIdentityIR":
        _exact(
            payload,
            {
                "comparison_key",
                "data_identity_id",
                "semantic_payload_json",
                "source_literal_id",
            },
            record_type,
        )
        return LiteralIdentityIR(
            _integer(payload["source_literal_id"], "source_literal_id"),
            _integer(payload["data_identity_id"], "data_identity_id"),
            _text(payload["comparison_key"], "comparison_key"),
            _text(payload["semantic_payload_json"], "semantic_payload_json"),
            schema,
        )
    if record_type == "DatatypeModelIR":
        _exact(
            payload,
            {
                "datatype_definitions",
                "literal_identities",
                "semantic_payload_json",
                "unknown_datatype_ids",
            },
            record_type,
        )
        return DatatypeModelIR(
            _records(payload["literal_identities"], LiteralIdentityIR, "literal_identities"),
            _pairs(payload["datatype_definitions"], "datatype_definitions"),
            _integers(payload["unknown_datatype_ids"], "unknown_datatype_ids"),
            _text(payload["semantic_payload_json"], "semantic_payload_json"),
            schema_version=schema,
        )
    if record_type == "Expressivity":
        expected = {
            "abox",
            "bottom_properties",
            "complex_roles",
            "datatypes",
            "inverse_roles",
            "keys",
            "nominals",
            "non_horn",
            "number_restrictions",
            "unknown_datatypes",
        }
        _exact(payload, expected, record_type)
        return Expressivity(
            **{name: _boolean(payload[name], name) for name in expected},
            schema_version=schema,
        )
    if record_type == "CompiledQuery":
        expected = {
            "first_local_predicate_id",
            "first_local_symbols",
            "permanent_program_sha256",
            "program",
            "query_hash",
            "reason",
            "requires_rebuild",
            "interpretation",
        }
        _exact(payload, expected, record_type)
        program_value = payload["program"]
        program = (
            None
            if program_value is None
            else _typed_record(program_value, ClauseProgram, "program")
        )
        return CompiledQuery(
            _text(payload["permanent_program_sha256"], "permanent_program_sha256"),
            _text(payload["query_hash"], "query_hash"),
            _integer(payload["first_local_predicate_id"], "first_local_predicate_id"),
            _string_int_pairs(
                payload["first_local_symbols"],
                "first_local_symbols",
            ),
            _boolean(payload["requires_rebuild"], "requires_rebuild"),
            program,
            _optional_text(payload["reason"], "reason"),
            tuple(
                _text(value, "interpretation")
                for value in _sequence(payload["interpretation"], "interpretation")
            ),
            schema_version=schema,
        )
    if record_type == "CompiledDelta":
        expected = {
            "addition_sha256",
            "base_program_sha256",
            "compatibility",
            "fact_additions",
            "fact_removals",
            "reasons",
            "removal_sha256",
            "result_program_sha256",
        }
        _exact(payload, expected, record_type)
        return CompiledDelta(
            _text(payload["base_program_sha256"], "base_program_sha256"),
            _text(payload["result_program_sha256"], "result_program_sha256"),
            DeltaCompatibility(_text(payload["compatibility"], "compatibility")),
            tuple(
                _text(value, "addition_sha256")
                for value in _sequence(payload["addition_sha256"], "addition_sha256")
            ),
            tuple(
                _text(value, "removal_sha256")
                for value in _sequence(payload["removal_sha256"], "removal_sha256")
            ),
            _records(payload["fact_additions"], DeltaFactIR, "fact_additions"),
            _records(payload["fact_removals"], DeltaFactIR, "fact_removals"),
            tuple(_text(value, "reason") for value in _sequence(payload["reasons"], "reasons")),
            schema_version=schema,
        )
    if record_type == "ClauseProgram":
        return _decode_clause_program(payload, schema)
    raise ValueError(f"unknown canonical record type {record_type!r}")


def _decode_role_model(payload: dict[str, object], schema: int) -> RoleModelIR:
    expected = {
        "automata",
        "bottom_data_property_id",
        "bottom_object_role_id",
        "complex_inclusions",
        "data_inclusions",
        "data_property_count",
        "inverse_role_ids",
        "non_simple_components",
        "object_role_count",
        "simple_inclusions",
        "top_data_property_id",
        "top_object_role_id",
    }
    _exact(payload, expected, "RoleModelIR")
    complex_values: list[tuple[tuple[int, ...], int]] = []
    for value in _sequence(payload["complex_inclusions"], "complex_inclusions"):
        pair = _sequence(value, "complex inclusion")
        if len(pair) != 2:
            raise ValueError("complex inclusion must contain chain and target")
        complex_values.append(
            (
                _integers(pair[0], "complex chain"),
                _integer(pair[1], "complex target"),
            )
        )
    return RoleModelIR(
        object_role_count=_integer(payload["object_role_count"], "object_role_count"),
        data_property_count=_integer(payload["data_property_count"], "data_property_count"),
        inverse_role_ids=_integers(payload["inverse_role_ids"], "inverse_role_ids"),
        simple_inclusions=_pairs(payload["simple_inclusions"], "simple_inclusions"),
        data_inclusions=_pairs(payload["data_inclusions"], "data_inclusions"),
        complex_inclusions=tuple(complex_values),
        non_simple_components=_integers(
            payload["non_simple_components"],
            "non_simple_components",
        ),
        automata=_records(payload["automata"], RoleAutomatonIR, "automata"),
        top_object_role_id=_integer(payload["top_object_role_id"], "top_object_role_id"),
        bottom_object_role_id=_integer(
            payload["bottom_object_role_id"],
            "bottom_object_role_id",
        ),
        top_data_property_id=_integer(
            payload["top_data_property_id"],
            "top_data_property_id",
        ),
        bottom_data_property_id=_integer(
            payload["bottom_data_property_id"],
            "bottom_data_property_id",
        ),
        schema_version=schema,
    )


def _decode_clause_program(payload: dict[str, object], schema: int) -> ClauseProgram:
    expected = {
        "clauses",
        "datatype_model",
        "expressivity",
        "ground_disjunctions",
        "negative_facts",
        "positive_facts",
        "predicates",
        "provenance",
        "role_model",
        "symbols",
    }
    _exact(payload, expected, "ClauseProgram")
    symbols = _typed_record(payload["symbols"], SymbolTable, "symbols")
    predicates = _typed_record(payload["predicates"], PredicateRegistry, "predicates")
    if symbols.predicates is not None and symbols.predicates is not predicates:
        # The canonical tree necessarily decodes the repeated registry twice. Rebind the
        # symbol table to the authoritative program instance before relational validation.
        if symbols.predicates != predicates:
            raise ValueError("symbol/program predicate registries disagree")
        symbols = SymbolTable(symbols.domains, predicates, symbols.schema_version)
    return ClauseProgram(
        symbols=symbols,
        predicates=predicates,
        clauses=_records(payload["clauses"], DLClause, "clauses"),
        positive_facts=_records(payload["positive_facts"], GroundAtom, "positive_facts"),
        negative_facts=_records(payload["negative_facts"], GroundAtom, "negative_facts"),
        ground_disjunctions=_records(
            payload["ground_disjunctions"],
            GroundDisjunctionIR,
            "ground_disjunctions",
        ),
        role_model=_typed_record(payload["role_model"], RoleModelIR, "role_model"),
        datatype_model=_typed_record(
            payload["datatype_model"],
            DatatypeModelIR,
            "datatype_model",
        ),
        expressivity=_typed_record(payload["expressivity"], Expressivity, "expressivity"),
        provenance=_typed_record(payload["provenance"], ProvenanceTable, "provenance"),
        schema_version=schema,
    )


def _mapping(value: object) -> dict[str, object]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise TypeError("canonical record must be a JSON object with string keys")
    return dict(cast(dict[str, object], value))


def _decode_canonical_text(encoded: str) -> CanonicalRecord:
    if not isinstance(encoded, str):
        raise TypeError("canonical JSON must be str")
    try:
        payload: object = json.loads(encoded)
    except json.JSONDecodeError as error:
        raise ValueError("invalid canonical JSON") from error
    return _decode_record(payload)


def _sequence(value: object, name: str) -> list[object]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a JSON array")
    return cast(list[object], value)


def _text(value: object, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be str")
    return value


def _optional_text(value: object, name: str) -> str | None:
    return None if value is None else _text(value, name)


def _integer(value: object, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be int")
    return value


def _optional_integer(value: object, name: str) -> int | None:
    return None if value is None else _integer(value, name)


def _boolean(value: object, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be bool")
    return value


def _integers(value: object, name: str) -> tuple[int, ...]:
    return tuple(_integer(item, name) for item in _sequence(value, name))


def _pairs(value: object, name: str) -> tuple[tuple[int, int], ...]:
    result: list[tuple[int, int]] = []
    for item in _sequence(value, name):
        pair = _sequence(item, name)
        if len(pair) != 2:
            raise ValueError(f"{name} entries must contain two integers")
        result.append((_integer(pair[0], name), _integer(pair[1], name)))
    return tuple(result)


def _string_int_pairs(value: object, name: str) -> tuple[tuple[str, int], ...]:
    result: list[tuple[str, int]] = []
    for item in _sequence(value, name):
        pair = _sequence(item, name)
        if len(pair) != 2:
            raise ValueError(f"{name} entries must contain a string and integer")
        result.append((_text(pair[0], name), _integer(pair[1], name)))
    return tuple(result)


def _typed_record(
    value: object,
    expected: type[_RecordT],
    name: str,
) -> _RecordT:
    decoded = _decode_record(value)
    if not isinstance(decoded, expected):
        raise TypeError(f"{name} has the wrong canonical record type")
    return decoded


def _records(
    value: object,
    expected: type[_RecordT],
    name: str,
) -> tuple[_RecordT, ...]:
    return tuple(_typed_record(item, expected, name) for item in _sequence(value, name))


def _terms(value: object, *, ground: bool) -> tuple[Term, ...]:
    result: list[Term] = []
    for item in _sequence(value, "arguments"):
        decoded = _decode_record(item)
        if not isinstance(decoded, (Variable, IndividualTerm, DataConstant)):
            raise TypeError("argument does not decode to a Term")
        if ground and isinstance(decoded, Variable):
            raise ValueError("ground arguments cannot contain Variable")
        result.append(decoded)
    return tuple(result)


def _exact(payload: dict[str, object], expected: set[str], name: str) -> None:
    if set(payload) != expected:
        raise ValueError(f"{name} has unexpected canonical fields")


__all__ = [
    "Atom",
    "CanonicalRecord",
    "ClauseProgram",
    "CompilationLimits",
    "CompiledDelta",
    "CompiledQuery",
    "DLClause",
    "DataConstant",
    "DatatypeModelIR",
    "DeltaCompatibility",
    "DeltaFactIR",
    "Expressivity",
    "GroundAtom",
    "GroundDisjunctionIR",
    "GroundTerm",
    "IndividualTerm",
    "LiteralIdentityIR",
    "Predicate",
    "PredicateKind",
    "PredicateRegistry",
    "ProvenanceEntry",
    "ProvenanceTable",
    "RoleAutomatonIR",
    "RoleModelIR",
    "RoleTransitionIR",
    "SymbolDomain",
    "SymbolKind",
    "SymbolTable",
    "SymbolValue",
    "Term",
    "TermSort",
    "Variable",
    "term_sort",
]
