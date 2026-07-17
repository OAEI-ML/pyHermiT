"""Immutable backend-neutral records produced by deterministic normalization.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass, field
from enum import Enum
from typing import Protocol, TypeAlias, cast

import pyowl_core.model as owl

_SHA256 = re.compile(r"[0-9a-f]{64}\Z")
_GENERATED_DEFINITION_NAMESPACE = "urn:pyhermit:generated:v1:"
_GENERATED_DEFINITION_IRI = re.compile(
    re.escape(_GENERATED_DEFINITION_NAMESPACE)
    + r"(class|data):([0-9a-f]{64}):(positive|negative):([0-9a-f]{64})\Z"
)
NORMALIZATION_SCHEMA_VERSION = 1


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class Polarity(_StringEnum):
    POSITIVE = "positive"
    NEGATIVE = "negative"


class NormalizedFamily(_StringEnum):
    CLASS = "class"
    OBJECT_PROPERTY = "object_property"
    DATA_PROPERTY = "data_property"
    DATATYPE = "datatype"
    KEY = "key"
    ASSERTION = "assertion"


def _generated_definition_iri(
    namespace: str,
    kind: str,
    encoded_expression: bytes,
    polarity: Polarity,
) -> str:
    _validate_digest(namespace, "definition namespace")
    if kind not in {"class", "data"}:
        raise ValueError("definition kind must be class or data")
    if not isinstance(encoded_expression, bytes) or not encoded_expression:
        raise ValueError("definition expression bytes must be nonempty")
    if not isinstance(polarity, Polarity):
        raise TypeError("definition polarity must be Polarity")
    digest = hashlib.sha256(
        b"pyhermit:normalization-definition:v1\x00"
        + namespace.encode("ascii")
        + b"\x00"
        + kind.encode("ascii")
        + b"\x00"
        + polarity.value.encode("ascii")
        + b"\x00"
        + encoded_expression
    ).hexdigest()
    return f"{_GENERATED_DEFINITION_NAMESPACE}{kind}:{namespace}:{polarity.value}:{digest}"


def _query_definition_namespace(
    permanent_normalization_digest: str,
    query_hash: str,
) -> str:
    _validate_digest(permanent_normalization_digest, "permanent_normalization_digest")
    _validate_digest(query_hash, "query_hash")
    return hashlib.sha256(
        b"pyhermit:query-normalization-namespace:v1\x00"
        + bytes.fromhex(permanent_normalization_digest)
        + bytes.fromhex(query_hash)
    ).hexdigest()


class _AnnotatedAxiom(Protocol):
    annotations: owl.CanonicalSet[owl.Annotation]


class _HashWriter(Protocol):
    def update(self, data: bytes, /) -> object: ...


@dataclass(frozen=True, slots=True)
class DataRangeInclusion:
    """Private one-way data-range implication absent from OWL surface syntax."""

    sub_range: owl.DataRange
    super_range: owl.DataRange

    def __post_init__(self) -> None:
        if not isinstance(self.sub_range, owl.DATA_RANGE_TYPES):
            raise TypeError("sub_range must be a pyowl_core DataRange")
        if not isinstance(self.super_range, owl.DATA_RANGE_TYPES):
            raise TypeError("super_range must be a pyowl_core DataRange")

    def canonical_bytes(self) -> bytes:
        sub = self.sub_range.canonical_bytes()
        sup = self.super_range.canonical_bytes()
        return (
            b"pyhermit:normalized-data-inclusion:v1\x00"
            + len(sub).to_bytes(8, "big")
            + sub
            + len(sup).to_bytes(8, "big")
            + sup
        )


NormalizedStatement: TypeAlias = owl.AxiomNode | DataRangeInclusion


def statement_bytes(statement: NormalizedStatement) -> bytes:
    if isinstance(statement, (owl.AxiomNode, DataRangeInclusion)):
        return statement.canonical_bytes()
    raise TypeError("statement must be an OWL axiom or DataRangeInclusion")


def _statement_matches_family(
    family: NormalizedFamily,
    statement: NormalizedStatement,
) -> bool:
    constructor = type(statement)
    if family is NormalizedFamily.CLASS:
        return constructor in {owl.SubClassOf, owl.DisjointClasses}
    if family is NormalizedFamily.OBJECT_PROPERTY:
        return constructor in {
            owl.SubObjectPropertyOf,
            owl.EquivalentObjectProperties,
            owl.DisjointObjectProperties,
            owl.InverseObjectProperties,
            owl.ObjectPropertyDomain,
            owl.ObjectPropertyRange,
            owl.FunctionalObjectProperty,
            owl.InverseFunctionalObjectProperty,
            owl.ReflexiveObjectProperty,
            owl.IrreflexiveObjectProperty,
            owl.SymmetricObjectProperty,
            owl.AsymmetricObjectProperty,
            owl.TransitiveObjectProperty,
        }
    if family is NormalizedFamily.DATA_PROPERTY:
        return constructor in {
            owl.SubDataPropertyOf,
            owl.EquivalentDataProperties,
            owl.DisjointDataProperties,
            owl.DataPropertyDomain,
            owl.DataPropertyRange,
            owl.FunctionalDataProperty,
        }
    if family is NormalizedFamily.DATATYPE:
        return constructor in {owl.DatatypeDefinition, DataRangeInclusion}
    if family is NormalizedFamily.KEY:
        return constructor is owl.HasKey
    if family is NormalizedFamily.ASSERTION:
        return constructor in {
            owl.SameIndividual,
            owl.DifferentIndividuals,
            owl.ClassAssertion,
            owl.ObjectPropertyAssertion,
            owl.NegativeObjectPropertyAssertion,
            owl.DataPropertyAssertion,
            owl.NegativeDataPropertyAssertion,
        }


@dataclass(frozen=True, slots=True)
class NormalizedRecord:
    family: NormalizedFamily
    statement: NormalizedStatement
    provenance_sha256: tuple[str, ...]
    generated: bool = False
    _canonical_statement: bytes = field(
        init=False,
        repr=False,
        compare=False,
    )

    def __post_init__(self) -> None:
        self._finish_initialization(statement_bytes(self.statement))

    def _finish_initialization(self, encoded: bytes) -> None:
        if not isinstance(self.family, NormalizedFamily):
            raise TypeError("family must be NormalizedFamily")
        if not isinstance(self.statement, (owl.AxiomNode, DataRangeInclusion)):
            raise TypeError("statement must be an OWL axiom or DataRangeInclusion")
        if not _statement_matches_family(self.family, self.statement):
            raise TypeError(
                f"{type(self.statement).__name__} is invalid for {self.family.value} records"
            )
        if (
            isinstance(self.statement, owl.AxiomNode)
            and cast(
                _AnnotatedAxiom,
                self.statement,
            ).annotations
        ):
            raise ValueError("normalized OWL statements must not retain annotations")
        if self.generated and self.family not in {
            NormalizedFamily.CLASS,
            NormalizedFamily.DATATYPE,
        }:
            raise ValueError("only class/datatype definition records may be generated")
        if not isinstance(encoded, bytes) or not encoded:
            raise ValueError("canonical statement cache must be nonempty bytes")
        provenance = tuple(sorted(set(self.provenance_sha256)))
        if not provenance or any(_SHA256.fullmatch(value) is None for value in provenance):
            raise ValueError("provenance_sha256 must contain lowercase SHA-256 hex digests")
        if not isinstance(self.generated, bool):
            raise TypeError("generated must be bool")
        object.__setattr__(self, "provenance_sha256", provenance)
        object.__setattr__(self, "_canonical_statement", encoded)

    @property
    def canonical_statement(self) -> bytes:
        return self._canonical_statement


def _record_from_trusted_canonical(
    family: NormalizedFamily,
    statement: NormalizedStatement,
    provenance_sha256: tuple[str, ...],
    generated: bool,
    canonical_statement: bytes,
) -> NormalizedRecord:
    """Construct an internal record from bytes already keyed by the normalizer.

    The public dataclass constructor always serializes the statement itself. This
    module-private fast path is used only after the normalizer obtained the bytes
    from that exact statement (or proved the unchanged source statement identity).
    """

    value = object.__new__(NormalizedRecord)
    object.__setattr__(value, "family", family)
    object.__setattr__(value, "statement", statement)
    object.__setattr__(value, "provenance_sha256", provenance_sha256)
    object.__setattr__(value, "generated", generated)
    value._finish_initialization(canonical_statement)
    return value


DefinitionSymbol: TypeAlias = owl.Class | owl.Datatype
DefinitionExpression: TypeAlias = owl.ClassExpression | owl.DataRange


def _definition_namespace(
    symbol: DefinitionSymbol,
    expression: DefinitionExpression,
    polarity: Polarity,
    encoded_expression: bytes,
) -> str:
    match = _GENERATED_DEFINITION_IRI.fullmatch(symbol.iri.value)
    if match is None:
        raise ValueError("definition symbol must use the generated definition namespace")
    kind, namespace, encoded_polarity, _ = match.groups()
    expected_kind = "class" if isinstance(symbol, owl.Class) else "data"
    if kind != expected_kind:
        raise ValueError("definition symbol kind does not match its structural sort")
    if encoded_polarity != polarity.value:
        raise ValueError("definition symbol polarity does not match its record")
    expected = _generated_definition_iri(
        namespace,
        expected_kind,
        encoded_expression,
        polarity,
    )
    if symbol.iri.value != expected:
        raise ValueError("definition symbol digest does not match its expression")
    return namespace


@dataclass(frozen=True, slots=True)
class DefinitionRecord:
    symbol: DefinitionSymbol
    expression: DefinitionExpression
    polarity: Polarity
    provenance_sha256: tuple[str, ...]
    query_local: bool = False
    _canonical_expression: bytes = field(
        init=False,
        repr=False,
        compare=False,
    )

    def __post_init__(self) -> None:
        if not isinstance(self.expression, owl.StructuralNode):
            raise TypeError("definition expression must be a core structural value")
        self._finish_initialization(self.expression.canonical_bytes())

    def _finish_initialization(self, encoded_expression: bytes) -> None:
        if isinstance(self.symbol, owl.Class):
            if not isinstance(self.expression, owl.CLASS_EXPRESSION_TYPES):
                raise TypeError("class definition expression must be a ClassExpression")
        elif isinstance(self.symbol, owl.Datatype):
            if not isinstance(self.expression, owl.DATA_RANGE_TYPES):
                raise TypeError("datatype definition expression must be a DataRange")
        else:
            raise TypeError("definition symbol must be a core Class or Datatype")
        if not isinstance(self.polarity, Polarity):
            raise TypeError("polarity must be Polarity")
        provenance = tuple(sorted(set(self.provenance_sha256)))
        if not provenance or any(_SHA256.fullmatch(value) is None for value in provenance):
            raise ValueError("definition provenance must contain lowercase SHA-256 digests")
        if not isinstance(self.query_local, bool):
            raise TypeError("query_local must be bool")
        if not isinstance(encoded_expression, bytes) or not encoded_expression:
            raise ValueError("canonical definition expression cache must be nonempty bytes")
        _definition_namespace(
            self.symbol,
            self.expression,
            self.polarity,
            encoded_expression,
        )
        object.__setattr__(self, "provenance_sha256", provenance)
        object.__setattr__(self, "_canonical_expression", encoded_expression)

    @property
    def canonical_expression(self) -> bytes:
        return self._canonical_expression


def _definition_from_trusted_canonical(
    symbol: DefinitionSymbol,
    expression: DefinitionExpression,
    polarity: Polarity,
    provenance_sha256: tuple[str, ...],
    query_local: bool,
    canonical_expression: bytes,
) -> DefinitionRecord:
    value = object.__new__(DefinitionRecord)
    object.__setattr__(value, "symbol", symbol)
    object.__setattr__(value, "expression", expression)
    object.__setattr__(value, "polarity", polarity)
    object.__setattr__(value, "provenance_sha256", provenance_sha256)
    object.__setattr__(value, "query_local", query_local)
    value._finish_initialization(canonical_expression)
    return value


@dataclass(frozen=True, slots=True)
class NormalizedOntology:
    logical_fingerprint: str
    records: tuple[NormalizedRecord, ...]
    definitions: tuple[DefinitionRecord, ...]
    declared_entities: tuple[owl.Entity, ...]
    source_axiom_count: int
    ignored_nonlogical_axiom_count: int
    expression_steps: int
    schema_version: int = NORMALIZATION_SCHEMA_VERSION
    _digest_cache: str | None = field(
        default=None,
        init=False,
        repr=False,
        compare=False,
    )

    def __post_init__(self) -> None:
        _validate_digest(self.logical_fingerprint, "logical_fingerprint")
        if isinstance(self.schema_version, bool) or not isinstance(
            self.schema_version,
            int,
        ):
            raise ValueError("normalization schema version must be an integer")
        if self.schema_version != NORMALIZATION_SCHEMA_VERSION:
            raise ValueError(f"unsupported normalization schema version {self.schema_version}")
        records = tuple(self.records)
        definitions = tuple(self.definitions)
        entities = tuple(self.declared_entities)
        object.__setattr__(self, "records", records)
        object.__setattr__(self, "definitions", definitions)
        object.__setattr__(self, "declared_entities", entities)
        if not all(isinstance(value, NormalizedRecord) for value in records):
            raise TypeError("records must contain NormalizedRecord values")
        if not all(isinstance(value, DefinitionRecord) for value in definitions):
            raise TypeError("definitions must contain DefinitionRecord values")
        if any(value.query_local for value in definitions):
            raise ValueError("permanent ontology definitions cannot be query-local")
        if not all(isinstance(value, owl.Entity) for value in entities):
            raise TypeError("declared_entities must contain exact core Entity values")
        _validate_record_order(records, prefix="")
        _validate_definition_order(definitions, prefix="")
        _validate_definition_graph(
            records,
            definitions,
            namespace=self.logical_fingerprint,
            prefix="",
        )
        _validate_entity_order(entities)
        if _definitions_intersect_entities(definitions, entities):
            raise ValueError("generated definitions must not enter the declared signature")
        for name in (
            "source_axiom_count",
            "ignored_nonlogical_axiom_count",
            "expression_steps",
        ):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")

    @property
    def generated_symbols(self) -> tuple[DefinitionSymbol, ...]:
        return tuple(value.symbol for value in self.definitions)

    def canonical_snapshot(self) -> str:
        """Return the complete deterministic diagnostic snapshot.

        Unlike :attr:`digest`, this includes source provenance and processing
        counters so that traces can be reproduced exactly.
        """

        return _canonical_json(
            _payload(
                logical_fingerprint=self.logical_fingerprint,
                records=self.records,
                definitions=self.definitions,
                declared_entities=self.declared_entities,
                source_axiom_count=self.source_axiom_count,
                ignored_nonlogical_axiom_count=self.ignored_nonlogical_axiom_count,
                expression_steps=self.expression_steps,
                schema_version=self.schema_version,
            )
        )

    def semantic_snapshot(self) -> str:
        """Return the deterministic cache identity for normalized semantics.

        Provenance, declarations, and processing counters are deliberately absent:
        they are diagnostic/signature metadata and cannot change rule truth.
        """

        return _canonical_json(
            {
                "definitions": [_semantic_definition_payload(value) for value in self.definitions],
                "logical_fingerprint": self.logical_fingerprint,
                "records": [_semantic_record_payload(value) for value in self.records],
                "schema_version": self.schema_version,
            }
        )

    @classmethod
    def from_canonical_snapshot(cls, encoded: str) -> NormalizedOntology:
        payload = _decode_payload(encoded)
        expected = {
            "declared_entities",
            "definitions",
            "expression_steps",
            "ignored_nonlogical_axiom_count",
            "logical_fingerprint",
            "records",
            "schema_version",
            "source_axiom_count",
        }
        if set(payload) != expected:
            raise ValueError("normalized ontology snapshot has unexpected fields")
        return cls(
            logical_fingerprint=_text(payload["logical_fingerprint"], "logical_fingerprint"),
            records=_decode_records(payload["records"]),
            definitions=_decode_definitions(payload["definitions"]),
            declared_entities=_decode_entities(payload["declared_entities"]),
            source_axiom_count=_nonnegative_int(
                payload["source_axiom_count"], "source_axiom_count"
            ),
            ignored_nonlogical_axiom_count=_nonnegative_int(
                payload["ignored_nonlogical_axiom_count"],
                "ignored_nonlogical_axiom_count",
            ),
            expression_steps=_nonnegative_int(payload["expression_steps"], "expression_steps"),
            schema_version=_nonnegative_int(payload["schema_version"], "schema_version"),
        )

    @property
    def digest(self) -> str:
        """Domain-separated semantic digest used by query/session cache keys."""

        retained = self._digest_cache
        if retained is None:
            hasher = hashlib.sha256(b"pyhermit:normalized-ontology-semantic:v1\x00")
            hasher.update(bytes.fromhex(self.logical_fingerprint))
            hasher.update(self.schema_version.to_bytes(8, "big"))
            _update_semantic_records(hasher, self.records)
            _update_semantic_definitions(hasher, self.definitions)
            retained = hasher.hexdigest()
            object.__setattr__(self, "_digest_cache", retained)
        return retained


@dataclass(frozen=True, slots=True)
class NormalizedQuery:
    permanent_normalization_digest: str
    query_hash: str
    records: tuple[NormalizedRecord, ...]
    definitions: tuple[DefinitionRecord, ...]
    requires_rebuild: bool
    source_axiom_count: int
    expression_steps: int
    schema_version: int = NORMALIZATION_SCHEMA_VERSION
    _digest_cache: str | None = field(
        default=None,
        init=False,
        repr=False,
        compare=False,
    )

    def __post_init__(self) -> None:
        _validate_digest(
            self.permanent_normalization_digest,
            "permanent_normalization_digest",
        )
        _validate_digest(self.query_hash, "query_hash")
        if isinstance(self.schema_version, bool) or not isinstance(
            self.schema_version,
            int,
        ):
            raise ValueError("query normalization schema version must be an integer")
        if self.schema_version != NORMALIZATION_SCHEMA_VERSION:
            raise ValueError("unsupported query normalization schema version")
        if not isinstance(self.requires_rebuild, bool):
            raise TypeError("requires_rebuild must be bool")
        records = tuple(self.records)
        definitions = tuple(self.definitions)
        object.__setattr__(self, "records", records)
        object.__setattr__(self, "definitions", definitions)
        if not all(isinstance(value, NormalizedRecord) for value in records):
            raise TypeError("records must contain NormalizedRecord values")
        if not all(isinstance(value, DefinitionRecord) for value in definitions):
            raise TypeError("definitions must contain DefinitionRecord values")
        if any(not value.query_local for value in definitions):
            raise ValueError("query definitions must be query-local")
        _validate_record_order(records, prefix="query ")
        _validate_definition_order(definitions, prefix="query ")
        _validate_definition_graph(
            records,
            definitions,
            namespace=_query_definition_namespace(
                self.permanent_normalization_digest,
                self.query_hash,
            ),
            prefix="query ",
        )
        for name in ("source_axiom_count", "expression_steps"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")

    def canonical_snapshot(self) -> str:
        return _canonical_json(
            {
                "definitions": [_definition_payload(value) for value in self.definitions],
                "expression_steps": self.expression_steps,
                "permanent_normalization_digest": self.permanent_normalization_digest,
                "query_hash": self.query_hash,
                "records": [_record_payload(value) for value in self.records],
                "requires_rebuild": self.requires_rebuild,
                "schema_version": self.schema_version,
                "source_axiom_count": self.source_axiom_count,
            }
        )

    def semantic_snapshot(self) -> str:
        """Return query semantics without provenance or processing counters."""

        return _canonical_json(
            {
                "definitions": [_semantic_definition_payload(value) for value in self.definitions],
                "permanent_normalization_digest": self.permanent_normalization_digest,
                "query_hash": self.query_hash,
                "records": [_semantic_record_payload(value) for value in self.records],
                "requires_rebuild": self.requires_rebuild,
                "schema_version": self.schema_version,
            }
        )

    @classmethod
    def from_canonical_snapshot(cls, encoded: str) -> NormalizedQuery:
        payload = _decode_payload(encoded)
        expected = {
            "definitions",
            "expression_steps",
            "permanent_normalization_digest",
            "query_hash",
            "records",
            "requires_rebuild",
            "schema_version",
            "source_axiom_count",
        }
        if set(payload) != expected:
            raise ValueError("normalized query snapshot has unexpected fields")
        requires_rebuild = payload["requires_rebuild"]
        if not isinstance(requires_rebuild, bool):
            raise TypeError("requires_rebuild must be bool")
        return cls(
            permanent_normalization_digest=_text(
                payload["permanent_normalization_digest"],
                "permanent_normalization_digest",
            ),
            query_hash=_text(payload["query_hash"], "query_hash"),
            records=_decode_records(payload["records"]),
            definitions=_decode_definitions(payload["definitions"]),
            requires_rebuild=requires_rebuild,
            source_axiom_count=_nonnegative_int(
                payload["source_axiom_count"], "source_axiom_count"
            ),
            expression_steps=_nonnegative_int(payload["expression_steps"], "expression_steps"),
            schema_version=_nonnegative_int(payload["schema_version"], "schema_version"),
        )

    @property
    def digest(self) -> str:
        retained = self._digest_cache
        if retained is None:
            hasher = hashlib.sha256(b"pyhermit:normalized-query-semantic:v1\x00")
            hasher.update(bytes.fromhex(self.permanent_normalization_digest))
            hasher.update(bytes.fromhex(self.query_hash))
            hasher.update(bytes((int(self.requires_rebuild),)))
            hasher.update(self.schema_version.to_bytes(8, "big"))
            _update_semantic_records(hasher, self.records)
            _update_semantic_definitions(hasher, self.definitions)
            retained = hasher.hexdigest()
            object.__setattr__(self, "_digest_cache", retained)
        return retained


def _update_semantic_records(
    hasher: _HashWriter,
    records: tuple[NormalizedRecord, ...],
) -> None:
    hasher.update(len(records).to_bytes(8, "big"))
    for value in records:
        _update_hash_frame(hasher, value.family.value.encode("ascii"))
        hasher.update(bytes((int(value.generated),)))
        _update_hash_frame(hasher, value.canonical_statement)


def _update_semantic_definitions(
    hasher: _HashWriter,
    definitions: tuple[DefinitionRecord, ...],
) -> None:
    hasher.update(len(definitions).to_bytes(8, "big"))
    for value in definitions:
        _update_hash_frame(hasher, value.symbol.canonical_bytes())
        _update_hash_frame(hasher, value.canonical_expression)
        _update_hash_frame(hasher, value.polarity.value.encode("ascii"))
        hasher.update(bytes((int(value.query_local),)))


def _update_hash_frame(hasher: _HashWriter, value: bytes) -> None:
    hasher.update(len(value).to_bytes(8, "big"))
    hasher.update(value)


def _validate_record_order(
    records: tuple[NormalizedRecord, ...],
    *,
    prefix: str,
) -> None:
    previous: tuple[str, bytes] | None = None
    for value in records:
        current = (value.family.value, value.canonical_statement)
        if previous is not None:
            if current < previous:
                raise ValueError(f"{prefix}records must be in canonical order")
            if current == previous:
                raise ValueError(f"{prefix}records must be unique by family and statement")
        previous = current


def _validate_definition_order(
    definitions: tuple[DefinitionRecord, ...],
    *,
    prefix: str,
) -> None:
    previous: tuple[bytes, str, bytes] | None = None
    previous_symbol: bytes | None = None
    for value in definitions:
        symbol = value.symbol.canonical_bytes()
        current = (
            symbol,
            value.polarity.value,
            value.canonical_expression,
        )
        if previous is not None and current < previous:
            raise ValueError(f"{prefix}definitions must be in canonical order")
        if previous_symbol == symbol:
            raise ValueError(f"{prefix}definition symbols must be unique")
        previous = current
        previous_symbol = symbol


def _validate_definition_graph(
    records: tuple[NormalizedRecord, ...],
    definitions: tuple[DefinitionRecord, ...],
    *,
    namespace: str,
    prefix: str,
) -> None:
    by_symbol: dict[bytes, DefinitionRecord] = {}
    for definition in definitions:
        observed_namespace = _definition_namespace(
            definition.symbol,
            definition.expression,
            definition.polarity,
            definition.canonical_expression,
        )
        if observed_namespace != namespace:
            raise ValueError(f"{prefix}definition symbol belongs to the wrong namespace")
        by_symbol[definition.symbol.canonical_bytes()] = definition

    seen: set[bytes] = set()
    for record in records:
        if not record.generated:
            continue
        candidates: list[DefinitionRecord] = []
        statement = record.statement
        if record.family is NormalizedFamily.CLASS and isinstance(
            statement,
            owl.SubClassOf,
        ):
            if isinstance(statement.sub_class, owl.Class):
                candidate = by_symbol.get(statement.sub_class.canonical_bytes())
                if candidate is not None and candidate.polarity is Polarity.POSITIVE:
                    candidates.append(candidate)
            if isinstance(statement.super_class, owl.Class):
                candidate = by_symbol.get(statement.super_class.canonical_bytes())
                if candidate is not None and candidate.polarity is Polarity.NEGATIVE:
                    candidates.append(candidate)
        elif record.family is NormalizedFamily.DATATYPE and isinstance(
            statement,
            DataRangeInclusion,
        ):
            if isinstance(statement.sub_range, owl.Datatype):
                candidate = by_symbol.get(statement.sub_range.canonical_bytes())
                if candidate is not None and candidate.polarity is Polarity.POSITIVE:
                    candidates.append(candidate)
            if isinstance(statement.super_range, owl.Datatype):
                candidate = by_symbol.get(statement.super_range.canonical_bytes())
                if candidate is not None and candidate.polarity is Polarity.NEGATIVE:
                    candidates.append(candidate)
        if len(candidates) != 1:
            raise ValueError(
                f"{prefix}generated record must have exactly one directional definition owner"
            )
        owner = candidates[0]
        owner_key = owner.symbol.canonical_bytes()
        if owner_key in seen:
            raise ValueError(f"{prefix}definition has more than one generated record")
        if record.provenance_sha256 != owner.provenance_sha256:
            raise ValueError(f"{prefix}definition and generated record provenance must agree")
        seen.add(owner_key)
    if len(seen) != len(definitions):
        raise ValueError(f"{prefix}definition is missing its generated record")


def _validate_entity_order(entities: tuple[owl.Entity, ...]) -> None:
    previous: bytes | None = None
    for value in entities:
        current = value.canonical_bytes()
        if previous is not None and current <= previous:
            raise ValueError("declared_entities must be unique and in canonical order")
        previous = current


def _definitions_intersect_entities(
    definitions: tuple[DefinitionRecord, ...],
    entities: tuple[owl.Entity, ...],
) -> bool:
    entity_index = 0
    for definition in definitions:
        symbol = definition.symbol.canonical_bytes()
        while entity_index < len(entities):
            entity = entities[entity_index].canonical_bytes()
            if entity < symbol:
                entity_index += 1
                continue
            if entity == symbol:
                return True
            break
    return False


def _payload(
    *,
    logical_fingerprint: str,
    records: tuple[NormalizedRecord, ...],
    definitions: tuple[DefinitionRecord, ...],
    declared_entities: tuple[owl.Entity, ...],
    source_axiom_count: int,
    ignored_nonlogical_axiom_count: int,
    expression_steps: int,
    schema_version: int,
) -> dict[str, object]:
    return {
        "declared_entities": [value.canonical_bytes().hex() for value in declared_entities],
        "definitions": [_definition_payload(value) for value in definitions],
        "expression_steps": expression_steps,
        "ignored_nonlogical_axiom_count": ignored_nonlogical_axiom_count,
        "logical_fingerprint": logical_fingerprint,
        "records": [_record_payload(value) for value in records],
        "schema_version": schema_version,
        "source_axiom_count": source_axiom_count,
    }


def _record_payload(value: NormalizedRecord) -> dict[str, object]:
    statement = value.statement
    if isinstance(statement, DataRangeInclusion):
        encoded: object = {
            "sub": statement.sub_range.canonical_bytes().hex(),
            "super": statement.super_range.canonical_bytes().hex(),
        }
        statement_kind = "data_range_inclusion"
    else:
        encoded = value.canonical_statement.hex()
        statement_kind = "owl_axiom"
    return {
        "family": value.family.value,
        "generated": value.generated,
        "provenance": list(value.provenance_sha256),
        "statement": encoded,
        "statement_kind": statement_kind,
    }


def _semantic_record_payload(value: NormalizedRecord) -> dict[str, object]:
    statement = value.statement
    if isinstance(statement, DataRangeInclusion):
        encoded: object = {
            "sub": statement.sub_range.canonical_bytes().hex(),
            "super": statement.super_range.canonical_bytes().hex(),
        }
        statement_kind = "data_range_inclusion"
    else:
        encoded = value.canonical_statement.hex()
        statement_kind = "owl_axiom"
    return {
        "family": value.family.value,
        "generated": value.generated,
        "statement": encoded,
        "statement_kind": statement_kind,
    }


def _definition_payload(value: DefinitionRecord) -> dict[str, object]:
    return {
        "expression": value.canonical_expression.hex(),
        "polarity": value.polarity.value,
        "provenance": list(value.provenance_sha256),
        "query_local": value.query_local,
        "symbol": value.symbol.canonical_bytes().hex(),
        "symbol_kind": "class" if isinstance(value.symbol, owl.Class) else "datatype",
    }


def _semantic_definition_payload(value: DefinitionRecord) -> dict[str, object]:
    return {
        "expression": value.canonical_expression.hex(),
        "polarity": value.polarity.value,
        "query_local": value.query_local,
        "symbol": value.symbol.canonical_bytes().hex(),
        "symbol_kind": "class" if isinstance(value.symbol, owl.Class) else "datatype",
    }


def _canonical_json(payload: object) -> str:
    return json.dumps(payload, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def _decode_payload(encoded: str) -> dict[str, object]:
    if not isinstance(encoded, str):
        raise TypeError("encoded snapshot must be str")
    try:
        value = cast(object, json.loads(encoded))
    except json.JSONDecodeError as error:
        raise ValueError("invalid normalized snapshot JSON") from error
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise TypeError("normalized snapshot must be a JSON object with string keys")
    return cast(dict[str, object], value)


def _decode_records(value: object) -> tuple[NormalizedRecord, ...]:
    if not isinstance(value, list):
        raise TypeError("records must be a JSON array")
    records: list[NormalizedRecord] = []
    for raw in value:
        if not isinstance(raw, dict) or not all(isinstance(key, str) for key in raw):
            raise TypeError("record must be a JSON object")
        item = cast(dict[str, object], raw)
        if set(item) != {
            "family",
            "generated",
            "provenance",
            "statement",
            "statement_kind",
        }:
            raise ValueError("normalized record has unexpected fields")
        kind = _text(item["statement_kind"], "statement_kind")
        if kind == "owl_axiom":
            statement_node = _decode_node(item["statement"])
            if not isinstance(statement_node, owl.AxiomNode):
                raise TypeError("owl_axiom record did not decode to AxiomNode")
            statement: NormalizedStatement = statement_node
        elif kind == "data_range_inclusion":
            raw_statement = item["statement"]
            if not isinstance(raw_statement, dict) or not all(
                isinstance(key, str) for key in raw_statement
            ):
                raise TypeError("data range inclusion statement must be an object")
            fields = cast(dict[str, object], raw_statement)
            if set(fields) != {"sub", "super"}:
                raise ValueError("data range inclusion has unexpected fields")
            sub = _decode_node(fields["sub"])
            sup = _decode_node(fields["super"])
            if not isinstance(sub, owl.DATA_RANGE_TYPES) or not isinstance(
                sup, owl.DATA_RANGE_TYPES
            ):
                raise TypeError("data range inclusion fields must decode to DataRange")
            statement = DataRangeInclusion(
                cast(owl.DataRange, sub),
                cast(owl.DataRange, sup),
            )
        else:
            raise ValueError(f"unknown normalized statement kind {kind!r}")
        generated = item["generated"]
        if not isinstance(generated, bool):
            raise TypeError("record generated must be bool")
        records.append(
            NormalizedRecord(
                NormalizedFamily(_text(item["family"], "family")),
                statement,
                _text_tuple(item["provenance"], "provenance"),
                generated,
            )
        )
    return tuple(records)


def _decode_definitions(value: object) -> tuple[DefinitionRecord, ...]:
    if not isinstance(value, list):
        raise TypeError("definitions must be a JSON array")
    definitions: list[DefinitionRecord] = []
    for raw in value:
        if not isinstance(raw, dict) or not all(isinstance(key, str) for key in raw):
            raise TypeError("definition must be a JSON object")
        item = cast(dict[str, object], raw)
        if set(item) != {
            "expression",
            "polarity",
            "provenance",
            "query_local",
            "symbol",
            "symbol_kind",
        }:
            raise ValueError("definition has unexpected fields")
        symbol = _decode_node(item["symbol"])
        expression = _decode_node(item["expression"])
        symbol_kind = _text(item["symbol_kind"], "symbol_kind")
        if symbol_kind == "class":
            if not isinstance(symbol, owl.Class) or not isinstance(
                expression, owl.CLASS_EXPRESSION_TYPES
            ):
                raise TypeError("class definition has invalid structural sorts")
        elif symbol_kind == "datatype":
            if not isinstance(symbol, owl.Datatype) or not isinstance(
                expression, owl.DATA_RANGE_TYPES
            ):
                raise TypeError("datatype definition has invalid structural sorts")
        else:
            raise ValueError(f"unknown definition symbol kind {symbol_kind!r}")
        query_local = item["query_local"]
        if not isinstance(query_local, bool):
            raise TypeError("definition query_local must be bool")
        definitions.append(
            DefinitionRecord(
                symbol,
                cast(DefinitionExpression, expression),
                Polarity(_text(item["polarity"], "polarity")),
                _text_tuple(item["provenance"], "provenance"),
                query_local,
            )
        )
    return tuple(definitions)


def _decode_entities(value: object) -> tuple[owl.Entity, ...]:
    if not isinstance(value, list):
        raise TypeError("declared_entities must be a JSON array")
    entities: list[owl.Entity] = []
    for raw in value:
        node = _decode_node(raw)
        if not isinstance(node, owl.Entity):
            raise TypeError("declared entity did not decode to core Entity")
        entities.append(node)
    return tuple(entities)


def _decode_node(value: object) -> owl.StructuralNode:
    encoded = _text(value, "canonical structural value")
    try:
        payload = bytes.fromhex(encoded)
    except ValueError as error:
        raise ValueError("canonical structural value must be hexadecimal") from error
    return owl.decode_canonical(payload)


def _text(value: object, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be str")
    return value


def _text_tuple(value: object, name: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise TypeError(f"{name} must be an array of strings")
    return tuple(value)


def _nonnegative_int(value: object, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")
    return value


def _validate_digest(value: str, name: str) -> None:
    if not isinstance(value, str) or _SHA256.fullmatch(value) is None:
        raise ValueError(f"{name} must be lowercase SHA-256 hex")


__all__ = [
    "NORMALIZATION_SCHEMA_VERSION",
    "DataRangeInclusion",
    "DefinitionRecord",
    "NormalizedFamily",
    "NormalizedOntology",
    "NormalizedQuery",
    "NormalizedRecord",
    "NormalizedStatement",
    "Polarity",
    "statement_bytes",
]
