# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Exhaustive, deterministic OWL axiom normalization.

SPDX-License-Identifier: LGPL-3.0-or-later

Source-guided behavior: pinned HermiT ``OWLNormalization`` and
``ExpressionManager`` at commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3.
"""

from __future__ import annotations

import hashlib
import re
from collections import deque
from collections.abc import Callable, Iterable, Mapping
from dataclasses import dataclass, field
from types import MappingProxyType
from typing import cast

import pyowl_core.model as owl
from pyowl_core import AxiomScope, OntologyView, logical_fingerprint

from pyhermit.exceptions import ReasonerInterruptedError, ResourceLimitError

from .expressions import (
    ExpressionDepthError,
    ExpressionNormalizationCancelled,
    ExpressionNormalizer,
)
from .model import (
    _GENERATED_DEFINITION_NAMESPACE,
    DataRangeInclusion,
    DefinitionRecord,
    NormalizedFamily,
    NormalizedOntology,
    NormalizedQuery,
    NormalizedRecord,
    NormalizedStatement,
    Polarity,
    _definition_from_trusted_canonical,
    _generated_definition_iri,
    _query_definition_namespace,
    _record_from_trusted_canonical,
    statement_bytes,
)

_SHA256 = re.compile(r"[0-9a-f]{64}\Z")
_GENERATED_NAMESPACE_BYTES = _GENERATED_DEFINITION_NAMESPACE.encode("ascii")


class UnknownAxiomError(TypeError):
    """Raised when an axiom constructor is outside the closed handler table."""


class UnsupportedNormalizationError(ValueError):
    """Raised for a known extension outside the OWL 2 DL normalization contract."""


@dataclass(frozen=True, slots=True)
class NormalizationLimits:
    max_source_axioms: int = 10_000_000
    max_records: int = 20_000_000
    max_definitions: int = 5_000_000
    max_expression_depth: int = 512

    def __post_init__(self) -> None:
        for name in (
            "max_source_axioms",
            "max_records",
            "max_definitions",
            "max_expression_depth",
        ):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 1:
                raise ValueError(f"{name} must be a positive integer")
        if self.max_expression_depth > 512:
            raise ValueError("max_expression_depth cannot exceed the core limit 512")


class _Handler(str):
    pass


_DECLARATION = _Handler("declaration")
_ANNOTATION = _Handler("annotation")
_SUBCLASS = _Handler("subclass")
_EQUIVALENT_CLASSES = _Handler("equivalent_classes")
_DISJOINT_CLASSES = _Handler("disjoint_classes")
_DISJOINT_UNION = _Handler("disjoint_union")
_SUB_OBJECT = _Handler("sub_object")
_EQUIVALENT_OBJECT = _Handler("equivalent_object")
_DISJOINT_OBJECT = _Handler("disjoint_object")
_INVERSE_OBJECT = _Handler("inverse_object")
_OBJECT_DOMAIN = _Handler("object_domain")
_OBJECT_RANGE = _Handler("object_range")
_FUNCTIONAL_OBJECT = _Handler("functional_object")
_INVERSE_FUNCTIONAL_OBJECT = _Handler("inverse_functional_object")
_REFLEXIVE_OBJECT = _Handler("reflexive_object")
_IRREFLEXIVE_OBJECT = _Handler("irreflexive_object")
_SYMMETRIC_OBJECT = _Handler("symmetric_object")
_ASYMMETRIC_OBJECT = _Handler("asymmetric_object")
_TRANSITIVE_OBJECT = _Handler("transitive_object")
_SUB_DATA = _Handler("sub_data")
_EQUIVALENT_DATA = _Handler("equivalent_data")
_DISJOINT_DATA = _Handler("disjoint_data")
_DATA_DOMAIN = _Handler("data_domain")
_DATA_RANGE = _Handler("data_range")
_FUNCTIONAL_DATA = _Handler("functional_data")
_DATATYPE_DEFINITION = _Handler("datatype_definition")
_HAS_KEY = _Handler("has_key")
_SAME = _Handler("same")
_DIFFERENT = _Handler("different")
_CLASS_ASSERTION = _Handler("class_assertion")
_OBJECT_ASSERTION = _Handler("object_assertion")
_NEGATIVE_OBJECT_ASSERTION = _Handler("negative_object_assertion")
_DATA_ASSERTION = _Handler("data_assertion")
_NEGATIVE_DATA_ASSERTION = _Handler("negative_data_assertion")

AXIOM_HANDLER_TABLE: Mapping[type[owl.AxiomNode], _Handler] = MappingProxyType(
    {
        owl.Declaration: _DECLARATION,
        owl.AnnotationAssertion: _ANNOTATION,
        owl.SubAnnotationPropertyOf: _ANNOTATION,
        owl.AnnotationPropertyDomain: _ANNOTATION,
        owl.AnnotationPropertyRange: _ANNOTATION,
        owl.SubClassOf: _SUBCLASS,
        owl.EquivalentClasses: _EQUIVALENT_CLASSES,
        owl.DisjointClasses: _DISJOINT_CLASSES,
        owl.DisjointUnion: _DISJOINT_UNION,
        owl.SubObjectPropertyOf: _SUB_OBJECT,
        owl.EquivalentObjectProperties: _EQUIVALENT_OBJECT,
        owl.DisjointObjectProperties: _DISJOINT_OBJECT,
        owl.InverseObjectProperties: _INVERSE_OBJECT,
        owl.ObjectPropertyDomain: _OBJECT_DOMAIN,
        owl.ObjectPropertyRange: _OBJECT_RANGE,
        owl.FunctionalObjectProperty: _FUNCTIONAL_OBJECT,
        owl.InverseFunctionalObjectProperty: _INVERSE_FUNCTIONAL_OBJECT,
        owl.ReflexiveObjectProperty: _REFLEXIVE_OBJECT,
        owl.IrreflexiveObjectProperty: _IRREFLEXIVE_OBJECT,
        owl.SymmetricObjectProperty: _SYMMETRIC_OBJECT,
        owl.AsymmetricObjectProperty: _ASYMMETRIC_OBJECT,
        owl.TransitiveObjectProperty: _TRANSITIVE_OBJECT,
        owl.SubDataPropertyOf: _SUB_DATA,
        owl.EquivalentDataProperties: _EQUIVALENT_DATA,
        owl.DisjointDataProperties: _DISJOINT_DATA,
        owl.DataPropertyDomain: _DATA_DOMAIN,
        owl.DataPropertyRange: _DATA_RANGE,
        owl.FunctionalDataProperty: _FUNCTIONAL_DATA,
        owl.DatatypeDefinition: _DATATYPE_DEFINITION,
        owl.HasKey: _HAS_KEY,
        owl.SameIndividual: _SAME,
        owl.DifferentIndividuals: _DIFFERENT,
        owl.ClassAssertion: _CLASS_ASSERTION,
        owl.ObjectPropertyAssertion: _OBJECT_ASSERTION,
        owl.NegativeObjectPropertyAssertion: _NEGATIVE_OBJECT_ASSERTION,
        owl.DataPropertyAssertion: _DATA_ASSERTION,
        owl.NegativeDataPropertyAssertion: _NEGATIVE_DATA_ASSERTION,
    }
)

if set(AXIOM_HANDLER_TABLE) != set(owl.AXIOM_TYPES):
    raise RuntimeError("normalization handler table is not exhaustive for pyowl-core AXIOM_TYPES")

_QUERY_ALWAYS_REBUILD_HANDLERS = frozenset(
    {
        _SUB_OBJECT,
        _EQUIVALENT_OBJECT,
        _DISJOINT_OBJECT,
        _INVERSE_OBJECT,
        _OBJECT_DOMAIN,
        _OBJECT_RANGE,
        _FUNCTIONAL_OBJECT,
        _INVERSE_FUNCTIONAL_OBJECT,
        _REFLEXIVE_OBJECT,
        _IRREFLEXIVE_OBJECT,
        _SYMMETRIC_OBJECT,
        _ASYMMETRIC_OBJECT,
        _TRANSITIVE_OBJECT,
        _SUB_DATA,
        _EQUIVALENT_DATA,
        _DISJOINT_DATA,
        _DATA_DOMAIN,
        _DATA_RANGE,
        _FUNCTIONAL_DATA,
        _DATATYPE_DEFINITION,
        _HAS_KEY,
        _DISJOINT_UNION,
        _SAME,
        _DIFFERENT,
        _NEGATIVE_OBJECT_ASSERTION,
        _NEGATIVE_DATA_ASSERTION,
    }
)
_QUERY_OVERLAY_SAFE_HANDLERS = frozenset(
    {
        _DECLARATION,
        _ANNOTATION,
        _SUBCLASS,
        _EQUIVALENT_CLASSES,
        _DISJOINT_CLASSES,
        _CLASS_ASSERTION,
        _OBJECT_ASSERTION,
        _DATA_ASSERTION,
    }
)
_QUERY_CLASSIFIED_HANDLERS = _QUERY_ALWAYS_REBUILD_HANDLERS | _QUERY_OVERLAY_SAFE_HANDLERS
if (
    set(AXIOM_HANDLER_TABLE.values()) != _QUERY_CLASSIFIED_HANDLERS
    or _QUERY_ALWAYS_REBUILD_HANDLERS & _QUERY_OVERLAY_SAFE_HANDLERS
):
    raise RuntimeError("query rebuild handler classification is not closed and disjoint")

_QUERY_OVERLAY_SAFE_CLASS_TYPES = (
    owl.Class,
    owl.ObjectIntersectionOf,
    owl.ObjectComplementOf,
    owl.ObjectSomeValuesFrom,
    owl.ObjectAllValuesFrom,
)
_QUERY_REBUILD_CLASS_TYPES = (
    owl.ObjectUnionOf,
    owl.ObjectOneOf,
    owl.ObjectHasValue,
    owl.ObjectHasSelf,
    owl.ObjectMinCardinality,
    owl.ObjectMaxCardinality,
    owl.ObjectExactCardinality,
    owl.DataSomeValuesFrom,
    owl.DataAllValuesFrom,
    owl.DataHasValue,
    owl.DataMinCardinality,
    owl.DataMaxCardinality,
    owl.DataExactCardinality,
)
_QUERY_OVERLAY_SAFE_DATA_TYPES = (owl.Datatype,)
_QUERY_REBUILD_DATA_TYPES = (
    owl.DataIntersectionOf,
    owl.DataUnionOf,
    owl.DataComplementOf,
    owl.DataOneOf,
    owl.DatatypeRestriction,
)
_QUERY_CLASSIFIED_CLASS_TYPES = set(_QUERY_OVERLAY_SAFE_CLASS_TYPES) | set(
    _QUERY_REBUILD_CLASS_TYPES
)
_QUERY_CLASSIFIED_DATA_TYPES = set(_QUERY_OVERLAY_SAFE_DATA_TYPES) | set(_QUERY_REBUILD_DATA_TYPES)
if (
    set(owl.CLASS_EXPRESSION_TYPES) != _QUERY_CLASSIFIED_CLASS_TYPES
    or set(_QUERY_OVERLAY_SAFE_CLASS_TYPES) & set(_QUERY_REBUILD_CLASS_TYPES)
    or set(owl.DATA_RANGE_TYPES) != _QUERY_CLASSIFIED_DATA_TYPES
    or set(_QUERY_OVERLAY_SAFE_DATA_TYPES) & set(_QUERY_REBUILD_DATA_TYPES)
):
    raise RuntimeError("query expression feature classification is not closed and disjoint")

_QUERY_STRATEGY_SENSITIVE_TYPES = (
    *_QUERY_REBUILD_CLASS_TYPES,
    *_QUERY_REBUILD_DATA_TYPES,
    owl.ObjectInverseOf,
)


@dataclass(slots=True)
class _MutableRecord:
    family: NormalizedFamily
    statement: NormalizedStatement
    provenance: set[str]
    generated: bool


@dataclass(slots=True)
class _MutableDefinition:
    symbol: owl.Class | owl.Datatype
    expression: owl.ClassExpression | owl.DataRange
    polarity: Polarity
    provenance: set[str]
    query_local: bool
    statement: NormalizedStatement | None = None
    propagated: set[str] = field(default_factory=set)


DefinitionKey = tuple[str, bytes, Polarity]


class _NormalizationState:
    __slots__ = (
        "cancelled",
        "declared_entities",
        "definitions",
        "expression_normalizer",
        "ignored",
        "limits",
        "namespace",
        "pending_definitions",
        "query_local",
        "queued_definitions",
        "records",
        "requires_rebuild",
        "reserved_signature_entities",
        "seed_symbols",
        "source_count",
    )

    def __init__(
        self,
        namespace: str,
        limits: NormalizationLimits,
        cancelled: Callable[[], bool] | None,
        *,
        query_local: bool,
        seed_definitions: Iterable[DefinitionRecord] = (),
    ) -> None:
        self.namespace = namespace
        self.limits = limits
        self.cancelled = cancelled
        self.query_local = query_local
        self.expression_normalizer = ExpressionNormalizer(
            max_depth=limits.max_expression_depth,
            cancelled=cancelled,
        )
        self.records: dict[tuple[NormalizedFamily, bytes], _MutableRecord] = {}
        self.definitions: dict[DefinitionKey, _MutableDefinition] = {}
        self.seed_symbols: dict[DefinitionKey, owl.Class | owl.Datatype] = {}
        for definition in seed_definitions:
            kind = "class" if isinstance(definition.symbol, owl.Class) else "data"
            self.seed_symbols[(kind, definition.canonical_expression, definition.polarity)] = (
                definition.symbol
            )
        self.pending_definitions: deque[DefinitionKey] = deque()
        self.queued_definitions: set[DefinitionKey] = set()
        self.declared_entities: dict[bytes, owl.Entity] = {}
        self.reserved_signature_entities: dict[
            bytes,
            owl.Class | owl.Datatype,
        ] = {}
        self.source_count = 0
        self.ignored = 0
        self.requires_rebuild = False

    def checkpoint(self) -> None:
        if self.cancelled is not None and self.cancelled():
            raise ReasonerInterruptedError("ontology normalization cancelled")

    def add_record(
        self,
        family: NormalizedFamily,
        statement: NormalizedStatement,
        provenance: str,
        *,
        generated: bool = False,
        canonical_statement: bytes | None = None,
    ) -> None:
        encoded = statement_bytes(statement) if canonical_statement is None else canonical_statement
        if not isinstance(encoded, bytes) or not encoded:
            raise ValueError("canonical_statement must be nonempty bytes or None")
        key = (family, encoded)
        known = self.records.get(key)
        if known is None:
            observed = len(self.records) + 1
            if observed > self.limits.max_records:
                raise ResourceLimitError(
                    "normalized record limit exceeded",
                    limit="max_records",
                    observed=observed,
                    allowed=self.limits.max_records,
                )
            self.records[key] = _MutableRecord(
                family,
                statement,
                {provenance},
                generated,
            )
            return
        known.provenance.add(provenance)
        known.generated = known.generated or generated

    def atomize_class(
        self,
        expression: owl.ClassExpression,
        polarity: Polarity,
        provenance: str | tuple[str, ...],
    ) -> owl.ClassExpression:
        if _is_class_literal(expression):
            return expression
        return self._class_definition(expression, polarity, provenance)

    def atomize_data(
        self,
        data_range: owl.DataRange,
        polarity: Polarity,
        provenance: str | tuple[str, ...],
    ) -> owl.DataRange:
        if _is_data_literal(data_range):
            return data_range
        return self._data_definition(data_range, polarity, provenance)

    def _class_definition(
        self,
        expression: owl.ClassExpression,
        polarity: Polarity,
        provenance: str | tuple[str, ...],
    ) -> owl.Class:
        provenances = _provenance_values(provenance)
        encoded_expression = expression.canonical_bytes()
        key = ("class", encoded_expression, polarity)
        seeded = self.seed_symbols.get(key)
        if seeded is not None:
            if not isinstance(seeded, owl.Class):
                raise RuntimeError("seeded class definition has the wrong symbol sort")
            return seeded
        known = self.definitions.get(key)
        if known is not None:
            added = set(provenances).difference(known.provenance)
            if added:
                known.provenance.update(added)
                self._queue_definition(key)
            if not isinstance(known.symbol, owl.Class):
                raise RuntimeError("class definition has the wrong symbol sort")
            return known.symbol
        self._check_definition_limit()
        symbol = owl.Class(owl.IRI(self._generated_iri("class", encoded_expression, polarity)))
        definition = _MutableDefinition(
            symbol,
            expression,
            polarity,
            set(provenances),
            self.query_local,
        )
        self.definitions[key] = definition
        self._queue_definition(key)
        return symbol

    def _data_definition(
        self,
        data_range: owl.DataRange,
        polarity: Polarity,
        provenance: str | tuple[str, ...],
    ) -> owl.Datatype:
        provenances = _provenance_values(provenance)
        encoded_range = data_range.canonical_bytes()
        key = ("data", encoded_range, polarity)
        seeded = self.seed_symbols.get(key)
        if seeded is not None:
            if not isinstance(seeded, owl.Datatype):
                raise RuntimeError("seeded data definition has the wrong symbol sort")
            return seeded
        known = self.definitions.get(key)
        if known is not None:
            added = set(provenances).difference(known.provenance)
            if added:
                known.provenance.update(added)
                self._queue_definition(key)
            if not isinstance(known.symbol, owl.Datatype):
                raise RuntimeError("data definition has the wrong symbol sort")
            return known.symbol
        self._check_definition_limit()
        symbol = owl.Datatype(owl.IRI(self._generated_iri("data", encoded_range, polarity)))
        definition = _MutableDefinition(
            symbol,
            data_range,
            polarity,
            set(provenances),
            self.query_local,
        )
        self.definitions[key] = definition
        self._queue_definition(key)
        return symbol

    def _queue_definition(self, key: DefinitionKey) -> None:
        if key not in self.queued_definitions:
            self.queued_definitions.add(key)
            self.pending_definitions.append(key)

    def drain_definitions(self) -> None:
        """Finish queued definitions iteratively, never through Python recursion."""

        while self.pending_definitions:
            self.checkpoint()
            key = self.pending_definitions.popleft()
            self.queued_definitions.discard(key)
            definition = self.definitions[key]
            new_provenance = tuple(sorted(definition.provenance.difference(definition.propagated)))
            if not new_provenance:
                continue
            if key[0] == "class":
                if not isinstance(definition.symbol, owl.Class) or not isinstance(
                    definition.expression,
                    owl.CLASS_EXPRESSION_TYPES,
                ):
                    raise RuntimeError("queued class definition has invalid sorts")
                rewritten = self.rewrite_class_root(
                    cast(owl.ClassExpression, definition.expression),
                    definition.polarity,
                    new_provenance,
                )
                statement: NormalizedStatement = (
                    owl.SubClassOf(definition.symbol, rewritten)
                    if definition.polarity is Polarity.POSITIVE
                    else owl.SubClassOf(rewritten, definition.symbol)
                )
                family = NormalizedFamily.CLASS
            elif key[0] == "data":
                if not isinstance(definition.symbol, owl.Datatype) or not isinstance(
                    definition.expression,
                    owl.DATA_RANGE_TYPES,
                ):
                    raise RuntimeError("queued data definition has invalid sorts")
                rewritten_data = self.rewrite_data_root(
                    cast(owl.DataRange, definition.expression),
                    definition.polarity,
                    new_provenance,
                )
                statement = (
                    DataRangeInclusion(definition.symbol, rewritten_data)
                    if definition.polarity is Polarity.POSITIVE
                    else DataRangeInclusion(rewritten_data, definition.symbol)
                )
                family = NormalizedFamily.DATATYPE
            else:
                raise RuntimeError(f"unknown queued definition sort {key[0]!r}")
            if definition.statement is None:
                definition.statement = statement
            elif definition.statement != statement:
                raise RuntimeError("definition rewrite changed while propagating provenance")
            definition.propagated.update(new_provenance)
            for source in new_provenance:
                self.add_record(
                    family,
                    statement,
                    source,
                    generated=True,
                )

    def _check_definition_limit(self) -> None:
        observed = len(self.definitions) + 1
        if observed > self.limits.max_definitions:
            raise ResourceLimitError(
                "normalization definition limit exceeded",
                limit="max_definitions",
                observed=observed,
                allowed=self.limits.max_definitions,
            )

    def _generated_iri(
        self,
        kind: str,
        encoded_expression: bytes,
        polarity: Polarity,
    ) -> str:
        return _generated_definition_iri(
            self.namespace,
            kind,
            encoded_expression,
            polarity,
        )

    def rewrite_class_root(
        self,
        expression: owl.ClassExpression,
        polarity: Polarity,
        provenance: str | tuple[str, ...],
    ) -> owl.ClassExpression:
        constructor = type(expression)
        if _is_class_literal(expression) or constructor is owl.ObjectHasSelf:
            return expression
        if constructor is owl.ObjectComplementOf:
            complement = cast(owl.ObjectComplementOf, expression)
            operand = self.atomize_class(complement.operand, _opposite(polarity), provenance)
            return owl.ObjectComplementOf(operand)
        if constructor is owl.ObjectIntersectionOf:
            intersection = cast(owl.ObjectIntersectionOf, expression)
            return owl.ObjectIntersectionOf(
                owl.CanonicalSet(
                    self.atomize_class(item, polarity, provenance) for item in intersection.operands
                )
            )
        if constructor is owl.ObjectUnionOf:
            union = cast(owl.ObjectUnionOf, expression)
            return owl.ObjectUnionOf(
                owl.CanonicalSet(
                    self.atomize_class(item, polarity, provenance) for item in union.operands
                )
            )
        if constructor is owl.ObjectSomeValuesFrom:
            some = cast(owl.ObjectSomeValuesFrom, expression)
            return owl.ObjectSomeValuesFrom(
                some.property,
                self.atomize_class(some.filler, polarity, provenance),
            )
        if constructor is owl.ObjectAllValuesFrom:
            all_values = cast(owl.ObjectAllValuesFrom, expression)
            return owl.ObjectAllValuesFrom(
                all_values.property,
                self.atomize_class(all_values.filler, polarity, provenance),
            )
        if constructor is owl.ObjectMinCardinality:
            object_min = cast(owl.ObjectMinCardinality, expression)
            return owl.ObjectMinCardinality(
                object_min.cardinality,
                object_min.property,
                self.atomize_class(object_min.filler, polarity, provenance),
            )
        if constructor is owl.ObjectMaxCardinality:
            object_max = cast(owl.ObjectMaxCardinality, expression)
            return owl.ObjectMaxCardinality(
                object_max.cardinality,
                object_max.property,
                self.atomize_class(object_max.filler, _opposite(polarity), provenance),
            )
        if constructor is owl.DataSomeValuesFrom:
            data_some = cast(owl.DataSomeValuesFrom, expression)
            return owl.DataSomeValuesFrom(
                data_some.properties,
                self.atomize_data(data_some.filler, polarity, provenance),
            )
        if constructor is owl.DataAllValuesFrom:
            data_all = cast(owl.DataAllValuesFrom, expression)
            return owl.DataAllValuesFrom(
                data_all.properties,
                self.atomize_data(data_all.filler, polarity, provenance),
            )
        if constructor is owl.DataMinCardinality:
            data_min = cast(owl.DataMinCardinality, expression)
            return owl.DataMinCardinality(
                data_min.cardinality,
                data_min.property,
                self.atomize_data(data_min.filler, polarity, provenance),
            )
        if constructor is owl.DataMaxCardinality:
            data_max = cast(owl.DataMaxCardinality, expression)
            return owl.DataMaxCardinality(
                data_max.cardinality,
                data_max.property,
                self.atomize_data(data_max.filler, _opposite(polarity), provenance),
            )
        # Has-value and exact-cardinality constructs are eliminated by ExpressionNormalizer.
        renormalized = self.expression_normalizer.class_nnf(expression)
        if renormalized == expression:
            raise RuntimeError(f"unhandled normalized class root {constructor.__name__}")
        return self.rewrite_class_root(renormalized, polarity, provenance)

    def rewrite_data_root(
        self,
        data_range: owl.DataRange,
        polarity: Polarity,
        provenance: str | tuple[str, ...],
    ) -> owl.DataRange:
        constructor = type(data_range)
        if _is_data_literal(data_range):
            return data_range
        if constructor is owl.DataComplementOf:
            complement = cast(owl.DataComplementOf, data_range)
            operand = self.atomize_data(complement.operand, _opposite(polarity), provenance)
            return owl.DataComplementOf(operand)
        if constructor is owl.DataIntersectionOf:
            intersection = cast(owl.DataIntersectionOf, data_range)
            return owl.DataIntersectionOf(
                owl.CanonicalSet(
                    self.atomize_data(item, polarity, provenance) for item in intersection.operands
                )
            )
        if constructor is owl.DataUnionOf:
            union = cast(owl.DataUnionOf, data_range)
            return owl.DataUnionOf(
                owl.CanonicalSet(
                    self.atomize_data(item, polarity, provenance) for item in union.operands
                )
            )
        raise RuntimeError(f"unhandled normalized data root {constructor.__name__}")

    def freeze_ontology(self, logical_fingerprint: str) -> NormalizedOntology:
        generated = self._freeze_definitions()
        self._reject_generated_symbol_collisions(generated)
        return NormalizedOntology(
            logical_fingerprint=logical_fingerprint,
            records=self._freeze_records(),
            definitions=generated,
            declared_entities=tuple(
                self.declared_entities[key] for key in sorted(self.declared_entities)
            ),
            source_axiom_count=self.source_count,
            ignored_nonlogical_axiom_count=self.ignored,
            expression_steps=self.expression_normalizer.steps,
        )

    def freeze_query(
        self,
        permanent_digest: str,
        query_hash: str,
    ) -> NormalizedQuery:
        generated = self._freeze_definitions()
        self._reject_generated_symbol_collisions(generated)
        return NormalizedQuery(
            permanent_normalization_digest=permanent_digest,
            query_hash=query_hash,
            records=self._freeze_records(),
            definitions=generated,
            requires_rebuild=self.requires_rebuild,
            source_axiom_count=self.source_count,
            expression_steps=self.expression_normalizer.steps,
        )

    def _reject_generated_symbol_collisions(
        self,
        definitions: tuple[DefinitionRecord, ...],
    ) -> None:
        collision = next(
            (
                value.symbol
                for value in definitions
                if value.symbol.canonical_bytes() in self.reserved_signature_entities
            ),
            None,
        )
        if collision is not None:
            raise ValueError(
                "generated definition symbol collides with the source signature: "
                f"{collision.iri.value}"
            )

    def _freeze_records(self) -> tuple[NormalizedRecord, ...]:
        return tuple(
            _record_from_trusted_canonical(
                value.family,
                value.statement,
                tuple(value.provenance),
                value.generated,
                key[1],
            )
            for key, value in sorted(
                self.records.items(),
                key=lambda item: (item[0][0].value, item[0][1]),
            )
        )

    def _freeze_definitions(self) -> tuple[DefinitionRecord, ...]:
        keyed = (
            (
                value.symbol.canonical_bytes(),
                value.polarity.value,
                key[1],
                _definition_from_trusted_canonical(
                    value.symbol,
                    value.expression,
                    value.polarity,
                    tuple(value.provenance),
                    value.query_local,
                    key[1],
                ),
            )
            for key, value in self.definitions.items()
        )
        return tuple(item[3] for item in sorted(keyed, key=lambda item: item[:3]))


def normalize_view(
    view: OntologyView,
    *,
    limits: NormalizationLimits | None = None,
    cancelled: Callable[[], bool] | None = None,
) -> NormalizedOntology:
    """Normalize one complete core view by direct closure iteration."""

    if not isinstance(view, OntologyView):
        raise TypeError("view must implement pyowl_core OntologyView")
    if not view.is_complete:
        raise ValueError("normalization requires a complete ontology view")
    for extension in view.iter_extensions(scope=AxiomScope.CLOSURE):
        raise UnsupportedNormalizationError(
            f"extension constructor {type(extension).__name__} is outside OWL 2 DL normalization"
        )
    return normalize_axioms(
        cast(Iterable[owl.AxiomNode], view.iter_axioms(scope=AxiomScope.CLOSURE)),
        logical_fingerprint=view.logical_fingerprint.hex,
        limits=limits,
        cancelled=cancelled,
    )


def normalize_axioms(
    axioms: Iterable[owl.AxiomNode],
    *,
    logical_fingerprint: str,
    limits: NormalizationLimits | None = None,
    cancelled: Callable[[], bool] | None = None,
) -> NormalizedOntology:
    """Normalize a logical closure with an explicit authoritative core fingerprint."""

    _validate_digest(logical_fingerprint, "logical_fingerprint")
    selected_limits = _validate_options(limits, cancelled)
    state = _NormalizationState(
        logical_fingerprint,
        selected_limits,
        cancelled,
        query_local=False,
    )
    try:
        _consume(state, axioms)
    except ExpressionNormalizationCancelled as error:
        raise ReasonerInterruptedError("ontology normalization cancelled") from error
    except ExpressionDepthError as error:
        raise ResourceLimitError(
            "normalization expression depth limit exceeded",
            limit="max_expression_depth",
            observed=error.observed,
            allowed=error.allowed,
        ) from error
    return state.freeze_ontology(logical_fingerprint)


def normalize_query(
    permanent: NormalizedOntology,
    axioms: Iterable[owl.AxiomNode],
    *,
    limits: NormalizationLimits | None = None,
    cancelled: Callable[[], bool] | None = None,
) -> NormalizedQuery:
    """Normalize query-local axioms without mutating permanent records or symbols."""

    if not isinstance(permanent, NormalizedOntology):
        raise TypeError("permanent must be NormalizedOntology")
    selected_limits = _validate_options(limits, cancelled)
    values = _collect_query_axioms(
        axioms,
        limits=selected_limits,
        cancelled=cancelled,
    )
    query_hash = _query_hash(values)
    permanent_digest = permanent.digest
    namespace = _query_definition_namespace(permanent_digest, query_hash)
    state = _NormalizationState(
        namespace,
        selected_limits,
        cancelled,
        query_local=True,
        seed_definitions=permanent.definitions,
    )
    try:
        _consume(state, values, query=True)
    except ExpressionNormalizationCancelled as error:
        raise ReasonerInterruptedError("query normalization cancelled") from error
    except ExpressionDepthError as error:
        raise ResourceLimitError(
            "query normalization expression depth limit exceeded",
            limit="max_expression_depth",
            observed=error.observed,
            allowed=error.allowed,
        ) from error
    return state.freeze_query(permanent_digest, query_hash)


def _collect_query_axioms(
    axioms: Iterable[owl.AxiomNode],
    *,
    limits: NormalizationLimits,
    cancelled: Callable[[], bool] | None,
) -> tuple[owl.AxiomNode, ...]:
    values: list[owl.AxiomNode] = []
    for axiom in axioms:
        if cancelled is not None and cancelled():
            raise ReasonerInterruptedError("query normalization cancelled")
        if not isinstance(axiom, owl.AxiomNode):
            raise TypeError("axioms must contain pyowl_core AxiomNode values")
        if type(axiom) not in AXIOM_HANDLER_TABLE:
            raise UnknownAxiomError(f"unhandled axiom constructor: {type(axiom).__name__}")
        observed = len(values) + 1
        if observed > limits.max_source_axioms:
            raise ResourceLimitError(
                "normalization source axiom limit exceeded",
                limit="max_source_axioms",
                observed=observed,
                allowed=limits.max_source_axioms,
            )
        values.append(axiom)
    return tuple(values)


def _validate_options(
    limits: NormalizationLimits | None,
    cancelled: Callable[[], bool] | None,
) -> NormalizationLimits:
    if limits is not None and not isinstance(limits, NormalizationLimits):
        raise TypeError("limits must be NormalizationLimits or None")
    if cancelled is not None and not callable(cancelled):
        raise TypeError("cancelled must be callable or None")
    return limits or NormalizationLimits()


def _consume(
    state: _NormalizationState,
    axioms: Iterable[owl.AxiomNode],
    *,
    query: bool = False,
) -> None:
    for axiom in axioms:
        state.checkpoint()
        if not isinstance(axiom, owl.AxiomNode):
            raise TypeError("axioms must contain pyowl_core AxiomNode values")
        handler = AXIOM_HANDLER_TABLE.get(type(axiom))
        if handler is None:
            raise UnknownAxiomError(f"unhandled axiom constructor: {type(axiom).__name__}")
        state.source_count += 1
        if state.source_count > state.limits.max_source_axioms:
            raise ResourceLimitError(
                "normalization source axiom limit exceeded",
                limit="max_source_axioms",
                observed=state.source_count,
                allowed=state.limits.max_source_axioms,
            )
        encoded_axiom = axiom.canonical_bytes()
        if _GENERATED_NAMESPACE_BYTES in encoded_axiom:
            for node in owl.walk(axiom):
                if isinstance(node, (owl.Class, owl.Datatype)) and node.iri.value.startswith(
                    _GENERATED_DEFINITION_NAMESPACE
                ):
                    state.reserved_signature_entities[node.canonical_bytes()] = node
        provenance = hashlib.sha256(encoded_axiom).hexdigest()
        if query and _query_requires_rebuild(axiom, handler):
            state.requires_rebuild = True
        _dispatch(state, handler, axiom, provenance, encoded_axiom)
    state.drain_definitions()


def _dispatch(
    state: _NormalizationState,
    handler: _Handler,
    axiom: owl.AxiomNode,
    provenance: str,
    encoded_axiom: bytes,
) -> None:
    if handler == _DECLARATION:
        declaration = cast(owl.Declaration, axiom)
        state.declared_entities[declaration.entity.canonical_bytes()] = declaration.entity
        state.ignored += 1
        return
    if handler == _ANNOTATION:
        state.ignored += 1
        return
    if handler == _SUBCLASS:
        subclass = cast(owl.SubClassOf, axiom)
        _add_subclass(
            state,
            subclass.sub_class,
            subclass.super_class,
            provenance,
            source_statement=(encoded_axiom if not subclass.annotations else None),
        )
        return
    if handler == _EQUIVALENT_CLASSES:
        equivalent_classes = cast(owl.EquivalentClasses, axiom)
        expressions = tuple(equivalent_classes.expressions)
        for index, expression in enumerate(expressions):
            _add_subclass(
                state,
                expression,
                expressions[(index + 1) % len(expressions)],
                provenance,
            )
        return
    if handler == _DISJOINT_CLASSES:
        disjoint_classes = cast(owl.DisjointClasses, axiom)
        _add_disjoint_classes(state, tuple(disjoint_classes.expressions), provenance)
        return
    if handler == _DISJOINT_UNION:
        disjoint_union = cast(owl.DisjointUnion, axiom)
        expressions = tuple(disjoint_union.expressions)
        _add_subclass(
            state,
            disjoint_union.defined_class,
            owl.ObjectUnionOf(owl.CanonicalSet(expressions)),
            provenance,
        )
        for expression in expressions:
            _add_subclass(state, expression, disjoint_union.defined_class, provenance)
        _add_disjoint_classes(state, expressions, provenance)
        return
    if handler == _SUB_OBJECT:
        sub_object = cast(owl.SubObjectPropertyOf, axiom)
        state.add_record(
            NormalizedFamily.OBJECT_PROPERTY,
            owl.SubObjectPropertyOf(sub_object.sub_property, sub_object.super_property),
            provenance,
        )
        return
    if handler == _EQUIVALENT_OBJECT:
        equivalent_object = cast(owl.EquivalentObjectProperties, axiom)
        statement: NormalizedStatement = owl.EquivalentObjectProperties(
            equivalent_object.properties
        )
        state.add_record(NormalizedFamily.OBJECT_PROPERTY, statement, provenance)
        return
    if handler == _DISJOINT_OBJECT:
        disjoint_object = cast(owl.DisjointObjectProperties, axiom)
        statement = owl.DisjointObjectProperties(disjoint_object.properties)
        state.add_record(NormalizedFamily.OBJECT_PROPERTY, statement, provenance)
        return
    if handler == _INVERSE_OBJECT:
        inverse_object = cast(owl.InverseObjectProperties, axiom)
        statement = owl.InverseObjectProperties(inverse_object.first, inverse_object.second)
        state.add_record(NormalizedFamily.OBJECT_PROPERTY, statement, provenance)
        return
    if handler == _OBJECT_DOMAIN:
        object_domain = cast(owl.ObjectPropertyDomain, axiom)
        domain = state.expression_normalizer.class_nnf(object_domain.domain)
        domain = state.atomize_class(domain, Polarity.POSITIVE, provenance)
        state.add_record(
            NormalizedFamily.OBJECT_PROPERTY,
            owl.ObjectPropertyDomain(object_domain.property, domain),
            provenance,
        )
        return
    if handler == _OBJECT_RANGE:
        object_range = cast(owl.ObjectPropertyRange, axiom)
        range_expression = state.expression_normalizer.class_nnf(object_range.range)
        range_expression = state.atomize_class(
            range_expression,
            Polarity.POSITIVE,
            provenance,
        )
        state.add_record(
            NormalizedFamily.OBJECT_PROPERTY,
            owl.ObjectPropertyRange(object_range.property, range_expression),
            provenance,
        )
        return
    if handler == _FUNCTIONAL_OBJECT:
        functional_object = cast(owl.FunctionalObjectProperty, axiom)
        statement = owl.FunctionalObjectProperty(functional_object.property)
        state.add_record(NormalizedFamily.OBJECT_PROPERTY, statement, provenance)
        return
    if handler == _INVERSE_FUNCTIONAL_OBJECT:
        inverse_functional = cast(owl.InverseFunctionalObjectProperty, axiom)
        statement = owl.InverseFunctionalObjectProperty(inverse_functional.property)
        state.add_record(NormalizedFamily.OBJECT_PROPERTY, statement, provenance)
        return
    if handler == _REFLEXIVE_OBJECT:
        reflexive = cast(owl.ReflexiveObjectProperty, axiom)
        statement = owl.ReflexiveObjectProperty(reflexive.property)
        state.add_record(NormalizedFamily.OBJECT_PROPERTY, statement, provenance)
        return
    if handler == _IRREFLEXIVE_OBJECT:
        irreflexive = cast(owl.IrreflexiveObjectProperty, axiom)
        statement = owl.IrreflexiveObjectProperty(irreflexive.property)
        state.add_record(NormalizedFamily.OBJECT_PROPERTY, statement, provenance)
        return
    if handler == _SYMMETRIC_OBJECT:
        symmetric = cast(owl.SymmetricObjectProperty, axiom)
        statement = owl.SymmetricObjectProperty(symmetric.property)
        state.add_record(NormalizedFamily.OBJECT_PROPERTY, statement, provenance)
        return
    if handler == _ASYMMETRIC_OBJECT:
        asymmetric = cast(owl.AsymmetricObjectProperty, axiom)
        statement = owl.AsymmetricObjectProperty(asymmetric.property)
        state.add_record(NormalizedFamily.OBJECT_PROPERTY, statement, provenance)
        return
    if handler == _TRANSITIVE_OBJECT:
        transitive = cast(owl.TransitiveObjectProperty, axiom)
        statement = owl.TransitiveObjectProperty(transitive.property)
        state.add_record(NormalizedFamily.OBJECT_PROPERTY, statement, provenance)
        return
    if handler == _SUB_DATA:
        sub_data = cast(owl.SubDataPropertyOf, axiom)
        statement = owl.SubDataPropertyOf(sub_data.sub_property, sub_data.super_property)
        state.add_record(NormalizedFamily.DATA_PROPERTY, statement, provenance)
        return
    if handler == _EQUIVALENT_DATA:
        equivalent_data = cast(owl.EquivalentDataProperties, axiom)
        statement = owl.EquivalentDataProperties(equivalent_data.properties)
        state.add_record(NormalizedFamily.DATA_PROPERTY, statement, provenance)
        return
    if handler == _DISJOINT_DATA:
        disjoint_data = cast(owl.DisjointDataProperties, axiom)
        statement = owl.DisjointDataProperties(disjoint_data.properties)
        state.add_record(NormalizedFamily.DATA_PROPERTY, statement, provenance)
        return
    if handler == _DATA_DOMAIN:
        data_domain = cast(owl.DataPropertyDomain, axiom)
        domain = state.expression_normalizer.class_nnf(data_domain.domain)
        domain = state.atomize_class(domain, Polarity.POSITIVE, provenance)
        state.add_record(
            NormalizedFamily.DATA_PROPERTY,
            owl.DataPropertyDomain(data_domain.property, domain),
            provenance,
        )
        return
    if handler == _DATA_RANGE:
        data_property_range = cast(owl.DataPropertyRange, axiom)
        data_range = state.expression_normalizer.data_nnf(data_property_range.range)
        data_range = state.atomize_data(data_range, Polarity.POSITIVE, provenance)
        state.add_record(
            NormalizedFamily.DATA_PROPERTY,
            owl.DataPropertyRange(data_property_range.property, data_range),
            provenance,
        )
        return
    if handler == _FUNCTIONAL_DATA:
        functional_data = cast(owl.FunctionalDataProperty, axiom)
        statement = owl.FunctionalDataProperty(functional_data.property)
        state.add_record(NormalizedFamily.DATA_PROPERTY, statement, provenance)
        return
    if handler == _DATATYPE_DEFINITION:
        datatype_definition = cast(owl.DatatypeDefinition, axiom)
        data_range = state.expression_normalizer.data_nnf(datatype_definition.data_range)
        state.add_record(
            NormalizedFamily.DATATYPE,
            owl.DatatypeDefinition(datatype_definition.datatype, data_range),
            provenance,
        )
        return
    if handler == _HAS_KEY:
        has_key = cast(owl.HasKey, axiom)
        class_expression = state.expression_normalizer.class_nnf(has_key.class_expression)
        class_expression = state.atomize_class(
            class_expression,
            Polarity.NEGATIVE,
            provenance,
        )
        state.add_record(
            NormalizedFamily.KEY,
            owl.HasKey(
                class_expression,
                has_key.object_properties,
                has_key.data_properties,
            ),
            provenance,
        )
        return
    if handler == _SAME:
        same = cast(owl.SameIndividual, axiom)
        state.add_record(
            NormalizedFamily.ASSERTION,
            owl.SameIndividual(same.individuals),
            provenance,
        )
        return
    if handler == _DIFFERENT:
        different = cast(owl.DifferentIndividuals, axiom)
        state.add_record(
            NormalizedFamily.ASSERTION,
            owl.DifferentIndividuals(different.individuals),
            provenance,
        )
        return
    if handler == _CLASS_ASSERTION:
        class_assertion = cast(owl.ClassAssertion, axiom)
        expression = state.expression_normalizer.class_nnf(class_assertion.class_expression)
        expression = state.atomize_class(expression, Polarity.POSITIVE, provenance)
        state.add_record(
            NormalizedFamily.ASSERTION,
            owl.ClassAssertion(expression, class_assertion.individual),
            provenance,
        )
        return
    if handler in {_OBJECT_ASSERTION, _NEGATIVE_OBJECT_ASSERTION}:
        object_assertion = cast(
            owl.ObjectPropertyAssertion | owl.NegativeObjectPropertyAssertion,
            axiom,
        )
        property, source, target = _forward_assertion(
            object_assertion.property,
            object_assertion.source,
            object_assertion.target,
        )
        statement = (
            owl.ObjectPropertyAssertion(property, source, target)
            if handler == _OBJECT_ASSERTION
            else owl.NegativeObjectPropertyAssertion(property, source, target)
        )
        state.add_record(NormalizedFamily.ASSERTION, statement, provenance)
        return
    if handler == _DATA_ASSERTION:
        data_assertion = cast(owl.DataPropertyAssertion, axiom)
        state.add_record(
            NormalizedFamily.ASSERTION,
            owl.DataPropertyAssertion(
                data_assertion.property,
                data_assertion.source,
                data_assertion.value,
            ),
            provenance,
        )
        return
    if handler == _NEGATIVE_DATA_ASSERTION:
        negative_data_assertion = cast(owl.NegativeDataPropertyAssertion, axiom)
        state.add_record(
            NormalizedFamily.ASSERTION,
            owl.NegativeDataPropertyAssertion(
                negative_data_assertion.property,
                negative_data_assertion.source,
                negative_data_assertion.value,
            ),
            provenance,
        )
        return
    raise RuntimeError(f"known handler {handler!r} has no normalization implementation")


def _add_subclass(
    state: _NormalizationState,
    sub_class: owl.ClassExpression,
    super_class: owl.ClassExpression,
    provenance: str,
    *,
    source_statement: bytes | None = None,
) -> None:
    left = state.expression_normalizer.class_nnf(sub_class)
    right = state.expression_normalizer.class_nnf(super_class)
    left = state.atomize_class(left, Polarity.NEGATIVE, provenance)
    right = state.atomize_class(right, Polarity.POSITIVE, provenance)
    if _is_nothing(left) or _is_thing(right) or _same_class_expression(left, right):
        return
    state.add_record(
        NormalizedFamily.CLASS,
        owl.SubClassOf(left, right),
        provenance,
        canonical_statement=(
            source_statement if left is sub_class and right is super_class else None
        ),
    )


def _add_disjoint_classes(
    state: _NormalizationState,
    expressions: tuple[owl.ClassExpression, ...],
    provenance: str,
) -> None:
    atoms: dict[bytes, owl.ClassExpression] = {}
    forced_empty: set[bytes] = set()
    for expression in expressions:
        normalized = state.expression_normalizer.class_nnf(expression)
        atom = state.atomize_class(normalized, Polarity.NEGATIVE, provenance)
        if _is_nothing(atom):
            continue
        key = atom.canonical_bytes()
        if key in atoms:
            _add_subclass(state, atom, owl.OWL_NOTHING, provenance)
            forced_empty.add(key)
        else:
            atoms[key] = atom

    live = {key: value for key, value in atoms.items() if key not in forced_empty}
    top_key = next((key for key, value in live.items() if _is_thing(value)), None)
    if top_key is not None:
        for key, value in live.items():
            if key != top_key:
                _add_subclass(state, value, owl.OWL_NOTHING, provenance)
        return
    if len(live) >= 2:
        state.add_record(
            NormalizedFamily.CLASS,
            owl.DisjointClasses(owl.CanonicalSet(live.values())),
            provenance,
        )


def _forward_assertion(
    property: owl.ObjectPropertyExpression,
    source: owl.Individual,
    target: owl.Individual,
) -> tuple[owl.ObjectProperty, owl.Individual, owl.Individual]:
    if isinstance(property, owl.ObjectInverseOf):
        return (property.property, target, source)
    return (property, source, target)


def _query_requires_rebuild(axiom: owl.AxiomNode, handler: _Handler) -> bool:
    if handler in _QUERY_ALWAYS_REBUILD_HANDLERS:
        return True
    if handler not in _QUERY_OVERLAY_SAFE_HANDLERS:
        raise RuntimeError(f"unclassified query handler {handler!r}")
    return any(isinstance(node, _QUERY_STRATEGY_SENSITIVE_TYPES) for node in owl.walk(axiom))


def _query_hash(axioms: tuple[owl.AxiomNode, ...]) -> str:
    fingerprint = logical_fingerprint(axioms, ())
    return hashlib.sha256(b"pyhermit:normalized-query:v1\x00" + fingerprint.digest).hexdigest()


def _is_class_literal(expression: owl.ClassExpression) -> bool:
    if isinstance(expression, (owl.Class, owl.ObjectOneOf)):
        return True
    return isinstance(expression, owl.ObjectComplementOf) and isinstance(
        expression.operand,
        (owl.Class, owl.ObjectOneOf),
    )


def _is_data_literal(data_range: owl.DataRange) -> bool:
    if isinstance(data_range, (owl.Datatype, owl.DatatypeRestriction, owl.DataOneOf)):
        return True
    return isinstance(data_range, owl.DataComplementOf) and isinstance(
        data_range.operand,
        (owl.Datatype, owl.DatatypeRestriction, owl.DataOneOf),
    )


def _is_thing(expression: owl.ClassExpression) -> bool:
    return isinstance(expression, owl.Class) and expression.iri.value == owl.OWL_THING.iri.value


def _is_nothing(expression: owl.ClassExpression) -> bool:
    return isinstance(expression, owl.Class) and expression.iri.value == owl.OWL_NOTHING.iri.value


def _same_class_expression(
    first: owl.ClassExpression,
    second: owl.ClassExpression,
) -> bool:
    if first is second:
        return True
    if isinstance(first, owl.Class) and isinstance(second, owl.Class):
        return first.iri.value == second.iri.value
    return first == second


def _opposite(polarity: Polarity) -> Polarity:
    return Polarity.NEGATIVE if polarity is Polarity.POSITIVE else Polarity.POSITIVE


def _provenance_values(value: str | tuple[str, ...]) -> tuple[str, ...]:
    return (value,) if isinstance(value, str) else value


def _validate_digest(value: str, name: str) -> None:
    if not isinstance(value, str) or _SHA256.fullmatch(value) is None:
        raise ValueError(f"{name} must be lowercase SHA-256 hex")


__all__ = [
    "AXIOM_HANDLER_TABLE",
    "NormalizationLimits",
    "UnknownAxiomError",
    "UnsupportedNormalizationError",
    "normalize_axioms",
    "normalize_query",
    "normalize_view",
]
