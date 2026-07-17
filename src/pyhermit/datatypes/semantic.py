"""Canonical backend-consumable datatype semantic payloads.

SPDX-License-Identifier: LGPL-3.0-or-later

The clause and backend boundary must carry datatype semantics, not hashes of private
Python objects.  This module freezes compiled literal identities/comparisons and OWL
data-range expressions into a small versioned JSON vocabulary.  Decoding reconstructs
the already compiled semantic records; it never reparses a literal lexical form.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, TypeVar, cast

import pyowl_core.model as owl

from pyhermit.events import CancellationToken
from pyhermit.exceptions import (
    OntologyProfileError,
    ResourceLimitError,
    UnsupportedDatatypeError,
)

from .facets import FacetRestriction, restrict_datatype
from .ieee754 import comparison_from_identity as ieee_comparison_from_identity
from .literals import SUPPORTED_DATATYPES, compile_literal
from .model import (
    BinaryComparison,
    BinaryIdentity,
    BinaryKind,
    BooleanComparison,
    BooleanIdentity,
    ComparisonValue,
    CompiledLiteral,
    DataIdentity,
    DatatypeLimits,
    DateTimeComparison,
    DateTimeIdentity,
    IEEECategory,
    IEEEComparison,
    IEEEFormat,
    IEEEIdentity,
    LexicalCompatibility,
    NumericComparison,
    NumericIdentity,
    SourceLiteralIdentity,
    StringComparison,
    StringIdentity,
    URIComparison,
    URIIdentity,
    XMLComparison,
    XMLIdentity,
)
from .ranges import DatatypeRange, range_for_datatype

DATATYPE_SEMANTIC_SCHEMA_VERSION: Final = 1
_INTEGER_TOKEN: Final = re.compile(r"[+-](?:0|[1-9a-f][0-9a-f]*)\Z")
_LOWER_HEX: Final = re.compile(r"(?:[0-9a-f]{2})*\Z")
_IEEE_HEX: Final = re.compile(r"[0-9a-f]+\Z")

PayloadScalar: TypeAlias = str | int | bool | None
TaggedSemanticValue: TypeAlias = tuple[PayloadScalar, ...]
_EnumT = TypeVar("_EnumT", bound=Enum)


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class DataRangePayloadKind(_StringEnum):
    """Closed language-neutral data-range expression vocabulary."""

    DATATYPE = "datatype"
    OPAQUE = "opaque"
    RESTRICTION = "restriction"
    INTERSECTION = "intersection"
    UNION = "union"
    COMPLEMENT = "complement"
    ENUMERATION = "enumeration"


def _canonical_json(payload: object) -> bytes:
    return json.dumps(
        payload,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")


def _digest(payload: object) -> str:
    return hashlib.sha256(_canonical_json(payload)).hexdigest()


def _integer_from_token(value: object, name: str) -> int:
    if not isinstance(value, str) or _INTEGER_TOKEN.fullmatch(value) is None:
        raise ValueError(f"{name} must be a canonical signed hexadecimal integer")
    sign = -1 if value[0] == "-" else 1
    return sign * int(value[1:], 16)


def _tagged(value: object, name: str) -> TaggedSemanticValue:
    sequence = _sequence(value, name)
    output: list[PayloadScalar] = []
    for item in sequence:
        if item is not None and not isinstance(item, (str, int, bool)):
            raise TypeError(f"{name} contains a non-scalar field")
        output.append(item)
    if not output or not isinstance(output[0], str):
        raise ValueError(f"{name} must start with a string tag")
    return tuple(output)


def _canonical_tagged(value: DataIdentity | ComparisonValue) -> TaggedSemanticValue:
    return cast(TaggedSemanticValue, value.as_tagged())


def data_identity_from_tagged(tagged: TaggedSemanticValue | Sequence[object]) -> DataIdentity:
    """Decode one exact data-identity token without consulting its lexical source."""

    fields = _tagged(tagged, "data_identity")
    tag = fields[0]
    identity: DataIdentity
    if tag == "numeric-rational-hex-v1" and len(fields) == 3:
        identity = NumericIdentity(
            _integer_from_token(fields[1], "numeric numerator"),
            _integer_from_token(fields[2], "numeric denominator"),
        )
    elif tag == "boolean" and len(fields) == 2 and isinstance(fields[1], bool):
        identity = BooleanIdentity(fields[1])
    elif tag == "ieee-identity-v1" and len(fields) == 3:
        format_ = _enum(IEEEFormat, fields[1], "IEEE format")
        bits = fields[2]
        if not isinstance(bits, str) or _IEEE_HEX.fullmatch(bits) is None:
            raise ValueError("IEEE bits must be lowercase hexadecimal")
        identity = IEEEIdentity(format_, int(bits, 16))
    elif tag == "plain-string-v1" and len(fields) == 3:
        identity = StringIdentity(
            _string(fields[1], "string text"),
            _optional_string(fields[2], "string language"),
        )
    elif tag == "binary-identity-v1" and len(fields) == 3:
        kind = _enum(BinaryKind, fields[1], "binary kind")
        octets = fields[2]
        if not isinstance(octets, str) or _LOWER_HEX.fullmatch(octets) is None:
            raise ValueError("binary octets must be canonical lowercase hexadecimal")
        identity = BinaryIdentity(kind, bytes.fromhex(octets))
    elif tag == "any-uri-v1" and len(fields) == 2:
        identity = URIIdentity(_string(fields[1], "URI value"))
    elif tag == "xml-literal-c14n-v1" and len(fields) == 2:
        identity = XMLIdentity(_string(fields[1], "canonical XML"))
    elif tag == "date-time-identity-v1" and len(fields) == 5:
        offset = _optional_integer(fields[3], "date/time offset")
        end_of_day = fields[4]
        if not isinstance(end_of_day, bool):
            raise TypeError("date/time end-of-day flag must be bool")
        identity = DateTimeIdentity(
            _integer_from_token(fields[1], "date/time numerator"),
            _integer_from_token(fields[2], "date/time denominator"),
            offset,
            end_of_day,
        )
    else:
        raise ValueError(f"unknown or malformed data-identity tag {tag!r}")
    if _canonical_tagged(identity) != fields:
        raise ValueError("data-identity payload is not canonical")
    return identity


def comparison_from_tagged(
    tagged: TaggedSemanticValue | Sequence[object],
) -> ComparisonValue:
    """Decode one facet-comparison token without host numeric/date coercion."""

    fields = _tagged(tagged, "comparison")
    tag = fields[0]
    comparison: ComparisonValue
    if tag == "ordered-numeric-rational-hex-v1" and len(fields) == 3:
        comparison = NumericComparison(
            _integer_from_token(fields[1], "numeric comparison numerator"),
            _integer_from_token(fields[2], "numeric comparison denominator"),
        )
    elif tag == "boolean-equality" and len(fields) == 2 and isinstance(fields[1], bool):
        comparison = BooleanComparison(fields[1])
    elif tag == "ieee-comparison-v1" and len(fields) == 5:
        comparison = IEEEComparison(
            _enum(IEEEFormat, fields[1], "IEEE format"),
            _enum(IEEECategory, fields[2], "IEEE category"),
            _integer_from_token(fields[3], "IEEE numerator"),
            _integer_from_token(fields[4], "IEEE denominator"),
        )
    elif tag == "plain-string-comparison-v1" and len(fields) == 3:
        comparison = StringComparison(
            _string(fields[1], "string comparison text"),
            _optional_string(fields[2], "string comparison language"),
        )
    elif tag == "binary-comparison-v1" and len(fields) == 3:
        kind = _enum(BinaryKind, fields[1], "binary kind")
        octets = fields[2]
        if not isinstance(octets, str) or _LOWER_HEX.fullmatch(octets) is None:
            raise ValueError("binary octets must be canonical lowercase hexadecimal")
        comparison = BinaryComparison(kind, bytes.fromhex(octets))
    elif tag == "any-uri-comparison-v1" and len(fields) == 2:
        comparison = URIComparison(_string(fields[1], "URI comparison value"))
    elif tag == "xml-literal-comparison-v1" and len(fields) == 2:
        comparison = XMLComparison(_string(fields[1], "XML comparison value"))
    elif tag == "date-time-comparison-v1" and len(fields) == 4:
        comparison = DateTimeComparison(
            _integer_from_token(fields[1], "date/time comparison numerator"),
            _integer_from_token(fields[2], "date/time comparison denominator"),
            _optional_integer(fields[3], "date/time comparison offset"),
        )
    else:
        raise ValueError(f"unknown or malformed comparison tag {tag!r}")
    if _canonical_tagged(comparison) != fields:
        raise ValueError("comparison payload is not canonical")
    return comparison


@dataclass(frozen=True, slots=True)
class LiteralSemanticPayload:
    """Source-preserving literal plus executable identity/comparison semantics."""

    lexical_form: str
    datatype_iri: str
    language: str | None
    data_identity: TaggedSemanticValue
    comparison: TaggedSemanticValue
    compatibility: LexicalCompatibility
    schema_version: int = DATATYPE_SEMANTIC_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _schema(self.schema_version)
        if not isinstance(self.lexical_form, str):
            raise TypeError("lexical_form must be str")
        if not isinstance(self.datatype_iri, str) or not self.datatype_iri:
            raise ValueError("datatype_iri must be a nonempty string")
        if self.language is not None and (not isinstance(self.language, str) or not self.language):
            raise ValueError("language must be a nonempty string or None")
        source = owl.Literal(
            self.lexical_form,
            owl.Datatype(owl.IRI(self.datatype_iri)),
            self.language,
        )
        if source.language != self.language:
            raise ValueError("literal payload language spelling is not canonical")
        identity_fields = _tagged(self.data_identity, "data_identity")
        comparison_fields = _tagged(self.comparison, "comparison")
        identity = data_identity_from_tagged(identity_fields)
        comparison = comparison_from_tagged(comparison_fields)
        _require_matching_pair(identity, comparison)
        if not isinstance(self.compatibility, LexicalCompatibility):
            raise TypeError("compatibility must be LexicalCompatibility")
        object.__setattr__(self, "data_identity", identity_fields)
        object.__setattr__(self, "comparison", comparison_fields)

    @classmethod
    def from_compiled(cls, value: CompiledLiteral) -> LiteralSemanticPayload:
        if not isinstance(value, CompiledLiteral):
            raise TypeError("value must be CompiledLiteral")
        source = value.source_identity
        return cls(
            source.lexical_form,
            source.datatype_iri,
            source.language,
            _canonical_tagged(value.data_identity),
            _canonical_tagged(value.comparison),
            value.compatibility,
        )

    def to_compiled(self) -> CompiledLiteral:
        """Reconstruct semantic records without validating the lexical form again."""

        source = owl.Literal(
            self.lexical_form,
            owl.Datatype(owl.IRI(self.datatype_iri)),
            self.language,
        )
        return CompiledLiteral(
            source,
            SourceLiteralIdentity.from_literal(source),
            data_identity_from_tagged(self.data_identity),
            comparison_from_tagged(self.comparison),
            self.compatibility,
        )

    def to_payload(self) -> dict[str, object]:
        return {
            "comparison": self.comparison,
            "compatibility": self.compatibility.value,
            "data_identity": self.data_identity,
            "datatype_iri": self.datatype_iri,
            "language": self.language,
            "lexical_form": self.lexical_form,
            "record": "literal_semantic",
            "schema_version": self.schema_version,
        }

    def canonical_bytes(self) -> bytes:
        return _canonical_json(self.to_payload())

    def canonical_digest(self) -> str:
        return _digest(self.to_payload())


@dataclass(frozen=True, slots=True)
class OpaqueLiteralSemanticPayload:
    """Source-specific token for a literal whose datatype has no value map.

    This is intentionally *not* a :class:`DataIdentity`: treating two unsupported
    lexical forms as equal, different, or ordered would invent OWL semantics.  It keeps
    dense source-literal tables canonical until the configured unknown-datatype policy
    decides whether evaluation is permitted.
    """

    lexical_form: str
    datatype_iri: str
    language: str | None
    compatibility: LexicalCompatibility
    schema_version: int = DATATYPE_SEMANTIC_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _schema(self.schema_version)
        if not isinstance(self.lexical_form, str):
            raise TypeError("lexical_form must be str")
        if not isinstance(self.datatype_iri, str) or not self.datatype_iri:
            raise ValueError("datatype_iri must be a nonempty string")
        source = owl.Literal(
            self.lexical_form,
            owl.Datatype(owl.IRI(self.datatype_iri)),
            self.language,
        )
        if source.language != self.language:
            raise ValueError("literal payload language spelling is not canonical")
        if not isinstance(self.compatibility, LexicalCompatibility):
            raise TypeError("compatibility must be LexicalCompatibility")

    @property
    def opaque_identity(self) -> tuple[str, str, str, str | None]:
        """Return a source-specific token without claiming data-value equality."""

        return (
            "opaque-source-literal-v1",
            self.lexical_form,
            self.datatype_iri,
            self.language,
        )

    def source_literal(self) -> owl.Literal:
        return owl.Literal(
            self.lexical_form,
            owl.Datatype(owl.IRI(self.datatype_iri)),
            self.language,
        )

    def to_payload(self) -> dict[str, object]:
        return {
            "compatibility": self.compatibility.value,
            "datatype_iri": self.datatype_iri,
            "language": self.language,
            "lexical_form": self.lexical_form,
            "opaque_identity": self.opaque_identity,
            "record": "opaque_literal_semantic",
            "schema_version": self.schema_version,
        }

    def canonical_bytes(self) -> bytes:
        return _canonical_json(self.to_payload())

    def canonical_digest(self) -> str:
        return _digest(self.to_payload())


BackendLiteralSemanticPayload: TypeAlias = LiteralSemanticPayload | OpaqueLiteralSemanticPayload


@dataclass(frozen=True, slots=True)
class FacetSemanticPayload:
    """One facet with an already compiled semantic literal value."""

    facet_iri: str
    value: LiteralSemanticPayload
    schema_version: int = DATATYPE_SEMANTIC_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _schema(self.schema_version)
        if not isinstance(self.facet_iri, str) or not self.facet_iri:
            raise ValueError("facet_iri must be a nonempty string")
        if not isinstance(self.value, LiteralSemanticPayload):
            raise TypeError("value must be LiteralSemanticPayload")

    def to_payload(self) -> dict[str, object]:
        return {
            "facet_iri": self.facet_iri,
            "record": "facet_semantic",
            "schema_version": self.schema_version,
            "value": self.value.to_payload(),
        }


@dataclass(frozen=True, slots=True)
class DataRangeSemanticPayload:
    """Canonical executable syntax tree for one OWL data range."""

    kind: DataRangePayloadKind
    datatype_iri: str | None = None
    operands: tuple[DataRangeSemanticPayload, ...] = ()
    facets: tuple[FacetSemanticPayload, ...] = ()
    values: tuple[LiteralSemanticPayload, ...] = ()
    schema_version: int = DATATYPE_SEMANTIC_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _schema(self.schema_version)
        if not isinstance(self.kind, DataRangePayloadKind):
            raise TypeError("kind must be DataRangePayloadKind")
        if self.datatype_iri is not None and (
            not isinstance(self.datatype_iri, str) or not self.datatype_iri
        ):
            raise ValueError("datatype_iri must be a nonempty string or None")
        if self.datatype_iri is not None:
            owl.IRI(self.datatype_iri)
        operands = tuple(self.operands)
        facets = tuple(self.facets)
        values = tuple(self.values)
        if not all(isinstance(value, DataRangeSemanticPayload) for value in operands):
            raise TypeError("operands must contain DataRangeSemanticPayload values")
        if not all(isinstance(value, FacetSemanticPayload) for value in facets):
            raise TypeError("facets must contain FacetSemanticPayload values")
        if not all(isinstance(value, LiteralSemanticPayload) for value in values):
            raise TypeError("values must contain LiteralSemanticPayload values")
        if self.kind in {DataRangePayloadKind.DATATYPE, DataRangePayloadKind.OPAQUE}:
            _shape(self.datatype_iri is not None and not operands and not facets and not values)
        elif self.kind is DataRangePayloadKind.RESTRICTION:
            _shape(self.datatype_iri is not None and not operands and bool(facets) and not values)
            facets = tuple(sorted(set(facets), key=lambda item: _canonical_json(item.to_payload())))
        elif self.kind in {DataRangePayloadKind.INTERSECTION, DataRangePayloadKind.UNION}:
            _shape(self.datatype_iri is None and len(operands) >= 2 and not facets and not values)
            operands = _canonical_operands(self.kind, operands)
            _shape(len(operands) >= 2)
        elif self.kind is DataRangePayloadKind.COMPLEMENT:
            _shape(self.datatype_iri is None and len(operands) == 1 and not facets and not values)
        elif self.kind is DataRangePayloadKind.ENUMERATION:
            _shape(self.datatype_iri is None and not operands and not facets and bool(values))
            values = tuple(sorted(set(values), key=lambda item: item.canonical_bytes()))
        object.__setattr__(self, "operands", operands)
        object.__setattr__(self, "facets", facets)
        object.__setattr__(self, "values", values)

    def to_payload(self) -> dict[str, object]:
        return {
            "datatype_iri": self.datatype_iri,
            "facets": tuple(value.to_payload() for value in self.facets),
            "kind": self.kind.value,
            "operands": tuple(value.to_payload() for value in self.operands),
            "record": "data_range_semantic",
            "schema_version": self.schema_version,
            "values": tuple(value.to_payload() for value in self.values),
        }

    def canonical_bytes(self) -> bytes:
        return _canonical_json(self.to_payload())

    def canonical_digest(self) -> str:
        return _digest(self.to_payload())


@dataclass(frozen=True, slots=True)
class DatatypeDefinitionSemanticPayload:
    """One validated custom datatype alias."""

    datatype_iri: str
    data_range: DataRangeSemanticPayload
    schema_version: int = DATATYPE_SEMANTIC_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _schema(self.schema_version)
        if not isinstance(self.datatype_iri, str) or not self.datatype_iri:
            raise ValueError("datatype_iri must be a nonempty string")
        if self.datatype_iri in SUPPORTED_DATATYPES:
            raise OntologyProfileError(
                "built-in OWL datatypes cannot be redefined",
                code="BUILTIN_DATATYPE_REDEFINITION",
                context={"datatype_iri": self.datatype_iri},
            )
        if not isinstance(self.data_range, DataRangeSemanticPayload):
            raise TypeError("data_range must be DataRangeSemanticPayload")

    def to_payload(self) -> dict[str, object]:
        return {
            "data_range": self.data_range.to_payload(),
            "datatype_iri": self.datatype_iri,
            "record": "datatype_definition_semantic",
            "schema_version": self.schema_version,
        }


@dataclass(frozen=True, slots=True)
class DatatypeSemanticModelPayload:
    """ID-aligned range table plus all custom definitions needed to execute it."""

    data_ranges: tuple[DataRangeSemanticPayload, ...]
    definitions: tuple[DatatypeDefinitionSemanticPayload, ...] = ()
    schema_version: int = DATATYPE_SEMANTIC_SCHEMA_VERSION

    def __post_init__(self) -> None:
        _schema(self.schema_version)
        ranges = tuple(self.data_ranges)
        definitions = tuple(self.definitions)
        if not all(isinstance(value, DataRangeSemanticPayload) for value in ranges):
            raise TypeError("data_ranges must contain DataRangeSemanticPayload values")
        if not all(isinstance(value, DatatypeDefinitionSemanticPayload) for value in definitions):
            raise TypeError("definitions must contain DatatypeDefinitionSemanticPayload values")
        definitions = tuple(sorted(definitions, key=lambda item: item.datatype_iri))
        names = tuple(value.datatype_iri for value in definitions)
        if len(names) != len(set(names)):
            raise OntologyProfileError(
                "each custom datatype must have exactly one definition",
                code="DUPLICATE_DATATYPE_DEFINITION",
            )
        object.__setattr__(self, "data_ranges", ranges)
        object.__setattr__(self, "definitions", definitions)
        _validate_model_graph(self)

    def to_payload(self) -> dict[str, object]:
        return {
            "data_ranges": tuple(value.to_payload() for value in self.data_ranges),
            "definitions": tuple(value.to_payload() for value in self.definitions),
            "record": "datatype_semantic_model",
            "schema_version": self.schema_version,
        }

    def canonical_bytes(self) -> bytes:
        return _canonical_json(self.to_payload())

    def canonical_digest(self) -> str:
        return _digest(self.to_payload())

    @property
    def opaque_data_range_ids(self) -> tuple[int, ...]:
        """Dense root IDs whose semantics are intentionally unavailable."""

        return tuple(
            index
            for index, value in enumerate(self.data_ranges)
            if value.kind is DataRangePayloadKind.OPAQUE
        )


class _CompileContext:
    __slots__ = ("cancellation", "compatibility", "limits", "literal_cache", "nodes")

    def __init__(
        self,
        *,
        compatibility: LexicalCompatibility,
        limits: DatatypeLimits,
        cancellation: CancellationToken | None,
    ) -> None:
        self.compatibility = compatibility
        self.limits = limits
        self.cancellation = cancellation
        self.literal_cache: dict[bytes, LiteralSemanticPayload] = {}
        self.nodes = 0

    def visit(self, depth: int) -> None:
        if depth > self.limits.max_data_range_depth:
            raise ResourceLimitError(
                "data-range expression exceeds the configured depth limit",
                limit="max_data_range_depth",
                observed=depth,
                allowed=self.limits.max_data_range_depth,
            )
        self.nodes += 1
        if self.nodes > self.limits.max_data_range_nodes:
            raise ResourceLimitError(
                "data-range compilation exceeds the configured node limit",
                limit="max_data_range_nodes",
                observed=self.nodes,
                allowed=self.limits.max_data_range_nodes,
            )
        if self.cancellation is not None and (
            self.nodes % self.limits.cancellation_poll_stride == 0
        ):
            self.cancellation.add_work(self.limits.cancellation_poll_stride)
            self.cancellation.check()

    def literal(self, value: owl.Literal) -> LiteralSemanticPayload:
        key = value.canonical_bytes()
        known = self.literal_cache.get(key)
        if known is not None:
            return known
        compiled = compile_literal(
            value,
            compatibility=self.compatibility,
            limits=self.limits,
            cancellation=self.cancellation,
        )
        payload = LiteralSemanticPayload.from_compiled(compiled)
        self.literal_cache[key] = payload
        return payload


def compile_literal_semantic_payload(
    value: owl.Literal | CompiledLiteral,
    *,
    allow_opaque: bool = False,
    compatibility: LexicalCompatibility = LexicalCompatibility.OWL2,
    limits: DatatypeLimits | None = None,
    cancellation: CancellationToken | None = None,
) -> BackendLiteralSemanticPayload:
    """Compile one source literal into the canonical backend payload."""

    if isinstance(value, CompiledLiteral):
        return LiteralSemanticPayload.from_compiled(value)
    if not isinstance(allow_opaque, bool):
        raise TypeError("allow_opaque must be bool")
    selected = _controls(compatibility, limits, cancellation)
    try:
        compiled = compile_literal(
            value,
            compatibility=compatibility,
            limits=selected,
            cancellation=cancellation,
        )
    except UnsupportedDatatypeError:
        if not allow_opaque:
            raise
        if not isinstance(value, owl.Literal):
            raise TypeError("value must be pyowl-core Literal or CompiledLiteral") from None
        return OpaqueLiteralSemanticPayload(
            value.lexical_form,
            value.datatype.iri.value,
            value.language,
            compatibility,
        )
    return LiteralSemanticPayload.from_compiled(compiled)


def compile_data_range_semantic_payload(
    data_range: owl.DataRange,
    *,
    definitions: Iterable[owl.DatatypeDefinition] = (),
    opaque_datatype_iris: Iterable[str] = (),
    compatibility: LexicalCompatibility = LexicalCompatibility.OWL2,
    limits: DatatypeLimits | None = None,
    cancellation: CancellationToken | None = None,
) -> DataRangeSemanticPayload:
    """Compile one executable range, validating its complete custom alias graph."""

    model = compile_datatype_semantic_model(
        (data_range,),
        definitions=definitions,
        opaque_datatype_iris=opaque_datatype_iris,
        compatibility=compatibility,
        limits=limits,
        cancellation=cancellation,
    )
    return model.data_ranges[0]


def compile_datatype_semantic_model(
    data_ranges: Iterable[owl.DataRange],
    *,
    definitions: Iterable[owl.DatatypeDefinition] = (),
    opaque_datatype_iris: Iterable[str] = (),
    compatibility: LexicalCompatibility = LexicalCompatibility.OWL2,
    limits: DatatypeLimits | None = None,
    cancellation: CancellationToken | None = None,
) -> DatatypeSemanticModelPayload:
    """Compile an ID-aligned range table and validated custom definitions.

    ``data_ranges`` order is retained intentionally so a clause compiler can use tuple
    positions as its dense data-range identifiers.  Definitions are sorted by IRI.
    """

    selected = _controls(compatibility, limits, cancellation)
    try:
        roots = tuple(data_ranges)
    except TypeError as error:
        raise TypeError("data_ranges must be an iterable of pyowl-core data ranges") from error
    if not all(isinstance(value, owl.DATA_RANGE_TYPES) for value in roots):
        raise TypeError("data_ranges must contain pyowl-core data ranges")
    definition_map = _core_definitions(definitions)
    opaque = _opaque_datatypes(opaque_datatype_iris, definition_map)
    _validate_core_definition_graph(definition_map, roots, opaque)
    context = _CompileContext(
        compatibility=compatibility,
        limits=selected,
        cancellation=cancellation,
    )
    compiled_definitions = tuple(
        DatatypeDefinitionSemanticPayload(
            iri,
            _compile_data_range(value.data_range, definition_map, opaque, context, depth=1),
        )
        for iri, value in sorted(definition_map.items())
    )
    compiled_ranges = tuple(
        _compile_data_range(value, definition_map, opaque, context, depth=1) for value in roots
    )
    if cancellation is not None:
        cancellation.check()
    return DatatypeSemanticModelPayload(compiled_ranges, compiled_definitions)


def _compile_data_range(
    value: owl.DataRange,
    definitions: Mapping[str, owl.DatatypeDefinition],
    opaque_datatypes: frozenset[str],
    context: _CompileContext,
    *,
    depth: int,
) -> DataRangeSemanticPayload:
    context.visit(depth)
    if isinstance(value, owl.Datatype):
        iri = value.iri.value
        if iri in opaque_datatypes:
            return DataRangeSemanticPayload(DataRangePayloadKind.OPAQUE, datatype_iri=iri)
        if iri not in SUPPORTED_DATATYPES and iri not in definitions:
            _unsupported(iri)
        return DataRangeSemanticPayload(DataRangePayloadKind.DATATYPE, datatype_iri=iri)
    if isinstance(value, owl.DatatypeRestriction):
        datatype_iri = value.datatype.iri.value
        if datatype_iri not in SUPPORTED_DATATYPES:
            _unsupported(datatype_iri)
        facets = tuple(
            FacetSemanticPayload(item.facet.value, context.literal(item.value))
            for item in value.restrictions
        )
        # Validate legal facet/datatype combinations now.  The payload then needs no
        # public OWL object or lexical parser at either backend.
        restrict_datatype(
            datatype_iri,
            tuple(FacetRestriction(item.facet_iri, item.value.to_compiled()) for item in facets),
            limits=context.limits,
            cancellation=context.cancellation,
        )
        return DataRangeSemanticPayload(
            DataRangePayloadKind.RESTRICTION,
            datatype_iri=datatype_iri,
            facets=facets,
        )
    if isinstance(value, owl.DataIntersectionOf):
        return DataRangeSemanticPayload(
            DataRangePayloadKind.INTERSECTION,
            operands=tuple(
                _compile_data_range(item, definitions, opaque_datatypes, context, depth=depth + 1)
                for item in value.operands
            ),
        )
    if isinstance(value, owl.DataUnionOf):
        return DataRangeSemanticPayload(
            DataRangePayloadKind.UNION,
            operands=tuple(
                _compile_data_range(item, definitions, opaque_datatypes, context, depth=depth + 1)
                for item in value.operands
            ),
        )
    if isinstance(value, owl.DataComplementOf):
        return DataRangeSemanticPayload(
            DataRangePayloadKind.COMPLEMENT,
            operands=(
                _compile_data_range(
                    value.operand,
                    definitions,
                    opaque_datatypes,
                    context,
                    depth=depth + 1,
                ),
            ),
        )
    if isinstance(value, owl.DataOneOf):
        return DataRangeSemanticPayload(
            DataRangePayloadKind.ENUMERATION,
            values=tuple(context.literal(item) for item in value.values),
        )
    raise AssertionError(f"unhandled pyowl-core data range {type(value).__name__}")


class DatatypeSemanticEvaluator:
    """Execute canonical range payloads over exact compiled literal semantics."""

    __slots__ = ("_atom_cache", "_definitions", "_limits", "model")

    def __init__(
        self,
        model: DatatypeSemanticModelPayload,
        *,
        limits: DatatypeLimits | None = None,
    ) -> None:
        if not isinstance(model, DatatypeSemanticModelPayload):
            raise TypeError("model must be DatatypeSemanticModelPayload")
        selected = limits or DatatypeLimits()
        if not isinstance(selected, DatatypeLimits):
            raise TypeError("limits must be DatatypeLimits or None")
        self.model = model
        self._limits = selected
        self._definitions = {value.datatype_iri: value.data_range for value in model.definitions}
        self._atom_cache: dict[DataRangeSemanticPayload, DatatypeRange] = {}

    def contains(
        self,
        data_range_id: int,
        value: CompiledLiteral | BackendLiteralSemanticPayload,
        *,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        """Test one dense range ID without lexical reparsing."""

        if isinstance(data_range_id, bool) or not isinstance(data_range_id, int):
            raise TypeError("data_range_id must be int")
        if data_range_id < 0 or data_range_id >= len(self.model.data_ranges):
            raise ValueError("data_range_id is dangling")
        return self.contains_payload(
            self.model.data_ranges[data_range_id],
            value,
            cancellation=cancellation,
        )

    def contains_payload(
        self,
        data_range: DataRangeSemanticPayload,
        value: CompiledLiteral | BackendLiteralSemanticPayload,
        *,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        if not isinstance(data_range, DataRangeSemanticPayload):
            raise TypeError("data_range must be DataRangeSemanticPayload")
        if cancellation is not None and not isinstance(cancellation, CancellationToken):
            raise TypeError("cancellation must be CancellationToken or None")
        if isinstance(value, OpaqueLiteralSemanticPayload):
            _unsupported(value.datatype_iri)
        compiled = value.to_compiled() if isinstance(value, LiteralSemanticPayload) else value
        if not isinstance(compiled, CompiledLiteral):
            raise TypeError("value must be CompiledLiteral or LiteralSemanticPayload")
        return self._contains(data_range, compiled, cancellation=cancellation, depth=1)

    def _contains(
        self,
        data_range: DataRangeSemanticPayload,
        value: CompiledLiteral,
        *,
        cancellation: CancellationToken | None,
        depth: int,
    ) -> bool:
        if depth > self._limits.max_data_range_depth:
            raise ResourceLimitError(
                "data-range evaluation exceeds the configured depth limit",
                limit="max_data_range_depth",
                observed=depth,
                allowed=self._limits.max_data_range_depth,
            )
        if cancellation is not None:
            cancellation.add_work(1)
            cancellation.check()
        if data_range.kind is DataRangePayloadKind.OPAQUE:
            _unsupported(cast(str, data_range.datatype_iri))
        if data_range.kind is DataRangePayloadKind.DATATYPE:
            iri = cast(str, data_range.datatype_iri)
            definition = self._definitions.get(iri)
            if definition is not None:
                return self._contains(
                    definition,
                    value,
                    cancellation=cancellation,
                    depth=depth + 1,
                )
            return self._atom(data_range).contains(value)
        if data_range.kind is DataRangePayloadKind.RESTRICTION:
            return self._atom(data_range).contains(value)
        if data_range.kind is DataRangePayloadKind.INTERSECTION:
            return all(
                self._contains(item, value, cancellation=cancellation, depth=depth + 1)
                for item in data_range.operands
            )
        if data_range.kind is DataRangePayloadKind.UNION:
            return any(
                self._contains(item, value, cancellation=cancellation, depth=depth + 1)
                for item in data_range.operands
            )
        if data_range.kind is DataRangePayloadKind.COMPLEMENT:
            return not self._contains(
                data_range.operands[0],
                value,
                cancellation=cancellation,
                depth=depth + 1,
            )
        if data_range.kind is DataRangePayloadKind.ENUMERATION:
            return any(
                item.data_identity == _canonical_tagged(value.data_identity)
                for item in data_range.values
            )
        raise AssertionError("closed DataRangePayloadKind dispatch is incomplete")

    def _atom(self, value: DataRangeSemanticPayload) -> DatatypeRange:
        known = self._atom_cache.get(value)
        if known is not None:
            return known
        iri = cast(str, value.datatype_iri)
        if value.kind is DataRangePayloadKind.DATATYPE:
            result = range_for_datatype(iri)
        elif value.kind is DataRangePayloadKind.RESTRICTION:
            result = restrict_datatype(
                iri,
                tuple(
                    FacetRestriction(item.facet_iri, item.value.to_compiled())
                    for item in value.facets
                ),
                limits=self._limits,
            )
        else:
            raise TypeError("only datatype and restriction payloads are atoms")
        self._atom_cache[value] = result
        return result


def decode_literal_semantic_payload(
    data: bytes,
    *,
    limits: DatatypeLimits | None = None,
    require_canonical: bool = True,
) -> BackendLiteralSemanticPayload:
    """Strictly decode one standalone literal semantic record."""

    payload = _decode_json(data, limits)
    mapping = _mapping(payload, "literal semantic payload")
    result = (
        _opaque_literal_from_payload(payload)
        if mapping.get("record") == "opaque_literal_semantic"
        else _literal_from_payload(payload)
    )
    _require_canonical_bytes(data, result.canonical_bytes(), require_canonical)
    return result


def decode_datatype_semantic_model(
    data: bytes,
    *,
    limits: DatatypeLimits | None = None,
    require_canonical: bool = True,
) -> DatatypeSemanticModelPayload:
    """Strictly decode a complete backend datatype table."""

    selected = limits or DatatypeLimits()
    payload = _decode_json(data, selected)
    context = _DecodeContext(selected)
    result = _model_from_payload(payload, context, depth=1)
    _require_canonical_bytes(data, result.canonical_bytes(), require_canonical)
    return result


class _DecodeContext:
    __slots__ = ("limits", "nodes")

    def __init__(self, limits: DatatypeLimits) -> None:
        self.limits = limits
        self.nodes = 0

    def visit(self, depth: int) -> None:
        if depth > self.limits.max_data_range_depth:
            raise ResourceLimitError(
                "semantic payload exceeds the configured data-range depth",
                limit="max_data_range_depth",
                observed=depth,
                allowed=self.limits.max_data_range_depth,
            )
        self.nodes += 1
        if self.nodes > self.limits.max_data_range_nodes:
            raise ResourceLimitError(
                "semantic payload exceeds the configured data-range node count",
                limit="max_data_range_nodes",
                observed=self.nodes,
                allowed=self.limits.max_data_range_nodes,
            )


def _model_from_payload(
    value: object,
    context: _DecodeContext,
    *,
    depth: int,
) -> DatatypeSemanticModelPayload:
    mapping = _record(value, "datatype_semantic_model", {"data_ranges", "definitions"})
    ranges = tuple(
        _range_from_payload(item, context, depth=depth + 1)
        for item in _sequence(mapping["data_ranges"], "data_ranges")
    )
    definitions = tuple(
        _definition_from_payload(item, context, depth=depth + 1)
        for item in _sequence(mapping["definitions"], "definitions")
    )
    return DatatypeSemanticModelPayload(ranges, definitions)


def _definition_from_payload(
    value: object,
    context: _DecodeContext,
    *,
    depth: int,
) -> DatatypeDefinitionSemanticPayload:
    mapping = _record(
        value,
        "datatype_definition_semantic",
        {"datatype_iri", "data_range"},
    )
    return DatatypeDefinitionSemanticPayload(
        _string(mapping["datatype_iri"], "datatype_iri"),
        _range_from_payload(mapping["data_range"], context, depth=depth + 1),
    )


def _range_from_payload(
    value: object,
    context: _DecodeContext,
    *,
    depth: int,
) -> DataRangeSemanticPayload:
    context.visit(depth)
    mapping = _record(
        value,
        "data_range_semantic",
        {"kind", "datatype_iri", "operands", "facets", "values"},
    )
    kind = _enum(DataRangePayloadKind, mapping["kind"], "data-range kind")
    datatype_iri = _optional_string(mapping["datatype_iri"], "datatype_iri")
    operands = tuple(
        _range_from_payload(item, context, depth=depth + 1)
        for item in _sequence(mapping["operands"], "operands")
    )
    facets = tuple(_facet_from_payload(item) for item in _sequence(mapping["facets"], "facets"))
    values = tuple(_literal_from_payload(item) for item in _sequence(mapping["values"], "values"))
    return DataRangeSemanticPayload(kind, datatype_iri, operands, facets, values)


def _facet_from_payload(value: object) -> FacetSemanticPayload:
    mapping = _record(value, "facet_semantic", {"facet_iri", "value"})
    return FacetSemanticPayload(
        _string(mapping["facet_iri"], "facet_iri"),
        _literal_from_payload(mapping["value"]),
    )


def _literal_from_payload(value: object) -> LiteralSemanticPayload:
    mapping = _record(
        value,
        "literal_semantic",
        {
            "lexical_form",
            "datatype_iri",
            "language",
            "data_identity",
            "comparison",
            "compatibility",
        },
    )
    return LiteralSemanticPayload(
        _string(mapping["lexical_form"], "lexical_form"),
        _string(mapping["datatype_iri"], "datatype_iri"),
        _optional_string(mapping["language"], "language"),
        _tagged(mapping["data_identity"], "data_identity"),
        _tagged(mapping["comparison"], "comparison"),
        _enum(LexicalCompatibility, mapping["compatibility"], "compatibility"),
    )


def _opaque_literal_from_payload(value: object) -> OpaqueLiteralSemanticPayload:
    mapping = _record(
        value,
        "opaque_literal_semantic",
        {
            "lexical_form",
            "datatype_iri",
            "language",
            "compatibility",
            "opaque_identity",
        },
    )
    result = OpaqueLiteralSemanticPayload(
        _string(mapping["lexical_form"], "lexical_form"),
        _string(mapping["datatype_iri"], "datatype_iri"),
        _optional_string(mapping["language"], "language"),
        _enum(LexicalCompatibility, mapping["compatibility"], "compatibility"),
    )
    if tuple(_tagged(mapping["opaque_identity"], "opaque_identity")) != result.opaque_identity:
        raise ValueError("opaque literal identity does not match its source triple")
    return result


def _core_definitions(
    definitions: Iterable[owl.DatatypeDefinition],
) -> dict[str, owl.DatatypeDefinition]:
    try:
        items = tuple(definitions)
    except TypeError as error:
        raise TypeError("definitions must be an iterable of DatatypeDefinition axioms") from error
    if not all(isinstance(value, owl.DatatypeDefinition) for value in items):
        raise TypeError("definitions must contain DatatypeDefinition axioms")
    output: dict[str, owl.DatatypeDefinition] = {}
    for item in items:
        iri = item.datatype.iri.value
        if iri in SUPPORTED_DATATYPES:
            raise OntologyProfileError(
                "built-in OWL datatypes cannot be redefined",
                code="BUILTIN_DATATYPE_REDEFINITION",
                context={"datatype_iri": iri},
            )
        if iri in output:
            raise OntologyProfileError(
                "each custom datatype must have exactly one definition",
                code="DUPLICATE_DATATYPE_DEFINITION",
                context={"datatype_iri": iri},
            )
        output[iri] = item
    return output


def _opaque_datatypes(
    values: Iterable[str],
    definitions: Mapping[str, owl.DatatypeDefinition],
) -> frozenset[str]:
    try:
        items = frozenset(values)
    except TypeError as error:
        raise TypeError("opaque_datatype_iris must be an iterable of strings") from error
    if not all(isinstance(value, str) and value for value in items):
        raise TypeError("opaque_datatype_iris must contain nonempty strings")
    for iri in items:
        owl.IRI(iri)
        if iri in SUPPORTED_DATATYPES or iri in definitions:
            raise ValueError("opaque datatypes cannot also be built-in or defined")
    return items


def _validate_core_definition_graph(
    definitions: Mapping[str, owl.DatatypeDefinition],
    roots: tuple[owl.DataRange, ...],
    opaque_datatypes: frozenset[str],
) -> None:
    graph = {
        iri: frozenset(
            reference
            for reference in _core_references(definition.data_range)
            if reference in definitions
        )
        for iri, definition in definitions.items()
    }
    for root in roots:
        for reference in _core_references(root):
            if (
                reference not in SUPPORTED_DATATYPES
                and reference not in definitions
                and reference not in opaque_datatypes
            ):
                _unsupported(reference)
    for definition in definitions.values():
        for reference in _core_references(definition.data_range):
            if reference not in SUPPORTED_DATATYPES and reference not in definitions:
                _unsupported(reference)
    _reject_cycle(graph)


def _core_references(value: owl.DataRange) -> tuple[str, ...]:
    if isinstance(value, owl.Datatype):
        return (value.iri.value,)
    if isinstance(value, owl.DatatypeRestriction):
        return (value.datatype.iri.value,)
    if isinstance(value, (owl.DataIntersectionOf, owl.DataUnionOf)):
        return tuple(
            reference for operand in value.operands for reference in _core_references(operand)
        )
    if isinstance(value, owl.DataComplementOf):
        return _core_references(value.operand)
    if isinstance(value, owl.DataOneOf):
        # Enumeration values are compiled independently.  Literals using a custom
        # datatype have no OWL lexical map and are rejected by compile_literal.
        return ()
    raise AssertionError(f"unhandled pyowl-core data range {type(value).__name__}")


def _validate_model_graph(model: DatatypeSemanticModelPayload) -> None:
    names = frozenset(value.datatype_iri for value in model.definitions)
    graph: dict[str, frozenset[str]] = {}
    for definition in model.definitions:
        references = _payload_references(definition.data_range)
        _validate_references(references, names)
        _validate_payload_atoms(definition.data_range)
        graph[definition.datatype_iri] = frozenset(value for value in references if value in names)
    for data_range in model.data_ranges:
        _validate_references(_payload_references(data_range), names)
        _validate_payload_atoms(data_range)
    _reject_cycle(graph)


def _validate_payload_atoms(value: DataRangeSemanticPayload) -> None:
    if value.kind is DataRangePayloadKind.RESTRICTION:
        restrict_datatype(
            cast(str, value.datatype_iri),
            tuple(
                FacetRestriction(item.facet_iri, item.value.to_compiled()) for item in value.facets
            ),
        )
    for operand in value.operands:
        _validate_payload_atoms(operand)


def _payload_references(value: DataRangeSemanticPayload) -> tuple[str, ...]:
    if value.kind is DataRangePayloadKind.OPAQUE:
        return ()
    if value.kind in {DataRangePayloadKind.DATATYPE, DataRangePayloadKind.RESTRICTION}:
        return (cast(str, value.datatype_iri),)
    return tuple(
        reference for operand in value.operands for reference in _payload_references(operand)
    )


def _validate_references(references: tuple[str, ...], definitions: frozenset[str]) -> None:
    for reference in references:
        if reference not in SUPPORTED_DATATYPES and reference not in definitions:
            _unsupported(reference)


def _reject_cycle(graph: Mapping[str, frozenset[str]]) -> None:
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(iri: str, path: tuple[str, ...]) -> None:
        if iri in visiting:
            start = path.index(iri)
            cycle = (*path[start:], iri)
            raise OntologyProfileError(
                "custom datatype definitions must form an acyclic graph",
                code="RECURSIVE_DATATYPE_DEFINITION",
                context={"cycle": " -> ".join(cycle)},
            )
        if iri in visited:
            return
        visiting.add(iri)
        for dependency in sorted(graph.get(iri, frozenset())):
            visit(dependency, (*path, dependency))
        visiting.remove(iri)
        visited.add(iri)

    for iri in sorted(graph):
        visit(iri, (iri,))


def _canonical_operands(
    kind: DataRangePayloadKind,
    operands: tuple[DataRangeSemanticPayload, ...],
) -> tuple[DataRangeSemanticPayload, ...]:
    flattened: list[DataRangeSemanticPayload] = []
    for operand in operands:
        if operand.kind is kind:
            flattened.extend(operand.operands)
        else:
            flattened.append(operand)
    return tuple(sorted(set(flattened), key=lambda item: item.canonical_bytes()))


def _require_matching_pair(identity: DataIdentity, comparison: ComparisonValue) -> None:
    matches = False
    if isinstance(identity, NumericIdentity) and isinstance(comparison, NumericComparison):
        matches = (identity.numerator, identity.denominator) == (
            comparison.numerator,
            comparison.denominator,
        )
    elif isinstance(identity, BooleanIdentity) and isinstance(comparison, BooleanComparison):
        matches = identity.value is comparison.value
    elif isinstance(identity, IEEEIdentity) and isinstance(comparison, IEEEComparison):
        matches = ieee_comparison_from_identity(identity) == comparison
    elif isinstance(identity, StringIdentity) and isinstance(comparison, StringComparison):
        matches = (identity.text, identity.language) == (comparison.text, comparison.language)
    elif isinstance(identity, BinaryIdentity) and isinstance(comparison, BinaryComparison):
        matches = (identity.kind, identity.octets) == (comparison.kind, comparison.octets)
    elif isinstance(identity, URIIdentity) and isinstance(comparison, URIComparison):
        matches = identity.value == comparison.value
    elif isinstance(identity, XMLIdentity) and isinstance(comparison, XMLComparison):
        matches = identity.canonical_xml == comparison.canonical_xml
    elif isinstance(identity, DateTimeIdentity) and isinstance(comparison, DateTimeComparison):
        matches = (
            identity.local_numerator,
            identity.local_denominator,
            identity.timezone_offset_minutes,
        ) == (
            comparison.local_numerator,
            comparison.local_denominator,
            comparison.timezone_offset_minutes,
        )
    if not matches:
        raise ValueError("data identity and comparison payloads do not describe one value")


def _controls(
    compatibility: LexicalCompatibility,
    limits: DatatypeLimits | None,
    cancellation: CancellationToken | None,
) -> DatatypeLimits:
    if not isinstance(compatibility, LexicalCompatibility):
        raise TypeError("compatibility must be LexicalCompatibility")
    selected = limits or DatatypeLimits()
    if not isinstance(selected, DatatypeLimits):
        raise TypeError("limits must be DatatypeLimits or None")
    if cancellation is not None and not isinstance(cancellation, CancellationToken):
        raise TypeError("cancellation must be CancellationToken or None")
    if cancellation is not None:
        cancellation.check()
    return selected


def _decode_json(data: bytes, limits: DatatypeLimits | None) -> object:
    selected = limits or DatatypeLimits()
    if not isinstance(selected, DatatypeLimits):
        raise TypeError("limits must be DatatypeLimits or None")
    if not isinstance(data, bytes):
        raise TypeError("semantic payload must be bytes")
    if len(data) > selected.max_semantic_payload_bytes:
        raise ResourceLimitError(
            "semantic payload exceeds the configured byte limit",
            limit="max_semantic_payload_bytes",
            observed=len(data),
            allowed=selected.max_semantic_payload_bytes,
        )
    try:
        return json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError) as error:
        raise ValueError("semantic payload is not valid bounded UTF-8 JSON") from error


def _require_canonical_bytes(data: bytes, canonical: bytes, required: bool) -> None:
    if not isinstance(required, bool):
        raise TypeError("require_canonical must be bool")
    if required and data != canonical:
        raise ValueError("semantic payload JSON is not canonical")


def _record(value: object, record: str, fields: set[str]) -> Mapping[str, object]:
    mapping = _mapping(value, record)
    expected = fields | {"record", "schema_version"}
    if set(mapping) != expected:
        missing = sorted(expected - set(mapping))
        unknown = sorted(set(mapping) - expected)
        raise ValueError(f"{record} fields are invalid; missing={missing!r}, unknown={unknown!r}")
    if mapping["record"] != record:
        raise ValueError(f"expected semantic record {record!r}")
    _schema(mapping["schema_version"])
    return mapping


def _mapping(value: object, name: str) -> Mapping[str, object]:
    if not isinstance(value, Mapping) or not all(isinstance(key, str) for key in value):
        raise TypeError(f"{name} must be a JSON object with string keys")
    return cast(Mapping[str, object], value)


def _sequence(value: object, name: str) -> Sequence[object]:
    if isinstance(value, (str, bytes)) or not isinstance(value, Sequence):
        raise TypeError(f"{name} must be a JSON array")
    return cast(Sequence[object], value)


def _string(value: object, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be str")
    return value


def _optional_string(value: object, name: str) -> str | None:
    if value is not None and not isinstance(value, str):
        raise TypeError(f"{name} must be str or None")
    return value


def _optional_integer(value: object, name: str) -> int | None:
    if value is not None and (isinstance(value, bool) or not isinstance(value, int)):
        raise TypeError(f"{name} must be int or None")
    return value


def _enum(enum: type[_EnumT], value: object, name: str) -> _EnumT:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be str")
    try:
        return enum(value)
    except ValueError as error:
        raise ValueError(f"unknown {name} {value!r}") from error


def _schema(value: object) -> None:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError("schema_version must be int")
    if value != DATATYPE_SEMANTIC_SCHEMA_VERSION:
        raise ValueError(f"unsupported datatype semantic schema version {value}")


def _shape(condition: bool) -> None:
    if not condition:
        raise ValueError("data-range semantic payload fields do not match its kind")


def _unsupported(datatype_iri: str) -> None:
    raise UnsupportedDatatypeError(
        "datatype is outside the implemented OWL 2 map and has no definition",
        context={"datatype_iri": datatype_iri},
    )


__all__ = [
    "DATATYPE_SEMANTIC_SCHEMA_VERSION",
    "BackendLiteralSemanticPayload",
    "DataRangePayloadKind",
    "DataRangeSemanticPayload",
    "DatatypeDefinitionSemanticPayload",
    "DatatypeSemanticEvaluator",
    "DatatypeSemanticModelPayload",
    "FacetSemanticPayload",
    "LiteralSemanticPayload",
    "OpaqueLiteralSemanticPayload",
    "PayloadScalar",
    "TaggedSemanticValue",
    "comparison_from_tagged",
    "compile_data_range_semantic_payload",
    "compile_datatype_semantic_model",
    "compile_literal_semantic_payload",
    "data_identity_from_tagged",
    "decode_datatype_semantic_model",
    "decode_literal_semantic_payload",
]
