"""Immutable identities for the pure-Python datatype layer.

SPDX-License-Identifier: LGPL-3.0-or-later

The source literal remains the exact :mod:`pyowl_core` object.  The records in this
module are private semantic compiler values: source identity, OWL data-domain
identity, and datatype comparison are deliberately represented by different types.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum, IntEnum
from typing import TypeAlias, cast

from pyowl_core.model import Literal


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class LexicalCompatibility(_StringEnum):
    """Lexical policy selected explicitly by private compilation."""

    OWL2 = "owl2"
    HERMIT_1_4 = "hermit-37ec30a"


class NumericDomain(IntEnum):
    """Nested exact domains: INTEGER ⊆ DECIMAL ⊆ RATIONAL ⊆ REAL."""

    INTEGER = 0
    DECIMAL = 1
    RATIONAL = 2
    REAL = 3


class ComparisonOrder(IntEnum):
    """Four-way datatype comparison result used by partial orders."""

    LESS = -1
    EQUAL = 0
    GREATER = 1
    UNORDERED = 2


class IEEEFormat(_StringEnum):
    """The two disjoint XML Schema IEEE-754 value spaces."""

    FLOAT32 = "float32"
    FLOAT64 = "float64"

    @property
    def width(self) -> int:
        return 32 if self is IEEEFormat.FLOAT32 else 64


class IEEECategory(_StringEnum):
    """Comparison category for an IEEE value."""

    FINITE = "finite"
    NEGATIVE_INFINITY = "negative-infinity"
    POSITIVE_INFINITY = "positive-infinity"
    NAN = "nan"


class BinaryKind(_StringEnum):
    """OWL keeps the two isomorphic binary value spaces disjoint."""

    HEX = "hexBinary"
    BASE64 = "base64Binary"


@dataclass(frozen=True, slots=True)
class DatatypeLimits:
    """Bounds for hostile lexical forms and finite materialization."""

    max_lexical_characters: int = 1_000_000
    max_numeric_digits: int = 100_000
    max_decimal_exponent: int = 100_000
    max_enumeration_values: int = 100_000
    max_binary_bytes: int = 1_000_000
    max_pattern_states: int = 20_000
    max_pattern_transitions: int = 200_000
    max_data_range_depth: int = 512
    max_data_range_nodes: int = 100_000
    max_solver_steps: int = 1_000_000
    max_semantic_payload_bytes: int = 16_000_000
    max_xml_depth: int = 256
    max_xml_nodes: int = 100_000
    cancellation_poll_stride: int = 64

    def __post_init__(self) -> None:
        for name in (
            "max_lexical_characters",
            "max_numeric_digits",
            "max_decimal_exponent",
            "max_enumeration_values",
            "max_binary_bytes",
            "max_pattern_states",
            "max_pattern_transitions",
            "max_data_range_depth",
            "max_data_range_nodes",
            "max_solver_steps",
            "max_semantic_payload_bytes",
            "max_xml_depth",
            "max_xml_nodes",
            "cancellation_poll_stride",
        ):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
                raise ValueError(f"{name} must be a positive integer")


@dataclass(frozen=True, slots=True)
class SourceLiteralIdentity:
    """Exact core structural token; lexical aliases intentionally stay distinct."""

    lexical_form: str
    datatype_iri: str
    language: str | None

    def __post_init__(self) -> None:
        if not isinstance(self.lexical_form, str):
            raise TypeError("lexical_form must be str")
        if not isinstance(self.datatype_iri, str) or not self.datatype_iri:
            raise ValueError("datatype_iri must be a nonempty string")
        if self.language is not None and (not isinstance(self.language, str) or not self.language):
            raise ValueError("language must be a nonempty string or None")

    @classmethod
    def from_literal(cls, literal: Literal) -> SourceLiteralIdentity:
        if not isinstance(literal, Literal):
            raise TypeError("literal must be pyowl_core.model.Literal")
        return cls(literal.lexical_form, literal.datatype.iri.value, literal.language)

    def as_tagged(self) -> tuple[str, str, str | None]:
        return (self.lexical_form, self.datatype_iri, self.language)


def _reduced(numerator: int, denominator: int) -> tuple[int, int]:
    if isinstance(numerator, bool) or not isinstance(numerator, int):
        raise TypeError("numerator must be int")
    if isinstance(denominator, bool) or not isinstance(denominator, int):
        raise TypeError("denominator must be int")
    if denominator == 0:
        raise ValueError("denominator must be nonzero")
    if denominator < 0:
        numerator = -numerator
        denominator = -denominator
    divisor = math.gcd(numerator, denominator)
    return numerator // divisor, denominator // divisor


def _integer_token(value: int) -> str:
    """Canonical hexadecimal integer token, unaffected by Python's decimal digit cap."""

    return ("-" if value < 0 else "+") + format(abs(value), "x")


@dataclass(frozen=True, slots=True)
class NumericIdentity:
    """Language-neutral OWL data identity for exact real-family values."""

    numerator: int
    denominator: int = 1

    def __post_init__(self) -> None:
        numerator, denominator = _reduced(self.numerator, self.denominator)
        object.__setattr__(self, "numerator", numerator)
        object.__setattr__(self, "denominator", denominator)

    def as_tagged(self) -> tuple[str, str, str]:
        return (
            "numeric-rational-hex-v1",
            _integer_token(self.numerator),
            _integer_token(self.denominator),
        )


@dataclass(frozen=True, slots=True)
class NumericComparison:
    """Exact total-order record used by numeric bounds, never as node identity."""

    numerator: int
    denominator: int = 1

    def __post_init__(self) -> None:
        numerator, denominator = _reduced(self.numerator, self.denominator)
        object.__setattr__(self, "numerator", numerator)
        object.__setattr__(self, "denominator", denominator)

    def compare(self, other: NumericComparison) -> int:
        if not isinstance(other, NumericComparison):
            raise TypeError("other must be NumericComparison")
        difference = self.numerator * other.denominator - other.numerator * self.denominator
        return (difference > 0) - (difference < 0)

    def as_tagged(self) -> tuple[str, str, str]:
        return (
            "ordered-numeric-rational-hex-v1",
            _integer_token(self.numerator),
            _integer_token(self.denominator),
        )


@dataclass(frozen=True, slots=True)
class BooleanIdentity:
    """Boolean data identity, kept disjoint from Python/numeric ``0`` and ``1``."""

    value: bool

    def __post_init__(self) -> None:
        if not isinstance(self.value, bool):
            raise TypeError("boolean identity value must be bool")

    def as_tagged(self) -> tuple[str, bool]:
        return ("boolean", self.value)


@dataclass(frozen=True, slots=True)
class BooleanComparison:
    """Separate equality-comparison record for the unordered Boolean family."""

    value: bool

    def __post_init__(self) -> None:
        if not isinstance(self.value, bool):
            raise TypeError("boolean comparison value must be bool")

    def as_tagged(self) -> tuple[str, bool]:
        return ("boolean-equality", self.value)


@dataclass(frozen=True, slots=True)
class IEEEIdentity:
    """Exact IEEE data identity; format and signed-zero bit are significant."""

    format: IEEEFormat
    bits: int

    def __post_init__(self) -> None:
        if not isinstance(self.format, IEEEFormat):
            raise TypeError("format must be IEEEFormat")
        if isinstance(self.bits, bool) or not isinstance(self.bits, int):
            raise TypeError("bits must be int")
        if self.bits < 0 or self.bits >= 1 << self.format.width:
            raise ValueError("bits do not fit the selected IEEE format")
        exponent_bits = 8 if self.format is IEEEFormat.FLOAT32 else 11
        fraction_bits = self.format.width - exponent_bits - 1
        exponent_mask = (1 << exponent_bits) - 1
        exponent = (self.bits >> fraction_bits) & exponent_mask
        fraction = self.bits & ((1 << fraction_bits) - 1)
        if exponent == exponent_mask and fraction:
            # XML Schema has one NaN value, not the many IEEE payload identities.
            canonical = (exponent_mask << fraction_bits) | (1 << (fraction_bits - 1))
            object.__setattr__(self, "bits", canonical)

    def as_tagged(self) -> tuple[str, str, str]:
        digits = self.format.width // 4
        return ("ieee-identity-v1", self.format.value, format(self.bits, f"0{digits}x"))


@dataclass(frozen=True, slots=True)
class IEEEComparison:
    """Facet comparison record; signed zeros compare equal and NaN is unordered."""

    format: IEEEFormat
    category: IEEECategory
    numerator: int = 0
    denominator: int = 1

    def __post_init__(self) -> None:
        if not isinstance(self.format, IEEEFormat):
            raise TypeError("format must be IEEEFormat")
        if not isinstance(self.category, IEEECategory):
            raise TypeError("category must be IEEECategory")
        numerator, denominator = _reduced(self.numerator, self.denominator)
        if self.category is not IEEECategory.FINITE and (numerator != 0 or denominator != 1):
            raise ValueError("non-finite comparison values cannot carry a rational payload")
        object.__setattr__(self, "numerator", numerator)
        object.__setattr__(self, "denominator", denominator)

    def compare(self, other: IEEEComparison) -> ComparisonOrder:
        if not isinstance(other, IEEEComparison):
            raise TypeError("other must be IEEEComparison")
        if self.format is not other.format:
            raise TypeError("IEEE comparisons require the same XML Schema datatype")
        if self.category is IEEECategory.NAN or other.category is IEEECategory.NAN:
            return ComparisonOrder.UNORDERED
        ranks = {
            IEEECategory.NEGATIVE_INFINITY: 0,
            IEEECategory.FINITE: 1,
            IEEECategory.POSITIVE_INFINITY: 2,
        }
        left_rank = ranks[self.category]
        right_rank = ranks[other.category]
        if left_rank != right_rank:
            return ComparisonOrder.LESS if left_rank < right_rank else ComparisonOrder.GREATER
        if self.category is not IEEECategory.FINITE:
            return ComparisonOrder.EQUAL
        difference = self.numerator * other.denominator - other.numerator * self.denominator
        if difference < 0:
            return ComparisonOrder.LESS
        if difference > 0:
            return ComparisonOrder.GREATER
        return ComparisonOrder.EQUAL

    def as_tagged(self) -> tuple[str, str, str, str, str]:
        return (
            "ieee-comparison-v1",
            self.format.value,
            self.category.value,
            _integer_token(self.numerator),
            _integer_token(self.denominator),
        )


@dataclass(frozen=True, slots=True)
class StringIdentity:
    """Plain/string-family identity shared across overlapping derived datatypes."""

    text: str
    language: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.text, str):
            raise TypeError("text must be str")
        if self.language is not None and (not isinstance(self.language, str) or not self.language):
            raise ValueError("language must be a nonempty string or None")

    def as_tagged(self) -> tuple[str, str, str | None]:
        return ("plain-string-v1", self.text, self.language)


@dataclass(frozen=True, slots=True)
class StringComparison:
    """Equality/length/pattern comparison record for plain literal values."""

    text: str
    language: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.text, str):
            raise TypeError("text must be str")
        if self.language is not None and (not isinstance(self.language, str) or not self.language):
            raise ValueError("language must be a nonempty string or None")

    def as_tagged(self) -> tuple[str, str, str | None]:
        return ("plain-string-comparison-v1", self.text, self.language)


@dataclass(frozen=True, slots=True)
class BinaryIdentity:
    """Binary identity tagged by the disjoint XML Schema primitive family."""

    kind: BinaryKind
    octets: bytes

    def __post_init__(self) -> None:
        if not isinstance(self.kind, BinaryKind):
            raise TypeError("kind must be BinaryKind")
        if not isinstance(self.octets, bytes):
            raise TypeError("octets must be bytes")

    def as_tagged(self) -> tuple[str, str, str]:
        return ("binary-identity-v1", self.kind.value, self.octets.hex())


@dataclass(frozen=True, slots=True)
class BinaryComparison:
    """Equality and length comparison record for a binary value."""

    kind: BinaryKind
    octets: bytes

    def __post_init__(self) -> None:
        if not isinstance(self.kind, BinaryKind):
            raise TypeError("kind must be BinaryKind")
        if not isinstance(self.octets, bytes):
            raise TypeError("octets must be bytes")

    def as_tagged(self) -> tuple[str, str, str]:
        return ("binary-comparison-v1", self.kind.value, self.octets.hex())


@dataclass(frozen=True, slots=True)
class URIIdentity:
    """Identity in the xsd:anyURI value space, disjoint from strings."""

    value: str

    def __post_init__(self) -> None:
        if not isinstance(self.value, str):
            raise TypeError("value must be str")

    def as_tagged(self) -> tuple[str, str]:
        return ("any-uri-v1", self.value)


@dataclass(frozen=True, slots=True)
class URIComparison:
    value: str

    def __post_init__(self) -> None:
        if not isinstance(self.value, str):
            raise TypeError("value must be str")

    def as_tagged(self) -> tuple[str, str]:
        return ("any-uri-comparison-v1", self.value)


@dataclass(frozen=True, slots=True)
class XMLIdentity:
    """Exclusive-canonical XML fragment identity, disjoint from strings."""

    canonical_xml: str

    def __post_init__(self) -> None:
        if not isinstance(self.canonical_xml, str):
            raise TypeError("canonical_xml must be str")

    def as_tagged(self) -> tuple[str, str]:
        return ("xml-literal-c14n-v1", self.canonical_xml)


@dataclass(frozen=True, slots=True)
class XMLComparison:
    canonical_xml: str

    def __post_init__(self) -> None:
        if not isinstance(self.canonical_xml, str):
            raise TypeError("canonical_xml must be str")

    def as_tagged(self) -> tuple[str, str]:
        return ("xml-literal-comparison-v1", self.canonical_xml)


@dataclass(frozen=True, slots=True)
class DateTimeIdentity:
    """Date/time identity retains offset while normalizing lexical aliases."""

    local_numerator: int
    local_denominator: int = 1
    timezone_offset_minutes: int | None = None
    hermit_end_of_day: bool = False

    def __post_init__(self) -> None:
        numerator, denominator = _reduced(self.local_numerator, self.local_denominator)
        offset = self.timezone_offset_minutes
        if offset is not None and (
            isinstance(offset, bool) or not isinstance(offset, int) or not -840 <= offset <= 840
        ):
            raise ValueError("timezone offset must be an integer from -840 through 840 or None")
        if not isinstance(self.hermit_end_of_day, bool):
            raise TypeError("hermit_end_of_day must be bool")
        object.__setattr__(self, "local_numerator", numerator)
        object.__setattr__(self, "local_denominator", denominator)

    def as_tagged(self) -> tuple[str, str, str, int | None, bool]:
        return (
            "date-time-identity-v1",
            _integer_token(self.local_numerator),
            _integer_token(self.local_denominator),
            self.timezone_offset_minutes,
            self.hermit_end_of_day,
        )


@dataclass(frozen=True, slots=True)
class DateTimeComparison:
    """Exact XML Schema dateTime partial-order record."""

    local_numerator: int
    local_denominator: int = 1
    timezone_offset_minutes: int | None = None

    def __post_init__(self) -> None:
        numerator, denominator = _reduced(self.local_numerator, self.local_denominator)
        offset = self.timezone_offset_minutes
        if offset is not None and (
            isinstance(offset, bool) or not isinstance(offset, int) or not -840 <= offset <= 840
        ):
            raise ValueError("timezone offset must be an integer from -840 through 840 or None")
        object.__setattr__(self, "local_numerator", numerator)
        object.__setattr__(self, "local_denominator", denominator)

    @property
    def timeline(self) -> NumericComparison:
        offset_seconds = (
            0 if self.timezone_offset_minutes is None else self.timezone_offset_minutes * 60
        )
        return NumericComparison(
            self.local_numerator - offset_seconds * self.local_denominator,
            self.local_denominator,
        )

    def compare(self, other: DateTimeComparison) -> ComparisonOrder:
        if not isinstance(other, DateTimeComparison):
            raise TypeError("other must be DateTimeComparison")
        if self.timezone_offset_minutes is None and other.timezone_offset_minutes is None:
            comparison = NumericComparison(self.local_numerator, self.local_denominator).compare(
                NumericComparison(other.local_numerator, other.local_denominator)
            )
        elif self.timezone_offset_minutes is not None and other.timezone_offset_minutes is not None:
            comparison = self.timeline.compare(other.timeline)
        else:
            zoned = self if self.timezone_offset_minutes is not None else other
            unzoned = other if zoned is self else self
            point = zoned.timeline
            center = NumericComparison(unzoned.local_numerator, unzoned.local_denominator)
            low = NumericComparison(
                center.numerator - 50_400 * center.denominator, center.denominator
            )
            high = NumericComparison(
                center.numerator + 50_400 * center.denominator, center.denominator
            )
            if point.compare(low) < 0:
                comparison = -1 if zoned is self else 1
            elif point.compare(high) > 0:
                comparison = 1 if zoned is self else -1
            else:
                return ComparisonOrder.UNORDERED
        if comparison < 0:
            return ComparisonOrder.LESS
        if comparison > 0:
            return ComparisonOrder.GREATER
        return ComparisonOrder.EQUAL

    def as_tagged(self) -> tuple[str, str, str, int | None]:
        return (
            "date-time-comparison-v1",
            _integer_token(self.local_numerator),
            _integer_token(self.local_denominator),
            self.timezone_offset_minutes,
        )


DataIdentity: TypeAlias = (
    NumericIdentity
    | BooleanIdentity
    | IEEEIdentity
    | StringIdentity
    | BinaryIdentity
    | URIIdentity
    | XMLIdentity
    | DateTimeIdentity
)


@dataclass(frozen=True, slots=True)
class SymbolicDataWitness:
    """Deterministic existential certificate when no literal identity can denote it.

    This is not a data-value identity and is never returned as an OWL literal. It
    records the exact range digest plus a stable ordinal for solver certificates such
    as an irrational member of ``owl:real`` outside ``owl:rational``.
    """

    family: str
    domain_digest: str
    ordinal: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.family, str) or not self.family:
            raise ValueError("family must be a nonempty string")
        if (
            not isinstance(self.domain_digest, str)
            or len(self.domain_digest) != 64
            or any(char not in "0123456789abcdef" for char in self.domain_digest)
        ):
            raise ValueError("domain_digest must be a lowercase SHA-256 hexadecimal digest")
        if isinstance(self.ordinal, bool) or not isinstance(self.ordinal, int):
            raise TypeError("ordinal must be int")
        if self.ordinal < 0:
            raise ValueError("ordinal must be nonnegative")

    def as_tagged(self) -> tuple[str, str, str, int]:
        return ("symbolic-data-witness-v1", self.family, self.domain_digest, self.ordinal)


DatatypeWitness: TypeAlias = DataIdentity | SymbolicDataWitness
ComparisonValue: TypeAlias = (
    NumericComparison
    | BooleanComparison
    | IEEEComparison
    | StringComparison
    | BinaryComparison
    | URIComparison
    | XMLComparison
    | DateTimeComparison
)


@dataclass(frozen=True, slots=True)
class CompiledLiteral:
    """One exact core literal plus its two distinct private semantic relations."""

    source_literal: Literal
    source_identity: SourceLiteralIdentity
    data_identity: DataIdentity
    comparison: ComparisonValue
    compatibility: LexicalCompatibility

    def __post_init__(self) -> None:
        if not isinstance(self.source_literal, Literal):
            raise TypeError("source_literal must be pyowl_core.model.Literal")
        if self.source_identity != SourceLiteralIdentity.from_literal(self.source_literal):
            raise ValueError("source_identity must describe source_literal exactly")
        if not isinstance(self.compatibility, LexicalCompatibility):
            raise TypeError("compatibility must be LexicalCompatibility")
        numeric = isinstance(self.data_identity, NumericIdentity) and isinstance(
            self.comparison, NumericComparison
        )
        boolean = isinstance(self.data_identity, BooleanIdentity) and isinstance(
            self.comparison, BooleanComparison
        )
        ieee = isinstance(self.data_identity, IEEEIdentity) and isinstance(
            self.comparison, IEEEComparison
        )
        string = isinstance(self.data_identity, StringIdentity) and isinstance(
            self.comparison, StringComparison
        )
        binary = isinstance(self.data_identity, BinaryIdentity) and isinstance(
            self.comparison, BinaryComparison
        )
        uri = isinstance(self.data_identity, URIIdentity) and isinstance(
            self.comparison, URIComparison
        )
        xml = isinstance(self.data_identity, XMLIdentity) and isinstance(
            self.comparison, XMLComparison
        )
        date_time = isinstance(self.data_identity, DateTimeIdentity) and isinstance(
            self.comparison, DateTimeComparison
        )
        if not (numeric or boolean or ieee or string or binary or uri or xml or date_time):
            raise TypeError("data identity and comparison records must use one family")
        if (
            isinstance(self.data_identity, IEEEIdentity)
            and isinstance(self.comparison, IEEEComparison)
            and self.data_identity.format is not self.comparison.format
        ):
            raise ValueError("IEEE identity and comparison formats must agree")
        if (
            isinstance(self.data_identity, BinaryIdentity)
            and isinstance(self.comparison, BinaryComparison)
            and self.data_identity.kind is not self.comparison.kind
        ):
            raise ValueError("binary identity and comparison kinds must agree")

    def as_tagged(self) -> dict[str, object]:
        """Return deterministic language-neutral diagnostics without rebuilding OWL."""

        return {
            "comparison": self.comparison.as_tagged(),
            "compatibility": self.compatibility.value,
            "data_identity": self.data_identity.as_tagged(),
            "source": self.source_identity.as_tagged(),
        }


__all__ = [
    "BinaryComparison",
    "BinaryIdentity",
    "BinaryKind",
    "BooleanComparison",
    "BooleanIdentity",
    "ComparisonOrder",
    "ComparisonValue",
    "CompiledLiteral",
    "DataIdentity",
    "DatatypeLimits",
    "DatatypeWitness",
    "DateTimeComparison",
    "DateTimeIdentity",
    "IEEECategory",
    "IEEEComparison",
    "IEEEFormat",
    "IEEEIdentity",
    "LexicalCompatibility",
    "NumericComparison",
    "NumericDomain",
    "NumericIdentity",
    "SourceLiteralIdentity",
    "StringComparison",
    "StringIdentity",
    "SymbolicDataWitness",
    "URIComparison",
    "URIIdentity",
    "XMLComparison",
    "XMLIdentity",
]
