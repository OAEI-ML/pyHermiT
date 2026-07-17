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


@dataclass(frozen=True, slots=True)
class DatatypeLimits:
    """Bounds for hostile lexical forms and finite materialization."""

    max_lexical_characters: int = 1_000_000
    max_numeric_digits: int = 100_000
    max_decimal_exponent: int = 100_000
    max_enumeration_values: int = 100_000
    cancellation_poll_stride: int = 64

    def __post_init__(self) -> None:
        for name in (
            "max_lexical_characters",
            "max_numeric_digits",
            "max_decimal_exponent",
            "max_enumeration_values",
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


DataIdentity: TypeAlias = NumericIdentity | BooleanIdentity
ComparisonValue: TypeAlias = NumericComparison | BooleanComparison


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
        if not (numeric or boolean):
            raise TypeError("data identity and comparison records must use one family")

    def as_tagged(self) -> dict[str, object]:
        """Return deterministic language-neutral diagnostics without rebuilding OWL."""

        return {
            "comparison": self.comparison.as_tagged(),
            "compatibility": self.compatibility.value,
            "data_identity": self.data_identity.as_tagged(),
            "source": self.source_identity.as_tagged(),
        }


__all__ = [
    "BooleanComparison",
    "BooleanIdentity",
    "ComparisonValue",
    "CompiledLiteral",
    "DataIdentity",
    "DatatypeLimits",
    "LexicalCompatibility",
    "NumericComparison",
    "NumericDomain",
    "NumericIdentity",
    "SourceLiteralIdentity",
]
