# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# SPDX-License-Identifier: LGPL-3.0-or-later
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Exact range primitives for OWL's nonnumeric datatype families.

String and URI restrictions retain symbolic XML Schema regular languages.  Plain
literal language tags are represented as a finite union of text/language products,
which keeps intersection, union, complement, and emptiness exact without smuggling a
private separator into either value space.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from functools import cache
from typing import TypeAlias

from pyhermit.events import CancellationToken
from pyhermit.exceptions import ResourceLimitError

from .language_tags import LanguageTagRange
from .model import (
    BinaryComparison,
    BinaryIdentity,
    BinaryKind,
    CompiledLiteral,
    DatatypeLimits,
    StringComparison,
    StringIdentity,
    URIComparison,
    URIIdentity,
    XMLComparison,
    XMLIdentity,
)
from .textual import (
    RDF_PLAIN_LITERAL,
    XSD_LANGUAGE,
    XSD_NAME,
    XSD_NCNAME,
    XSD_NMTOKEN,
    XSD_NORMALIZED_STRING,
    XSD_STRING,
    XSD_TOKEN,
)
from .xsd_regex import XSDRegex


@dataclass(frozen=True, slots=True)
class LengthInterval:
    """One inclusive interval over nonnegative lengths."""

    lower: int = 0
    upper: int | None = None

    def __post_init__(self) -> None:
        if isinstance(self.lower, bool) or not isinstance(self.lower, int) or self.lower < 0:
            raise ValueError("lower must be a nonnegative integer")
        if self.upper is not None and (
            isinstance(self.upper, bool)
            or not isinstance(self.upper, int)
            or self.upper < self.lower
        ):
            raise ValueError("upper must be an integer not smaller than lower or None")

    def contains(self, length: int) -> bool:
        return self.lower <= length and (self.upper is None or length <= self.upper)


@dataclass(frozen=True, slots=True)
class LengthRange:
    """Canonical finite union of length intervals."""

    intervals: tuple[LengthInterval, ...]

    def __post_init__(self) -> None:
        intervals = tuple(self.intervals)
        if not all(isinstance(interval, LengthInterval) for interval in intervals):
            raise TypeError("intervals must contain LengthInterval values")
        object.__setattr__(self, "intervals", _normalize_lengths(intervals))

    @classmethod
    def all(cls) -> LengthRange:
        return cls((LengthInterval(),))

    @classmethod
    def empty(cls) -> LengthRange:
        return cls(())

    @classmethod
    def between(cls, minimum: int = 0, maximum: int | None = None) -> LengthRange:
        return cls((LengthInterval(minimum, maximum),))

    def contains(self, length: int) -> bool:
        if isinstance(length, bool) or not isinstance(length, int):
            raise TypeError("length must be int")
        return any(interval.contains(length) for interval in self.intervals)

    def is_empty_exact(self) -> bool:
        return not self.intervals

    def intersection(self, other: LengthRange) -> LengthRange:
        if not isinstance(other, LengthRange):
            raise TypeError("other must be LengthRange")
        intersections: list[LengthInterval] = []
        for left in self.intervals:
            for right in other.intervals:
                lower = max(left.lower, right.lower)
                if left.upper is None:
                    upper = right.upper
                elif right.upper is None:
                    upper = left.upper
                else:
                    upper = min(left.upper, right.upper)
                if upper is None or lower <= upper:
                    intersections.append(LengthInterval(lower, upper))
        return LengthRange(tuple(intersections))

    def union(self, other: LengthRange) -> LengthRange:
        if not isinstance(other, LengthRange):
            raise TypeError("other must be LengthRange")
        return LengthRange(self.intervals + other.intervals)

    def complement(self) -> LengthRange:
        cursor = 0
        output: list[LengthInterval] = []
        for interval in self.intervals:
            if cursor < interval.lower:
                output.append(LengthInterval(cursor, interval.lower - 1))
            if interval.upper is None:
                return LengthRange(tuple(output))
            cursor = interval.upper + 1
        output.append(LengthInterval(cursor, None))
        return LengthRange(tuple(output))


BinaryValue: TypeAlias = BinaryIdentity | BinaryComparison | CompiledLiteral


@dataclass(frozen=True, slots=True)
class BinaryRange:
    """A byte-length subset of one disjoint binary primitive value space."""

    kind: BinaryKind
    lengths: LengthRange

    def __post_init__(self) -> None:
        if not isinstance(self.kind, BinaryKind):
            raise TypeError("kind must be BinaryKind")
        if not isinstance(self.lengths, LengthRange):
            raise TypeError("lengths must be LengthRange")

    @classmethod
    def all(cls, kind: BinaryKind) -> BinaryRange:
        return cls(kind, LengthRange.all())

    @classmethod
    def empty(cls, kind: BinaryKind) -> BinaryRange:
        return cls(kind, LengthRange.empty())

    def contains(self, value: BinaryValue) -> bool:
        selected = _binary_value(value)
        return (
            selected is not None
            and selected.kind is self.kind
            and self.lengths.contains(len(selected.octets))
        )

    def is_empty_exact(self) -> bool:
        return self.lengths.is_empty_exact()

    def intersection(self, other: BinaryRange) -> BinaryRange:
        self._require_kind(other)
        return BinaryRange(self.kind, self.lengths.intersection(other.lengths))

    def union(self, other: BinaryRange) -> BinaryRange:
        self._require_kind(other)
        return BinaryRange(self.kind, self.lengths.union(other.lengths))

    def complement(self) -> BinaryRange:
        return BinaryRange(self.kind, self.lengths.complement())

    def finite_cardinality(self) -> int | None:
        total = 0
        for interval in self.lengths.intervals:
            if interval.upper is None:
                return None
            if interval.upper > DatatypeLimits().max_binary_bytes:
                # The exact value is finite but intentionally not materialized as
                # a hostile multi-million-bit Python integer.
                return None
            # Geometric sum of 256**length, avoiding one enormous intermediate
            # allocation per length in wide finite intervals.
            total += ((1 << ((interval.upper + 1) * 8)) - (1 << (interval.lower * 8))) // 255
        return total

    def cardinality_at_least(
        self,
        minimum: int,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        """Compare exactly while capping geometric byte-string counts."""

        if isinstance(minimum, bool) or not isinstance(minimum, int):
            raise TypeError("minimum must be int")
        if minimum < 0:
            raise ValueError("minimum must be nonnegative")
        return (
            self.cardinality_up_to(
                minimum,
                limits=limits,
                cancellation=cancellation,
            )
            == minimum
        )

    def cardinality_up_to(
        self,
        maximum: int,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> int:
        """Return ``min(actual cardinality, maximum)`` without giant integers."""

        selected_limits = _controls(limits, cancellation)
        if isinstance(maximum, bool) or not isinstance(maximum, int):
            raise TypeError("maximum must be int")
        if maximum < 0:
            raise ValueError("maximum must be nonnegative")
        if maximum == 0:
            return 0
        total = 0
        work = 0
        for interval in self.lengths.intervals:
            if interval.upper is None:
                return maximum
            remaining_lengths = interval.upper - interval.lower + 1
            exponent = interval.lower * 8
            if exponent >= (maximum - total).bit_length():
                return maximum
            term = 1 << exponent
            while remaining_lengths and total < maximum:
                total += term
                term <<= 8
                remaining_lengths -= 1
                work += 1
                if work == selected_limits.cancellation_poll_stride:
                    _poll(cancellation, work)
                    work = 0
            if total >= maximum:
                return maximum
        _poll(cancellation, work)
        return total

    def enumerate_values(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> tuple[BinaryIdentity, ...]:
        selected_limits = _controls(limits, cancellation)
        cardinality = self.finite_cardinality()
        if cardinality is None:
            raise ValueError("cannot enumerate an infinite binary range")
        if cardinality > selected_limits.max_enumeration_values:
            raise ResourceLimitError(
                "binary range enumeration exceeds the configured value limit",
                limit="max_enumeration_values",
                observed=cardinality,
                allowed=selected_limits.max_enumeration_values,
            )
        output: list[BinaryIdentity] = []
        work = 0
        for interval in self.lengths.intervals:
            if interval.upper is None:
                raise AssertionError("finite binary range has an unbounded length")
            for length in range(interval.lower, interval.upper + 1):
                for number in range(1 << (length * 8)):
                    output.append(BinaryIdentity(self.kind, number.to_bytes(length, "big")))
                    work += 1
                    if work == selected_limits.cancellation_poll_stride:
                        _poll(cancellation, work)
                        work = 0
        _poll(cancellation, work)
        return tuple(output)

    def first_identity(
        self,
        *,
        excluding: Iterable[BinaryIdentity] = (),
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> BinaryIdentity:
        """Return the deterministic least-length/lexicographic available value."""

        selected_limits = _controls(limits, cancellation)
        forbidden = frozenset(excluding)
        if not all(isinstance(value, BinaryIdentity) for value in forbidden):
            raise TypeError("excluding must contain BinaryIdentity values")
        by_length: dict[int, set[int]] = {}
        for value in forbidden:
            if value.kind is self.kind:
                by_length.setdefault(len(value.octets), set()).add(
                    int.from_bytes(value.octets, "big")
                )
        for interval in self.lengths.intervals:
            length = interval.lower
            while interval.upper is None or length <= interval.upper:
                if length > selected_limits.max_binary_bytes:
                    raise ResourceLimitError(
                        "binary witness exceeds the configured byte limit",
                        limit="max_binary_bytes",
                        observed=length,
                        allowed=selected_limits.max_binary_bytes,
                    )
                blocked = by_length.get(length, set())
                number = 0
                while number in blocked:
                    number += 1
                if number.bit_length() <= length * 8:
                    return BinaryIdentity(self.kind, number.to_bytes(length, "big"))
                length += 1
                _poll(cancellation, 1)
        raise ValueError("binary range has no nonexcluded member")

    def _require_kind(self, other: BinaryRange) -> None:
        if not isinstance(other, BinaryRange):
            raise TypeError("other must be BinaryRange")
        if self.kind is not other.kind:
            raise ValueError("hexBinary and base64Binary value spaces are disjoint")


@dataclass(frozen=True, slots=True)
class TextLanguageRectangle:
    """One symbolic product of text and nonempty language-tag languages."""

    text: XSDRegex
    language: LanguageTagRange

    def __post_init__(self) -> None:
        if not isinstance(self.text, XSDRegex) or not isinstance(self.language, LanguageTagRange):
            raise TypeError("text must be XSDRegex and language must be LanguageTagRange")

    def intersection(self, other: TextLanguageRectangle) -> TextLanguageRectangle:
        if not isinstance(other, TextLanguageRectangle):
            raise TypeError("other must be TextLanguageRectangle")
        return TextLanguageRectangle(
            self.text.intersection(other.text),
            self.language.intersection(other.language),
        )

    def is_empty_exact(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        return self.text.is_empty_exact(
            limits=limits, cancellation=cancellation
        ) or self.language.is_empty_exact(limits=limits, cancellation=cancellation)


StringValue: TypeAlias = StringIdentity | StringComparison | CompiledLiteral


@dataclass(frozen=True, slots=True)
class StringRange:
    """Exact regular-language subset of one OWL string-family datatype."""

    datatype_iri: str
    universe_without_language: XSDRegex
    universe_with_language: TextLanguageRectangle | None
    without_language: XSDRegex
    with_language: tuple[TextLanguageRectangle, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.datatype_iri, str) or not self.datatype_iri:
            raise ValueError("datatype_iri must be a nonempty string")
        if not isinstance(self.universe_without_language, XSDRegex):
            raise TypeError("universe_without_language must be XSDRegex")
        if self.universe_with_language is not None and not isinstance(
            self.universe_with_language, TextLanguageRectangle
        ):
            raise TypeError("universe_with_language must be TextLanguageRectangle or None")
        if not isinstance(self.without_language, XSDRegex):
            raise TypeError("without_language must be XSDRegex")
        clauses = tuple(dict.fromkeys(self.with_language))
        if not all(isinstance(clause, TextLanguageRectangle) for clause in clauses):
            raise TypeError("with_language must contain TextLanguageRectangle values")
        if self.universe_with_language is None and clauses:
            raise ValueError("this datatype does not contain language-tagged values")
        if len(clauses) > DatatypeLimits().max_pattern_states:
            raise ResourceLimitError(
                "plain-literal product range exceeds the configured clause limit",
                limit="max_pattern_states",
                observed=len(clauses),
                allowed=DatatypeLimits().max_pattern_states,
            )
        object.__setattr__(self, "with_language", clauses)

    @classmethod
    def all(cls, datatype_iri: str) -> StringRange:
        absent, present = _string_universe(datatype_iri)
        return cls(datatype_iri, absent, present, absent, (() if present is None else (present,)))

    @classmethod
    def empty(cls, datatype_iri: str) -> StringRange:
        absent, present = _string_universe(datatype_iri)
        return cls(datatype_iri, absent, present, XSDRegex.empty(), ())

    def contains(self, value: StringValue) -> bool:
        selected = _string_value(value)
        if selected is None:
            return False
        if selected.language is None:
            return self.without_language.fullmatch(selected.text)
        return any(
            clause.text.fullmatch(selected.text) and clause.language.contains(selected.language)
            for clause in self.with_language
        )

    def is_empty_exact(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        selected_limits = _controls(limits, cancellation)
        if not self.without_language.is_empty_exact(
            limits=selected_limits, cancellation=cancellation
        ):
            return False
        return all(
            clause.is_empty_exact(limits=selected_limits, cancellation=cancellation)
            for clause in self.with_language
        )

    def intersection(self, other: StringRange) -> StringRange:
        self._require_universe(other)
        return StringRange(
            self.datatype_iri,
            self.universe_without_language,
            self.universe_with_language,
            self.without_language.intersection(other.without_language),
            tuple(
                left.intersection(right)
                for left in self.with_language
                for right in other.with_language
            ),
        )

    def union(self, other: StringRange) -> StringRange:
        self._require_universe(other)
        return StringRange(
            self.datatype_iri,
            self.universe_without_language,
            self.universe_with_language,
            self.without_language.union(other.without_language),
            self.with_language + other.with_language,
        )

    def complement(self) -> StringRange:
        absent = self.universe_without_language.intersection(self.without_language.complement())
        present: tuple[TextLanguageRectangle, ...]
        if self.universe_with_language is None:
            present = ()
        else:
            clauses: tuple[TextLanguageRectangle, ...] = (self.universe_with_language,)
            for excluded in self.with_language:
                expanded: list[TextLanguageRectangle] = []
                for retained in clauses:
                    expanded.extend(
                        (
                            TextLanguageRectangle(
                                retained.text.intersection(excluded.text.complement()),
                                retained.language,
                            ),
                            TextLanguageRectangle(
                                retained.text,
                                retained.language.intersection(excluded.language.complement()),
                            ),
                        )
                    )
                clauses = tuple(dict.fromkeys(expanded))
                if len(clauses) > DatatypeLimits().max_pattern_states:
                    raise ResourceLimitError(
                        "plain-literal complement exceeds the configured clause limit",
                        limit="max_pattern_states",
                        observed=len(clauses),
                        allowed=DatatypeLimits().max_pattern_states,
                    )
            present = clauses
        return StringRange(
            self.datatype_iri,
            self.universe_without_language,
            self.universe_with_language,
            absent,
            present,
        )

    def with_text_language(self, language: LanguageTagRange) -> StringRange:
        """Intersect this range with a case-folded language-range language."""

        if not isinstance(language, LanguageTagRange):
            raise TypeError("language must be LanguageTagRange")
        return StringRange(
            self.datatype_iri,
            self.universe_without_language,
            self.universe_with_language,
            XSDRegex.empty(),
            tuple(
                TextLanguageRectangle(clause.text, clause.language.intersection(language))
                for clause in self.with_language
            ),
        )

    def with_text_pattern(self, pattern: XSDRegex) -> StringRange:
        if not isinstance(pattern, XSDRegex):
            raise TypeError("pattern must be XSDRegex")
        return StringRange(
            self.datatype_iri,
            self.universe_without_language,
            self.universe_with_language,
            self.without_language.intersection(pattern),
            tuple(
                TextLanguageRectangle(clause.text.intersection(pattern), clause.language)
                for clause in self.with_language
            ),
        )

    def finite_cardinality(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> int | None:
        selected_limits = _controls(limits, cancellation)
        absent = self.without_language.finite_cardinality(
            limits=selected_limits,
            cancellation=cancellation,
        )
        if absent is None:
            return None
        total = absent
        for clause in _disjoint_text_language_rectangles(
            self.with_language,
            limits=selected_limits,
            cancellation=cancellation,
        ):
            text_count = clause.text.finite_cardinality(
                limits=selected_limits,
                cancellation=cancellation,
            )
            language_count = clause.language.finite_cardinality(
                limits=selected_limits,
                cancellation=cancellation,
            )
            if text_count == 0 or language_count == 0:
                continue
            if text_count is None or language_count is None:
                return None
            total += text_count * language_count
        return total

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
        return (
            self.cardinality_up_to(
                minimum,
                limits=limits,
                cancellation=cancellation,
            )
            == minimum
        )

    def cardinality_up_to(
        self,
        maximum: int,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> int:
        if isinstance(maximum, bool) or not isinstance(maximum, int):
            raise TypeError("maximum must be int")
        if maximum < 0:
            raise ValueError("maximum must be nonnegative")
        if maximum == 0:
            return 0
        selected_limits = _controls(limits, cancellation)
        total = self.without_language.cardinality_up_to(
            maximum,
            limits=selected_limits,
            cancellation=cancellation,
        )
        if total == maximum:
            return maximum
        for clause in _disjoint_text_language_rectangles(
            self.with_language,
            limits=selected_limits,
            cancellation=cancellation,
        ):
            remaining = maximum - total
            text_count = clause.text.cardinality_up_to(
                remaining,
                limits=selected_limits,
                cancellation=cancellation,
            )
            if text_count == 0:
                continue
            if text_count == remaining:
                language_count = clause.language.cardinality_up_to(
                    1,
                    limits=selected_limits,
                    cancellation=cancellation,
                )
                if language_count:
                    return maximum
                continue
            language_limit = (remaining + text_count - 1) // text_count
            language_count = clause.language.cardinality_up_to(
                language_limit,
                limits=selected_limits,
                cancellation=cancellation,
            )
            total += min(remaining, text_count * language_count)
            if total == maximum:
                return maximum
        return total

    def enumerate_values(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> tuple[StringIdentity, ...]:
        selected_limits = _controls(limits, cancellation)
        cardinality = self.finite_cardinality(
            limits=selected_limits,
            cancellation=cancellation,
        )
        if cardinality is None:
            raise ValueError("cannot enumerate an infinite symbolic string range")
        if cardinality > selected_limits.max_enumeration_values:
            raise ResourceLimitError(
                "string-range enumeration exceeds the configured value limit",
                limit="max_enumeration_values",
                observed=cardinality,
                allowed=selected_limits.max_enumeration_values,
            )
        output = {
            StringIdentity(text)
            for text in self.without_language.enumerate_strings(
                limits=selected_limits,
                cancellation=cancellation,
            )
        }
        for clause in _disjoint_text_language_rectangles(
            self.with_language,
            limits=selected_limits,
            cancellation=cancellation,
        ):
            texts = clause.text.enumerate_strings(
                limits=selected_limits,
                cancellation=cancellation,
            )
            languages = clause.language.enumerate_tags(
                limits=selected_limits,
                cancellation=cancellation,
            )
            output.update(
                StringIdentity(text, language) for text in texts for language in languages
            )
        if len(output) != cardinality:
            raise AssertionError("string-range cardinality and enumeration disagree")
        return tuple(sorted(output, key=lambda value: (value.text, value.language or "")))

    def first_identity(
        self,
        *,
        excluding: Iterable[StringIdentity] = (),
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> StringIdentity:
        """Return the deterministic first text/language product member."""

        selected_limits = _controls(limits, cancellation)
        forbidden = frozenset(excluding)
        if not all(isinstance(value, StringIdentity) for value in forbidden):
            raise TypeError("excluding must contain StringIdentity values")
        try:
            text = self.without_language.first_string(
                excluding=(value.text for value in forbidden if value.language is None),
                limits=selected_limits,
                cancellation=cancellation,
            )
        except ValueError:
            pass
        else:
            return StringIdentity(text)
        for clause in self.with_language:
            skipped_texts: set[str] = set()
            for _attempt in range(len(forbidden) + 1):
                try:
                    text = clause.text.first_string(
                        excluding=skipped_texts,
                        limits=selected_limits,
                        cancellation=cancellation,
                    )
                except ValueError:
                    break
                try:
                    language = clause.language.first_tag(
                        excluding=(
                            value.language
                            for value in forbidden
                            if value.text == text and value.language is not None
                        ),
                        limits=selected_limits,
                        cancellation=cancellation,
                    )
                except ValueError:
                    skipped_texts.add(text)
                    continue
                return StringIdentity(text, language)
        raise ValueError("string range has no nonexcluded member")

    def _require_universe(self, other: StringRange) -> None:
        if not isinstance(other, StringRange):
            raise TypeError("other must be StringRange")
        if self.datatype_iri != other.datatype_iri:
            raise ValueError("string-range algebra requires the same declared datatype")


URIValue: TypeAlias = URIIdentity | URIComparison | CompiledLiteral


@dataclass(frozen=True, slots=True)
class URIRange:
    """Exact regular-language subset of the disjoint xsd:anyURI value space."""

    universe: XSDRegex
    language: XSDRegex

    def __post_init__(self) -> None:
        if not isinstance(self.universe, XSDRegex) or not isinstance(self.language, XSDRegex):
            raise TypeError("universe and language must be XSDRegex values")

    @classmethod
    def all(cls) -> URIRange:
        universe = XSDRegex.all()
        return cls(universe, universe)

    @classmethod
    def empty(cls) -> URIRange:
        return cls(XSDRegex.all(), XSDRegex.empty())

    def contains(self, value: URIValue) -> bool:
        selected = _uri_value(value)
        return selected is not None and self.language.fullmatch(selected.value)

    def is_empty_exact(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        return self.language.is_empty_exact(limits=limits, cancellation=cancellation)

    def intersection(self, other: URIRange) -> URIRange:
        if not isinstance(other, URIRange):
            raise TypeError("other must be URIRange")
        return URIRange(self.universe, self.language.intersection(other.language))

    def union(self, other: URIRange) -> URIRange:
        if not isinstance(other, URIRange):
            raise TypeError("other must be URIRange")
        return URIRange(self.universe, self.language.union(other.language))

    def complement(self) -> URIRange:
        return URIRange(self.universe, self.universe.intersection(self.language.complement()))

    def finite_cardinality(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> int | None:
        return self.language.finite_cardinality(
            limits=limits,
            cancellation=cancellation,
        )

    def cardinality_at_least(
        self,
        minimum: int,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        return self.language.cardinality_at_least(
            minimum,
            limits=limits,
            cancellation=cancellation,
        )

    def cardinality_up_to(
        self,
        maximum: int,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> int:
        return self.language.cardinality_up_to(
            maximum,
            limits=limits,
            cancellation=cancellation,
        )

    def enumerate_values(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> tuple[URIIdentity, ...]:
        return tuple(
            URIIdentity(value)
            for value in self.language.enumerate_strings(
                limits=limits,
                cancellation=cancellation,
            )
        )

    def first_identity(
        self,
        *,
        excluding: Iterable[URIIdentity] = (),
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> URIIdentity:
        forbidden = frozenset(excluding)
        if not all(isinstance(value, URIIdentity) for value in forbidden):
            raise TypeError("excluding must contain URIIdentity values")
        return URIIdentity(
            self.language.first_string(
                excluding=(value.value for value in forbidden),
                limits=limits,
                cancellation=cancellation,
            )
        )


XMLValue: TypeAlias = XMLIdentity | XMLComparison | CompiledLiteral


@dataclass(frozen=True, slots=True)
class XMLRange:
    """The unfaceted XMLLiteral space or its exact complement."""

    include_all: bool

    def __post_init__(self) -> None:
        if not isinstance(self.include_all, bool):
            raise TypeError("include_all must be bool")

    @classmethod
    def all(cls) -> XMLRange:
        return cls(True)

    @classmethod
    def empty(cls) -> XMLRange:
        return cls(False)

    def contains(self, value: XMLValue) -> bool:
        return self.include_all and _xml_value(value) is not None

    def is_empty_exact(self) -> bool:
        return not self.include_all

    def intersection(self, other: XMLRange) -> XMLRange:
        if not isinstance(other, XMLRange):
            raise TypeError("other must be XMLRange")
        return XMLRange(self.include_all and other.include_all)

    def union(self, other: XMLRange) -> XMLRange:
        if not isinstance(other, XMLRange):
            raise TypeError("other must be XMLRange")
        return XMLRange(self.include_all or other.include_all)

    def complement(self) -> XMLRange:
        return XMLRange(not self.include_all)

    def finite_cardinality(self) -> int | None:
        return None if self.include_all else 0

    def first_identity(self, *, excluding: Iterable[XMLIdentity] = ()) -> XMLIdentity:
        forbidden = frozenset(excluding)
        if not all(isinstance(value, XMLIdentity) for value in forbidden):
            raise TypeError("excluding must contain XMLIdentity values")
        if not self.include_all:
            raise ValueError("XML range is empty")
        index = 0
        while True:
            # Plain character data is a valid XML fragment and already canonical.
            candidate = XMLIdentity("" if index == 0 else str(index - 1))
            if candidate not in forbidden:
                return candidate
            index += 1


@dataclass(frozen=True, slots=True)
class LiteralRange:
    """The universal rdfs:Literal data domain or its empty complement."""

    include_all: bool

    @classmethod
    def all(cls) -> LiteralRange:
        return cls(True)

    @classmethod
    def empty(cls) -> LiteralRange:
        return cls(False)

    def contains(self, value: object) -> bool:
        return self.include_all and isinstance(value, CompiledLiteral)

    def is_empty_exact(self) -> bool:
        return not self.include_all

    def intersection(self, other: LiteralRange) -> LiteralRange:
        if not isinstance(other, LiteralRange):
            raise TypeError("other must be LiteralRange")
        return LiteralRange(self.include_all and other.include_all)

    def union(self, other: LiteralRange) -> LiteralRange:
        if not isinstance(other, LiteralRange):
            raise TypeError("other must be LiteralRange")
        return LiteralRange(self.include_all or other.include_all)

    def complement(self) -> LiteralRange:
        return LiteralRange(not self.include_all)

    def finite_cardinality(self) -> int | None:
        return None if self.include_all else 0


def length_regex(
    lengths: LengthRange,
    *,
    limits: DatatypeLimits | None = None,
    cancellation: CancellationToken | None = None,
) -> XSDRegex:
    """Convert a canonical length union into an exact symbolic language."""

    if not isinstance(lengths, LengthRange):
        raise TypeError("lengths must be LengthRange")
    result = XSDRegex.empty()
    for interval in lengths.intervals:
        result = result.union(
            XSDRegex.length_range(
                interval.lower,
                interval.upper,
                limits=limits,
                cancellation=cancellation,
            )
        )
    return result


def _disjoint_text_language_rectangles(
    clauses: tuple[TextLanguageRectangle, ...],
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> tuple[TextLanguageRectangle, ...]:
    output: list[TextLanguageRectangle] = []
    for clause in clauses:
        pending = [clause]
        for excluded in output:
            retained: list[TextLanguageRectangle] = []
            for value in pending:
                pieces = (
                    TextLanguageRectangle(
                        value.text.intersection(excluded.text.complement()),
                        value.language,
                    ),
                    TextLanguageRectangle(
                        value.text.intersection(excluded.text),
                        value.language.intersection(excluded.language.complement()),
                    ),
                )
                retained.extend(
                    piece
                    for piece in pieces
                    if not piece.is_empty_exact(
                        limits=limits,
                        cancellation=cancellation,
                    )
                )
            pending = retained
            if not pending:
                break
        output.extend(pending)
        if len(output) > limits.max_pattern_states:
            raise ResourceLimitError(
                "plain-literal disjointization exceeds the configured clause limit",
                limit="max_pattern_states",
                observed=len(output),
                allowed=limits.max_pattern_states,
            )
        _poll(cancellation, 1)
    return tuple(output)


@cache
def _string_universe(
    datatype_iri: str,
) -> tuple[XSDRegex, TextLanguageRectangle | None]:
    patterns = {
        RDF_PLAIN_LITERAL: ".*",
        XSD_STRING: ".*",
        XSD_NORMALIZED_STRING: "[^\\t\\n\\r]*",
        XSD_TOKEN: "([^\\t\\n\\r ]+( [^\\t\\n\\r ]+)*)?",
        XSD_LANGUAGE: "[A-Za-z]{1,8}(-[A-Za-z0-9]{1,8})*",
        XSD_NAME: "\\i\\c*",
        XSD_NCNAME: "[\\i-[:]][\\c-[:]]*",
        XSD_NMTOKEN: "\\c+",
    }
    pattern = patterns.get(datatype_iri)
    if pattern is None:
        raise ValueError("datatype is not in the OWL string family")
    text = XSDRegex.compile(pattern)
    if datatype_iri != RDF_PLAIN_LITERAL:
        return text, None
    return text, TextLanguageRectangle(text, LanguageTagRange.all())


def _normalize_lengths(intervals: Iterable[LengthInterval]) -> tuple[LengthInterval, ...]:
    ordered = sorted(intervals, key=lambda interval: interval.lower)
    output: list[LengthInterval] = []
    for interval in ordered:
        if not output:
            output.append(interval)
            continue
        prior = output[-1]
        if prior.upper is None:
            continue
        if interval.lower <= prior.upper + 1:
            upper = None if interval.upper is None else max(prior.upper, interval.upper)
            output[-1] = LengthInterval(prior.lower, upper)
        else:
            output.append(interval)
    return tuple(output)


def _binary_value(value: BinaryValue) -> BinaryComparison | None:
    selected = value.comparison if isinstance(value, CompiledLiteral) else value
    if isinstance(selected, BinaryIdentity):
        return BinaryComparison(selected.kind, selected.octets)
    return selected if isinstance(selected, BinaryComparison) else None


def _string_value(value: StringValue) -> StringComparison | None:
    selected = value.comparison if isinstance(value, CompiledLiteral) else value
    if isinstance(selected, StringIdentity):
        return StringComparison(selected.text, selected.language)
    return selected if isinstance(selected, StringComparison) else None


def _uri_value(value: URIValue) -> URIComparison | None:
    selected = value.comparison if isinstance(value, CompiledLiteral) else value
    if isinstance(selected, URIIdentity):
        return URIComparison(selected.value)
    return selected if isinstance(selected, URIComparison) else None


def _xml_value(value: XMLValue) -> XMLComparison | None:
    selected = value.comparison if isinstance(value, CompiledLiteral) else value
    if isinstance(selected, XMLIdentity):
        return XMLComparison(selected.canonical_xml)
    return selected if isinstance(selected, XMLComparison) else None


def _controls(
    limits: DatatypeLimits | None,
    cancellation: CancellationToken | None,
) -> DatatypeLimits:
    selected = limits or DatatypeLimits()
    if not isinstance(selected, DatatypeLimits):
        raise TypeError("limits must be DatatypeLimits or None")
    if cancellation is not None and not isinstance(cancellation, CancellationToken):
        raise TypeError("cancellation must be CancellationToken or None")
    _poll(cancellation)
    return selected


def _poll(cancellation: CancellationToken | None, work: int = 0) -> None:
    if cancellation is None:
        return
    if work:
        cancellation.add_work(work)
    cancellation.check()


__all__ = [
    "BinaryRange",
    "BinaryValue",
    "LengthInterval",
    "LengthRange",
    "LiteralRange",
    "StringRange",
    "StringValue",
    "TextLanguageRectangle",
    "URIRange",
    "URIValue",
    "XMLRange",
    "XMLValue",
    "length_regex",
]
