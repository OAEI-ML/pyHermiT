"""Bounded symbolic automata for the XML Schema regular-expression language.

SPDX-License-Identifier: LGPL-3.0-or-later

Patterns are implicitly anchored, as required by XSD 1.1.  This module uses
Brzozowski derivatives over interval character sets, giving exact intersection,
union, complement, membership, and emptiness without delegating to Python/PCRE.
Unicode general categories are pinned to the stable UCD 3.2 table exposed by all
supported Python versions; updating that table to the OWL-normative Unicode
inventory remains an explicitly tracked WP07 compatibility item.
"""

from __future__ import annotations

import threading
import unicodedata
from collections import deque
from collections.abc import Iterable
from dataclasses import dataclass
from functools import cache, lru_cache
from typing import Final, NoReturn, TypeAlias

from pyhermit.events import CancellationToken
from pyhermit.exceptions import OntologyProfileError, ResourceLimitError

from .model import DatatypeLimits
from .textual import is_xml_character

Interval: TypeAlias = tuple[int, int]

XML_INTERVALS: Final[tuple[Interval, ...]] = (
    (0x9, 0xA),
    (0xD, 0xD),
    (0x20, 0xD7FF),
    (0xE000, 0xFFFD),
    (0x10000, 0x10FFFF),
)
PINNED_UNICODE_VERSION: Final = "3.2.0"


def _normalize_intervals(intervals: tuple[Interval, ...]) -> tuple[Interval, ...]:
    values = sorted(intervals)
    output: list[Interval] = []
    for lower, upper in values:
        if isinstance(lower, bool) or not isinstance(lower, int):
            raise TypeError("character interval lower endpoint must be int")
        if isinstance(upper, bool) or not isinstance(upper, int):
            raise TypeError("character interval upper endpoint must be int")
        if lower < 0 or upper > 0x10FFFF or lower > upper:
            raise ValueError("invalid Unicode character interval")
        if output and lower <= output[-1][1] + 1:
            output[-1] = (output[-1][0], max(output[-1][1], upper))
        else:
            output.append((lower, upper))
    return tuple(output)


@dataclass(frozen=True, slots=True)
class CharSet:
    intervals: tuple[Interval, ...]

    def __post_init__(self) -> None:
        normalized = _normalize_intervals(self.intervals)
        if normalized != self.intervals:
            object.__setattr__(self, "intervals", normalized)

    @classmethod
    def one(cls, codepoint: int) -> CharSet:
        return cls(((codepoint, codepoint),))

    def contains(self, codepoint: int) -> bool:
        for lower, upper in self.intervals:
            if codepoint < lower:
                return False
            if codepoint <= upper:
                return True
        return False

    def union(self, other: CharSet) -> CharSet:
        if not isinstance(other, CharSet):
            raise TypeError("other must be CharSet")
        return CharSet(self.intervals + other.intervals)

    def intersection(self, other: CharSet) -> CharSet:
        if not isinstance(other, CharSet):
            raise TypeError("other must be CharSet")
        output: list[Interval] = []
        left_index = right_index = 0
        while left_index < len(self.intervals) and right_index < len(other.intervals):
            left = self.intervals[left_index]
            right = other.intervals[right_index]
            lower = max(left[0], right[0])
            upper = min(left[1], right[1])
            if lower <= upper:
                output.append((lower, upper))
            if left[1] < right[1]:
                left_index += 1
            else:
                right_index += 1
        return CharSet(tuple(output))

    def difference(self, other: CharSet) -> CharSet:
        if not isinstance(other, CharSet):
            raise TypeError("other must be CharSet")
        output: list[Interval] = []
        for lower, upper in self.intervals:
            cursor = lower
            for excluded_lower, excluded_upper in other.intervals:
                if excluded_upper < cursor:
                    continue
                if excluded_lower > upper:
                    break
                if cursor < excluded_lower:
                    output.append((cursor, min(upper, excluded_lower - 1)))
                cursor = max(cursor, excluded_upper + 1)
                if cursor > upper:
                    break
            if cursor <= upper:
                output.append((cursor, upper))
        return CharSet(tuple(output))

    def complement(self) -> CharSet:
        return XML_CHARACTERS.difference(self)

    def is_empty(self) -> bool:
        return not self.intervals


XML_CHARACTERS: Final = CharSet(XML_INTERVALS)
_SPACE = CharSet(((0x9, 0xA), (0xD, 0xD), (0x20, 0x20)))


@dataclass(frozen=True, slots=True)
class _Empty:
    pass


@dataclass(frozen=True, slots=True)
class _Epsilon:
    pass


@dataclass(frozen=True, slots=True)
class _Characters:
    characters: CharSet


@dataclass(frozen=True, slots=True)
class _Alternative:
    parts: frozenset[_Expr]


@dataclass(frozen=True, slots=True)
class _Sequence:
    parts: tuple[_Expr, ...]


@dataclass(frozen=True, slots=True)
class _Star:
    part: _Expr


@dataclass(frozen=True, slots=True)
class _Intersection:
    parts: frozenset[_Expr]


@dataclass(frozen=True, slots=True)
class _Complement:
    part: _Expr


_Expr: TypeAlias = (
    _Empty | _Epsilon | _Characters | _Alternative | _Sequence | _Star | _Intersection | _Complement
)

_EMPTY = _Empty()
_EPSILON = _Epsilon()


@dataclass(frozen=True, slots=True)
class XSDRegex:
    """One immutable symbolic DFA language over XML characters."""

    _expression: _Expr

    @classmethod
    def compile(
        cls,
        pattern: str,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> XSDRegex:
        if not isinstance(pattern, str):
            raise TypeError("pattern must be str")
        selected_limits = _controls(limits, cancellation)
        if len(pattern) > selected_limits.max_lexical_characters:
            raise ResourceLimitError(
                "pattern exceeds the configured character limit",
                limit="max_lexical_characters",
                observed=len(pattern),
                allowed=selected_limits.max_lexical_characters,
            )
        parser = _Parser(pattern, selected_limits, cancellation)
        return cls(parser.parse())

    @classmethod
    def all(cls) -> XSDRegex:
        return cls(_star(_Characters(XML_CHARACTERS)))

    @classmethod
    def empty(cls) -> XSDRegex:
        return cls(_EMPTY)

    @classmethod
    def characters(cls, characters: CharSet) -> XSDRegex:
        """Return the one-character language for ``characters``."""

        if not isinstance(characters, CharSet):
            raise TypeError("characters must be CharSet")
        return cls(_Characters(characters))

    @classmethod
    def length_range(
        cls,
        minimum: int = 0,
        maximum: int | None = None,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> XSDRegex:
        """Return all XML strings whose code-point length is in the given range."""

        selected_limits = _controls(limits, cancellation)
        if isinstance(minimum, bool) or not isinstance(minimum, int) or minimum < 0:
            raise ValueError("minimum must be a nonnegative integer")
        if maximum is not None and (
            isinstance(maximum, bool) or not isinstance(maximum, int) or maximum < minimum
        ):
            raise ValueError("maximum must be an integer not smaller than minimum or None")
        expansion = minimum if maximum is None else maximum
        if expansion > selected_limits.max_pattern_states:
            raise ResourceLimitError(
                "length language exceeds the configured automaton expansion limit",
                limit="max_pattern_states",
                observed=expansion,
                allowed=selected_limits.max_pattern_states,
            )
        character = _Characters(XML_CHARACTERS)
        required = (character,) * minimum
        if maximum is None:
            return cls(_sequence((*required, _star(character))))
        optional = (_alternative((_EPSILON, character)),) * (maximum - minimum)
        return cls(_sequence((*required, *optional)))

    def fullmatch(
        self,
        value: str,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        if not isinstance(value, str):
            raise TypeError("value must be str")
        selected_limits = _controls(limits, cancellation)
        expression = self._expression
        since_poll = 0
        for char in value:
            if not is_xml_character(char):
                return False
            expression = _derivative(expression, ord(char))
            since_poll += 1
            if since_poll == selected_limits.cancellation_poll_stride:
                _poll(cancellation, since_poll)
                since_poll = 0
        _poll(cancellation, since_poll)
        return _nullable(expression)

    def intersection(self, other: XSDRegex) -> XSDRegex:
        if not isinstance(other, XSDRegex):
            raise TypeError("other must be XSDRegex")
        return XSDRegex(_intersection((self._expression, other._expression)))

    def union(self, other: XSDRegex) -> XSDRegex:
        if not isinstance(other, XSDRegex):
            raise TypeError("other must be XSDRegex")
        return XSDRegex(_alternative((self._expression, other._expression)))

    def complement(self) -> XSDRegex:
        return XSDRegex(_complement(self._expression))

    def is_empty_exact(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        selected_limits = _controls(limits, cancellation)
        pending: deque[_Expr] = deque((self._expression,))
        visited: set[_Expr] = set()
        transitions = 0
        while pending:
            expression = pending.popleft()
            if expression in visited:
                continue
            visited.add(expression)
            if len(visited) > selected_limits.max_pattern_states:
                raise ResourceLimitError(
                    "pattern determinization exceeds the configured state limit",
                    limit="max_pattern_states",
                    observed=len(visited),
                    allowed=selected_limits.max_pattern_states,
                )
            if _nullable(expression):
                return False
            for representative in _representatives(expression):
                derivative = _derivative(expression, representative)
                transitions += 1
                if transitions > selected_limits.max_pattern_transitions:
                    raise ResourceLimitError(
                        "pattern determinization exceeds the configured transition limit",
                        limit="max_pattern_transitions",
                        observed=transitions,
                        allowed=selected_limits.max_pattern_transitions,
                    )
                if derivative is not _EMPTY and derivative not in visited:
                    pending.append(derivative)
            _poll(cancellation, 1)
        return True

    def is_empty(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        """Alias retained for range-protocol consistency."""

        return self.is_empty_exact(limits=limits, cancellation=cancellation)


class _Parser:
    def __init__(
        self,
        pattern: str,
        limits: DatatypeLimits,
        cancellation: CancellationToken | None,
    ) -> None:
        self.pattern = pattern
        self.position = 0
        self.limits = limits
        self.cancellation = cancellation
        self.nodes = 0

    def parse(self) -> _Expr:
        result = self._regular_expression()
        if self.position != len(self.pattern):
            self._syntax("unexpected trailing pattern input")
        return result

    def _regular_expression(self) -> _Expr:
        branches = [self._branch()]
        while self._peek() == "|":
            self.position += 1
            branches.append(self._branch())
        return _alternative(branches)

    def _branch(self) -> _Expr:
        parts: list[_Expr] = []
        while (selected := self._peek()) is not None and selected not in {"|", ")"}:
            parts.append(self._piece())
        return _sequence(parts)

    def _piece(self) -> _Expr:
        atom = self._atom()
        selected = self._peek()
        if selected == "?":
            self.position += 1
            return _alternative((_EPSILON, atom))
        if selected == "*":
            self.position += 1
            return _star(atom)
        if selected == "+":
            self.position += 1
            return _sequence((atom, _star(atom)))
        if selected == "{":
            return self._quantified(atom)
        return atom

    def _atom(self) -> _Expr:
        selected = self._peek()
        if selected is None:
            self._syntax("expected a regular-expression atom")
        self._node()
        if selected == "(":
            self.position += 1
            expression = self._regular_expression()
            if self._peek() != ")":
                self._syntax("unclosed regular-expression group")
            self.position += 1
            return expression
        if selected == "[":
            return _Characters(self._character_class())
        if selected == ".":
            self.position += 1
            return _Characters(XML_CHARACTERS)
        if selected == "\\":
            return _Characters(self._escape())
        if selected in {"?", "*", "+", "{", "}", ")", "]"}:
            self._syntax("metacharacter must be escaped")
        self.position += 1
        return _Characters(CharSet.one(ord(selected)))

    def _quantified(self, atom: _Expr) -> _Expr:
        self.position += 1
        minimum = self._quantity()
        maximum: int | None = minimum
        if self._peek() == ",":
            self.position += 1
            maximum = None if self._peek() == "}" else self._quantity()
        if self._peek() != "}":
            self._syntax("unclosed quantifier")
        self.position += 1
        if maximum is not None and minimum > maximum:
            self._syntax("quantifier minimum exceeds maximum")
        expansion = minimum + (0 if maximum is None else maximum - minimum)
        if expansion > self.limits.max_pattern_states:
            raise ResourceLimitError(
                "pattern quantifier exceeds the configured expansion limit",
                limit="max_pattern_states",
                observed=expansion,
                allowed=self.limits.max_pattern_states,
            )
        required = [atom] * minimum
        if maximum is None:
            return _sequence((*required, _star(atom)))
        optional = [_alternative((_EPSILON, atom))] * (maximum - minimum)
        return _sequence((*required, *optional))

    def _quantity(self) -> int:
        found = False
        value = 0
        while (selected := self._peek()) is not None and "0" <= selected <= "9":
            found = True
            self.position += 1
            value = value * 10 + ord(selected) - ord("0")
            if value > self.limits.max_pattern_states:
                raise ResourceLimitError(
                    "pattern quantifier exceeds the configured expansion limit",
                    limit="max_pattern_states",
                    observed=self.limits.max_pattern_states + 1,
                    allowed=self.limits.max_pattern_states,
                )
        if not found:
            self._syntax("quantifier requires a decimal integer")
        return value

    def _character_class(self) -> CharSet:
        self.position += 1
        negative = self._peek() == "^"
        if negative:
            self.position += 1
        result = CharSet(())
        found = False
        while True:
            selected = self._peek()
            if selected is None:
                self._syntax("unclosed character class")
            if selected == "]":
                if not found:
                    self._syntax("empty character class")
                self.position += 1
                break
            if selected == "-" and self._peek(1) == "[":
                if not found:
                    self._syntax("character-class subtraction requires a left operand")
                self.position += 1
                result = result.difference(self._character_class())
                if self._peek() != "]":
                    self._syntax("character-class subtraction must be final")
                self.position += 1
                break
            first = self._class_atom()
            found = True
            if self._peek() == "-" and self._peek(1) not in {None, "]", "["}:
                self.position += 1
                second = self._class_atom()
                if len(first.intervals) != 1 or first.intervals[0][0] != first.intervals[0][1]:
                    self._syntax("character range start must denote one character")
                if len(second.intervals) != 1 or second.intervals[0][0] != second.intervals[0][1]:
                    self._syntax("character range end must denote one character")
                lower = first.intervals[0][0]
                upper = second.intervals[0][0]
                if lower > upper:
                    self._syntax("character range is reversed")
                first = CharSet(((lower, upper),)).intersection(XML_CHARACTERS)
            result = result.union(first)
        return result.complement() if negative else result

    def _class_atom(self) -> CharSet:
        selected = self._peek()
        if selected is None or selected == "]":
            self._syntax("expected character-class item")
        if selected == "\\":
            return self._escape()
        if selected in {"["}:
            self._syntax("unescaped bracket in character class")
        self.position += 1
        return CharSet.one(ord(selected)).intersection(XML_CHARACTERS)

    def _escape(self) -> CharSet:
        self.position += 1
        selected = self._peek()
        if selected is None:
            self._syntax("trailing escape")
        self.position += 1
        single = {
            "n": "\n",
            "r": "\r",
            "t": "\t",
            "\\": "\\",
            "|": "|",
            ".": ".",
            "-": "-",
            "^": "^",
            "?": "?",
            "*": "*",
            "+": "+",
            "{": "{",
            "}": "}",
            "(": "(",
            ")": ")",
            "[": "[",
            "]": "]",
        }
        if selected in single:
            return CharSet.one(ord(single[selected])).intersection(XML_CHARACTERS)
        if selected == "s":
            return _SPACE
        if selected == "S":
            return _SPACE.complement()
        if selected in {"p", "P"}:
            if self._peek() != "{":
                self._syntax("Unicode category escape requires braces")
            self.position += 1
            start = self.position
            while self._peek() not in {None, "}"}:
                self.position += 1
            if self._peek() != "}":
                self._syntax("unclosed Unicode category escape")
            property_name = self.pattern[start : self.position]
            self.position += 1
            category = _unicode_category(
                property_name,
                limits=self.limits,
                cancellation=self.cancellation,
            )
            return category.complement() if selected == "P" else category
        if selected in {"d", "D"}:
            digits = _unicode_category("Nd", limits=self.limits, cancellation=self.cancellation)
            return digits.complement() if selected == "D" else digits
        if selected in {"w", "W"}:
            excluded = _unicode_category_group(
                ("P", "Z", "C"), limits=self.limits, cancellation=self.cancellation
            )
            word = excluded.complement()
            return word.complement() if selected == "W" else word
        if selected in {"i", "I", "c", "C"}:
            characters = _xml_name_characters(start=selected.lower() == "i")
            return characters.complement() if selected.isupper() else characters
        self._syntax("unknown XML Schema character escape")

    def _node(self) -> None:
        self.nodes += 1
        if self.nodes > self.limits.max_pattern_states:
            raise ResourceLimitError(
                "pattern syntax exceeds the configured node limit",
                limit="max_pattern_states",
                observed=self.nodes,
                allowed=self.limits.max_pattern_states,
            )
        if self.nodes % self.limits.cancellation_poll_stride == 0:
            _poll(self.cancellation, self.limits.cancellation_poll_stride)

    def _peek(self, offset: int = 0) -> str | None:
        position = self.position + offset
        return self.pattern[position] if position < len(self.pattern) else None

    def _syntax(self, message: str) -> NoReturn:
        raise OntologyProfileError(
            message,
            code="INVALID_XSD_PATTERN",
            context={"position": self.position},
        )


@cache
def _nullable(expression: _Expr) -> bool:
    if expression is _EMPTY:
        return False
    if expression is _EPSILON:
        return True
    if isinstance(expression, _Characters):
        return False
    if isinstance(expression, _Alternative):
        return any(_nullable(part) for part in expression.parts)
    if isinstance(expression, _Sequence):
        return all(_nullable(part) for part in expression.parts)
    if isinstance(expression, _Star):
        return True
    if isinstance(expression, _Intersection):
        return all(_nullable(part) for part in expression.parts)
    if not isinstance(expression, _Complement):
        raise AssertionError("unknown regular-expression node")
    return not _nullable(expression.part)


@lru_cache(maxsize=200_000)
def _derivative(expression: _Expr, codepoint: int) -> _Expr:
    if expression is _EMPTY or expression is _EPSILON:
        return _EMPTY
    if isinstance(expression, _Characters):
        return _EPSILON if expression.characters.contains(codepoint) else _EMPTY
    if isinstance(expression, _Alternative):
        return _alternative(_derivative(part, codepoint) for part in expression.parts)
    if isinstance(expression, _Sequence):
        alternatives: list[_Expr] = []
        for index, part in enumerate(expression.parts):
            alternatives.append(
                _sequence((_derivative(part, codepoint), *expression.parts[index + 1 :]))
            )
            if not _nullable(part):
                break
        return _alternative(alternatives)
    if isinstance(expression, _Star):
        return _sequence((_derivative(expression.part, codepoint), expression))
    if isinstance(expression, _Intersection):
        return _intersection(_derivative(part, codepoint) for part in expression.parts)
    if not isinstance(expression, _Complement):
        raise AssertionError("unknown regular-expression node")
    return _complement(_derivative(expression.part, codepoint))


def _alternative(expressions: Iterable[_Expr]) -> _Expr:
    parts: set[_Expr] = set()
    for expression in expressions:
        if expression is _EMPTY:
            continue
        if isinstance(expression, _Alternative):
            parts.update(expression.parts)
        else:
            parts.add(expression)
    if not parts:
        return _EMPTY
    if len(parts) == 1:
        return next(iter(parts))
    return _Alternative(frozenset(parts))


def _sequence(expressions: Iterable[_Expr]) -> _Expr:
    parts: list[_Expr] = []
    for expression in expressions:
        if expression is _EMPTY:
            return _EMPTY
        if expression is _EPSILON:
            continue
        if isinstance(expression, _Sequence):
            parts.extend(expression.parts)
        else:
            parts.append(expression)
    if not parts:
        return _EPSILON
    if len(parts) == 1:
        return parts[0]
    return _Sequence(tuple(parts))


def _star(expression: _Expr) -> _Expr:
    if expression is _EMPTY or expression is _EPSILON:
        return _EPSILON
    if isinstance(expression, _Star):
        return expression
    return _Star(expression)


def _intersection(expressions: Iterable[_Expr]) -> _Expr:
    parts: set[_Expr] = set()
    for expression in expressions:
        if expression is _EMPTY:
            return _EMPTY
        if isinstance(expression, _Intersection):
            parts.update(expression.parts)
        else:
            parts.add(expression)
    if not parts:
        return _complement(_EMPTY)
    if len(parts) == 1:
        return next(iter(parts))
    for part in tuple(parts):
        if _complement(part) in parts:
            return _EMPTY
    return _Intersection(frozenset(parts))


def _complement(expression: _Expr) -> _Expr:
    if isinstance(expression, _Complement):
        return expression.part
    return _Complement(expression)


def _representatives(expression: _Expr) -> tuple[int, ...]:
    boundaries = {value for interval in XML_INTERVALS for value in (interval[0], interval[1] + 1)}
    _collect_boundaries(expression, boundaries)
    ordered = sorted(boundaries)
    representatives: list[int] = []
    for index in range(len(ordered) - 1):
        candidate = ordered[index]
        if candidate < ordered[index + 1] and XML_CHARACTERS.contains(candidate):
            representatives.append(candidate)
    return tuple(representatives)


def _collect_boundaries(expression: _Expr, output: set[int]) -> None:
    if isinstance(expression, _Characters):
        for lower, upper in expression.characters.intervals:
            output.add(lower)
            output.add(upper + 1)
    elif isinstance(expression, (_Alternative, _Intersection, _Sequence)):
        for part in expression.parts:
            _collect_boundaries(part, output)
    elif isinstance(expression, (_Star, _Complement)):
        _collect_boundaries(expression.part, output)


_CATEGORY_CACHE: dict[str, CharSet] = {}
_CATEGORY_LOCK = threading.Lock()


def _unicode_category(
    property_name: str,
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> CharSet:
    valid_major = {"L", "M", "N", "P", "Z", "S", "C"}
    valid_minor = {
        "Lu",
        "Ll",
        "Lt",
        "Lm",
        "Lo",
        "Mn",
        "Mc",
        "Me",
        "Nd",
        "Nl",
        "No",
        "Pc",
        "Pd",
        "Ps",
        "Pe",
        "Pi",
        "Pf",
        "Po",
        "Zs",
        "Zl",
        "Zp",
        "Sm",
        "Sc",
        "Sk",
        "So",
        "Cc",
        "Cf",
        "Co",
        "Cn",
    }
    if property_name.startswith("Is"):
        raise OntologyProfileError(
            "Unicode block escapes await the pinned OWL Unicode block inventory",
            code="UNSUPPORTED_XSD_PATTERN_BLOCK",
            context={"property": property_name},
        )
    if property_name not in valid_major | valid_minor:
        raise OntologyProfileError(
            "unknown XML Schema Unicode category",
            code="INVALID_XSD_PATTERN",
            context={"property": property_name},
        )
    with _CATEGORY_LOCK:
        cached = _CATEGORY_CACHE.get(property_name)
    if cached is not None:
        return cached
    intervals: list[Interval] = []
    start: int | None = None
    previous = -2
    work = 0
    database = unicodedata.ucd_3_2_0
    for lower, upper in XML_INTERVALS:
        for codepoint in range(lower, upper + 1):
            category = database.category(chr(codepoint))
            matches = (
                category == property_name
                if len(property_name) == 2
                else category[0] == property_name
            )
            if matches:
                if start is None:
                    start = codepoint
                elif codepoint != previous + 1:
                    intervals.append((start, previous))
                    start = codepoint
                previous = codepoint
            elif start is not None:
                intervals.append((start, previous))
                start = None
            work += 1
            if work == limits.cancellation_poll_stride * 64:
                _poll(cancellation, work)
                work = 0
    if start is not None:
        intervals.append((start, previous))
    _poll(cancellation, work)
    result = CharSet(tuple(intervals))
    with _CATEGORY_LOCK:
        _CATEGORY_CACHE.setdefault(property_name, result)
        return _CATEGORY_CACHE[property_name]


def _unicode_category_group(
    categories: tuple[str, ...],
    *,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
) -> CharSet:
    result = CharSet(())
    for category in categories:
        result = result.union(_unicode_category(category, limits=limits, cancellation=cancellation))
    return result


@lru_cache(maxsize=2)
def _xml_name_characters(*, start: bool) -> CharSet:
    start_intervals = (
        (0x3A, 0x3A),
        (0x41, 0x5A),
        (0x5F, 0x5F),
        (0x61, 0x7A),
        (0xC0, 0xD6),
        (0xD8, 0xF6),
        (0xF8, 0x2FF),
        (0x370, 0x37D),
        (0x37F, 0x1FFF),
        (0x200C, 0x200D),
        (0x2070, 0x218F),
        (0x2C00, 0x2FEF),
        (0x3001, 0xD7FF),
        (0xF900, 0xFDCF),
        (0xFDF0, 0xFFFD),
        (0x10000, 0xEFFFF),
    )
    result = CharSet(start_intervals).intersection(XML_CHARACTERS)
    if start:
        return result
    return result.union(
        CharSet(((0x2D, 0x2E), (0x30, 0x39), (0xB7, 0xB7), (0x300, 0x36F), (0x203F, 0x2040)))
    )


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
    "PINNED_UNICODE_VERSION",
    "XML_CHARACTERS",
    "CharSet",
    "XSDRegex",
]
