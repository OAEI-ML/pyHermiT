"""Exact canonical BCP 47 language-tag subsets for ``rdf:langRange``.

SPDX-License-Identifier: LGPL-3.0-or-later

Core OWL literals admit only structurally valid, lowercase BCP 47 tags. Treating the
language dimension as ``.+`` creates phantom values (for example tags with duplicate
variants or extension singletons) during complement and cardinality reasoning. This
module keeps a bounded Boolean algebra of RFC 4647 basic-prefix predicates and decides
it over the exact core tag universe.

OWL 2 permits basic filtering here, while string ``pattern`` facets apply to lexical
text rather than to the tag. A conjunction therefore has at most one effective
positive prefix plus finitely many excluded descendant prefixes. Every nonempty
regular/private-use subtree is infinite; only legacy ``i-*`` and irregular
grandfathered leaves can form finite cells.
"""

from __future__ import annotations

import re
from collections.abc import Iterable
from dataclasses import dataclass

from pyhermit.events import CancellationToken
from pyhermit.exceptions import ResourceLimitError

from .model import DatatypeLimits

_LANGUAGE = re.compile(
    r"^(?:"
    r"(?:[A-Za-z]{2,3}(?:-[A-Za-z]{3}){0,3}|[A-Za-z]{4}|[A-Za-z]{5,8})"
    r"(?:-[A-Za-z]{4})?(?:-(?:[A-Za-z]{2}|[0-9]{3}))?"
    r"(?:-(?:[A-Za-z0-9]{5,8}|[0-9][A-Za-z0-9]{3}))*"
    r"(?:-[0-9A-WY-Za-wy-z](?:-[A-Za-z0-9]{2,8})+)*"
    r"(?:-x(?:-[A-Za-z0-9]{1,8})+)?"
    r"|x(?:-[A-Za-z0-9]{1,8})+"
    r"|(?:en-GB-oed|i-ami|i-bnn|i-default|i-enochian|i-hak|i-klingon|i-lux|"
    r"i-mingo|i-navajo|i-pwn|i-tao|i-tay|i-tsu|sgn-BE-FR|sgn-BE-NL|sgn-CH-DE)"
    r"|(?:art-lojban|cel-gaulish|no-bok|no-nyn|zh-guoyu|zh-hakka|zh-min|"
    r"zh-min-nan|zh-xiang)"
    r")$",
    re.IGNORECASE,
)
_GRANDFATHERED = frozenset(
    {
        "art-lojban",
        "cel-gaulish",
        "en-gb-oed",
        "i-ami",
        "i-bnn",
        "i-default",
        "i-enochian",
        "i-hak",
        "i-klingon",
        "i-lux",
        "i-mingo",
        "i-navajo",
        "i-pwn",
        "i-tao",
        "i-tay",
        "i-tsu",
        "no-bok",
        "no-nyn",
        "sgn-be-fr",
        "sgn-be-nl",
        "sgn-ch-de",
        "zh-guoyu",
        "zh-hakka",
        "zh-min",
        "zh-min-nan",
        "zh-xiang",
    }
)
_I_GRANDFATHERED = tuple(sorted(tag for tag in _GRANDFATHERED if tag.startswith("i-")))
_IRREGULAR_LEAVES = frozenset({"en-gb-oed", "sgn-be-fr", "sgn-be-nl", "sgn-ch-de"})
_ALPHANUMERIC = "abcdefghijklmnopqrstuvwxyz0123456789"


def is_valid_language_tag(language: str) -> bool:
    """Return whether ``language`` has the exact core BCP 47 structure."""

    if not isinstance(language, str) or _LANGUAGE.fullmatch(language) is None:
        return False
    lowered = language.lower()
    if lowered in _GRANDFATHERED or lowered.startswith("x-"):
        return True
    parts = lowered.split("-")
    index = 1
    if len(parts[0]) in {2, 3}:
        extlangs = 0
        while index < len(parts) and len(parts[index]) == 3 and parts[index].isalpha():
            extlangs += 1
            index += 1
            if extlangs == 3:
                break
    if index < len(parts) and len(parts[index]) == 4 and parts[index].isalpha():
        index += 1
    if index < len(parts) and (
        (len(parts[index]) == 2 and parts[index].isalpha())
        or (len(parts[index]) == 3 and parts[index].isdigit())
    ):
        index += 1
    variants: set[str] = set()
    while index < len(parts) and (
        5 <= len(parts[index]) <= 8 or (len(parts[index]) == 4 and parts[index][0].isdigit())
    ):
        if parts[index] in variants:
            return False
        variants.add(parts[index])
        index += 1
    singletons: set[str] = set()
    while index < len(parts) and len(parts[index]) == 1 and parts[index] != "x":
        if parts[index] in singletons:
            return False
        singletons.add(parts[index])
        index += 1
        while index < len(parts) and 2 <= len(parts[index]) <= 8:
            index += 1
    return True


@dataclass(frozen=True, slots=True, order=True)
class _TagAtom:
    prefix: tuple[str, ...]
    positive: bool


_Clause = tuple[_TagAtom, ...]
_DNF = tuple[_Clause, ...]


@dataclass(frozen=True, slots=True)
class LanguageTagRange:
    """A canonical Boolean subset of structurally valid canonical BCP 47 tags."""

    _clauses: _DNF

    def __post_init__(self) -> None:
        clauses = _normalize_dnf(tuple(tuple(clause) for clause in self._clauses))
        _require_size(clauses)
        object.__setattr__(self, "_clauses", clauses)

    @classmethod
    def all(cls) -> LanguageTagRange:
        return cls(((),))

    @classmethod
    def empty(cls) -> LanguageTagRange:
        return cls(())

    @classmethod
    def basic(cls, language_range: str) -> LanguageTagRange:
        """Create one case-insensitive RFC 4647 basic-filtering range."""

        if not isinstance(language_range, str):
            raise TypeError("language_range must be str")
        if language_range == "*":
            return cls.all()
        parts = language_range.lower().split("-")
        if not (
            1 <= len(parts[0]) <= 8
            and parts[0].isascii()
            and parts[0].isalpha()
            and all(1 <= len(part) <= 8 and part.isascii() and part.isalnum() for part in parts[1:])
        ):
            raise ValueError("language_range must be an RFC 4647 basic language range")
        return cls(((_TagAtom(tuple(parts), True),),))

    def contains(self, language: str) -> bool:
        if not is_valid_language_tag(language) or language != language.lower():
            return False
        return _dnf_contains(self._clauses, tuple(language.split("-")))

    def intersection(self, other: LanguageTagRange) -> LanguageTagRange:
        if not isinstance(other, LanguageTagRange):
            raise TypeError("other must be LanguageTagRange")
        return LanguageTagRange(
            tuple(left + right for left in self._clauses for right in other._clauses)
        )

    def union(self, other: LanguageTagRange) -> LanguageTagRange:
        if not isinstance(other, LanguageTagRange):
            raise TypeError("other must be LanguageTagRange")
        return LanguageTagRange(self._clauses + other._clauses)

    def complement(self) -> LanguageTagRange:
        result: _DNF = ((),)
        for clause in self._clauses:
            if not clause:
                return LanguageTagRange.empty()
            inverted = tuple((_TagAtom(atom.prefix, not atom.positive),) for atom in clause)
            result = tuple(left + right for left in result for right in inverted)
            _require_size(result)
        return LanguageTagRange(result)

    def is_empty_exact(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> bool:
        selected = _controls(limits, cancellation)
        for index, clause in enumerate(self._clauses, 1):
            finite = _finite_clause_values(clause)
            if finite is None or finite:
                return False
            _poll(cancellation, index, selected.cancellation_poll_stride)
        return True

    def finite_cardinality(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> int | None:
        selected = _controls(limits, cancellation)
        values: set[str] = set()
        for index, clause in enumerate(self._clauses, 1):
            finite = _finite_clause_values(clause)
            if finite is None:
                return None
            values.update(finite)
            _poll(cancellation, index, selected.cancellation_poll_stride)
        return len(values)

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
        selected = _controls(limits, cancellation)
        values: set[str] = set()
        for index, clause in enumerate(self._clauses, 1):
            finite = _finite_clause_values(clause)
            if finite is None:
                return maximum
            values.update(finite)
            if len(values) >= maximum:
                return maximum
            _poll(cancellation, index, selected.cancellation_poll_stride)
        return len(values)

    def enumerate_tags(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> tuple[str, ...]:
        selected = _controls(limits, cancellation)
        cardinality = self.finite_cardinality(limits=selected, cancellation=cancellation)
        if cardinality is None:
            raise ValueError("cannot enumerate an infinite language-tag range")
        if cardinality > selected.max_enumeration_values:
            raise ResourceLimitError(
                "language-tag enumeration exceeds the configured value limit",
                limit="max_enumeration_values",
                observed=cardinality,
                allowed=selected.max_enumeration_values,
            )
        values = {
            tag
            for clause in self._clauses
            for tag in (_finite_clause_values(clause) or ())
            if self.contains(tag)
        }
        return tuple(sorted(values))

    def first_tag(
        self,
        *,
        excluding: Iterable[str] = (),
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> str:
        """Return the deterministic first valid member outside ``excluding``."""

        selected = _controls(limits, cancellation)
        forbidden = frozenset(excluding)
        if not all(isinstance(value, str) for value in forbidden):
            raise TypeError("excluding must contain strings")
        for index, clause in enumerate(self._clauses, 1):
            finite = _finite_clause_values(clause)
            if finite is not None:
                available = sorted(tag for tag in finite if tag not in forbidden)
                if available:
                    return available[0]
            else:
                value = _infinite_clause_witness(clause, forbidden)
                if value is not None:
                    return value
            _poll(cancellation, index, selected.cancellation_poll_stride)
        raise ValueError("language-tag range has no nonexcluded member")


def _normalize_dnf(clauses: _DNF) -> _DNF:
    output: list[_Clause] = []
    for clause in clauses:
        normalized = _normalize_clause(clause)
        if normalized is not None and normalized not in output:
            output.append(normalized)
    return tuple(sorted(output))


def _normalize_clause(clause: _Clause) -> _Clause | None:
    polarities: dict[tuple[str, ...], bool] = {}
    for atom in clause:
        if not isinstance(atom, _TagAtom):
            raise TypeError("language-tag clauses must contain internal tag atoms")
        prior = polarities.get(atom.prefix)
        if prior is not None and prior is not atom.positive:
            return None
        polarities[atom.prefix] = atom.positive
    positives = sorted((prefix for prefix, positive in polarities.items() if positive), key=len)
    required: tuple[str, ...] | None = None
    for prefix in positives:
        if required is not None and not _is_prefix(required, prefix):
            return None
        required = prefix
    negatives = sorted(
        (prefix for prefix, positive in polarities.items() if not positive),
        key=lambda value: (len(value), value),
    )
    retained_negatives: list[tuple[str, ...]] = []
    for prefix in negatives:
        if required is not None:
            if _is_prefix(prefix, required):
                return None
            if not _is_prefix(required, prefix):
                continue
        if any(_is_prefix(known, prefix) for known in retained_negatives):
            continue
        retained_negatives.append(prefix)
    result = [] if required is None else [_TagAtom(required, True)]
    result.extend(_TagAtom(prefix, False) for prefix in retained_negatives)
    return tuple(result)


def _finite_clause_values(clause: _Clause) -> frozenset[str] | None:
    required = next((atom.prefix for atom in clause if atom.positive), None)
    if required is None:
        return None
    if required[0] == "i":
        values = frozenset(
            tag for tag in _I_GRANDFATHERED if _matches_prefix(tuple(tag.split("-")), required)
        )
        return frozenset(tag for tag in values if _clause_contains(clause, tag))
    if len(required[0]) == 1 and required[0] != "x":
        return frozenset()
    joined = "-".join(required)
    if joined in _IRREGULAR_LEAVES:
        return frozenset({joined}) if _clause_contains(clause, joined) else frozenset()
    if _completion_for_clause(clause) is None:
        return frozenset()
    return None


def _infinite_clause_witness(clause: _Clause, forbidden: frozenset[str]) -> str | None:
    base = _completion_for_clause(clause)
    if base is None:
        return None
    if base not in forbidden and _clause_contains(clause, base):
        return base
    candidates = [base]
    blocked = _blocked_children(clause, tuple(base.split("-")))
    token_count = len(blocked) + len(forbidden) + 2
    for token in _token_candidates(token_count):
        candidates.extend(
            (
                f"{base}-{token}",
                f"{base}-x-{token}",
                f"{base}-a-{_two_character(token)}",
                f"{base}-{_variant(token)}",
            )
        )
        for candidate in candidates[-4:]:
            if (
                candidate not in forbidden
                and is_valid_language_tag(candidate)
                and _clause_contains(clause, candidate)
            ):
                return candidate
    return None


def _completion_for_clause(clause: _Clause) -> str | None:
    required = next((atom.prefix for atom in clause if atom.positive), None)
    if required is None:
        blocked = _blocked_children(clause, ())
        for token in _token_candidates(len(blocked) + 2):
            candidate = _two_character(token)
            if _clause_contains(clause, candidate) and is_valid_language_tag(candidate):
                return candidate
        return None
    joined = "-".join(required)
    if is_valid_language_tag(joined) and _clause_contains(clause, joined):
        return joined
    blocked = _blocked_children(clause, required)
    for token in _token_candidates(len(blocked) + 2):
        if token in blocked:
            continue
        candidate = f"{joined}-{token}"
        if is_valid_language_tag(candidate) and _clause_contains(clause, candidate):
            return candidate
    return None


def _blocked_children(clause: _Clause, prefix: tuple[str, ...]) -> frozenset[str]:
    return frozenset(
        atom.prefix[len(prefix)]
        for atom in clause
        if not atom.positive
        and len(atom.prefix) == len(prefix) + 1
        and _is_prefix(prefix, atom.prefix)
    )


def _token_candidates(count: int) -> Iterable[str]:
    for index in range(max(8, count)):
        encoded = _base36(index)
        yield encoded[-8:]
        yield _two_character(encoded)
        yield ("a" * max(0, 4 - len(encoded)) + encoded)[-4:]
        yield _variant(encoded)


def _base36(value: int) -> str:
    result = ""
    while True:
        value, remainder = divmod(value, len(_ALPHANUMERIC))
        result = _ALPHANUMERIC[remainder] + result
        if value == 0:
            return result


def _two_character(value: str) -> str:
    return ("a" + value)[-2:] if len(value) < 2 else value[-2:]


def _variant(value: str) -> str:
    return ("aaaa" + value)[-5:]


def _dnf_contains(clauses: _DNF, parts: tuple[str, ...]) -> bool:
    return any(
        all(_matches_prefix(parts, atom.prefix) is atom.positive for atom in clause)
        for clause in clauses
    )


def _clause_contains(clause: _Clause, language: str) -> bool:
    parts = tuple(language.split("-"))
    return all(_matches_prefix(parts, atom.prefix) is atom.positive for atom in clause)


def _matches_prefix(parts: tuple[str, ...], prefix: tuple[str, ...]) -> bool:
    return len(prefix) <= len(parts) and parts[: len(prefix)] == prefix


def _is_prefix(left: tuple[str, ...], right: tuple[str, ...]) -> bool:
    return len(left) <= len(right) and right[: len(left)] == left


def _require_size(clauses: _DNF) -> None:
    observed = len(clauses) + sum(len(clause) for clause in clauses)
    allowed = DatatypeLimits().max_pattern_states
    if observed > allowed:
        raise ResourceLimitError(
            "language-tag Boolean algebra exceeds the configured clause limit",
            limit="max_pattern_states",
            observed=observed,
            allowed=allowed,
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
    if cancellation is not None:
        cancellation.check()
    return selected


def _poll(cancellation: CancellationToken | None, work: int, stride: int) -> None:
    if cancellation is not None and work % stride == 0:
        cancellation.add_work(stride)
        cancellation.check()


__all__ = ["LanguageTagRange", "is_valid_language_tag"]
