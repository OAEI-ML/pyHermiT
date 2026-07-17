# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# SPDX-License-Identifier: LGPL-3.0-or-later

"""Exact immutable range primitives for numeric and Boolean value spaces.

The interval shape is source-guided by HermiT ``NumberInterval`` and
``OWLRealValueSpaceSubset`` at commit
``37ec30aced32ac81ebecc5e33fad255ddefcb4c3``.  This implementation uses one
arbitrary-precision rational endpoint representation and explicit family-relative
complement semantics; it does not import tableau state.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from functools import cmp_to_key
from typing import TypeAlias

from pyhermit.events import CancellationToken
from pyhermit.exceptions import ResourceLimitError, UnsupportedDatatypeError

from .literals import XSD_BOOLEAN, numeric_datatype_spec
from .model import (
    BooleanComparison,
    CompiledLiteral,
    DatatypeLimits,
    NumericComparison,
    NumericDomain,
)

RangeValue: TypeAlias = NumericComparison | BooleanComparison | CompiledLiteral


def _numeric_value(value: RangeValue) -> NumericComparison | None:
    selected = value.comparison if isinstance(value, CompiledLiteral) else value
    return selected if isinstance(selected, NumericComparison) else None


def _boolean_value(value: RangeValue) -> BooleanComparison | None:
    selected = value.comparison if isinstance(value, CompiledLiteral) else value
    return selected if isinstance(selected, BooleanComparison) else None


def numeric_domain_contains(domain: NumericDomain, value: NumericComparison) -> bool:
    """Return exact membership in the four nested OWL numeric domains."""

    if not isinstance(domain, NumericDomain):
        raise TypeError("domain must be NumericDomain")
    if not isinstance(value, NumericComparison):
        raise TypeError("value must be NumericComparison")
    if domain is NumericDomain.INTEGER:
        return value.denominator == 1
    if domain is NumericDomain.DECIMAL:
        denominator = value.denominator
        while denominator % 2 == 0:
            denominator //= 2
        while denominator % 5 == 0:
            denominator //= 5
        return denominator == 1
    return True


@dataclass(frozen=True, slots=True)
class NumericInterval:
    """One open/closed interval; ``None`` denotes the corresponding infinity."""

    lower: NumericComparison | None = None
    lower_inclusive: bool = False
    upper: NumericComparison | None = None
    upper_inclusive: bool = False

    def __post_init__(self) -> None:
        for name in ("lower", "upper"):
            value = getattr(self, name)
            if value is not None and not isinstance(value, NumericComparison):
                raise TypeError(f"{name} must be NumericComparison or None")
        for name in ("lower_inclusive", "upper_inclusive"):
            if not isinstance(getattr(self, name), bool):
                raise TypeError(f"{name} must be bool")
        if self.lower is None and self.lower_inclusive:
            raise ValueError("negative infinity cannot be inclusive")
        if self.upper is None and self.upper_inclusive:
            raise ValueError("positive infinity cannot be inclusive")

    def contains(self, value: RangeValue, *, domain: NumericDomain) -> bool:
        selected = _numeric_value(value)
        if selected is None or not numeric_domain_contains(domain, selected):
            return False
        if self.lower is not None:
            comparison = selected.compare(self.lower)
            if comparison < 0 or (comparison == 0 and not self.lower_inclusive):
                return False
        if self.upper is not None:
            comparison = selected.compare(self.upper)
            if comparison > 0 or (comparison == 0 and not self.upper_inclusive):
                return False
        return True

    def intersection(self, other: NumericInterval) -> NumericInterval:
        if not isinstance(other, NumericInterval):
            raise TypeError("other must be NumericInterval")
        lower, lower_inclusive = _stronger_lower(self, other)
        upper, upper_inclusive = _stronger_upper(self, other)
        return NumericInterval(lower, lower_inclusive, upper, upper_inclusive)

    def is_empty_exact(self, domain: NumericDomain) -> bool:
        if not isinstance(domain, NumericDomain):
            raise TypeError("domain must be NumericDomain")
        if domain is NumericDomain.INTEGER:
            bounds = self.integer_bounds()
            return bounds is not None and bounds[0] > bounds[1]
        if self.lower is None or self.upper is None:
            return False
        comparison = self.lower.compare(self.upper)
        if comparison > 0:
            return True
        if comparison < 0:
            return False
        return not (
            self.lower_inclusive
            and self.upper_inclusive
            and numeric_domain_contains(domain, self.lower)
        )

    def integer_bounds(self) -> tuple[int, int] | None:
        """Return inclusive integer endpoints, or ``None`` when either is infinite."""

        if self.lower is None or self.upper is None:
            return None
        lower = _ceil(self.lower) if self.lower_inclusive else _floor(self.lower) + 1
        upper = _floor(self.upper) if self.upper_inclusive else _ceil(self.upper) - 1
        return lower, upper

    def finite_cardinality(self, domain: NumericDomain) -> int | None:
        if self.is_empty_exact(domain):
            return 0
        if domain is NumericDomain.INTEGER:
            bounds = self.integer_bounds()
            if bounds is None:
                return None
            return bounds[1] - bounds[0] + 1
        if (
            self.lower is not None
            and self.upper is not None
            and self.lower.compare(self.upper) == 0
            and self.lower_inclusive
            and self.upper_inclusive
            and numeric_domain_contains(domain, self.lower)
        ):
            return 1
        return None


@dataclass(frozen=True, slots=True)
class NumericRange:
    """Canonical union of intervals over one exact numeric domain."""

    domain: NumericDomain
    intervals: tuple[NumericInterval, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.domain, NumericDomain):
            raise TypeError("domain must be NumericDomain")
        intervals = tuple(self.intervals)
        if not all(isinstance(interval, NumericInterval) for interval in intervals):
            raise TypeError("intervals must contain NumericInterval values")
        object.__setattr__(self, "intervals", _normalize_intervals(self.domain, intervals))

    @classmethod
    def empty(cls, domain: NumericDomain) -> NumericRange:
        return cls(domain, ())

    @classmethod
    def all(cls, domain: NumericDomain) -> NumericRange:
        return cls(domain, (NumericInterval(),))

    @classmethod
    def between(
        cls,
        domain: NumericDomain,
        *,
        lower: NumericComparison | None = None,
        lower_inclusive: bool = False,
        upper: NumericComparison | None = None,
        upper_inclusive: bool = False,
    ) -> NumericRange:
        return cls(
            domain,
            (NumericInterval(lower, lower_inclusive, upper, upper_inclusive),),
        )

    def contains(self, value: RangeValue) -> bool:
        return any(interval.contains(value, domain=self.domain) for interval in self.intervals)

    def is_empty_exact(self) -> bool:
        return not self.intervals

    def intersection(self, other: NumericRange) -> NumericRange:
        if not isinstance(other, NumericRange):
            raise TypeError("other must be NumericRange")
        domain = min(self.domain, other.domain)
        return NumericRange(
            domain,
            tuple(left.intersection(right) for left in self.intervals for right in other.intervals),
        )

    def union(self, other: NumericRange) -> NumericRange:
        """Return an exact union when both operands use the same family partition."""

        if not isinstance(other, NumericRange):
            raise TypeError("other must be NumericRange")
        if self.domain is not other.domain:
            raise ValueError("mixed-domain union requires the later full data-domain algebra")
        return NumericRange(self.domain, self.intervals + other.intervals)

    def complement(self) -> NumericRange:
        """Complement relative to this range's declared numeric domain."""

        if not self.intervals:
            return NumericRange.all(self.domain)
        output: list[NumericInterval] = []
        lower: NumericComparison | None = None
        lower_inclusive = False
        for interval in self.intervals:
            if interval.lower is not None:
                output.append(
                    NumericInterval(
                        lower,
                        lower_inclusive,
                        interval.lower,
                        not interval.lower_inclusive,
                    )
                )
            if interval.upper is None:
                return NumericRange(self.domain, tuple(output))
            lower = interval.upper
            lower_inclusive = not interval.upper_inclusive
        output.append(NumericInterval(lower, lower_inclusive, None, False))
        return NumericRange(self.domain, tuple(output))

    def finite_cardinality(self) -> int | None:
        total = 0
        for interval in self.intervals:
            cardinality = interval.finite_cardinality(self.domain)
            if cardinality is None:
                return None
            total += cardinality
        return total

    def enumerate_values(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> tuple[NumericComparison, ...]:
        selected_limits = _validate_controls(limits, cancellation)
        cardinality = self.finite_cardinality()
        if cardinality is None:
            raise ValueError("cannot enumerate an infinite numeric range")
        if cardinality > selected_limits.max_enumeration_values:
            raise ResourceLimitError(
                "numeric range enumeration exceeds the configured value limit",
                limit="max_enumeration_values",
                observed=cardinality,
                allowed=selected_limits.max_enumeration_values,
            )
        output: list[NumericComparison] = []
        stride = selected_limits.cancellation_poll_stride
        since_poll = 0
        for interval in self.intervals:
            if self.domain is NumericDomain.INTEGER:
                bounds = interval.integer_bounds()
                if bounds is None:
                    raise AssertionError("finite integer interval has infinite endpoint")
                for value in range(bounds[0], bounds[1] + 1):
                    output.append(NumericComparison(value))
                    since_poll += 1
                    if since_poll == stride:
                        _poll(cancellation, since_poll)
                        since_poll = 0
            else:
                if interval.lower is None:
                    raise AssertionError("finite dense interval has no singleton endpoint")
                output.append(interval.lower)
                since_poll += 1
        _poll(cancellation, since_poll)
        return tuple(output)


@dataclass(frozen=True, slots=True)
class BooleanRange:
    """Exact two-element Boolean value-space subset."""

    values: frozenset[bool]

    def __post_init__(self) -> None:
        values = frozenset(self.values)
        if any(not isinstance(value, bool) for value in values):
            raise TypeError("BooleanRange values must be bool")
        object.__setattr__(self, "values", values)

    @classmethod
    def all(cls) -> BooleanRange:
        return cls(frozenset((False, True)))

    @classmethod
    def empty(cls) -> BooleanRange:
        return cls(frozenset())

    def contains(self, value: RangeValue) -> bool:
        selected = _boolean_value(value)
        return selected is not None and selected.value in self.values

    def is_empty_exact(self) -> bool:
        return not self.values

    def intersection(self, other: BooleanRange) -> BooleanRange:
        if not isinstance(other, BooleanRange):
            raise TypeError("other must be BooleanRange")
        return BooleanRange(self.values & other.values)

    def union(self, other: BooleanRange) -> BooleanRange:
        if not isinstance(other, BooleanRange):
            raise TypeError("other must be BooleanRange")
        return BooleanRange(self.values | other.values)

    def complement(self) -> BooleanRange:
        return BooleanRange(frozenset((False, True)) - self.values)

    def finite_cardinality(self) -> int:
        return len(self.values)

    def enumerate_values(
        self,
        *,
        cancellation: CancellationToken | None = None,
    ) -> tuple[BooleanComparison, ...]:
        if cancellation is not None and not isinstance(cancellation, CancellationToken):
            raise TypeError("cancellation must be CancellationToken or None")
        _poll(cancellation, len(self.values))
        return tuple(BooleanComparison(value) for value in (False, True) if value in self.values)


DatatypeRange: TypeAlias = NumericRange | BooleanRange


def range_for_datatype(datatype_iri: str) -> DatatypeRange:
    """Return the exact unfaceted range for one implemented datatype."""

    if not isinstance(datatype_iri, str):
        raise TypeError("datatype_iri must be str")
    if datatype_iri == XSD_BOOLEAN:
        return BooleanRange.all()
    spec = numeric_datatype_spec(datatype_iri)
    if spec is None:
        raise UnsupportedDatatypeError(
            "datatype is outside the implemented WP07 numeric/Boolean tranche",
            context={"datatype_iri": datatype_iri},
        )
    lower = None if spec.lower_inclusive is None else NumericComparison(spec.lower_inclusive)
    upper = None if spec.upper_inclusive is None else NumericComparison(spec.upper_inclusive)
    return NumericRange.between(
        spec.domain,
        lower=lower,
        lower_inclusive=lower is not None,
        upper=upper,
        upper_inclusive=upper is not None,
    )


def _normalize_intervals(
    domain: NumericDomain,
    intervals: Iterable[NumericInterval],
) -> tuple[NumericInterval, ...]:
    retained = [interval for interval in intervals if not interval.is_empty_exact(domain)]
    retained.sort(key=cmp_to_key(_compare_interval_lower))
    output: list[NumericInterval] = []
    for interval in retained:
        if output and _can_merge(output[-1], interval):
            output[-1] = _merge(output[-1], interval)
        else:
            output.append(interval)
    return tuple(output)


def _compare_interval_lower(left: NumericInterval, right: NumericInterval) -> int:
    if left.lower is None:
        return 0 if right.lower is None else -1
    if right.lower is None:
        return 1
    comparison = left.lower.compare(right.lower)
    if comparison:
        return comparison
    if left.lower_inclusive is right.lower_inclusive:
        return 0
    return -1 if left.lower_inclusive else 1


def _can_merge(left: NumericInterval, right: NumericInterval) -> bool:
    if left.upper is None or right.lower is None:
        return True
    comparison = left.upper.compare(right.lower)
    return comparison > 0 or (comparison == 0 and (left.upper_inclusive or right.lower_inclusive))


def _merge(left: NumericInterval, right: NumericInterval) -> NumericInterval:
    if left.upper is None or right.upper is None:
        upper = None
        upper_inclusive = False
    else:
        comparison = left.upper.compare(right.upper)
        if comparison > 0:
            upper, upper_inclusive = left.upper, left.upper_inclusive
        elif comparison < 0:
            upper, upper_inclusive = right.upper, right.upper_inclusive
        else:
            upper = left.upper
            upper_inclusive = left.upper_inclusive or right.upper_inclusive
    return NumericInterval(left.lower, left.lower_inclusive, upper, upper_inclusive)


def _stronger_lower(
    left: NumericInterval,
    right: NumericInterval,
) -> tuple[NumericComparison | None, bool]:
    if left.lower is None:
        return right.lower, right.lower_inclusive
    if right.lower is None:
        return left.lower, left.lower_inclusive
    comparison = left.lower.compare(right.lower)
    if comparison > 0:
        return left.lower, left.lower_inclusive
    if comparison < 0:
        return right.lower, right.lower_inclusive
    return left.lower, left.lower_inclusive and right.lower_inclusive


def _stronger_upper(
    left: NumericInterval,
    right: NumericInterval,
) -> tuple[NumericComparison | None, bool]:
    if left.upper is None:
        return right.upper, right.upper_inclusive
    if right.upper is None:
        return left.upper, left.upper_inclusive
    comparison = left.upper.compare(right.upper)
    if comparison < 0:
        return left.upper, left.upper_inclusive
    if comparison > 0:
        return right.upper, right.upper_inclusive
    return left.upper, left.upper_inclusive and right.upper_inclusive


def _floor(value: NumericComparison) -> int:
    return value.numerator // value.denominator


def _ceil(value: NumericComparison) -> int:
    return -((-value.numerator) // value.denominator)


def _validate_controls(
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
    "BooleanRange",
    "DatatypeRange",
    "NumericInterval",
    "NumericRange",
    "RangeValue",
    "numeric_domain_contains",
    "range_for_datatype",
]
