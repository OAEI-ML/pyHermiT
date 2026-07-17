# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# SPDX-License-Identifier: LGPL-3.0-or-later

"""Exact two-part range algebra for XML Schema dateTime partial order."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeAlias

from pyhermit.events import CancellationToken
from pyhermit.exceptions import ResourceLimitError

from .model import (
    CompiledLiteral,
    DatatypeLimits,
    DateTimeComparison,
    DateTimeIdentity,
    NumericComparison,
    NumericDomain,
)
from .ranges import NumericRange

DateTimeValue: TypeAlias = DateTimeIdentity | DateTimeComparison | CompiledLiteral

_MAX_TIMEZONE_SECONDS = 14 * 60 * 60


@dataclass(frozen=True, slots=True)
class DateTimeRange:
    """Date/time range partitioned into zoned UTC and unzoned local timelines."""

    zoned: NumericRange
    unzoned: NumericRange
    include_unzoned_domain: bool

    def __post_init__(self) -> None:
        if not isinstance(self.zoned, NumericRange) or not isinstance(self.unzoned, NumericRange):
            raise TypeError("zoned and unzoned must be NumericRange values")
        if (
            self.zoned.domain is not NumericDomain.REAL
            or self.unzoned.domain is not NumericDomain.REAL
        ):
            raise ValueError("date/time timeline ranges must use NumericDomain.REAL")
        if not isinstance(self.include_unzoned_domain, bool):
            raise TypeError("include_unzoned_domain must be bool")
        if not self.include_unzoned_domain and not self.unzoned.is_empty_exact():
            raise ValueError("dateTimeStamp ranges cannot contain unzoned values")

    @classmethod
    def all(cls, *, require_timezone: bool = False) -> DateTimeRange:
        return cls(
            NumericRange.all(NumericDomain.REAL),
            (
                NumericRange.empty(NumericDomain.REAL)
                if require_timezone
                else NumericRange.all(NumericDomain.REAL)
            ),
            not require_timezone,
        )

    @classmethod
    def empty(cls, *, require_timezone: bool = False) -> DateTimeRange:
        empty = NumericRange.empty(NumericDomain.REAL)
        return cls(empty, empty, not require_timezone)

    @classmethod
    def bounded(
        cls,
        *,
        require_timezone: bool = False,
        lower: DateTimeValue | None = None,
        lower_inclusive: bool = False,
        upper: DateTimeValue | None = None,
        upper_inclusive: bool = False,
    ) -> DateTimeRange:
        result = cls.all(require_timezone=require_timezone)
        if lower is not None:
            result = result.intersection(
                _one_bound(
                    require_timezone=require_timezone,
                    bound=_comparison(lower),
                    lower=True,
                    inclusive=lower_inclusive,
                )
            )
        if upper is not None:
            result = result.intersection(
                _one_bound(
                    require_timezone=require_timezone,
                    bound=_comparison(upper),
                    lower=False,
                    inclusive=upper_inclusive,
                )
            )
        return result

    def contains(self, value: DateTimeValue) -> bool:
        comparison = _comparison(value)
        if comparison.timezone_offset_minutes is None:
            if not self.include_unzoned_domain:
                return False
            point = NumericComparison(
                comparison.local_numerator,
                comparison.local_denominator,
            )
            return self.unzoned.contains(point)
        return self.zoned.contains(comparison.timeline)

    def is_empty_exact(self) -> bool:
        return self.zoned.is_empty_exact() and self.unzoned.is_empty_exact()

    def intersection(self, other: DateTimeRange) -> DateTimeRange:
        if not isinstance(other, DateTimeRange):
            raise TypeError("other must be DateTimeRange")
        include_unzoned = self.include_unzoned_domain and other.include_unzoned_domain
        unzoned = self.unzoned.intersection(other.unzoned)
        if not include_unzoned:
            unzoned = NumericRange.empty(NumericDomain.REAL)
        return DateTimeRange(
            self.zoned.intersection(other.zoned),
            unzoned,
            include_unzoned,
        )

    def union(self, other: DateTimeRange) -> DateTimeRange:
        if not isinstance(other, DateTimeRange):
            raise TypeError("other must be DateTimeRange")
        if self.include_unzoned_domain is not other.include_unzoned_domain:
            raise ValueError("union requires ranges relative to the same date/time datatype")
        return DateTimeRange(
            self.zoned.union(other.zoned),
            self.unzoned.union(other.unzoned),
            self.include_unzoned_domain,
        )

    def complement(self) -> DateTimeRange:
        return DateTimeRange(
            self.zoned.complement(),
            (
                self.unzoned.complement()
                if self.include_unzoned_domain
                else NumericRange.empty(NumericDomain.REAL)
            ),
            self.include_unzoned_domain,
        )

    def finite_cardinality(self) -> int | None:
        zoned_points = self.zoned.finite_cardinality()
        unzoned_points = self.unzoned.finite_cardinality()
        if zoned_points is None or unzoned_points is None:
            return None
        return zoned_points * 1_681 + unzoned_points

    def enumerate_values(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> tuple[DateTimeComparison, ...]:
        selected_limits = limits or DatatypeLimits()
        if not isinstance(selected_limits, DatatypeLimits):
            raise TypeError("limits must be DatatypeLimits or None")
        cardinality = self.finite_cardinality()
        if cardinality is None:
            raise ValueError("cannot enumerate an infinite date/time range")
        if cardinality > selected_limits.max_enumeration_values:
            raise ResourceLimitError(
                "date/time range enumeration exceeds the configured value limit",
                limit="max_enumeration_values",
                observed=cardinality,
                allowed=selected_limits.max_enumeration_values,
            )
        output: list[DateTimeComparison] = []
        work = 0
        for point in self.zoned.enumerate_values(limits=selected_limits, cancellation=cancellation):
            for offset in range(-840, 841):
                output.append(
                    DateTimeComparison(
                        point.numerator + offset * 60 * point.denominator,
                        point.denominator,
                        offset,
                    )
                )
                work += 1
                if work == selected_limits.cancellation_poll_stride:
                    _poll(cancellation, work)
                    work = 0
        for point in self.unzoned.enumerate_values(
            limits=selected_limits,
            cancellation=cancellation,
        ):
            output.append(DateTimeComparison(point.numerator, point.denominator, None))
            work += 1
        _poll(cancellation, work)
        return tuple(output)


def _one_bound(
    *,
    require_timezone: bool,
    bound: DateTimeComparison,
    lower: bool,
    inclusive: bool,
) -> DateTimeRange:
    bound_is_zoned = bound.timezone_offset_minutes is not None
    base = (
        bound.timeline
        if bound_is_zoned
        else NumericComparison(
            bound.local_numerator,
            bound.local_denominator,
        )
    )
    if lower:
        zoned_endpoint = (
            base
            if bound_is_zoned
            else NumericComparison(
                base.numerator + _MAX_TIMEZONE_SECONDS * base.denominator,
                base.denominator,
            )
        )
        unzoned_endpoint = (
            NumericComparison(
                base.numerator + _MAX_TIMEZONE_SECONDS * base.denominator,
                base.denominator,
            )
            if bound_is_zoned
            else base
        )
        zoned = NumericRange.between(
            NumericDomain.REAL,
            lower=zoned_endpoint,
            lower_inclusive=inclusive if bound_is_zoned else False,
        )
        unzoned = NumericRange.between(
            NumericDomain.REAL,
            lower=unzoned_endpoint,
            lower_inclusive=inclusive if not bound_is_zoned else False,
        )
    else:
        zoned_endpoint = (
            base
            if bound_is_zoned
            else NumericComparison(
                base.numerator - _MAX_TIMEZONE_SECONDS * base.denominator,
                base.denominator,
            )
        )
        unzoned_endpoint = (
            NumericComparison(
                base.numerator - _MAX_TIMEZONE_SECONDS * base.denominator,
                base.denominator,
            )
            if bound_is_zoned
            else base
        )
        zoned = NumericRange.between(
            NumericDomain.REAL,
            upper=zoned_endpoint,
            upper_inclusive=inclusive if bound_is_zoned else False,
        )
        unzoned = NumericRange.between(
            NumericDomain.REAL,
            upper=unzoned_endpoint,
            upper_inclusive=inclusive if not bound_is_zoned else False,
        )
    if require_timezone:
        unzoned = NumericRange.empty(NumericDomain.REAL)
    return DateTimeRange(zoned, unzoned, not require_timezone)


def _comparison(value: DateTimeValue) -> DateTimeComparison:
    if isinstance(value, CompiledLiteral):
        comparison = value.comparison
        if not isinstance(comparison, DateTimeComparison):
            raise TypeError("compiled literal is not a date/time value")
        return comparison
    if isinstance(value, DateTimeIdentity):
        return DateTimeComparison(
            value.local_numerator,
            value.local_denominator,
            value.timezone_offset_minutes,
        )
    if isinstance(value, DateTimeComparison):
        return value
    raise TypeError("value must be DateTimeIdentity, DateTimeComparison, or CompiledLiteral")


def _poll(cancellation: CancellationToken | None, work: int = 0) -> None:
    if cancellation is None:
        return
    if work:
        cancellation.add_work(work)
    cancellation.check()


__all__ = ["DateTimeRange", "DateTimeValue"]
