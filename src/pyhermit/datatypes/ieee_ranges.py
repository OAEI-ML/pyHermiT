# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# SPDX-License-Identifier: LGPL-3.0-or-later
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Exact discrete range algebra for XML Schema float and double."""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from typing import TypeAlias

from pyhermit.events import CancellationToken
from pyhermit.exceptions import ResourceLimitError

from .ieee754 import (
    comparison_from_identity,
    identity_from_comparison,
    identity_from_ordered_rank,
    ordered_rank,
    rank_bounds,
    zero_ranks,
)
from .model import (
    CompiledLiteral,
    DatatypeLimits,
    IEEECategory,
    IEEEComparison,
    IEEEFormat,
    IEEEIdentity,
)

IEEEValue: TypeAlias = IEEEIdentity | IEEEComparison | CompiledLiteral


@dataclass(frozen=True, slots=True)
class IEEEInterval:
    """Inclusive interval in the non-NaN discrete IEEE ordering."""

    lower_rank: int
    upper_rank: int

    def __post_init__(self) -> None:
        for name in ("lower_rank", "upper_rank"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int):
                raise TypeError(f"{name} must be int")

    def is_empty_exact(self) -> bool:
        return self.lower_rank > self.upper_rank

    def intersection(self, other: IEEEInterval) -> IEEEInterval:
        if not isinstance(other, IEEEInterval):
            raise TypeError("other must be IEEEInterval")
        return IEEEInterval(
            max(self.lower_rank, other.lower_rank),
            min(self.upper_rank, other.upper_rank),
        )


@dataclass(frozen=True, slots=True)
class IEEERange:
    """Canonical union of IEEE ranks plus the singleton NaN identity."""

    format: IEEEFormat
    intervals: tuple[IEEEInterval, ...]
    include_nan: bool = False

    def __post_init__(self) -> None:
        if not isinstance(self.format, IEEEFormat):
            raise TypeError("format must be IEEEFormat")
        if not isinstance(self.include_nan, bool):
            raise TypeError("include_nan must be bool")
        intervals = tuple(self.intervals)
        if not all(isinstance(interval, IEEEInterval) for interval in intervals):
            raise TypeError("intervals must contain IEEEInterval values")
        minimum, maximum = rank_bounds(self.format)
        for interval in intervals:
            if not interval.is_empty_exact() and (
                interval.lower_rank < minimum or interval.upper_rank > maximum
            ):
                raise ValueError("IEEE interval endpoint is outside the selected format")
        object.__setattr__(self, "intervals", _normalize(intervals))
        negative_zero, positive_zero = zero_ranks(self.format)
        has_negative = any(
            interval.lower_rank <= negative_zero <= interval.upper_rank
            for interval in self.intervals
        )
        has_positive = any(
            interval.lower_rank <= positive_zero <= interval.upper_rank
            for interval in self.intervals
        )
        if has_negative is not has_positive:
            raise ValueError("facet ranges must contain either both signed zeros or neither")

    @classmethod
    def all(cls, format_: IEEEFormat) -> IEEERange:
        minimum, maximum = rank_bounds(format_)
        return cls(format_, (IEEEInterval(minimum, maximum),), True)

    @classmethod
    def empty(cls, format_: IEEEFormat) -> IEEERange:
        return cls(format_, (), False)

    @classmethod
    def bounded(
        cls,
        format_: IEEEFormat,
        *,
        lower: IEEEValue | None = None,
        lower_inclusive: bool = False,
        upper: IEEEValue | None = None,
        upper_inclusive: bool = False,
    ) -> IEEERange:
        minimum, maximum = rank_bounds(format_)
        lower_rank = minimum
        upper_rank = maximum
        if lower is not None:
            selected = _identity(lower, format_)
            comparison = comparison_from_identity(selected)
            if comparison.category is IEEECategory.NAN:
                return cls.empty(format_)
            lower_rank = _lower_rank(selected, inclusive=lower_inclusive)
        if upper is not None:
            selected = _identity(upper, format_)
            comparison = comparison_from_identity(selected)
            if comparison.category is IEEECategory.NAN:
                return cls.empty(format_)
            upper_rank = _upper_rank(selected, inclusive=upper_inclusive)
        return cls(format_, (IEEEInterval(lower_rank, upper_rank),), False)

    def contains(self, value: IEEEValue) -> bool:
        identity = _identity(value, self.format)
        if comparison_from_identity(identity).category is IEEECategory.NAN:
            return self.include_nan
        rank = ordered_rank(identity)
        return any(
            interval.lower_rank <= rank <= interval.upper_rank for interval in self.intervals
        )

    def is_empty_exact(self) -> bool:
        return not self.include_nan and not self.intervals

    def intersection(self, other: IEEERange) -> IEEERange:
        self._require_same_format(other)
        return IEEERange(
            self.format,
            tuple(left.intersection(right) for left in self.intervals for right in other.intervals),
            self.include_nan and other.include_nan,
        )

    def union(self, other: IEEERange) -> IEEERange:
        self._require_same_format(other)
        return IEEERange(
            self.format,
            self.intervals + other.intervals,
            self.include_nan or other.include_nan,
        )

    def complement(self) -> IEEERange:
        minimum, maximum = rank_bounds(self.format)
        output: list[IEEEInterval] = []
        cursor = minimum
        for interval in self.intervals:
            if cursor < interval.lower_rank:
                output.append(IEEEInterval(cursor, interval.lower_rank - 1))
            cursor = interval.upper_rank + 1
        if cursor <= maximum:
            output.append(IEEEInterval(cursor, maximum))
        return IEEERange(self.format, tuple(output), not self.include_nan)

    def finite_cardinality(self) -> int:
        return int(self.include_nan) + sum(
            interval.upper_rank - interval.lower_rank + 1 for interval in self.intervals
        )

    def enumerate_values(
        self,
        *,
        limits: DatatypeLimits | None = None,
        cancellation: CancellationToken | None = None,
    ) -> tuple[IEEEIdentity, ...]:
        selected_limits = limits or DatatypeLimits()
        if not isinstance(selected_limits, DatatypeLimits):
            raise TypeError("limits must be DatatypeLimits or None")
        if cancellation is not None and not isinstance(cancellation, CancellationToken):
            raise TypeError("cancellation must be CancellationToken or None")
        cardinality = self.finite_cardinality()
        if cardinality > selected_limits.max_enumeration_values:
            raise ResourceLimitError(
                "IEEE range enumeration exceeds the configured value limit",
                limit="max_enumeration_values",
                observed=cardinality,
                allowed=selected_limits.max_enumeration_values,
            )
        output: list[IEEEIdentity] = []
        since_poll = 0
        for interval in self.intervals:
            for rank in range(interval.lower_rank, interval.upper_rank + 1):
                output.append(identity_from_ordered_rank(self.format, rank))
                since_poll += 1
                if since_poll == selected_limits.cancellation_poll_stride:
                    _poll(cancellation, since_poll)
                    since_poll = 0
        if self.include_nan:
            output.append(identity_from_comparison(IEEEComparison(self.format, IEEECategory.NAN)))
            since_poll += 1
        _poll(cancellation, since_poll)
        return tuple(output)

    def _require_same_format(self, other: IEEERange) -> None:
        if not isinstance(other, IEEERange):
            raise TypeError("other must be IEEERange")
        if self.format is not other.format:
            raise ValueError("float and double value spaces are disjoint")


def _identity(value: IEEEValue, format_: IEEEFormat) -> IEEEIdentity:
    if isinstance(value, CompiledLiteral):
        identity = value.data_identity
        if not isinstance(identity, IEEEIdentity):
            raise TypeError("compiled literal is not an IEEE value")
    elif isinstance(value, IEEEComparison):
        identity = identity_from_comparison(value)
    elif isinstance(value, IEEEIdentity):
        identity = value
    else:
        raise TypeError("value must be IEEEIdentity, IEEEComparison, or CompiledLiteral")
    if identity.format is not format_:
        raise TypeError("IEEE value uses a different XML Schema datatype")
    return identity


def _lower_rank(identity: IEEEIdentity, *, inclusive: bool) -> int:
    comparison = comparison_from_identity(identity)
    rank = ordered_rank(identity)
    if comparison.category is IEEECategory.FINITE and comparison.numerator == 0:
        negative_zero, positive_zero = zero_ranks(identity.format)
        return negative_zero if inclusive else positive_zero + 1
    return rank if inclusive else rank + 1


def _upper_rank(identity: IEEEIdentity, *, inclusive: bool) -> int:
    comparison = comparison_from_identity(identity)
    rank = ordered_rank(identity)
    if comparison.category is IEEECategory.FINITE and comparison.numerator == 0:
        negative_zero, positive_zero = zero_ranks(identity.format)
        return positive_zero if inclusive else negative_zero - 1
    return rank if inclusive else rank - 1


def _normalize(intervals: Iterable[IEEEInterval]) -> tuple[IEEEInterval, ...]:
    retained = sorted(
        (interval for interval in intervals if not interval.is_empty_exact()),
        key=lambda interval: interval.lower_rank,
    )
    output: list[IEEEInterval] = []
    for interval in retained:
        if output and interval.lower_rank <= output[-1].upper_rank + 1:
            output[-1] = IEEEInterval(
                output[-1].lower_rank,
                max(output[-1].upper_rank, interval.upper_rank),
            )
        else:
            output.append(interval)
    return tuple(output)


def _poll(cancellation: CancellationToken | None, work: int = 0) -> None:
    if cancellation is None:
        return
    if work:
        cancellation.add_work(work)
    cancellation.check()


__all__ = ["IEEEInterval", "IEEERange", "IEEEValue"]
