# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Compact immutable dependency sets and bounded per-session interning.

SPDX-License-Identifier: LGPL-3.0-or-later

Source-guided behavior: pinned HermiT ``DependencySetFactory`` at commit
37ec30aced32ac81ebecc5e33fad255ddefcb4c3.  Representation and implementation are
original Python; the observable contract follows ``specs/tableau-state.md``.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator
from dataclasses import dataclass


@dataclass(frozen=True, slots=True, order=True)
class DependencySet:
    """An immutable set of nonnegative branching levels encoded as one Python int."""

    bits: int = 0

    def __post_init__(self) -> None:
        if isinstance(self.bits, bool) or not isinstance(self.bits, int):
            raise TypeError("dependency bits must be an integer")
        if self.bits < 0:
            raise ValueError("dependency bits must be nonnegative")

    @classmethod
    def of(cls, levels: Iterable[int] = ()) -> DependencySet:
        bits = 0
        for level in levels:
            if isinstance(level, bool) or not isinstance(level, int):
                raise TypeError("dependency levels must be integers")
            if level < 0:
                raise ValueError("dependency levels must be nonnegative")
            bits |= 1 << level
        return cls(bits)

    def __iter__(self) -> Iterator[int]:
        bits = self.bits
        while bits:
            low = bits & -bits
            yield low.bit_length() - 1
            bits ^= low

    def __len__(self) -> int:
        return self.bits.bit_count()

    def __bool__(self) -> bool:
        return self.bits != 0

    def __contains__(self, level: object) -> bool:
        return (
            isinstance(level, int)
            and not isinstance(level, bool)
            and level >= 0
            and bool(self.bits & (1 << level))
        )

    @property
    def maximum(self) -> int | None:
        return None if self.bits == 0 else self.bits.bit_length() - 1

    def add(self, level: int) -> DependencySet:
        if isinstance(level, bool) or not isinstance(level, int):
            raise TypeError("dependency level must be an integer")
        if level < 0:
            raise ValueError("dependency level must be nonnegative")
        return DependencySet(self.bits | (1 << level))

    def union(self, *others: DependencySet) -> DependencySet:
        bits = self.bits
        for other in others:
            if not isinstance(other, DependencySet):
                raise TypeError("dependency union requires DependencySet values")
            bits |= other.bits
        return DependencySet(bits)

    def is_subset_of(self, other: DependencySet) -> bool:
        if not isinstance(other, DependencySet):
            raise TypeError("dependency subset requires DependencySet")
        return self.bits & ~other.bits == 0

    def without_above(self, level: int) -> DependencySet:
        """Return levels no greater than ``level`` (useful in debug/reference checks)."""

        if isinstance(level, bool) or not isinstance(level, int):
            raise TypeError("dependency level must be an integer")
        if level < 0:
            return DependencySet()
        return DependencySet(self.bits & ((1 << (level + 1)) - 1))

    def as_tuple(self) -> tuple[int, ...]:
        return tuple(self)


class DependencyPool:
    """Per-session canonicalization pool; ``clear`` bounds cross-query retention."""

    __slots__ = ("_items",)

    def __init__(self) -> None:
        empty = DependencySet()
        self._items: dict[int, DependencySet] = {0: empty}

    @property
    def empty(self) -> DependencySet:
        return self._items[0]

    def intern(self, value: DependencySet | Iterable[int]) -> DependencySet:
        dependency = value if isinstance(value, DependencySet) else DependencySet.of(value)
        known = self._items.get(dependency.bits)
        if known is not None:
            return known
        self._items[dependency.bits] = dependency
        return dependency

    def union(self, *values: DependencySet) -> DependencySet:
        bits = 0
        for value in values:
            if not isinstance(value, DependencySet):
                raise TypeError("dependency union requires DependencySet values")
            bits |= value.bits
        return self.intern(DependencySet(bits))

    def clear(self) -> None:
        empty = self._items[0]
        self._items.clear()
        self._items[0] = empty

    def compact(self, live: Iterable[DependencySet] = ()) -> None:
        """Drop dead intern entries while retaining canonical live values."""

        retained: dict[int, DependencySet] = {0: self._items[0]}
        for dependency in live:
            if not isinstance(dependency, DependencySet):
                raise TypeError("live dependency values must be DependencySet instances")
            retained.setdefault(dependency.bits, dependency)
        self._items = retained

    def __len__(self) -> int:
        return len(self._items)


__all__ = ["DependencyPool", "DependencySet"]
