"""Deterministic rollback-safe work queues with duplicate membership guards.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import heapq
from collections.abc import Callable, Hashable
from dataclasses import dataclass, field
from typing import Generic, TypeVar

from pyhermit.exceptions import InternalInvariantError

from .trail import Trail

T = TypeVar("T", bound=Hashable)


@dataclass(frozen=True, slots=True, order=True)
class QueueEntry(Generic[T]):
    priority: tuple[int, ...]
    value: T = field(compare=False)

    def __post_init__(self) -> None:
        if not isinstance(self.priority, tuple) or not all(
            isinstance(item, int) and not isinstance(item, bool) for item in self.priority
        ):
            raise TypeError("queue priority must be a tuple of integers")


class StableQueue(Generic[T]):
    __slots__ = ("_heap", "_members", "_name", "_trail")

    def __init__(self, name: str, trail: Trail) -> None:
        if not isinstance(name, str) or not name:
            raise ValueError("queue name must be a nonempty string")
        self._name = name
        self._trail = trail
        self._heap: list[QueueEntry[T]] = []
        self._members: set[T] = set()

    def enqueue(self, value: T, priority: tuple[int, ...]) -> bool:
        if value in self._members:
            return False
        entry = QueueEntry(priority, value)
        if any(item.priority == priority for item in self._heap):
            raise ValueError(
                f"queue {self._name} priorities must uniquely include a stable identifier"
            )
        self._members.add(value)
        heapq.heappush(self._heap, entry)

        def undo() -> None:
            self._members.remove(value)
            self._heap.remove(entry)
            heapq.heapify(self._heap)

        self._trail.record(f"queue.{self._name}.enqueue", undo)
        return True

    def pop(self, valid: Callable[[T], bool] | None = None) -> T | None:
        while self._heap:
            entry = heapq.heappop(self._heap)
            if entry.value not in self._members:
                raise InternalInvariantError("queue heap/member set diverged")
            self._members.remove(entry.value)

            def undo(entry: QueueEntry[T] = entry) -> None:
                self._members.add(entry.value)
                heapq.heappush(self._heap, entry)

            self._trail.record(f"queue.{self._name}.pop", undo)
            if valid is None or valid(entry.value):
                return entry.value
        return None

    def discard(self, value: T) -> bool:
        if value not in self._members:
            return False
        entry = next(item for item in self._heap if item.value == value)
        self._members.remove(value)
        self._heap.remove(entry)
        heapq.heapify(self._heap)

        def undo() -> None:
            self._members.add(value)
            heapq.heappush(self._heap, entry)

        self._trail.record(f"queue.{self._name}.discard", undo)
        return True

    def __contains__(self, value: object) -> bool:
        return value in self._members

    def __len__(self) -> int:
        return len(self._members)

    def values(self) -> tuple[T, ...]:
        return tuple(entry.value for entry in sorted(self._heap))

    def check_invariants(self) -> None:
        values = [entry.value for entry in self._heap]
        if len(values) != len(set(values)):
            raise InternalInvariantError(f"queue {self._name} contains duplicate values")
        if set(values) != self._members:
            raise InternalInvariantError(f"queue {self._name} membership differs from heap")
        for index, entry in enumerate(self._heap):
            left = index * 2 + 1
            right = left + 1
            if left < len(self._heap) and self._heap[left] < entry:
                raise InternalInvariantError(f"queue {self._name} violates heap order")
            if right < len(self._heap) and self._heap[right] < entry:
                raise InternalInvariantError(f"queue {self._name} violates heap order")


__all__ = ["QueueEntry", "StableQueue"]
