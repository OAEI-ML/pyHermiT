"""One reverse-order mutation trail shared by every tableau component.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field

from pyhermit.exceptions import InternalInvariantError


@dataclass(frozen=True, slots=True, order=True)
class Checkpoint:
    sequence: int
    trail_length: int
    label: str = field(compare=False)

    def __post_init__(self) -> None:
        for name in ("sequence", "trail_length"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")
        if not isinstance(self.label, str) or not self.label:
            raise ValueError("checkpoint label must be a nonempty string")


@dataclass(slots=True)
class _TrailEntry:
    kind: str
    undo: Callable[[], None] = field(repr=False)


class Trail:
    """Append-only undo log with strict LIFO rollback."""

    __slots__ = ("_entries", "_rolling_back", "_sequence")

    def __init__(self) -> None:
        self._entries: list[_TrailEntry] = []
        self._rolling_back = False
        self._sequence = 0

    @property
    def length(self) -> int:
        return len(self._entries)

    @property
    def rolling_back(self) -> bool:
        return self._rolling_back

    def checkpoint(self, label: str) -> Checkpoint:
        self._sequence += 1
        return Checkpoint(self._sequence, len(self._entries), label)

    def record(self, kind: str, undo: Callable[[], None]) -> None:
        if self._rolling_back:
            raise InternalInvariantError("cannot append trail entries while rolling back")
        if not isinstance(kind, str) or not kind:
            raise ValueError("trail kind must be a nonempty string")
        if not callable(undo):
            raise TypeError("trail undo must be callable")
        self._entries.append(_TrailEntry(kind, undo))

    def rollback(self, checkpoint: Checkpoint) -> tuple[str, ...]:
        if not isinstance(checkpoint, Checkpoint):
            raise TypeError("checkpoint must be Checkpoint")
        if checkpoint.trail_length > len(self._entries):
            raise ValueError("checkpoint belongs to an unavailable future trail state")
        undone: list[str] = []
        self._rolling_back = True
        try:
            while len(self._entries) > checkpoint.trail_length:
                entry = self._entries.pop()
                entry.undo()
                undone.append(entry.kind)
        finally:
            self._rolling_back = False
        return tuple(undone)

    def discard_before(self, checkpoint: Checkpoint) -> None:
        """Forget committed history before a root checkpoint.

        Existing checkpoints become invalid by design; callers use this only between
        independent operations when no branching point survives.
        """

        if checkpoint.trail_length > len(self._entries):
            raise ValueError("checkpoint is outside the trail")
        del self._entries[: checkpoint.trail_length]

    def kinds(self) -> tuple[str, ...]:
        """Stable diagnostics containing no callback/object identity."""

        return tuple(entry.kind for entry in self._entries)


__all__ = ["Checkpoint", "Trail"]
