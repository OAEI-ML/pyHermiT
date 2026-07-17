"""Thread-safe cooperative cancellation and immutable observability events.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import math
import threading
import time
from collections.abc import Callable, Mapping
from dataclasses import dataclass, field
from types import MappingProxyType
from typing import TypeAlias

from .exceptions import (
    ReasonerInterruptedError,
    ReasonerTimeoutError,
    ResourceLimitError,
)

EventScalar: TypeAlias = str | int | float | bool | None


def _freeze_details(details: Mapping[str, EventScalar]) -> Mapping[str, EventScalar]:
    clean: dict[str, EventScalar] = {}
    for key, value in details.items():
        if not isinstance(key, str) or not key:
            raise TypeError("event detail keys must be nonempty strings")
        if value is not None and not isinstance(value, (str, int, float, bool)):
            raise TypeError("event detail values must be scalar")
        if isinstance(value, float) and not math.isfinite(value):
            raise ValueError("event detail floats must be finite")
        clean[key] = value
    return MappingProxyType(dict(sorted(clean.items())))


@dataclass(frozen=True, slots=True)
class ProgressEvent:
    version: int
    operation_id: str
    kind: str
    completed: int
    total: int | None
    elapsed_seconds: float
    details: Mapping[str, EventScalar] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if self.version != 1:
            raise ValueError("unsupported progress event version")
        for name in ("operation_id", "kind"):
            value = getattr(self, name)
            if not isinstance(value, str) or not value:
                raise ValueError(f"{name} must be a nonempty string")
        if isinstance(self.completed, bool) or not isinstance(self.completed, int):
            raise TypeError("completed must be a nonnegative integer")
        if self.completed < 0:
            raise ValueError("completed must be a nonnegative integer")
        if self.total is not None:
            if isinstance(self.total, bool) or not isinstance(self.total, int):
                raise TypeError("total must be a nonnegative integer or None")
            if self.total < 0 or self.completed > self.total:
                raise ValueError("total must be nonnegative and at least completed")
        if isinstance(self.elapsed_seconds, bool) or not isinstance(
            self.elapsed_seconds, (int, float)
        ):
            raise TypeError("elapsed_seconds must be a finite nonnegative number")
        elapsed = float(self.elapsed_seconds)
        if not math.isfinite(elapsed) or elapsed < 0:
            raise ValueError("elapsed_seconds must be a finite nonnegative number")
        object.__setattr__(self, "elapsed_seconds", elapsed)
        object.__setattr__(self, "details", _freeze_details(self.details))

    def as_dict(self) -> dict[str, object]:
        return {
            "completed": self.completed,
            "details": dict(self.details),
            "elapsed_seconds": self.elapsed_seconds,
            "kind": self.kind,
            "operation_id": self.operation_id,
            "total": self.total,
            "version": self.version,
        }


@dataclass(frozen=True, slots=True)
class WarningEvent:
    version: int
    operation_id: str
    code: str
    message: str
    details: Mapping[str, EventScalar] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if self.version != 1:
            raise ValueError("unsupported warning event version")
        for name in ("operation_id", "code", "message"):
            value = getattr(self, name)
            if not isinstance(value, str) or not value:
                raise ValueError(f"{name} must be a nonempty string")
        object.__setattr__(self, "details", _freeze_details(self.details))

    def as_dict(self) -> dict[str, object]:
        return {
            "code": self.code,
            "details": dict(self.details),
            "message": self.message,
            "operation_id": self.operation_id,
            "version": self.version,
        }


ProgressCallback: TypeAlias = Callable[[ProgressEvent], None]
WarningCallback: TypeAlias = Callable[[WarningEvent], None]


class CancellationToken:
    """Read-only cancellation state polled by either complete backend.

    Work and memory counters are monotonic. They are intentionally small control-plane
    values; backends keep their hot counters internally and publish at polling boundaries.
    """

    __slots__ = (
        "_cancelled",
        "_deadline",
        "_lock",
        "_max_memory_bytes",
        "_memory_bytes",
        "_reason",
        "_work",
    )

    def __init__(
        self,
        *,
        timeout: float | None = None,
        max_memory_bytes: int | None = None,
    ) -> None:
        if timeout is not None:
            if isinstance(timeout, bool) or not isinstance(timeout, (int, float)):
                raise TypeError("timeout must be a finite positive number or None")
            timeout = float(timeout)
            if not math.isfinite(timeout) or timeout <= 0:
                raise ValueError("timeout must be a finite positive number or None")
        if max_memory_bytes is not None:
            if isinstance(max_memory_bytes, bool) or not isinstance(max_memory_bytes, int):
                raise TypeError("max_memory_bytes must be a positive integer or None")
            if max_memory_bytes <= 0:
                raise ValueError("max_memory_bytes must be a positive integer or None")
        self._cancelled = threading.Event()
        self._deadline = None if timeout is None else time.monotonic() + timeout
        self._lock = threading.Lock()
        self._max_memory_bytes = max_memory_bytes
        self._memory_bytes = 0
        self._reason: str | None = None
        self._work = 0

    @property
    def interrupted(self) -> bool:
        return self._cancelled.is_set()

    @property
    def deadline_exceeded(self) -> bool:
        deadline = self._deadline
        return deadline is not None and time.monotonic() >= deadline

    @property
    def reason(self) -> str | None:
        with self._lock:
            return self._reason

    @property
    def remaining_seconds(self) -> float | None:
        deadline = self._deadline
        if deadline is None:
            return None
        return max(0.0, deadline - time.monotonic())

    @property
    def work(self) -> int:
        with self._lock:
            return self._work

    @property
    def memory_bytes(self) -> int:
        with self._lock:
            return self._memory_bytes

    def add_work(self, amount: int = 1) -> int:
        if isinstance(amount, bool) or not isinstance(amount, int) or amount < 0:
            raise ValueError("work amount must be a nonnegative integer")
        with self._lock:
            self._work += amount
            return self._work

    def observe_memory(self, memory_bytes: int) -> None:
        if isinstance(memory_bytes, bool) or not isinstance(memory_bytes, int) or memory_bytes < 0:
            raise ValueError("memory_bytes must be a nonnegative integer")
        with self._lock:
            if memory_bytes > self._memory_bytes:
                self._memory_bytes = memory_bytes

    def check(self) -> None:
        if self.deadline_exceeded:
            raise ReasonerTimeoutError("reasoning operation exceeded its timeout")
        if self.interrupted:
            reason = self.reason
            raise ReasonerInterruptedError(reason or "reasoning operation was interrupted")
        with self._lock:
            memory = self._memory_bytes
            maximum = self._max_memory_bytes
        if maximum is not None and memory > maximum:
            raise ResourceLimitError(
                "reasoning memory limit exceeded",
                limit="max_memory_bytes",
                observed=memory,
                allowed=maximum,
            )

    def _interrupt(self, reason: str | None) -> bool:
        if reason is not None and (not isinstance(reason, str) or not reason):
            raise ValueError("reason must be a nonempty string or None")
        with self._lock:
            if self._cancelled.is_set():
                return False
            self._reason = reason
            self._cancelled.set()
            return True


class CancellationSource:
    __slots__ = ("_token",)

    def __init__(
        self,
        *,
        timeout: float | None = None,
        max_memory_bytes: int | None = None,
    ) -> None:
        self._token = CancellationToken(timeout=timeout, max_memory_bytes=max_memory_bytes)

    @property
    def token(self) -> CancellationToken:
        return self._token

    def interrupt(self, reason: str | None = None) -> bool:
        return self._token._interrupt(reason)


__all__ = [
    "CancellationSource",
    "CancellationToken",
    "EventScalar",
    "ProgressCallback",
    "ProgressEvent",
    "WarningCallback",
    "WarningEvent",
]
