"""Immutable, backend-neutral pyHermiT configuration contracts.

SPDX-License-Identifier: LGPL-3.0-or-later

The defaults follow the public behavior of the pinned HermiT configuration while
keeping strategy choices explicit and serializable.  This module is deliberately a
leaf: importing it performs no core loading or backend discovery.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from enum import Enum
from typing import TypeAlias, cast

from .events import ProgressCallback, WarningCallback


class _StringEnum(str, Enum):
    """Python-3.10-compatible equivalent of :class:`enum.StrEnum`."""

    def __str__(self) -> str:
        return cast(str, self.value)


class BackendName(_StringEnum):
    AUTO = "auto"
    PYTHON = "python"
    NATIVE = "native"
    VERIFY = "verify"


class FreshEntityPolicy(_StringEnum):
    DISALLOW = "disallow"
    ALLOW = "allow"


class IndividualGrouping(_StringEnum):
    BY_SAME_AS = "by_same_as"
    BY_NAME = "by_name"


class UnsupportedDatatypePolicy(_StringEnum):
    ERROR = "error"
    IGNORE_WITH_WARNING = "ignore_with_warning"


class BlockingMode(_StringEnum):
    AUTO = "auto"
    ANYWHERE = "anywhere"
    VALIDATED_ANYWHERE = "validated_anywhere"
    ANCESTOR = "ancestor"


class ExistentialMode(_StringEnum):
    AUTO = "auto"
    CREATION_ORDER = "creation_order"
    INDIVIDUAL_REUSE = "individual_reuse"


ConfigScalar: TypeAlias = str | int | float | bool | None


def _coerce_enum(value: object, enum_type: type[_StringEnum], field_name: str) -> _StringEnum:
    if isinstance(value, enum_type):
        return value
    if isinstance(value, str):
        try:
            return enum_type(value)
        except ValueError as exc:
            choices = ", ".join(member.value for member in enum_type)
            raise ValueError(f"{field_name} must be one of: {choices}") from exc
    raise TypeError(f"{field_name} must be {enum_type.__name__} or str")


@dataclass(frozen=True, slots=True)
class ReasonerConfig:
    """Complete immutable configuration captured when a reasoner is constructed."""

    backend: BackendName = BackendName.AUTO
    timeout: float | None = None
    buffer_changes: bool = True
    fresh_entities: FreshEntityPolicy = FreshEntityPolicy.ALLOW
    individual_grouping: IndividualGrouping = IndividualGrouping.BY_NAME
    unsupported_datatypes: UnsupportedDatatypePolicy = UnsupportedDatatypePolicy.ERROR
    blocking: BlockingMode = BlockingMode.AUTO
    existentials: ExistentialMode = ExistentialMode.AUTO
    disjunction_learning: bool = True
    force_quasi_order_classification: bool = False
    workers: int = 0
    max_memory_bytes: int | None = None
    deterministic: bool = True
    progress: ProgressCallback | None = field(default=None, compare=False, repr=False)
    warnings: WarningCallback | None = field(default=None, compare=False, repr=False)

    def __post_init__(self) -> None:
        enum_fields: tuple[tuple[str, type[_StringEnum]], ...] = (
            ("backend", BackendName),
            ("fresh_entities", FreshEntityPolicy),
            ("individual_grouping", IndividualGrouping),
            ("unsupported_datatypes", UnsupportedDatatypePolicy),
            ("blocking", BlockingMode),
            ("existentials", ExistentialMode),
        )
        for name, enum_type in enum_fields:
            object.__setattr__(self, name, _coerce_enum(getattr(self, name), enum_type, name))

        if self.timeout is not None:
            if isinstance(self.timeout, bool) or not isinstance(self.timeout, (int, float)):
                raise TypeError("timeout must be a finite positive number or None")
            timeout = float(self.timeout)
            if not math.isfinite(timeout) or timeout <= 0:
                raise ValueError("timeout must be a finite positive number or None")
            object.__setattr__(self, "timeout", timeout)

        if isinstance(self.workers, bool) or not isinstance(self.workers, int):
            raise TypeError("workers must be a nonnegative integer")
        if self.workers < 0:
            raise ValueError("workers must be a nonnegative integer")
        if self.max_memory_bytes is not None:
            if isinstance(self.max_memory_bytes, bool) or not isinstance(
                self.max_memory_bytes, int
            ):
                raise TypeError("max_memory_bytes must be a positive integer or None")
            if self.max_memory_bytes <= 0:
                raise ValueError("max_memory_bytes must be a positive integer or None")

        for name in (
            "buffer_changes",
            "disjunction_learning",
            "force_quasi_order_classification",
            "deterministic",
        ):
            if not isinstance(getattr(self, name), bool):
                raise TypeError(f"{name} must be bool")
        for name in ("progress", "warnings"):
            callback = getattr(self, name)
            if callback is not None and not callable(callback):
                raise TypeError(f"{name} must be callable or None")

    def semantic_items(self) -> tuple[tuple[str, ConfigScalar], ...]:
        """Canonical options that affect compilation or reasoning semantics.

        Callbacks are observability hooks and intentionally do not partition caches.
        """

        return (
            ("backend", self.backend.value),
            ("blocking", self.blocking.value),
            ("buffer_changes", self.buffer_changes),
            ("deterministic", self.deterministic),
            ("disjunction_learning", self.disjunction_learning),
            ("existentials", self.existentials.value),
            ("force_quasi_order_classification", self.force_quasi_order_classification),
            ("fresh_entities", self.fresh_entities.value),
            ("individual_grouping", self.individual_grouping.value),
            ("max_memory_bytes", self.max_memory_bytes),
            ("timeout", self.timeout),
            ("unsupported_datatypes", self.unsupported_datatypes.value),
            ("workers", self.workers),
        )

    def as_dict(self) -> dict[str, ConfigScalar]:
        """Return a stable diagnostic mapping without callback/object identities."""

        return dict(self.semantic_items())


__all__ = [
    "BackendName",
    "BlockingMode",
    "ConfigScalar",
    "ExistentialMode",
    "FreshEntityPolicy",
    "IndividualGrouping",
    "ReasonerConfig",
    "UnsupportedDatatypePolicy",
]
