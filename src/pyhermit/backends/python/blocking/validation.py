"""Validated/core blocking boundary and fixed-point result records.

SPDX-License-Identifier: LGPL-3.0-or-later

WP06/WP09 provide the compiled-clause implementation of ``BlockingValidator``.  WP11
owns deterministic block enumeration, core promotion, rescheduling, cancellation, and
the no-SAT-before-validation gate around this narrow protocol.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol, runtime_checkable

from pyhermit.backends.python.state import NodeHandle, TableauSession

from .signatures import BlockingSignature


@dataclass(frozen=True, slots=True)
class ValidationDecision:
    valid: bool
    promote_row_ids: tuple[int, ...] = ()
    reschedule_nodes: tuple[NodeHandle, ...] = ()
    violation_ids: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.valid, bool):
            raise TypeError("valid must be bool")
        row_ids = tuple(self.promote_row_ids)
        violations = tuple(self.violation_ids)
        for name, values in (("promote_row_ids", row_ids), ("violation_ids", violations)):
            if values != tuple(sorted(set(values))) or any(
                isinstance(value, bool) or not isinstance(value, int) or value < 0
                for value in values
            ):
                raise ValueError(f"{name} must be sorted unique nonnegative IDs")
        nodes = tuple(self.reschedule_nodes)
        if nodes != tuple(sorted(set(nodes))) or not all(
            isinstance(node, NodeHandle) for node in nodes
        ):
            raise ValueError("reschedule_nodes must be sorted unique NodeHandle values")
        if self.valid and (row_ids or nodes or violations):
            raise ValueError("a valid block cannot request repair side effects")
        object.__setattr__(self, "promote_row_ids", row_ids)
        object.__setattr__(self, "reschedule_nodes", nodes)
        object.__setattr__(self, "violation_ids", violations)


@runtime_checkable
class BlockingValidator(Protocol):
    """Compiled-clause validator implemented once WP06 private IR is available."""

    def validate_block(
        self,
        session: TableauSession,
        blocked: NodeHandle,
        blocker: NodeHandle,
        signature: BlockingSignature,
    ) -> ValidationDecision: ...


@dataclass(frozen=True, slots=True)
class ValidationPassResult:
    valid: bool
    checked_blocks: int
    invalidated_blocks: int
    promoted_rows: int
    rescheduled_nodes: int
    violation_ids: tuple[int, ...]
    state_digest: str

    def __post_init__(self) -> None:
        if not isinstance(self.valid, bool):
            raise TypeError("valid must be bool")
        for name in (
            "checked_blocks",
            "invalidated_blocks",
            "promoted_rows",
            "rescheduled_nodes",
        ):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")
        if not isinstance(self.state_digest, str) or not self.state_digest:
            raise ValueError("state_digest must be a nonempty string")


__all__ = ["BlockingValidator", "ValidationDecision", "ValidationPassResult"]
