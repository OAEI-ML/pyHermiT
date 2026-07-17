"""Immutable private records for Python hyperresolution.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import cast

from pyhermit.backends.python.state import DependencySet, NodeHandle
from pyhermit.clauses import TermSort


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class BranchTransition(_StringEnum):
    NO_WORK = "no_work"
    SATISFIED = "satisfied"
    DETERMINISTIC = "deterministic"
    BRANCHED = "branched"
    ADVANCED = "advanced"
    EXHAUSTED = "exhausted"
    UNSAT = "unsat"


@dataclass(frozen=True, slots=True, order=True)
class VariableBinding:
    sort: TermSort
    variable_id: int
    node: NodeHandle

    def __post_init__(self) -> None:
        if not isinstance(self.sort, TermSort):
            raise TypeError("binding sort must be TermSort")
        if (
            isinstance(self.variable_id, bool)
            or not isinstance(self.variable_id, int)
            or self.variable_id < 0
        ):
            raise ValueError("binding variable_id must be a nonnegative integer")
        if not isinstance(self.node, NodeHandle):
            raise TypeError("binding node must be NodeHandle")


@dataclass(frozen=True, slots=True)
class JoinMatch:
    clause_id: int
    delta_body_index: int
    bindings: tuple[VariableBinding, ...]
    dependency: DependencySet
    premise_row_ids: tuple[int, ...]

    def __post_init__(self) -> None:
        for name in ("clause_id", "delta_body_index"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")
        bindings = tuple(self.bindings)
        keys = tuple((value.sort.value, value.variable_id) for value in bindings)
        if keys != tuple(sorted(set(keys))):
            raise ValueError("join bindings must be uniquely sorted by variable")
        if not isinstance(self.dependency, DependencySet):
            raise TypeError("join dependency must be DependencySet")
        rows = tuple(sorted(set(self.premise_row_ids)))
        if any(
            isinstance(value, bool) or not isinstance(value, int) or value < 0 for value in rows
        ):
            raise ValueError("premise row IDs must be nonnegative integers")
        object.__setattr__(self, "bindings", bindings)
        object.__setattr__(self, "premise_row_ids", rows)


@dataclass(frozen=True, slots=True, order=True)
class GroundRuleAtom:
    predicate_id: int
    arguments: tuple[NodeHandle, ...]

    def __post_init__(self) -> None:
        if (
            isinstance(self.predicate_id, bool)
            or not isinstance(self.predicate_id, int)
            or self.predicate_id < 0
        ):
            raise ValueError("ground predicate ID must be a nonnegative integer")
        arguments = tuple(self.arguments)
        if not 1 <= len(arguments) <= 3:
            raise ValueError("ground rule atoms must have arity one, two, or three")
        if not all(isinstance(value, NodeHandle) for value in arguments):
            raise TypeError("ground rule arguments must be NodeHandle values")
        object.__setattr__(self, "arguments", arguments)


@dataclass(frozen=True, slots=True)
class PendingAnnotatedEquality:
    action_id: int
    atom: GroundRuleAtom
    supports: tuple[DependencySet, ...]
    provenance_ids: tuple[int, ...]

    def __post_init__(self) -> None:
        if (
            isinstance(self.action_id, bool)
            or not isinstance(self.action_id, int)
            or self.action_id < 0
        ):
            raise ValueError("annotated-equality action ID must be a nonnegative integer")
        if not isinstance(self.atom, GroundRuleAtom) or len(self.atom.arguments) != 3:
            raise ValueError("annotated equality requires a ternary ground atom")
        supports = tuple(sorted(set(self.supports), key=lambda value: value.bits))
        if not supports or not all(isinstance(value, DependencySet) for value in supports):
            raise ValueError("annotated equality requires dependency supports")
        provenance = tuple(sorted(set(self.provenance_ids)))
        if any(
            isinstance(value, bool) or not isinstance(value, int) or value < 0
            for value in provenance
        ):
            raise ValueError("annotated-equality provenance IDs must be nonnegative integers")
        object.__setattr__(self, "supports", supports)
        object.__setattr__(self, "provenance_ids", provenance)


@dataclass(frozen=True, slots=True)
class RuleLimits:
    max_join_steps: int = 10_000_000
    max_matches_per_generation: int = 2_000_000
    cancellation_interval: int = 256

    def __post_init__(self) -> None:
        for name in (
            "max_join_steps",
            "max_matches_per_generation",
            "cancellation_interval",
        ):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
                raise ValueError(f"{name} must be a positive integer")


__all__ = [
    "BranchTransition",
    "GroundRuleAtom",
    "JoinMatch",
    "PendingAnnotatedEquality",
    "RuleLimits",
    "VariableBinding",
]
