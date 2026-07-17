"""Rollback-safe ground-disjunction and clash records.

SPDX-License-Identifier: LGPL-3.0-or-later

The records in this module deliberately contain stable compiled-IR identifiers.  Rule
interpretation and disjunct satisfaction belong to WP09, not to mutable state.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import cast

from pyhermit.exceptions import InternalInvariantError

from .dependencies import DependencyPool, DependencySet
from .trail import Trail


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class ClashKind(_StringEnum):
    BOTTOM = "bottom"
    EMPTY_HEAD = "empty_head"
    POSITIVE_NEGATIVE_ATOM = "positive_negative_atom"
    EQUALITY_INEQUALITY = "equality_inequality"
    IRREFLEXIVE_ROLE = "irreflexive_role"
    ASYMMETRIC_ROLE = "asymmetric_role"
    DISJOINT_ROLES = "disjoint_roles"
    IMPOSSIBLE_CARDINALITY = "impossible_cardinality"
    DATATYPE_UNSATISFIABLE = "datatype_unsatisfiable"


@dataclass(slots=True)
class GroundDisjunction:
    disjunction_id: int
    disjunct_ids: tuple[int, ...]
    base_dependency: DependencySet
    creation_checkpoint: int
    active: bool = True
    processed: bool = False

    def logical_dict(self) -> dict[str, object]:
        return {
            "active": self.active,
            "base_dependency": list(self.base_dependency),
            "creation_checkpoint": self.creation_checkpoint,
            "disjunct_ids": list(self.disjunct_ids),
            "disjunction_id": self.disjunction_id,
            "processed": self.processed,
        }


class GroundDisjunctionStore:
    __slots__ = ("_dependencies", "_records", "_trail")

    def __init__(self, trail: Trail, dependencies: DependencyPool) -> None:
        self._trail = trail
        self._dependencies = dependencies
        self._records: list[GroundDisjunction] = []

    def add(
        self,
        disjunct_ids: tuple[int, ...],
        dependency: DependencySet,
        *,
        creation_checkpoint: int,
    ) -> int:
        disjuncts = tuple(disjunct_ids)
        if not disjuncts:
            raise ValueError("a ground disjunction must contain at least one disjunct")
        if len(set(disjuncts)) != len(disjuncts):
            raise ValueError("ground disjunct identifiers must be unique")
        if any(
            isinstance(item, bool) or not isinstance(item, int) or item < 0 for item in disjuncts
        ):
            raise ValueError("ground disjunct identifiers must be nonnegative integers")
        if not isinstance(dependency, DependencySet):
            raise TypeError("dependency must be DependencySet")
        if (
            isinstance(creation_checkpoint, bool)
            or not isinstance(creation_checkpoint, int)
            or creation_checkpoint < 0
        ):
            raise ValueError("creation_checkpoint must be a nonnegative integer")
        record = GroundDisjunction(
            len(self._records),
            disjuncts,
            self._dependencies.intern(dependency),
            creation_checkpoint,
        )
        self._records.append(record)

        def undo() -> None:
            if self._records[-1] is not record:
                raise InternalInvariantError("disjunction creation rollback is not LIFO")
            self._records.pop()

        self._trail.record("disjunction.create", undo)
        return record.disjunction_id

    def get(self, disjunction_id: int) -> GroundDisjunction:
        if isinstance(disjunction_id, bool) or not isinstance(disjunction_id, int):
            raise TypeError("disjunction_id must be an integer")
        if not 0 <= disjunction_id < len(self._records):
            raise KeyError(disjunction_id)
        return self._records[disjunction_id]

    def set_processed(self, disjunction_id: int, processed: bool = True) -> None:
        if not isinstance(processed, bool):
            raise TypeError("processed must be bool")
        record = self.get(disjunction_id)
        if record.processed == processed:
            return
        previous = record.processed
        self._trail.record(
            "disjunction.processed",
            lambda: setattr(record, "processed", previous),
        )
        record.processed = processed

    def set_active(self, disjunction_id: int, active: bool) -> None:
        if not isinstance(active, bool):
            raise TypeError("active must be bool")
        record = self.get(disjunction_id)
        if record.active == active:
            return
        previous = record.active
        self._trail.record(
            "disjunction.active",
            lambda: setattr(record, "active", previous),
        )
        record.active = active

    def records(self) -> tuple[GroundDisjunction, ...]:
        return tuple(self._records)

    def check_invariants(self, *, highest_branch_level: int | None = None) -> None:
        for disjunction_id, record in enumerate(self._records):
            if record.disjunction_id != disjunction_id:
                raise InternalInvariantError("ground-disjunction ID disagrees with position")
            if not record.disjunct_ids or len(set(record.disjunct_ids)) != len(record.disjunct_ids):
                raise InternalInvariantError("invalid ground-disjunction disjuncts")
            maximum = record.base_dependency.maximum
            if (
                highest_branch_level is not None
                and maximum is not None
                and maximum > highest_branch_level
            ):
                raise InternalInvariantError("disjunction depends on a future branch")

    def logical_snapshot(self) -> tuple[dict[str, object], ...]:
        return tuple(record.logical_dict() for record in self._records)

    def dependency_sets(self) -> tuple[DependencySet, ...]:
        return tuple(record.base_dependency for record in self._records if record.active)


@dataclass(frozen=True, slots=True)
class Clash:
    kind: ClashKind
    dependency: DependencySet
    participants: tuple[int, ...] = ()
    provenance_id: int | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.kind, ClashKind):
            raise TypeError("kind must be ClashKind")
        if not isinstance(self.dependency, DependencySet):
            raise TypeError("dependency must be DependencySet")
        participants = tuple(self.participants)
        if participants != tuple(sorted(set(participants))) or any(
            isinstance(item, bool) or not isinstance(item, int) or item < 0 for item in participants
        ):
            raise ValueError("clash participants must be sorted unique nonnegative IDs")
        if self.provenance_id is not None and (
            isinstance(self.provenance_id, bool)
            or not isinstance(self.provenance_id, int)
            or self.provenance_id < 0
        ):
            raise ValueError("provenance_id must be a nonnegative integer or None")
        object.__setattr__(self, "participants", participants)

    def logical_dict(self) -> dict[str, object]:
        return {
            "dependency": list(self.dependency),
            "kind": self.kind.value,
            "participants": list(self.participants),
            "provenance_id": self.provenance_id,
        }


class ClashStore:
    """Own the single current clash and deterministically retain a useful support."""

    __slots__ = ("_current", "_dependencies", "_trail")

    def __init__(self, trail: Trail, dependencies: DependencyPool) -> None:
        self._trail = trail
        self._dependencies = dependencies
        self._current: Clash | None = None

    @property
    def current(self) -> Clash | None:
        return self._current

    def install(self, clash: Clash) -> bool:
        if not isinstance(clash, Clash):
            raise TypeError("clash must be Clash")
        candidate = Clash(
            clash.kind,
            self._dependencies.intern(clash.dependency),
            clash.participants,
            clash.provenance_id,
        )
        selected = self._select(self._current, candidate)
        if selected == self._current:
            return False
        previous = self._current
        self._trail.record("clash.install", lambda: setattr(self, "_current", previous))
        self._current = selected
        return True

    def clear(self) -> bool:
        if self._current is None:
            return False
        previous = self._current
        self._trail.record("clash.clear", lambda: setattr(self, "_current", previous))
        self._current = None
        return True

    @staticmethod
    def _select(current: Clash | None, candidate: Clash) -> Clash:
        if current is None:
            return candidate
        if current.dependency.is_subset_of(candidate.dependency):
            return current
        if candidate.dependency.is_subset_of(current.dependency):
            return candidate
        current_key = ClashStore._rank(current)
        candidate_key = ClashStore._rank(candidate)
        return min((current_key, current), (candidate_key, candidate), key=lambda item: item[0])[1]

    @staticmethod
    def _rank(clash: Clash) -> tuple[object, ...]:
        maximum = clash.dependency.maximum
        return (
            len(clash.dependency),
            -1 if maximum is None else maximum,
            clash.dependency.bits,
            clash.kind.value,
            clash.participants,
            -1 if clash.provenance_id is None else clash.provenance_id,
        )

    def check_invariants(self, *, highest_branch_level: int | None = None) -> None:
        clash = self._current
        if clash is None or highest_branch_level is None:
            return
        maximum = clash.dependency.maximum
        if maximum is not None and maximum > highest_branch_level:
            raise InternalInvariantError("clash depends on a future branch")


__all__ = [
    "Clash",
    "ClashKind",
    "ClashStore",
    "GroundDisjunction",
    "GroundDisjunctionStore",
]
