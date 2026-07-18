# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Unique fact rows, support alternatives, delta partitions, and exact indexes.

SPDX-License-Identifier: LGPL-3.0-or-later

Source-guided behavior: pinned HermiT ``ExtensionManager``, ``ExtensionTable``, and
``TupleIndex`` at commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3.  This is an
independent Python storage design with rollback-safe multi-support semantics.
"""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from dataclasses import dataclass, field
from enum import Enum
from typing import cast

from pyhermit.exceptions import InternalInvariantError

from .dependencies import DependencyPool, DependencySet
from .nodes import NodeArena, NodeHandle, NodeLifecycle
from .trail import Trail


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class DeltaView(_StringEnum):
    TOTAL = "total"
    OLD = "delta_old"
    NEW = "delta_new"


@dataclass(frozen=True, slots=True, order=True)
class FactKey:
    predicate_id: int
    arguments: tuple[NodeHandle, ...]

    def __post_init__(self) -> None:
        if (
            isinstance(self.predicate_id, bool)
            or not isinstance(self.predicate_id, int)
            or self.predicate_id < 0
        ):
            raise ValueError("predicate_id must be a nonnegative integer")
        arguments = tuple(self.arguments)
        if not arguments:
            raise ValueError("fact rows must have positive arity")
        if not all(isinstance(argument, NodeHandle) for argument in arguments):
            raise TypeError("fact arguments must be NodeHandle values")
        object.__setattr__(self, "arguments", arguments)


@dataclass(slots=True)
class FactRow:
    row_id: int
    key: FactKey
    supports: tuple[DependencySet, ...]
    core: bool
    active: bool
    derivation_generation: int
    provenance_ids: tuple[int, ...] = field(default_factory=tuple)

    @property
    def minimal_dependency(self) -> DependencySet:
        if not self.supports:
            raise InternalInvariantError("active fact row has no support")
        return min(
            self.supports,
            key=lambda value: (
                len(value),
                value.maximum if value.maximum is not None else -1,
                value.bits,
            ),
        )

    def logical_dict(self) -> dict[str, object]:
        return {
            "arguments": [[item.slot, item.generation] for item in self.key.arguments],
            "core": self.core,
            "generation": self.derivation_generation,
            "predicate_id": self.key.predicate_id,
            "provenance_ids": list(self.provenance_ids),
            "row_id": self.row_id,
            "supports": [list(value) for value in self.supports],
        }


@dataclass(frozen=True, slots=True)
class AddFactOutcome:
    row_id: int
    created: bool
    support_changed: bool


IndexPattern = tuple[int, ...]
IndexKey = tuple[int, tuple[NodeHandle, ...]]


class ExtensionStore:
    """Rollback-safe unique assertion store with on-demand exact indexes."""

    __slots__ = (
        "_by_key",
        "_by_node",
        "_dependencies",
        "_index_data",
        "_nodes",
        "_read_generation",
        "_rows",
        "_trail",
        "_write_generation",
    )

    def __init__(self, trail: Trail, nodes: NodeArena, dependencies: DependencyPool) -> None:
        self._trail = trail
        self._nodes = nodes
        self._dependencies = dependencies
        self._rows: list[FactRow] = []
        self._by_key: dict[FactKey, int] = {}
        self._by_node: dict[NodeHandle, set[int]] = {}
        self._index_data: dict[IndexPattern, dict[IndexKey, set[int]]] = {}
        self._read_generation = 0
        self._write_generation = 0

    @property
    def read_generation(self) -> int:
        return self._read_generation

    @property
    def write_generation(self) -> int:
        return self._write_generation

    def prepare_next_delta(self) -> None:
        """Seal the current NEW view; subsequent derivations enter its successor."""

        previous = (self._read_generation, self._write_generation)
        if self._write_generation == self._read_generation:
            new_values = (self._read_generation, self._write_generation + 1)
        else:
            new_values = (self._write_generation, self._write_generation + 1)
        self._trail.record(
            "extensions.delta",
            lambda: self._restore_generations(previous),
        )
        self._read_generation, self._write_generation = new_values

    def _restore_generations(self, values: tuple[int, int]) -> None:
        self._read_generation, self._write_generation = values

    def add(
        self,
        predicate_id: int,
        arguments: tuple[NodeHandle, ...],
        dependency: DependencySet,
        *,
        core: bool = False,
        provenance_id: int | None = None,
    ) -> AddFactOutcome:
        if not isinstance(dependency, DependencySet):
            raise TypeError("dependency must be DependencySet")
        if not isinstance(core, bool):
            raise TypeError("core must be bool")
        if provenance_id is not None and (
            isinstance(provenance_id, bool)
            or not isinstance(provenance_id, int)
            or provenance_id < 0
        ):
            raise ValueError("provenance_id must be a nonnegative integer or None")
        canonical_arguments: list[NodeHandle] = []
        path_dependencies: list[DependencySet] = [dependency]
        for argument in arguments:
            representative, path = self._nodes.representative(argument)
            node = self._nodes.require_active(representative)
            if node.lifecycle is not NodeLifecycle.ACTIVE:
                raise ValueError("facts may reference only active canonical nodes")
            canonical_arguments.append(representative)
            path_dependencies.append(path)
        key = FactKey(predicate_id, tuple(canonical_arguments))
        support = self._dependencies.union(*path_dependencies)
        existing_id = self._by_key.get(key)
        if existing_id is not None:
            row = self._rows[existing_id]
            return self._update_existing(row, support, core=core, provenance_id=provenance_id)

        row_id = len(self._rows)
        provenance = () if provenance_id is None else (provenance_id,)
        row = FactRow(
            row_id=row_id,
            key=key,
            supports=(support,),
            core=core,
            active=True,
            derivation_generation=self._write_generation,
            provenance_ids=provenance,
        )
        self._rows.append(row)
        self._by_key[key] = row_id
        self._index_insert(row)

        def undo() -> None:
            if self._rows[-1] is not row:
                raise InternalInvariantError("fact creation rollback is not LIFO")
            self._index_remove(row)
            self._by_key.pop(key)
            self._rows.pop()

        self._trail.record("fact.create", undo)
        return AddFactOutcome(row_id, True, True)

    def _update_existing(
        self,
        row: FactRow,
        support: DependencySet,
        *,
        core: bool,
        provenance_id: int | None,
    ) -> AddFactOutcome:
        old_supports = row.supports
        old_core = row.core
        old_provenance = row.provenance_ids
        if any(existing.is_subset_of(support) for existing in old_supports):
            new_supports = old_supports
        else:
            retained = tuple(
                existing for existing in old_supports if not support.is_subset_of(existing)
            )
            new_supports = tuple(sorted((*retained, support), key=lambda item: item.bits))
        new_core = old_core or core
        new_provenance = old_provenance
        if provenance_id is not None and provenance_id not in old_provenance:
            new_provenance = tuple(sorted((*old_provenance, provenance_id)))
        if (
            new_supports == old_supports
            and new_core == old_core
            and new_provenance == old_provenance
        ):
            return AddFactOutcome(row.row_id, False, False)

        def undo() -> None:
            row.supports = old_supports
            row.core = old_core
            row.provenance_ids = old_provenance

        self._trail.record("fact.support", undo)
        row.supports = new_supports
        row.core = new_core
        row.provenance_ids = new_provenance
        return AddFactOutcome(row.row_id, False, new_supports != old_supports)

    def deactivate(self, row_id: int) -> None:
        row = self.row(row_id)
        if not row.active:
            return

        def undo() -> None:
            row.active = True
            self._by_key[row.key] = row.row_id
            self._index_insert(row)

        self._trail.record("fact.deactivate", undo)
        self._index_remove(row)
        self._by_key.pop(row.key, None)
        row.active = False

    def set_core(self, row_id: int, core: bool = True) -> bool:
        """Change a row's blocking/expansion core flag with exact rollback."""

        if not isinstance(core, bool):
            raise TypeError("core must be bool")
        row = self.row(row_id)
        if not row.active:
            raise ValueError("cannot change the core flag of an inactive fact")
        if row.core == core:
            return False
        previous = row.core
        self._trail.record("fact.core", lambda: setattr(row, "core", previous))
        row.core = core
        return True

    def rewrite_node(
        self,
        source: NodeHandle,
        target: NodeHandle,
        dependency: DependencySet,
    ) -> None:
        """Copy affected rows to a representative and deactivate their old keys."""

        affected = [
            self._rows[row_id]
            for row_id in sorted(self._by_node.get(source, ()))
            if self._rows[row_id].active
        ]
        for row in affected:
            arguments = tuple(target if item == source else item for item in row.key.arguments)
            for support in row.supports:
                self.add(
                    row.key.predicate_id,
                    arguments,
                    self._dependencies.union(support, dependency),
                    core=row.core,
                )
            for provenance_id in row.provenance_ids:
                self.add(
                    row.key.predicate_id,
                    arguments,
                    self._dependencies.union(row.minimal_dependency, dependency),
                    core=row.core,
                    provenance_id=provenance_id,
                )
            self.deactivate(row.row_id)

    def deactivate_for_nodes(self, handles: frozenset[NodeHandle]) -> None:
        row_ids = {row_id for handle in handles for row_id in self._by_node.get(handle, ())}
        for row_id in sorted(row_ids):
            if self._rows[row_id].active:
                self.deactivate(row_id)

    def rows_for_node(self, handle: NodeHandle) -> tuple[FactRow, ...]:
        """Return active rows incident on the canonical node in row-ID order."""

        representative, _path = self._nodes.representative(handle)
        self._nodes.require_active(representative)
        return tuple(
            self._rows[row_id]
            for row_id in sorted(self._by_node.get(representative, ()))
            if self._rows[row_id].active
        )

    def row(self, row_id: int) -> FactRow:
        if isinstance(row_id, bool) or not isinstance(row_id, int):
            raise TypeError("row_id must be an integer")
        if not 0 <= row_id < len(self._rows):
            raise KeyError(row_id)
        return self._rows[row_id]

    def register_index(self, pattern: IndexPattern) -> None:
        pattern = tuple(pattern)
        if pattern in self._index_data:
            return
        if pattern != tuple(sorted(set(pattern))):
            raise ValueError("index pattern positions must be sorted and unique")
        if any(
            isinstance(position, bool) or not isinstance(position, int) or position < 0
            for position in pattern
        ):
            raise ValueError("index positions must be nonnegative integers")
        index: dict[IndexKey, set[int]] = {}
        for row in self._rows:
            if row.active and all(position < len(row.key.arguments) for position in pattern):
                key = self._index_key(row.key, pattern)
                index.setdefault(key, set()).add(row.row_id)
        self._index_data[pattern] = index

        def undo() -> None:
            self._index_data.pop(pattern, None)

        self._trail.record("index.register", undo)

    def retrieve(
        self,
        predicate_id: int,
        *,
        bindings: Mapping[int, NodeHandle] | None = None,
        view: DeltaView = DeltaView.TOTAL,
    ) -> Iterator[FactRow]:
        if not isinstance(view, DeltaView):
            raise TypeError("view must be DeltaView")
        clean_bindings: dict[int, NodeHandle] = {}
        for position, handle in (bindings or {}).items():
            if isinstance(position, bool) or not isinstance(position, int) or position < 0:
                raise ValueError("binding positions must be nonnegative integers")
            representative, _dependency = self._nodes.representative(handle)
            self._nodes.require_active(representative)
            clean_bindings[position] = representative
        pattern = tuple(sorted(clean_bindings))
        self.register_index(pattern)
        bound = tuple(clean_bindings[position] for position in pattern)
        row_ids = sorted(self._index_data[pattern].get((predicate_id, bound), ()))
        for row_id in row_ids:
            row = self._rows[row_id]
            if not row.active or not self._in_view(row, view):
                continue
            if any(
                self._nodes.get(argument).lifecycle is not NodeLifecycle.ACTIVE
                for argument in row.key.arguments
            ):
                continue
            yield row

    def active_rows(self, view: DeltaView = DeltaView.TOTAL) -> tuple[FactRow, ...]:
        return tuple(self.iter_active_rows(view))

    def iter_active_rows(self, view: DeltaView = DeltaView.TOTAL) -> Iterator[FactRow]:
        """Stream active rows without allocating a second ontology-scale tuple."""

        if not isinstance(view, DeltaView):
            raise TypeError("view must be DeltaView")
        for row in self._rows:
            if row.active and self._in_view(row, view):
                yield row

    def _in_view(self, row: FactRow, view: DeltaView) -> bool:
        if view is DeltaView.TOTAL:
            return True
        if view is DeltaView.NEW:
            return row.derivation_generation == self._read_generation
        return row.derivation_generation < self._read_generation

    @staticmethod
    def _index_key(key: FactKey, pattern: IndexPattern) -> IndexKey:
        return key.predicate_id, tuple(key.arguments[position] for position in pattern)

    def _index_insert(self, row: FactRow) -> None:
        for argument in set(row.key.arguments):
            self._by_node.setdefault(argument, set()).add(row.row_id)
        for pattern, index in self._index_data.items():
            if all(position < len(row.key.arguments) for position in pattern):
                index.setdefault(self._index_key(row.key, pattern), set()).add(row.row_id)

    def _index_remove(self, row: FactRow) -> None:
        for argument in set(row.key.arguments):
            node_rows = self._by_node.get(argument)
            if node_rows is None or row.row_id not in node_rows:
                raise InternalInvariantError("fact row missing from node incidence index")
            node_rows.remove(row.row_id)
            if not node_rows:
                del self._by_node[argument]
        for pattern, index in self._index_data.items():
            if not all(position < len(row.key.arguments) for position in pattern):
                continue
            key = self._index_key(row.key, pattern)
            members = index.get(key)
            if members is None or row.row_id not in members:
                raise InternalInvariantError("fact row missing from registered index")
            members.remove(row.row_id)
            if not members:
                del index[key]

    def check_invariants(self, *, highest_branch_level: int | None = None) -> None:
        expected_by_key: dict[FactKey, int] = {}
        expected_by_node: dict[NodeHandle, set[int]] = {}
        for row_id, row in enumerate(self._rows):
            if row.row_id != row_id:
                raise InternalInvariantError("fact row ID disagrees with storage position")
            if not row.active:
                continue
            if row.key in expected_by_key:
                raise InternalInvariantError("duplicate active fact key")
            expected_by_key[row.key] = row.row_id
            for argument in set(row.key.arguments):
                expected_by_node.setdefault(argument, set()).add(row.row_id)
            if not row.supports:
                raise InternalInvariantError("active fact has no supports")
            if row.supports != tuple(sorted(set(row.supports), key=lambda item: item.bits)):
                raise InternalInvariantError("fact supports are not sorted and unique")
            for left in row.supports:
                for right in row.supports:
                    if left != right and left.is_subset_of(right):
                        raise InternalInvariantError("fact retains a dominated support")
                if highest_branch_level is not None:
                    maximum = left.maximum
                    if maximum is not None and maximum > highest_branch_level:
                        raise InternalInvariantError("fact support references a future branch")
            for argument in row.key.arguments:
                node = self._nodes.get(argument)
                if node.lifecycle is not NodeLifecycle.ACTIVE:
                    raise InternalInvariantError("active fact references an inactive node")
        if expected_by_key != self._by_key:
            raise InternalInvariantError("fact key map does not match active rows")
        if expected_by_node != self._by_node:
            raise InternalInvariantError("node incidence index does not match active rows")
        for pattern, actual in self._index_data.items():
            rebuilt: dict[IndexKey, set[int]] = {}
            for row in self._rows:
                if row.active and all(position < len(row.key.arguments) for position in pattern):
                    rebuilt.setdefault(self._index_key(row.key, pattern), set()).add(row.row_id)
            if actual != rebuilt:
                raise InternalInvariantError("registered fact index differs from reconstruction")
        if self._write_generation < self._read_generation:
            raise InternalInvariantError("delta write generation precedes read generation")

    def logical_snapshot(self) -> tuple[dict[str, object], ...]:
        return tuple(row.logical_dict() for row in self._rows if row.active)

    def dependency_sets(self) -> tuple[DependencySet, ...]:
        return tuple(support for row in self._rows if row.active for support in row.supports)


__all__ = [
    "AddFactOutcome",
    "DeltaView",
    "ExtensionStore",
    "FactKey",
    "FactRow",
    "IndexPattern",
]
