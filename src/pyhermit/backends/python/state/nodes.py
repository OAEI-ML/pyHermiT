"""Generation-safe tableau node arena and lifecycle mechanics.

SPDX-License-Identifier: LGPL-3.0-or-later

Source-guided behavior: pinned HermiT ``tableau/Node.java`` at commit
37ec30aced32ac81ebecc5e33fad255ddefcb4c3.  Arena/generation and rollback design are
Python-native and follow ``specs/tableau-state.md``.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import cast

from pyhermit.exceptions import InternalInvariantError

from .dependencies import DependencyPool, DependencySet
from .trail import Trail


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class NodeKind(_StringEnum):
    ROOT = "root"
    TREE = "tree"
    NI = "ni"
    CONCRETE = "concrete"


class NodeSort(_StringEnum):
    OBJECT = "object"
    DATA = "data"


class NodeLifecycle(_StringEnum):
    ACTIVE = "active"
    MERGED = "merged"
    PRUNED = "pruned"
    RETIRED = "retired"


@dataclass(frozen=True, slots=True, order=True)
class NodeHandle:
    slot: int
    generation: int

    def __post_init__(self) -> None:
        for name in ("slot", "generation"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"node handle {name} must be a nonnegative integer")


@dataclass(slots=True)
class Node:
    handle: NodeHandle
    creation_id: int
    kind: NodeKind
    sort: NodeSort
    lifecycle: NodeLifecycle
    parent: NodeHandle | None
    tree_depth: int
    creation_checkpoint: int
    is_owl_named_individual: bool = False
    source_individual_id: int | None = None
    representative: NodeHandle | None = None
    merge_dependency: DependencySet = field(default_factory=DependencySet)
    blocker: NodeHandle | None = None
    directly_blocked: bool = False
    blocking_generation: int = 0
    unprocessed_existentials: set[int] = field(default_factory=set)
    nominal_level: int | None = None
    cardinality_tag: int | None = None

    def logical_dict(self) -> dict[str, object]:
        return {
            "blocker": None
            if self.blocker is None
            else [self.blocker.slot, self.blocker.generation],
            "blocking_generation": self.blocking_generation,
            "cardinality_tag": self.cardinality_tag,
            "creation_id": self.creation_id,
            "directly_blocked": self.directly_blocked,
            "existentials": sorted(self.unprocessed_existentials),
            "handle": [self.handle.slot, self.handle.generation],
            "is_owl_named_individual": self.is_owl_named_individual,
            "kind": self.kind.value,
            "lifecycle": self.lifecycle.value,
            "merge_dependency": list(self.merge_dependency),
            "nominal_level": self.nominal_level,
            "parent": None if self.parent is None else [self.parent.slot, self.parent.generation],
            "representative": None
            if self.representative is None
            else [self.representative.slot, self.representative.generation],
            "sort": self.sort.value,
            "source_individual_id": self.source_individual_id,
            "tree_depth": self.tree_depth,
        }


class NodeArena:
    __slots__ = ("_dependencies", "_free", "_generations", "_next_creation_id", "_slots", "_trail")

    def __init__(self, trail: Trail, dependencies: DependencyPool) -> None:
        if not isinstance(trail, Trail):
            raise TypeError("trail must be Trail")
        if not isinstance(dependencies, DependencyPool):
            raise TypeError("dependencies must be DependencyPool")
        self._trail = trail
        self._dependencies = dependencies
        self._slots: list[Node | None] = []
        self._generations: list[int] = []
        self._free: list[int] = []
        self._next_creation_id = 0

    def create(
        self,
        kind: NodeKind,
        *,
        parent: NodeHandle | None = None,
        is_owl_named_individual: bool = False,
        source_individual_id: int | None = None,
        creation_checkpoint: int = 0,
        nominal_level: int | None = None,
        cardinality_tag: int | None = None,
    ) -> NodeHandle:
        if not isinstance(kind, NodeKind):
            raise TypeError("kind must be NodeKind")
        if not isinstance(is_owl_named_individual, bool):
            raise TypeError("is_owl_named_individual must be bool")
        for name, value in (
            ("source_individual_id", source_individual_id),
            ("nominal_level", nominal_level),
            ("cardinality_tag", cardinality_tag),
        ):
            if value is not None and (
                isinstance(value, bool) or not isinstance(value, int) or value < 0
            ):
                raise ValueError(f"{name} must be a nonnegative integer or None")
        if isinstance(creation_checkpoint, bool) or not isinstance(creation_checkpoint, int):
            raise TypeError("creation_checkpoint must be a nonnegative integer")
        if creation_checkpoint < 0:
            raise ValueError("creation_checkpoint must be a nonnegative integer")

        sort = NodeSort.DATA if kind is NodeKind.CONCRETE else NodeSort.OBJECT
        if kind is NodeKind.TREE:
            if parent is None:
                raise ValueError("tree nodes require a parent")
            parent_node = self.require_active(parent)
            if parent_node.sort is not NodeSort.OBJECT:
                raise ValueError("tree node parent must be an object node")
            depth = parent_node.tree_depth + 1
        else:
            if parent is not None:
                raise ValueError(f"{kind.value} nodes cannot have a parent")
            depth = 0
        if is_owl_named_individual and (kind is not NodeKind.ROOT or source_individual_id is None):
            raise ValueError("only source named-individual root nodes may carry the named guard")

        if self._free:
            slot = self._free.pop(0)
        else:
            slot = len(self._slots)
            self._slots.append(None)
            self._generations.append(0)
        self._generations[slot] += 1
        handle = NodeHandle(slot, self._generations[slot])
        creation_id = self._next_creation_id
        self._next_creation_id += 1
        node = Node(
            handle=handle,
            creation_id=creation_id,
            kind=kind,
            sort=sort,
            lifecycle=NodeLifecycle.ACTIVE,
            parent=parent,
            tree_depth=depth,
            creation_checkpoint=creation_checkpoint,
            is_owl_named_individual=is_owl_named_individual,
            source_individual_id=source_individual_id,
            nominal_level=nominal_level,
            cardinality_tag=cardinality_tag,
        )
        self._slots[slot] = node

        def undo() -> None:
            current = self._slots[slot]
            if current is not node:
                raise InternalInvariantError("node creation rollback found a replaced slot")
            self._slots[slot] = None
            self._insert_free(slot)
            self._next_creation_id = creation_id

        self._trail.record("node.create", undo)
        return handle

    def get(self, handle: NodeHandle) -> Node:
        if not isinstance(handle, NodeHandle):
            raise TypeError("handle must be NodeHandle")
        if handle.slot >= len(self._slots):
            raise KeyError(f"stale node handle {handle}")
        node = self._slots[handle.slot]
        if node is None or node.handle.generation != handle.generation:
            raise KeyError(f"stale node handle {handle}")
        if node.lifecycle is NodeLifecycle.RETIRED:
            raise KeyError(f"retired node handle {handle}")
        return node

    def require_active(self, handle: NodeHandle) -> Node:
        node = self.get(handle)
        if node.lifecycle is not NodeLifecycle.ACTIVE:
            raise ValueError(f"node {handle} is not active ({node.lifecycle.value})")
        return node

    def active_handles(self) -> tuple[NodeHandle, ...]:
        return tuple(
            node.handle
            for node in self._slots
            if node is not None and node.lifecycle is NodeLifecycle.ACTIVE
        )

    def existing_nodes(self) -> tuple[Node, ...]:
        return tuple(
            node
            for node in self._slots
            if node is not None and node.lifecycle is not NodeLifecycle.RETIRED
        )

    def representative(self, handle: NodeHandle) -> tuple[NodeHandle, DependencySet]:
        node = self.get(handle)
        dependencies: list[DependencySet] = []
        seen: set[NodeHandle] = set()
        while node.representative is not None:
            if node.handle in seen:
                raise InternalInvariantError("cycle in node representative relation")
            seen.add(node.handle)
            dependencies.append(node.merge_dependency)
            node = self.get(node.representative)
        return node.handle, self._dependencies.union(*dependencies)

    def merge(
        self,
        source: NodeHandle,
        target: NodeHandle,
        dependency: DependencySet,
    ) -> None:
        source_node = self.require_active(source)
        target_handle, path_dependency = self.representative(target)
        target_node = self.require_active(target_handle)
        if source_node.handle == target_node.handle:
            return
        if source_node.sort is not target_node.sort:
            raise InternalInvariantError("cannot merge object and concrete nodes")
        combined = self._dependencies.union(dependency, path_dependency)
        previous = (
            source_node.lifecycle,
            source_node.representative,
            source_node.merge_dependency,
        )

        def undo() -> None:
            (
                source_node.lifecycle,
                source_node.representative,
                source_node.merge_dependency,
            ) = previous

        self._trail.record("node.merge", undo)
        source_node.lifecycle = NodeLifecycle.MERGED
        source_node.representative = target_node.handle
        source_node.merge_dependency = combined

    def prune(self, handle: NodeHandle) -> None:
        node = self.require_active(handle)
        previous = node.lifecycle
        self._trail.record("node.prune", lambda: setattr(node, "lifecycle", previous))
        node.lifecycle = NodeLifecycle.PRUNED

    def retire(self, handle: NodeHandle) -> None:
        node = self.get(handle)
        slot = handle.slot
        if node.lifecycle is NodeLifecycle.RETIRED:
            return
        for other in self.existing_nodes():
            if other is node:
                continue
            if handle in (other.parent, other.representative, other.blocker):
                raise ValueError("cannot retire a node that remains structurally referenced")

        def undo() -> None:
            self._remove_free(slot)
            self._slots[slot] = node
            node.lifecycle = previous

        previous = node.lifecycle
        self._trail.record("node.retire", undo)
        node.lifecycle = NodeLifecycle.RETIRED
        self._slots[slot] = None
        self._insert_free(slot)

    def set_blocked(
        self,
        handle: NodeHandle,
        blocker: NodeHandle | None,
        *,
        directly: bool,
    ) -> None:
        node = self.require_active(handle)
        if node.sort is NodeSort.DATA:
            raise ValueError("concrete nodes cannot be blocked")
        if blocker is not None:
            blocker_node = self.require_active(blocker)
            if blocker_node.sort is NodeSort.DATA:
                raise ValueError("a concrete node cannot be a blocker")
        if not isinstance(directly, bool):
            raise TypeError("directly must be bool")
        previous = (node.blocker, node.directly_blocked, node.blocking_generation)

        def undo() -> None:
            node.blocker, node.directly_blocked, node.blocking_generation = previous

        self._trail.record("node.blocking", undo)
        node.blocker = blocker
        node.directly_blocked = directly if blocker is not None else False
        node.blocking_generation += 1

    def mark_existential(self, handle: NodeHandle, existential_id: int, *, pending: bool) -> None:
        node = self.require_active(handle)
        if (
            isinstance(existential_id, bool)
            or not isinstance(existential_id, int)
            or existential_id < 0
        ):
            raise ValueError("existential_id must be a nonnegative integer")
        if not isinstance(pending, bool):
            raise TypeError("pending must be bool")
        existed = existential_id in node.unprocessed_existentials
        if existed == pending:
            return

        def undo() -> None:
            if existed:
                node.unprocessed_existentials.add(existential_id)
            else:
                node.unprocessed_existentials.discard(existential_id)

        self._trail.record("node.existential", undo)
        if pending:
            node.unprocessed_existentials.add(existential_id)
        else:
            node.unprocessed_existentials.remove(existential_id)

    def check_invariants(self, *, highest_branch_level: int | None = None) -> None:
        free = set(self._free)
        if len(free) != len(self._free) or self._free != sorted(self._free):
            raise InternalInvariantError("node free list is not sorted and unique")
        expected_free = {index for index, node in enumerate(self._slots) if node is None}
        if free != expected_free:
            raise InternalInvariantError("node free list does not match empty slots")
        creation_ids: set[int] = set()
        for slot, node in enumerate(self._slots):
            if node is None:
                continue
            if node.handle.slot != slot or node.handle.generation > self._generations[slot]:
                raise InternalInvariantError("node handle does not match its arena slot")
            if node.creation_id in creation_ids:
                raise InternalInvariantError("duplicate node creation ID")
            creation_ids.add(node.creation_id)
            if (
                highest_branch_level is not None
                and highest_branch_level >= 0
                and node.creation_checkpoint > highest_branch_level
            ):
                raise InternalInvariantError("node was created at a future branch level")
            if node.kind is NodeKind.TREE:
                if node.parent is None:
                    raise InternalInvariantError("tree node has no parent")
                parent = self.get(node.parent)
                if node.tree_depth != parent.tree_depth + 1:
                    raise InternalInvariantError("tree node depth disagrees with parent")
            elif node.parent is not None or node.tree_depth != 0:
                raise InternalInvariantError("root/concrete node has tree parent/depth")
            if node.sort is NodeSort.DATA and node.kind is not NodeKind.CONCRETE:
                raise InternalInvariantError("only concrete nodes have data sort")
            if node.lifecycle is NodeLifecycle.MERGED:
                if node.representative is None:
                    raise InternalInvariantError("merged node has no representative")
                representative, _dependency = self.representative(node.handle)
                if self.get(representative).lifecycle is not NodeLifecycle.ACTIVE:
                    raise InternalInvariantError("merge representative is not active")
                maximum = node.merge_dependency.maximum
                if (
                    highest_branch_level is not None
                    and maximum is not None
                    and maximum > highest_branch_level
                ):
                    raise InternalInvariantError("merge depends on a future branch")
            elif node.representative is not None:
                raise InternalInvariantError("nonmerged node has a representative")
            if node.blocker is not None:
                blocker = self.require_active(node.blocker)
                if blocker.sort is not NodeSort.OBJECT or node.sort is not NodeSort.OBJECT:
                    raise InternalInvariantError("invalid concrete blocking relation")

    def logical_snapshot(self) -> tuple[dict[str, object], ...]:
        return tuple(
            node.logical_dict()
            for node in sorted(self.existing_nodes(), key=lambda value: value.creation_id)
        )

    def dependency_sets(self) -> tuple[DependencySet, ...]:
        return tuple(
            node.merge_dependency for node in self.existing_nodes() if node.merge_dependency
        )

    def _insert_free(self, slot: int) -> None:
        if slot in self._free:
            raise InternalInvariantError("node slot was freed twice")
        self._free.append(slot)
        self._free.sort()

    def _remove_free(self, slot: int) -> None:
        try:
            self._free.remove(slot)
        except ValueError as exc:
            raise InternalInvariantError("node slot missing from free list") from exc


__all__ = [
    "Node",
    "NodeArena",
    "NodeHandle",
    "NodeKind",
    "NodeLifecycle",
    "NodeSort",
]
