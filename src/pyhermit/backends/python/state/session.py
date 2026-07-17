"""Whole-session tableau state, branch checkpoints, and recovery orchestration.

SPDX-License-Identifier: LGPL-3.0-or-later

This module coordinates state mechanics only.  It contains no clause, equality-rule,
or ground-disjunction semantics; those are supplied by later Python rule work packages.
"""

from __future__ import annotations

import json
from collections.abc import Callable
from dataclasses import dataclass, field
from enum import Enum
from typing import TypeVar, cast

from pyhermit.events import CancellationToken
from pyhermit.exceptions import InternalInvariantError, ReasoningAbortedError

from .dependencies import DependencyPool, DependencySet
from .disjunctions import (
    Clash,
    ClashStore,
    GroundDisjunction,
    GroundDisjunctionStore,
)
from .extensions import ExtensionStore
from .nodes import Node, NodeArena, NodeHandle, NodeKind, NodeLifecycle
from .queues import StableQueue
from .trail import Checkpoint, Trail

ResultT = TypeVar("ResultT")


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class BranchChoiceKind(_StringEnum):
    GROUND_DISJUNCTION = "ground_disjunction"
    MERGE = "merge"
    DATATYPE = "datatype"


@dataclass(slots=True)
class BranchingPoint:
    level: int
    choice_kind: BranchChoiceKind
    checkpoint: Checkpoint
    alternatives: tuple[int, ...]
    source_id: int
    base_dependency: DependencySet
    next_alternative: int = 0
    learned_dependency: DependencySet = field(default_factory=DependencySet)

    @property
    def current(self) -> int:
        if self.next_alternative >= len(self.alternatives):
            raise IndexError("branching point has no remaining alternative")
        return self.alternatives[self.next_alternative]

    @property
    def remaining(self) -> tuple[int, ...]:
        return self.alternatives[self.next_alternative :]

    def logical_dict(self) -> dict[str, object]:
        return {
            "alternatives": list(self.alternatives),
            "base_dependency": list(self.base_dependency),
            "checkpoint": {
                "label": self.checkpoint.label,
                "sequence": self.checkpoint.sequence,
                "trail_length": self.checkpoint.trail_length,
            },
            "choice_kind": self.choice_kind.value,
            "learned_dependency": list(self.learned_dependency),
            "level": self.level,
            "next_alternative": self.next_alternative,
            "source_id": self.source_id,
        }


class TableauSession:
    """Own every mutable component for one compiled ontology/query pair."""

    __slots__ = (
        "annotated_equalities",
        "blocking_invalidations",
        "branches",
        "clashes",
        "datatype_components",
        "delta_rows",
        "dependencies",
        "disjunction_queue",
        "disjunctions",
        "existential_candidates",
        "extensions",
        "nodes",
        "operation_root",
        "trail",
    )

    def __init__(self) -> None:
        self.trail = Trail()
        self.dependencies = DependencyPool()
        self.nodes = NodeArena(self.trail, self.dependencies)
        self.extensions = ExtensionStore(self.trail, self.nodes, self.dependencies)
        self.disjunctions = GroundDisjunctionStore(self.trail, self.dependencies)
        self.clashes = ClashStore(self.trail, self.dependencies)
        self.delta_rows: StableQueue[int] = StableQueue("delta", self.trail)
        self.annotated_equalities: StableQueue[int] = StableQueue("equality", self.trail)
        self.existential_candidates: StableQueue[NodeHandle] = StableQueue(
            "existential", self.trail
        )
        self.disjunction_queue: StableQueue[int] = StableQueue("disjunction", self.trail)
        self.datatype_components: StableQueue[int] = StableQueue("datatype", self.trail)
        self.blocking_invalidations: StableQueue[NodeHandle] = StableQueue("blocking", self.trail)
        self.branches: list[BranchingPoint] = []
        self.operation_root = self.trail.checkpoint("operation-root")

    @property
    def highest_branch_level(self) -> int | None:
        return None if not self.branches else self.branches[-1].level

    def begin_operation(self) -> Checkpoint:
        if self.branches:
            raise ValueError("cannot replace the operation root while branches survive")
        self.operation_root = self.trail.checkpoint("operation-root")
        return self.operation_root

    def create_node(
        self,
        kind: NodeKind,
        *,
        parent: NodeHandle | None = None,
        is_owl_named_individual: bool = False,
        source_individual_id: int | None = None,
        nominal_level: int | None = None,
        cardinality_tag: int | None = None,
    ) -> NodeHandle:
        """Create a node stamped with the current logical branch level.

        Keyword validation remains centralized in :meth:`NodeArena.create`.
        """

        checkpoint = 0 if self.highest_branch_level is None else self.highest_branch_level
        return self.nodes.create(
            kind,
            parent=parent,
            is_owl_named_individual=is_owl_named_individual,
            source_individual_id=source_individual_id,
            creation_checkpoint=checkpoint,
            nominal_level=nominal_level,
            cardinality_tag=cardinality_tag,
        )

    def push_branch(
        self,
        choice_kind: BranchChoiceKind,
        alternatives: tuple[int, ...],
        *,
        source_id: int,
        base_dependency: DependencySet,
    ) -> BranchingPoint:
        if not isinstance(choice_kind, BranchChoiceKind):
            raise TypeError("choice_kind must be BranchChoiceKind")
        choices = tuple(alternatives)
        if len(choices) < 2 or len(set(choices)) != len(choices):
            raise ValueError("a branch requires at least two unique alternatives")
        if any(isinstance(item, bool) or not isinstance(item, int) or item < 0 for item in choices):
            raise ValueError("branch alternatives must be nonnegative integer IDs")
        if isinstance(source_id, bool) or not isinstance(source_id, int) or source_id < 0:
            raise ValueError("source_id must be a nonnegative integer")
        if not isinstance(base_dependency, DependencySet):
            raise TypeError("base_dependency must be DependencySet")
        if self.clashes.current is not None:
            raise ValueError("cannot create a branch while a clash is installed")
        level = len(self.branches)
        maximum = base_dependency.maximum
        if maximum is not None and maximum >= level:
            raise ValueError("a branch base dependency must reference only earlier levels")
        branch = BranchingPoint(
            level,
            choice_kind,
            self.trail.checkpoint(f"branch-{level}"),
            choices,
            source_id,
            self.dependencies.intern(base_dependency),
        )
        self.branches.append(branch)
        return branch

    def backtrack_to(self, level: int) -> BranchingPoint:
        if isinstance(level, bool) or not isinstance(level, int):
            raise TypeError("branch level must be an integer")
        if not 0 <= level < len(self.branches):
            raise KeyError(level)
        target = self.branches[level]
        self.trail.rollback(target.checkpoint)
        del self.branches[level + 1 :]
        self._compact_dependencies()
        self.check_invariants()
        return target

    def advance_branch(
        self,
        level: int,
        learned_dependency: DependencySet,
    ) -> int | None:
        """Restore a branch checkpoint and move to its next ordered alternative."""

        if not isinstance(learned_dependency, DependencySet):
            raise TypeError("learned_dependency must be DependencySet")
        branch = self.backtrack_to(level)
        branch.learned_dependency = self.dependencies.union(
            branch.learned_dependency, learned_dependency
        )
        branch.next_alternative += 1
        if branch.next_alternative >= len(branch.alternatives):
            self.branches.pop()
            return None
        self.check_invariants()
        return branch.current

    @staticmethod
    def backjump_level(dependency: DependencySet) -> int | None:
        if not isinstance(dependency, DependencySet):
            raise TypeError("dependency must be DependencySet")
        return dependency.maximum

    def reset_to_operation_root(self, *, validate: bool = True) -> None:
        if not isinstance(validate, bool):
            raise TypeError("validate must be bool")
        self.trail.rollback(self.operation_root)
        self.branches.clear()
        if validate:
            self._compact_dependencies()
            self.check_invariants()

    def poll(self, token: CancellationToken) -> None:
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        try:
            token.check()
        except ReasoningAbortedError:
            # Cancellation latency must not scale with the whole ontology. Trail
            # rollback is exact; callers can request an explicit debug validation.
            self.reset_to_operation_root(validate=False)
            raise

    def run_with_recovery(
        self,
        token: CancellationToken,
        operation: Callable[[], ResultT],
    ) -> ResultT:
        if not callable(operation):
            raise TypeError("operation must be callable")
        try:
            token.check()
            result = operation()
            token.check()
            return result
        except ReasoningAbortedError:
            self.reset_to_operation_root(validate=False)
            raise

    def merge_nodes(
        self,
        left: NodeHandle,
        right: NodeHandle,
        dependency: DependencySet,
    ) -> NodeHandle:
        """Apply deterministic representative mechanics and rewrite affected rows."""

        if not isinstance(dependency, DependencySet):
            raise TypeError("dependency must be DependencySet")
        left_rep, left_path = self.nodes.representative(left)
        right_rep, right_path = self.nodes.representative(right)
        combined = self.dependencies.union(dependency, left_path, right_path)
        if left_rep == right_rep:
            return left_rep
        left_node = self.nodes.require_active(left_rep)
        right_node = self.nodes.require_active(right_rep)
        if left_node.sort is not right_node.sort:
            raise InternalInvariantError("cannot merge object and concrete nodes")
        target, source = self._merge_direction(left_node, right_node)
        checkpoint = self.trail.checkpoint("merge-atomic")
        try:
            self._clear_blocking_references(frozenset({source.handle}))
            self.extensions.rewrite_node(source.handle, target.handle, combined)
            self.nodes.merge(source.handle, target.handle, combined)
        except Exception:
            self.trail.rollback(checkpoint)
            raise
        return target.handle

    def prune_subtree(self, root: NodeHandle) -> tuple[NodeHandle, ...]:
        self.nodes.require_active(root)
        affected = [
            node
            for node in self.nodes.existing_nodes()
            if node.lifecycle is NodeLifecycle.ACTIVE
            and (node.handle == root or self._has_ancestor(node, root))
        ]
        affected.sort(key=lambda item: (-item.tree_depth, item.creation_id))
        handles = frozenset(node.handle for node in affected)
        checkpoint = self.trail.checkpoint("prune-atomic")
        try:
            self._clear_blocking_references(handles)
            self.extensions.deactivate_for_nodes(handles)
            for node in affected:
                self.nodes.prune(node.handle)
        except Exception:
            self.trail.rollback(checkpoint)
            raise
        return tuple(node.handle for node in affected)

    def add_ground_disjunction(
        self,
        disjunct_ids: tuple[int, ...],
        dependency: DependencySet,
    ) -> int:
        maximum = dependency.maximum
        highest = self.highest_branch_level
        if maximum is not None and (highest is None or maximum > highest):
            raise ValueError("disjunction dependency references a future branch")
        checkpoint = 0 if self.highest_branch_level is None else self.highest_branch_level
        disjunction_id = self.disjunctions.add(
            disjunct_ids,
            dependency,
            creation_checkpoint=checkpoint,
        )
        self.disjunction_queue.enqueue(disjunction_id, (disjunction_id,))
        return disjunction_id

    def take_ground_disjunction(self) -> GroundDisjunction | None:
        def valid(disjunction_id: int) -> bool:
            record = self.disjunctions.get(disjunction_id)
            return record.active and not record.processed

        disjunction_id = self.disjunction_queue.pop(valid)
        if disjunction_id is None:
            return None
        self.disjunctions.set_processed(disjunction_id)
        return self.disjunctions.get(disjunction_id)

    def deactivate_ground_disjunction(self, disjunction_id: int) -> None:
        self.disjunction_queue.discard(disjunction_id)
        self.disjunctions.set_active(disjunction_id, False)

    def install_clash(self, clash: Clash) -> bool:
        maximum = clash.dependency.maximum
        highest = self.highest_branch_level
        if maximum is not None and (highest is None or maximum > highest):
            raise ValueError("clash dependency references a future branch")
        return self.clashes.install(clash)

    def check_invariants(self) -> None:
        highest = self.highest_branch_level
        validation_level = -1 if highest is None else highest
        self.nodes.check_invariants(highest_branch_level=validation_level)
        self.extensions.check_invariants(highest_branch_level=validation_level)
        self.disjunctions.check_invariants(highest_branch_level=validation_level)
        self.clashes.check_invariants(highest_branch_level=validation_level)
        queues = (
            self.delta_rows,
            self.annotated_equalities,
            self.existential_candidates,
            self.disjunction_queue,
            self.datatype_components,
            self.blocking_invalidations,
        )
        for queue in queues:
            queue.check_invariants()
        expected_disjunctions = {
            record.disjunction_id
            for record in self.disjunctions.records()
            if record.active and not record.processed
        }
        if set(self.disjunction_queue.values()) != expected_disjunctions:
            raise InternalInvariantError(
                "ground-disjunction queue does not match active unprocessed records"
            )
        if [branch.level for branch in self.branches] != list(range(len(self.branches))):
            raise InternalInvariantError("branch levels are not contiguous")
        previous_length = self.operation_root.trail_length
        for branch in self.branches:
            if branch.checkpoint.trail_length < previous_length:
                raise InternalInvariantError("branch checkpoints are not monotonic")
            if branch.checkpoint.trail_length > self.trail.length:
                raise InternalInvariantError("branch checkpoint lies beyond the trail")
            if not 0 <= branch.next_alternative < len(branch.alternatives):
                raise InternalInvariantError("branch has no current alternative")
            maximum = branch.base_dependency.maximum
            if maximum is not None and maximum >= branch.level:
                raise InternalInvariantError("branch base dependency is not from an earlier level")
            previous_length = branch.checkpoint.trail_length

    def logical_snapshot(self) -> dict[str, object]:
        return {
            "branches": [branch.logical_dict() for branch in self.branches],
            "clash": None if self.clashes.current is None else self.clashes.current.logical_dict(),
            "delta": {
                "read_generation": self.extensions.read_generation,
                "write_generation": self.extensions.write_generation,
            },
            "disjunctions": list(self.disjunctions.logical_snapshot()),
            "facts": list(self.extensions.logical_snapshot()),
            "nodes": list(self.nodes.logical_snapshot()),
            "queues": {
                "annotated_equalities": list(self.annotated_equalities.values()),
                "blocking_invalidations": self._node_values(self.blocking_invalidations),
                "datatype_components": list(self.datatype_components.values()),
                "delta_rows": list(self.delta_rows.values()),
                "disjunctions": list(self.disjunction_queue.values()),
                "existential_candidates": self._node_values(self.existential_candidates),
            },
        }

    def canonical_snapshot(self) -> str:
        return json.dumps(
            self.logical_snapshot(),
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        )

    @staticmethod
    def _node_values(queue: StableQueue[NodeHandle]) -> list[list[int]]:
        return [[value.slot, value.generation] for value in queue.values()]

    def _merge_direction(self, left: Node, right: Node) -> tuple[Node, Node]:
        if self._has_ancestor(left, right.handle):
            return right, left
        if self._has_ancestor(right, left.handle):
            return left, right
        return (left, right) if self._merge_rank(left) <= self._merge_rank(right) else (right, left)

    @staticmethod
    def _merge_rank(node: Node) -> tuple[int, int, int]:
        if node.is_owl_named_individual:
            kind_rank = 0
        elif node.kind is NodeKind.NI:
            kind_rank = 1
        elif node.kind is NodeKind.ROOT:
            kind_rank = 2
        elif node.kind is NodeKind.TREE:
            kind_rank = 3
        else:
            kind_rank = 4
        nominal = node.nominal_level if node.nominal_level is not None else (1 << 31)
        return kind_rank, nominal, node.creation_id

    def _has_ancestor(self, node: Node, ancestor: NodeHandle) -> bool:
        parent = node.parent
        seen: set[NodeHandle] = set()
        while parent is not None:
            if parent == ancestor:
                return True
            if parent in seen:
                raise InternalInvariantError("cycle in tree parent relation")
            seen.add(parent)
            parent = self.nodes.get(parent).parent
        return False

    def _compact_dependencies(self) -> None:
        live = [*self.nodes.dependency_sets(), *self.extensions.dependency_sets()]
        live.extend(self.disjunctions.dependency_sets())
        for branch in self.branches:
            live.extend((branch.base_dependency, branch.learned_dependency))
        if self.clashes.current is not None:
            live.append(self.clashes.current.dependency)
        self.dependencies.compact(live)

    def _clear_blocking_references(self, handles: frozenset[NodeHandle]) -> None:
        for node in self.nodes.existing_nodes():
            if node.lifecycle is not NodeLifecycle.ACTIVE:
                continue
            if node.blocker in handles:
                self.nodes.set_blocked(node.handle, None, directly=False)


__all__ = ["BranchChoiceKind", "BranchingPoint", "TableauSession"]
