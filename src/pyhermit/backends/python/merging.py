"""Dependency-exact node merging above the rollback-safe tableau substrate.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from pyhermit.backends.python.rules import GroundRuleAtom
from pyhermit.backends.python.state import (
    Clash,
    ClashKind,
    DependencySet,
    Node,
    NodeHandle,
    NodeKind,
    NodeLifecycle,
    NodeSort,
    TableauSession,
)
from pyhermit.backends.python.state.extensions import FactRow
from pyhermit.clauses import ClauseProgram, PredicateKind, TermSort
from pyhermit.events import CancellationToken
from pyhermit.exceptions import InternalInvariantError


class MergeRuleAccess(Protocol):
    @property
    def program(self) -> ClauseProgram: ...

    def dispatch_ground_atom(
        self,
        atom: GroundRuleAtom,
        dependency: DependencySet,
        *,
        core: bool = False,
        provenance_ids: tuple[int, ...] = (),
    ) -> bool: ...


@dataclass(frozen=True, slots=True)
class MergeResult:
    representative: NodeHandle
    merged: NodeHandle | None
    pruned: tuple[NodeHandle, ...] = ()
    clashed: bool = False


class MergingManager:
    """Apply one equality with HermiT-compatible orientation and rescheduling."""

    __slots__ = ("_access", "_inequality_by_sort", "_session")

    def __init__(self, session: TableauSession, access: MergeRuleAccess) -> None:
        if not isinstance(session, TableauSession):
            raise TypeError("session must be TableauSession")
        self._session = session
        self._access = access
        self._inequality_by_sort = {
            predicate.argument_sorts[0]: predicate.predicate_id
            for predicate in access.program.predicates.predicates
            if predicate.kind is PredicateKind.INEQUALITY
        }

    def merge(
        self,
        left: NodeHandle,
        right: NodeHandle,
        dependency: DependencySet,
        token: CancellationToken,
    ) -> MergeResult:
        if not isinstance(left, NodeHandle) or not isinstance(right, NodeHandle):
            raise TypeError("merge arguments must be NodeHandle values")
        if not isinstance(dependency, DependencySet):
            raise TypeError("dependency must be DependencySet")
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        return self._session.run_with_recovery(
            token,
            lambda: self._merge(left, right, dependency, token),
        )

    def _merge(
        self,
        left: NodeHandle,
        right: NodeHandle,
        dependency: DependencySet,
        token: CancellationToken,
    ) -> MergeResult:
        token.check()
        left_rep, left_path = self._session.nodes.representative(left)
        right_rep, right_path = self._session.nodes.representative(right)
        support = self._session.dependencies.union(dependency, left_path, right_path)
        if left_rep == right_rep:
            return MergeResult(left_rep, None)
        left_node = self._session.nodes.require_active(left_rep)
        right_node = self._session.nodes.require_active(right_rep)
        if left_node.sort is not right_node.sort:
            raise InternalInvariantError("cannot merge object and concrete nodes")
        inequality_rows = self._inequality_rows(left_node.sort, left_rep, right_rep)
        if inequality_rows:
            inequality_support = min(
                (item for row in inequality_rows for item in row.supports),
                key=_dependency_rank,
            )
            clash_dependency = self._session.dependencies.union(support, inequality_support)
            self._session.install_clash(
                Clash(
                    ClashKind.EQUALITY_INEQUALITY,
                    clash_dependency,
                    tuple(row.row_id for row in inequality_rows),
                )
            )
            return MergeResult(left_rep, None, clashed=True)

        target, source = self._orientation(left_node, right_node)
        pruned: list[NodeHandle] = []
        direct_children = sorted(
            (
                node
                for node in self._session.nodes.existing_nodes()
                if node.lifecycle is NodeLifecycle.ACTIVE and node.parent == source.handle
            ),
            key=lambda value: value.creation_id,
        )
        for child in direct_children:
            token.check()
            pruned.extend(self._session.prune_subtree(child.handle))

        pending = tuple(sorted(source.unprocessed_existentials))
        for existential_id in pending:
            self._session.nodes.mark_existential(
                target.handle,
                existential_id,
                pending=True,
            )
        representative = self._session.merge_nodes(source.handle, target.handle, support)
        if representative != target.handle:
            raise InternalInvariantError("tableau merge orientation changed unexpectedly")

        if self._session.nodes.get(target.handle).unprocessed_existentials:
            self._session.existential_candidates.enqueue(
                target.handle,
                (target.creation_id, target.handle.slot, target.handle.generation),
            )
        self._session.blocking_invalidations.enqueue(
            target.handle,
            (target.creation_id, target.handle.slot, target.handle.generation),
        )

        # State-level rewriting preserves rows/supports/core/provenance. Re-dispatching
        # only rows incident on the survivor performs semantic clash checks and queues
        # work that a plain extension-table copy deliberately does not own.
        for row in self._session.extensions.rows_for_node(target.handle):
            token.check()
            atom = GroundRuleAtom(row.key.predicate_id, row.key.arguments)
            for row_support in row.supports:
                self._access.dispatch_ground_atom(
                    atom,
                    row_support,
                    core=row.core,
                    provenance_ids=row.provenance_ids,
                )
                if self._session.clashes.current is not None:
                    break
            if self._session.clashes.current is not None:
                break
        token.check()
        return MergeResult(
            representative,
            source.handle,
            tuple(pruned),
            self._session.clashes.current is not None,
        )

    def _inequality_rows(
        self,
        sort: NodeSort,
        left: NodeHandle,
        right: NodeHandle,
    ) -> tuple[FactRow, ...]:
        term_sort = TermSort.OBJECT if sort is NodeSort.OBJECT else TermSort.DATA
        predicate_id = self._inequality_by_sort.get(term_sort)
        if predicate_id is None:
            return ()
        first, second = sorted((left, right), key=self._node_rank)
        return tuple(
            self._session.extensions.retrieve(
                predicate_id,
                bindings={0: first, 1: second},
            )
        )

    def _orientation(self, left: Node, right: Node) -> tuple[Node, Node]:
        if self._has_ancestor(left, right.handle):
            return right, left
        if self._has_ancestor(right, left.handle):
            return left, right
        return (left, right) if self._merge_rank(left) <= self._merge_rank(right) else (right, left)

    def _has_ancestor(self, node: Node, ancestor: NodeHandle) -> bool:
        parent = node.parent
        seen: set[NodeHandle] = set()
        while parent is not None:
            if parent == ancestor:
                return True
            if parent in seen:
                raise InternalInvariantError("cycle in tree parent relation")
            seen.add(parent)
            parent = self._session.nodes.get(parent).parent
        return False

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

    def _node_rank(self, handle: NodeHandle) -> tuple[int, int, int]:
        node = self._session.nodes.get(handle)
        return node.creation_id, handle.slot, handle.generation


def _dependency_rank(value: DependencySet) -> tuple[int, int, int]:
    maximum = value.maximum
    return len(value), -1 if maximum is None else maximum, value.bits


__all__ = ["MergeResult", "MergeRuleAccess", "MergingManager"]
