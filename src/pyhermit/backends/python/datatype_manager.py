"""Tableau adapter for exact datatype-component checks.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from pyhermit.backends.python.state import (
    Clash,
    ClashKind,
    DependencySet,
    NodeHandle,
    NodeLifecycle,
    NodeSort,
    TableauSession,
)
from pyhermit.clauses import ClauseProgram, PredicateKind, TermSort
from pyhermit.datatypes import (
    BackendLiteralSemanticPayload,
    DatatypeConstraintSolver,
    InequalityConstraint,
    SemanticDatatypeConstraintComponent,
    SemanticFixedValueConstraint,
    SemanticRangeConstraint,
    compile_datatype_constraint_component,
    decode_datatype_semantic_model,
    decode_literal_semantic_payload,
)
from pyhermit.events import CancellationToken


@dataclass(frozen=True, slots=True)
class DatatypeCheckResult:
    checked_components: int
    changed: bool
    clashed: bool

    def __post_init__(self) -> None:
        if (
            isinstance(self.checked_components, bool)
            or not isinstance(self.checked_components, int)
            or self.checked_components < 0
        ):
            raise ValueError("checked_components must be a nonnegative integer")
        if not isinstance(self.changed, bool) or not isinstance(self.clashed, bool):
            raise TypeError("datatype result flags must be bool")


class TableauDatatypeManager:
    """Project active concrete assertions into exact solver components."""

    __slots__ = (
        "_data_nodes",
        "_enabled",
        "_last_satisfiable_signature",
        "_model",
        "_payloads_by_identity",
        "_program",
        "_session",
        "_solver",
    )

    def __init__(
        self,
        program: ClauseProgram,
        session: TableauSession,
        *,
        data_nodes: Mapping[int, NodeHandle],
    ) -> None:
        if not isinstance(program, ClauseProgram):
            raise TypeError("program must be ClauseProgram")
        if not isinstance(session, TableauSession):
            raise TypeError("session must be TableauSession")
        selected_nodes = dict(data_nodes)
        if any(
            isinstance(identifier, bool)
            or not isinstance(identifier, int)
            or identifier < 0
            or not isinstance(handle, NodeHandle)
            for identifier, handle in selected_nodes.items()
        ):
            raise TypeError("data_nodes must map nonnegative IDs to NodeHandle values")
        self._program = program
        self._session = session
        self._data_nodes = selected_nodes
        self._enabled = program.expressivity.datatypes
        self._model = decode_datatype_semantic_model(
            program.datatype_model.semantic_payload_json.encode("utf-8")
        )
        payloads: dict[int, list[BackendLiteralSemanticPayload]] = {}
        for record in program.datatype_model.literal_identities:
            payloads.setdefault(record.data_identity_id, []).append(
                decode_literal_semantic_payload(record.semantic_payload_json.encode("utf-8"))
            )
        self._payloads_by_identity = {
            identifier: tuple(values) for identifier, values in payloads.items()
        }
        self._solver = DatatypeConstraintSolver()
        self._last_satisfiable_signature: tuple[object, ...] | None = None

    def invalidate(self) -> None:
        self._last_satisfiable_signature = None

    def check(self, token: CancellationToken) -> DatatypeCheckResult:
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        token.check()
        if not self._enabled:
            return DatatypeCheckResult(0, False, False)
        signature = self._signature()
        if signature == self._last_satisfiable_signature:
            return DatatypeCheckResult(0, False, False)
        components, participant_ids = self._components()
        checked = 0
        for component, participants in zip(components, participant_ids, strict=True):
            token.check()
            executable = compile_datatype_constraint_component(
                self._model,
                component,
                cancellation=token,
            )
            result = self._solver.solve(executable, cancellation=token)
            checked += 1
            if result.satisfiable:
                continue
            clash = result.clash
            if clash is None:
                raise RuntimeError("unsatisfiable datatype result has no clash")
            dependency = DependencySet.of(clash.dependencies)
            self._session.install_clash(
                Clash(
                    ClashKind.DATATYPE_UNSATISFIABLE,
                    dependency,
                    participants,
                )
            )
            return DatatypeCheckResult(checked, True, True)
        self._last_satisfiable_signature = signature
        return DatatypeCheckResult(checked, True, False)

    def _signature(self) -> tuple[object, ...]:
        relevant = {
            PredicateKind.DATA_RANGE,
            PredicateKind.NEGATED_DATA_RANGE,
            PredicateKind.INEQUALITY,
        }
        rows = tuple(
            (
                row.row_id,
                row.key.predicate_id,
                tuple((value.slot, value.generation) for value in row.key.arguments),
                tuple(value.bits for value in row.supports),
            )
            for row in self._session.extensions.active_rows()
            if self._program.predicates.predicate(row.key.predicate_id).kind in relevant
        )
        constrained = {
            argument
            for row in self._session.extensions.active_rows()
            if self._program.predicates.predicate(row.key.predicate_id).kind in relevant
            for argument in row.key.arguments
            if self._session.nodes.get(argument).sort is NodeSort.DATA
        }
        fixed = tuple(
            sorted(
                (
                    identifier,
                    representative.slot,
                    representative.generation,
                )
                for identifier, handle in self._data_nodes.items()
                for representative in (self._session.nodes.representative(handle)[0],)
                if representative in constrained
            )
        )
        return rows, fixed

    def _components(
        self,
    ) -> tuple[
        tuple[SemanticDatatypeConstraintComponent, ...],
        tuple[tuple[int, ...], ...],
    ]:
        handles: set[NodeHandle] = set()
        ranges: list[tuple[NodeHandle, SemanticRangeConstraint, int]] = []
        inequalities: list[tuple[NodeHandle, NodeHandle, InequalityConstraint, int]] = []
        adjacency: dict[NodeHandle, set[NodeHandle]] = {}

        for row in self._session.extensions.active_rows():
            predicate = self._program.predicates.predicate(row.key.predicate_id)
            if predicate.kind in {
                PredicateKind.DATA_RANGE,
                PredicateKind.NEGATED_DATA_RANGE,
            }:
                if len(row.key.arguments) != 1 or predicate.symbol_id is None:
                    continue
                handle = self._canonical_data(row.key.arguments[0])
                variable = self._variable(handle)
                ranges.append(
                    (
                        handle,
                        SemanticRangeConstraint(
                            variable,
                            predicate.symbol_id,
                            predicate.kind is PredicateKind.DATA_RANGE,
                            frozenset(row.minimal_dependency),
                        ),
                        row.row_id,
                    )
                )
                handles.add(handle)
                adjacency.setdefault(handle, set())
            elif (
                predicate.kind is PredicateKind.INEQUALITY
                and predicate.argument_sorts[0] is TermSort.DATA
            ):
                left = self._canonical_data(row.key.arguments[0])
                right = self._canonical_data(row.key.arguments[1])
                left_variable = self._variable(left)
                right_variable = self._variable(right)
                inequalities.append(
                    (
                        left,
                        right,
                        InequalityConstraint(
                            left_variable,
                            right_variable,
                            frozenset(row.minimal_dependency),
                        ),
                        row.row_id,
                    )
                )
                handles.update((left, right))
                adjacency.setdefault(left, set()).add(right)
                adjacency.setdefault(right, set()).add(left)

        fixed: list[tuple[NodeHandle, SemanticFixedValueConstraint]] = []
        for identity, source in sorted(self._data_nodes.items()):
            handle = self._canonical_data(source)
            if handle not in handles:
                continue
            payloads = self._payloads_by_identity.get(identity, ())
            if not payloads:
                continue
            handles.add(handle)
            adjacency.setdefault(handle, set())
            fixed.append(
                (
                    handle,
                    SemanticFixedValueConstraint(
                        self._variable(handle),
                        payloads[0],
                    ),
                )
            )

        components: list[SemanticDatatypeConstraintComponent] = []
        participant_groups: list[tuple[int, ...]] = []
        unseen = set(handles)
        while unseen:
            first = min(unseen, key=self._node_rank)
            pending = [first]
            members: set[NodeHandle] = set()
            while pending:
                current = pending.pop()
                if current in members:
                    continue
                members.add(current)
                unseen.discard(current)
                pending.extend(adjacency.get(current, set()).difference(members))
            variables = tuple(sorted(self._variable(value) for value in members))
            component_ranges = tuple(value for handle, value, _row in ranges if handle in members)
            component_fixed = tuple(value for handle, value in fixed if handle in members)
            component_inequalities = tuple(
                value
                for left, right, value, _row in inequalities
                if left in members and right in members
            )
            participants = tuple(
                sorted(
                    {row_id for handle, _value, row_id in ranges if handle in members}
                    | {
                        row_id
                        for left, right, _value, row_id in inequalities
                        if left in members and right in members
                    }
                )
            )
            components.append(
                SemanticDatatypeConstraintComponent(
                    variables,
                    ranges=component_ranges,
                    fixed_values=component_fixed,
                    inequalities=component_inequalities,
                )
            )
            participant_groups.append(participants)
        return tuple(components), tuple(participant_groups)

    def _canonical_data(self, handle: NodeHandle) -> NodeHandle:
        representative, _path = self._session.nodes.representative(handle)
        node = self._session.nodes.require_active(representative)
        if node.lifecycle is not NodeLifecycle.ACTIVE or node.sort is not NodeSort.DATA:
            raise ValueError("datatype constraints require active concrete nodes")
        return representative

    def _variable(self, handle: NodeHandle) -> int:
        return self._session.nodes.get(handle).creation_id

    def _node_rank(self, handle: NodeHandle) -> tuple[int, int, int]:
        node = self._session.nodes.get(handle)
        return node.creation_id, handle.slot, handle.generation


__all__ = ["DatatypeCheckResult", "TableauDatatypeManager"]
