"""Indexed semi-naive and deliberately slow hyperresolution joins.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import itertools
from collections.abc import Iterable, Mapping
from typing import TypeAlias, cast

from pyhermit.backends.python.state import (
    DeltaView,
    DependencySet,
    FactRow,
    NodeHandle,
    NodeSort,
    TableauSession,
)
from pyhermit.clauses import (
    Atom,
    ClauseProgram,
    DataConstant,
    IndividualTerm,
    PredicateKind,
    TermSort,
    Variable,
)
from pyhermit.clauses.model import Term
from pyhermit.events import CancellationToken
from pyhermit.exceptions import InternalInvariantError, ResourceLimitError

from .model import JoinMatch, RuleLimits, VariableBinding
from .plans import ClauseJoinPlan

BindingKey: TypeAlias = tuple[TermSort, int]
Bindings: TypeAlias = dict[BindingKey, NodeHandle]


class IndexedJoinEvaluator:
    """Execute one compiled plan using extension-store access-pattern indexes."""

    __slots__ = (
        "_data_nodes",
        "_limits",
        "_program",
        "_session",
        "_source_nodes",
        "_steps",
        "_token",
    )

    def __init__(
        self,
        program: ClauseProgram,
        session: TableauSession,
        *,
        source_nodes: Mapping[int, NodeHandle],
        data_nodes: Mapping[int, NodeHandle],
        token: CancellationToken,
        limits: RuleLimits,
    ) -> None:
        if not isinstance(program, ClauseProgram):
            raise TypeError("program must be ClauseProgram")
        if not isinstance(session, TableauSession):
            raise TypeError("session must be TableauSession")
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        if not isinstance(limits, RuleLimits):
            raise TypeError("limits must be RuleLimits")
        self._program = program
        self._session = session
        self._source_nodes = _validate_node_map(source_nodes, "source_nodes")
        self._data_nodes = _validate_node_map(data_nodes, "data_nodes")
        self._token = token
        self._limits = limits
        self._steps = 0

    @property
    def steps(self) -> int:
        return self._steps

    def matches(self, plan: ClauseJoinPlan, delta_row: FactRow) -> tuple[JoinMatch, ...]:
        if not isinstance(plan, ClauseJoinPlan):
            raise TypeError("plan must be ClauseJoinPlan")
        if not isinstance(delta_row, FactRow):
            raise TypeError("delta_row must be FactRow")
        clause = self._program.clauses[plan.clause_id]
        trigger = clause.body[plan.delta_body_index]
        if (
            not delta_row.active
            or delta_row.derivation_generation != self._session.extensions.read_generation
            or delta_row.key.predicate_id != trigger.predicate_id
        ):
            return ()
        seeded = self._unify_handles(trigger, delta_row.key.arguments, {})
        if seeded is None:
            return ()
        bindings, seed_dependency = seeded
        found: dict[
            tuple[tuple[VariableBinding, ...], int],
            JoinMatch,
        ] = {}
        for support in delta_row.supports:
            self._join_steps(
                plan,
                0,
                bindings,
                self._session.dependencies.union(seed_dependency, support),
                (delta_row.row_id,),
                found,
            )
        return tuple(
            found[key]
            for key in sorted(
                found,
                key=lambda value: (
                    tuple(
                        (item.sort.value, item.variable_id, item.node.slot, item.node.generation)
                        for item in value[0]
                    ),
                    value[1],
                ),
            )
        )

    def _join_steps(
        self,
        plan: ClauseJoinPlan,
        step_index: int,
        bindings: Bindings,
        dependency: DependencySet,
        row_ids: tuple[int, ...],
        found: dict[tuple[tuple[VariableBinding, ...], int], JoinMatch],
    ) -> None:
        self._tick()
        if step_index == len(plan.steps):
            frozen = _freeze_bindings(bindings)
            key = frozen, dependency.bits
            candidate = JoinMatch(
                plan.clause_id,
                plan.delta_body_index,
                frozen,
                dependency,
                row_ids,
            )
            previous = found.get(key)
            if previous is None or candidate.premise_row_ids < previous.premise_row_ids:
                found[key] = candidate
            return
        clause = self._program.clauses[plan.clause_id]
        body_index = plan.steps[step_index].body_index
        atom = clause.body[body_index]
        predicate = self._program.predicates.predicate(atom.predicate_id)
        if predicate.kind is PredicateKind.ORDERING_GUARD:
            guarded = self._ordering_guard(atom, bindings)
            if guarded is not None:
                next_bindings, guard_dependency = guarded
                self._join_steps(
                    plan,
                    step_index + 1,
                    next_bindings,
                    self._session.dependencies.union(dependency, guard_dependency),
                    row_ids,
                    found,
                )
            return
        if predicate.kind is PredicateKind.EQUALITY:
            for next_bindings, equality_dependency in self._equality_candidates(atom, bindings):
                self._join_steps(
                    plan,
                    step_index + 1,
                    next_bindings,
                    self._session.dependencies.union(dependency, equality_dependency),
                    row_ids,
                    found,
                )
            return
        if predicate.kind is PredicateKind.INEQUALITY:
            candidates = self._inequality_candidates(atom, bindings, plan, body_index)
        else:
            candidates = self._relation_candidates(atom, bindings, plan, body_index)
        for row, handles, lookup_dependency in candidates:
            unified = self._unify_handles(atom, handles, bindings)
            if unified is None:
                continue
            next_bindings, unification_dependency = unified
            for support in row.supports:
                self._join_steps(
                    plan,
                    step_index + 1,
                    next_bindings,
                    self._session.dependencies.union(
                        dependency,
                        lookup_dependency,
                        unification_dependency,
                        support,
                    ),
                    (*row_ids, row.row_id),
                    found,
                )

    def _relation_candidates(
        self,
        atom: Atom,
        bindings: Bindings,
        plan: ClauseJoinPlan,
        body_index: int,
    ) -> tuple[tuple[FactRow, tuple[NodeHandle, ...], DependencySet], ...]:
        lookup, lookup_dependency = self._lookup_bindings(atom, bindings)
        rows = self._session.extensions.retrieve(
            atom.predicate_id,
            bindings=lookup,
            view=DeltaView.TOTAL,
        )
        return tuple(
            (row, row.key.arguments, lookup_dependency)
            for row in rows
            if self._in_plan_view(row, plan, body_index)
        )

    def _inequality_candidates(
        self,
        atom: Atom,
        bindings: Bindings,
        plan: ClauseJoinPlan,
        body_index: int,
    ) -> tuple[tuple[FactRow, tuple[NodeHandle, ...], DependencySet], ...]:
        resolved = tuple(self._resolved_term(argument, bindings) for argument in atom.arguments)
        dependency = self._session.dependencies.union(
            *(value[1] for value in resolved if value is not None)
        )
        row_by_id: dict[int, FactRow] = {}
        known = tuple(index for index, value in enumerate(resolved) if value is not None)
        queries: tuple[dict[int, NodeHandle], ...]
        if len(known) == 2:
            left = cast(tuple[NodeHandle, DependencySet], resolved[0])[0]
            right = cast(tuple[NodeHandle, DependencySet], resolved[1])[0]
            first, second = sorted((left, right), key=self._node_rank)
            queries = ({0: first, 1: second},)
        elif len(known) == 1:
            handle = cast(tuple[NodeHandle, DependencySet], resolved[known[0]])[0]
            queries = ({0: handle}, {1: handle})
        else:
            queries = ({},)
        for query in queries:
            for row in self._session.extensions.retrieve(
                atom.predicate_id,
                bindings=query,
                view=DeltaView.TOTAL,
            ):
                if self._in_plan_view(row, plan, body_index):
                    row_by_id[row.row_id] = row
        result: list[tuple[FactRow, tuple[NodeHandle, ...], DependencySet]] = []
        for row in (row_by_id[key] for key in sorted(row_by_id)):
            orientations = (row.key.arguments, tuple(reversed(row.key.arguments)))
            for handles in dict.fromkeys(orientations):
                if self._unify_handles(atom, handles, bindings) is not None:
                    result.append((row, handles, dependency))
        return tuple(result)

    def _equality_candidates(
        self,
        atom: Atom,
        bindings: Bindings,
    ) -> tuple[tuple[Bindings, DependencySet], ...]:
        left = self._resolved_term(atom.arguments[0], bindings)
        right = self._resolved_term(atom.arguments[1], bindings)
        if left is not None and right is not None:
            if left[0] != right[0]:
                return ()
            return ((dict(bindings), self._session.dependencies.union(left[1], right[1])),)
        if left is not None:
            bound = self._bind_unresolved(atom.arguments[1], left[0], bindings)
            return () if bound is None else ((bound, left[1]),)
        if right is not None:
            bound = self._bind_unresolved(atom.arguments[0], right[0], bindings)
            return () if bound is None else ((bound, right[1]),)
        first, second = atom.arguments
        if not isinstance(first, Variable) or not isinstance(second, Variable):
            raise InternalInvariantError("unresolved equality constants are absent from node maps")
        expected_sort = _node_sort(first.sort)
        result: list[tuple[Bindings, DependencySet]] = []
        for handle in self._session.nodes.active_handles():
            if self._session.nodes.get(handle).sort is not expected_sort:
                continue
            candidate = dict(bindings)
            candidate[(first.sort, first.index)] = handle
            candidate[(second.sort, second.index)] = handle
            result.append((candidate, self._session.dependencies.empty))
        return tuple(result)

    def _ordering_guard(
        self,
        atom: Atom,
        bindings: Bindings,
    ) -> tuple[Bindings, DependencySet] | None:
        left = self._resolved_term(atom.arguments[0], bindings)
        right = self._resolved_term(atom.arguments[1], bindings)
        if left is None or right is None:
            raise InternalInvariantError("ordering guard was scheduled before its variables bound")
        if self._node_rank(left[0]) >= self._node_rank(right[0]):
            return None
        return dict(bindings), self._session.dependencies.union(left[1], right[1])

    def _lookup_bindings(
        self,
        atom: Atom,
        bindings: Bindings,
    ) -> tuple[dict[int, NodeHandle], DependencySet]:
        result: dict[int, NodeHandle] = {}
        dependencies: list[DependencySet] = []
        for index, argument in enumerate(atom.arguments):
            resolved = self._resolved_term(argument, bindings)
            if resolved is not None:
                result[index] = resolved[0]
                dependencies.append(resolved[1])
        return result, self._session.dependencies.union(*dependencies)

    def _unify_handles(
        self,
        atom: Atom,
        handles: tuple[NodeHandle, ...],
        bindings: Bindings,
    ) -> tuple[Bindings, DependencySet] | None:
        if len(atom.arguments) != len(handles):
            return None
        result = dict(bindings)
        dependencies: list[DependencySet] = []
        for term, raw_handle in zip(atom.arguments, handles, strict=True):
            representative, path = self._session.nodes.representative(raw_handle)
            node = self._session.nodes.require_active(representative)
            if node.sort is not _node_sort(_term_sort(term)):
                return None
            dependencies.append(path)
            if isinstance(term, Variable):
                key = (term.sort, term.index)
                known = result.get(key)
                if known is not None and known != representative:
                    return None
                result[key] = representative
            else:
                expected = self._resolved_constant(term)
                dependencies.append(expected[1])
                if expected[0] != representative:
                    return None
        return result, self._session.dependencies.union(*dependencies)

    def _resolved_term(
        self,
        term: Term,
        bindings: Bindings,
    ) -> tuple[NodeHandle, DependencySet] | None:
        if isinstance(term, Variable):
            handle = bindings.get((term.sort, term.index))
            if handle is None:
                return None
            representative, dependency = self._session.nodes.representative(handle)
            self._session.nodes.require_active(representative)
            return representative, dependency
        return self._resolved_constant(term)

    def _resolved_constant(
        self,
        term: IndividualTerm | DataConstant,
    ) -> tuple[NodeHandle, DependencySet]:
        if isinstance(term, IndividualTerm):
            handle = self._source_nodes.get(term.individual_id)
            name = f"individual ID {term.individual_id}"
        else:
            handle = self._data_nodes.get(term.data_identity_id)
            name = f"data identity ID {term.data_identity_id}"
        if handle is None:
            raise InternalInvariantError(f"compiled {name} has no tableau node")
        representative, dependency = self._session.nodes.representative(handle)
        node = self._session.nodes.require_active(representative)
        if node.sort is not _node_sort(_term_sort(term)):
            raise InternalInvariantError(f"compiled {name} maps to the wrong node sort")
        return representative, dependency

    def _bind_unresolved(
        self,
        term: Term,
        handle: NodeHandle,
        bindings: Bindings,
    ) -> Bindings | None:
        if not isinstance(term, Variable):
            return None
        node = self._session.nodes.require_active(handle)
        if node.sort is not _node_sort(term.sort):
            return None
        result = dict(bindings)
        result[(term.sort, term.index)] = handle
        return result

    def _in_plan_view(
        self,
        row: FactRow,
        plan: ClauseJoinPlan,
        body_index: int,
    ) -> bool:
        generation = self._session.extensions.read_generation
        if body_index < plan.delta_body_index:
            return row.derivation_generation < generation
        return row.derivation_generation <= generation

    def _node_rank(self, handle: NodeHandle) -> tuple[int, int, int]:
        node = self._session.nodes.get(handle)
        return node.creation_id, handle.slot, handle.generation

    def _tick(self) -> None:
        self._steps += 1
        if self._steps > self._limits.max_join_steps:
            raise ResourceLimitError(
                "hyperresolution join-step limit exceeded",
                limit="max_join_steps",
                observed=self._steps,
                allowed=self._limits.max_join_steps,
            )
        if self._steps % self._limits.cancellation_interval == 0:
            self._token.add_work(self._limits.cancellation_interval)
            self._token.check()


class NaiveJoinEvaluator:
    """Slow substitution oracle independent of join plans and indexes."""

    __slots__ = ("_indexed", "_program", "_session")

    def __init__(self, indexed: IndexedJoinEvaluator) -> None:
        if not isinstance(indexed, IndexedJoinEvaluator):
            raise TypeError("indexed must be IndexedJoinEvaluator")
        self._indexed = indexed
        self._program = indexed._program
        self._session = indexed._session

    def matches(self, clause_id: int, *, require_new: bool = True) -> tuple[JoinMatch, ...]:
        clause = self._program.clauses[clause_id]
        variables = sorted(
            {
                (argument.sort, argument.index)
                for atom in clause.body
                for argument in atom.arguments
                if isinstance(argument, Variable)
            },
            key=lambda value: (value[0].value, value[1]),
        )
        domains: list[tuple[NodeHandle, ...]] = []
        for sort, _identifier in variables:
            domains.append(
                tuple(
                    handle
                    for handle in self._session.nodes.active_handles()
                    if self._session.nodes.get(handle).sort is _node_sort(sort)
                )
            )
        found: dict[tuple[tuple[VariableBinding, ...], int], JoinMatch] = {}
        for assignment in itertools.product(*domains):
            bindings = dict(zip(variables, assignment, strict=True))
            rows_by_atom: list[tuple[FactRow | None, ...]] = []
            virtual_dependencies: list[DependencySet] = []
            rejected = False
            for atom in clause.body:
                predicate = self._program.predicates.predicate(atom.predicate_id)
                if predicate.kind is PredicateKind.ORDERING_GUARD:
                    guarded = self._indexed._ordering_guard(atom, bindings)
                    if guarded is None:
                        rejected = True
                        break
                    virtual_dependencies.append(guarded[1])
                    rows_by_atom.append((None,))
                    continue
                if predicate.kind is PredicateKind.EQUALITY:
                    equality = self._indexed._equality_candidates(atom, bindings)
                    if not equality:
                        rejected = True
                        break
                    virtual_dependencies.append(equality[0][1])
                    rows_by_atom.append((None,))
                    continue
                matching = tuple(
                    row
                    for row in self._session.extensions.active_rows()
                    if row.key.predicate_id == atom.predicate_id
                    and self._row_satisfies(atom, row, bindings)
                )
                if not matching:
                    rejected = True
                    break
                rows_by_atom.append(matching)
            if rejected:
                continue
            for selected in itertools.product(*rows_by_atom):
                rows = tuple(row for row in selected if row is not None)
                if require_new and not any(
                    row.derivation_generation == self._session.extensions.read_generation
                    for row in rows
                ):
                    continue
                support_domains = tuple(row.supports for row in rows)
                for supports in itertools.product(*support_domains):
                    dependency = self._session.dependencies.union(
                        *virtual_dependencies,
                        *supports,
                    )
                    frozen = _freeze_bindings(bindings)
                    key = frozen, dependency.bits
                    candidate = JoinMatch(
                        clause.clause_id,
                        0,
                        frozen,
                        dependency,
                        tuple(row.row_id for row in rows),
                    )
                    previous = found.get(key)
                    if previous is None or candidate.premise_row_ids < previous.premise_row_ids:
                        found[key] = candidate
        return tuple(found[key] for key in sorted(found, key=lambda value: (value[0], value[1])))

    def _row_satisfies(self, atom: Atom, row: FactRow, bindings: Bindings) -> bool:
        if self._program.predicates.predicate(atom.predicate_id).kind is PredicateKind.INEQUALITY:
            orientations: Iterable[tuple[NodeHandle, ...]] = (
                row.key.arguments,
                tuple(reversed(row.key.arguments)),
            )
        else:
            orientations = (row.key.arguments,)
        return any(
            self._indexed._unify_handles(atom, handles, bindings) is not None
            for handles in orientations
        )


def _validate_node_map(
    values: Mapping[int, NodeHandle],
    name: str,
) -> dict[int, NodeHandle]:
    result = dict(values)
    if any(
        isinstance(identifier, bool)
        or not isinstance(identifier, int)
        or identifier < 0
        or not isinstance(handle, NodeHandle)
        for identifier, handle in result.items()
    ):
        raise TypeError(f"{name} must map nonnegative integer IDs to NodeHandle values")
    return result


def _freeze_bindings(bindings: Bindings) -> tuple[VariableBinding, ...]:
    return tuple(
        VariableBinding(sort, identifier, handle)
        for (sort, identifier), handle in sorted(
            bindings.items(),
            key=lambda value: (value[0][0].value, value[0][1]),
        )
    )


def _term_sort(term: Term) -> TermSort:
    if isinstance(term, Variable):
        return term.sort
    if isinstance(term, IndividualTerm):
        return TermSort.OBJECT
    return TermSort.DATA


def _node_sort(sort: TermSort) -> NodeSort:
    return NodeSort.OBJECT if sort is TermSort.OBJECT else NodeSort.DATA


__all__ = ["IndexedJoinEvaluator", "NaiveJoinEvaluator"]
