"""Deterministic semi-naive join-plan compilation.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from dataclasses import dataclass

from pyhermit.clauses import ClauseProgram, DLClause, PredicateKind, Variable

_VIRTUAL_FILTERS = frozenset({PredicateKind.EQUALITY, PredicateKind.ORDERING_GUARD})
_NON_TRIGGER_KINDS = frozenset({PredicateKind.ORDERING_GUARD})


@dataclass(frozen=True, slots=True)
class JoinStep:
    body_index: int
    bound_positions: tuple[int, ...]

    def __post_init__(self) -> None:
        if (
            isinstance(self.body_index, bool)
            or not isinstance(self.body_index, int)
            or self.body_index < 0
        ):
            raise ValueError("join body index must be a nonnegative integer")
        positions = tuple(self.bound_positions)
        if positions != tuple(sorted(set(positions))):
            raise ValueError("bound positions must be sorted and unique")
        object.__setattr__(self, "bound_positions", positions)


@dataclass(frozen=True, slots=True)
class ClauseJoinPlan:
    clause_id: int
    delta_body_index: int
    steps: tuple[JoinStep, ...]

    def __post_init__(self) -> None:
        if (
            isinstance(self.clause_id, bool)
            or not isinstance(self.clause_id, int)
            or self.clause_id < 0
        ):
            raise ValueError("join clause ID must be a nonnegative integer")
        if (
            isinstance(self.delta_body_index, bool)
            or not isinstance(self.delta_body_index, int)
            or self.delta_body_index < 0
        ):
            raise ValueError("delta body index must be a nonnegative integer")
        steps = tuple(self.steps)
        indices = (self.delta_body_index, *(value.body_index for value in steps))
        if len(indices) != len(set(indices)):
            raise ValueError("join plan body indices must be unique")
        object.__setattr__(self, "steps", steps)


@dataclass(frozen=True, slots=True)
class JoinProgram:
    plans: tuple[ClauseJoinPlan, ...]
    unconditional_clause_ids: tuple[int, ...]

    def __post_init__(self) -> None:
        plans = tuple(self.plans)
        keys = tuple((value.clause_id, value.delta_body_index) for value in plans)
        if keys != tuple(sorted(set(keys))):
            raise ValueError("join plans must be uniquely sorted")
        unconditional = tuple(self.unconditional_clause_ids)
        if unconditional != tuple(sorted(set(unconditional))):
            raise ValueError("unconditional clause IDs must be sorted and unique")
        object.__setattr__(self, "plans", plans)
        object.__setattr__(self, "unconditional_clause_ids", unconditional)

    def for_predicate(
        self, program: ClauseProgram, predicate_id: int
    ) -> tuple[ClauseJoinPlan, ...]:
        return tuple(
            plan
            for plan in self.plans
            if program.clauses[plan.clause_id].body[plan.delta_body_index].predicate_id
            == predicate_id
        )


def compile_join_program(program: ClauseProgram) -> JoinProgram:
    if not isinstance(program, ClauseProgram):
        raise TypeError("program must be ClauseProgram")
    plans: list[ClauseJoinPlan] = []
    unconditional: list[int] = []
    for clause in program.clauses:
        triggers = tuple(
            index
            for index, atom in enumerate(clause.body)
            if program.predicates.predicate(atom.predicate_id).kind not in _NON_TRIGGER_KINDS
        )
        if not triggers:
            unconditional.append(clause.clause_id)
            continue
        plans.extend(_compile_clause_plan(program, clause, trigger) for trigger in triggers)
    return JoinProgram(
        tuple(sorted(plans, key=lambda value: (value.clause_id, value.delta_body_index))),
        tuple(unconditional),
    )


def _compile_clause_plan(
    program: ClauseProgram,
    clause: DLClause,
    trigger: int,
) -> ClauseJoinPlan:
    bound = {
        (argument.sort, argument.index)
        for argument in clause.body[trigger].arguments
        if isinstance(argument, Variable)
    }
    remaining = set(range(len(clause.body))) - {trigger}
    steps: list[JoinStep] = []
    join_rank = {body_index: rank for rank, body_index in enumerate(clause.join_order)}
    while remaining:

        def rank(body_index: int) -> tuple[int, int, int, int, bytes]:
            atom = clause.body[body_index]
            predicate = program.predicates.predicate(atom.predicate_id)
            variables = {
                (argument.sort, argument.index)
                for argument in atom.arguments
                if isinstance(argument, Variable)
            }
            unbound = variables - bound
            is_unready_filter = int(predicate.kind in _VIRTUAL_FILTERS and bool(unbound))
            return (
                is_unready_filter,
                -len(variables & bound),
                len(unbound),
                join_rank[body_index],
                atom.canonical_bytes(),
            )

        selected = min(remaining, key=rank)
        atom = clause.body[selected]
        positions = tuple(
            index
            for index, argument in enumerate(atom.arguments)
            if not isinstance(argument, Variable) or (argument.sort, argument.index) in bound
        )
        steps.append(JoinStep(selected, positions))
        bound.update(
            (argument.sort, argument.index)
            for argument in atom.arguments
            if isinstance(argument, Variable)
        )
        remaining.remove(selected)
    return ClauseJoinPlan(clause.clause_id, trigger, tuple(steps))


__all__ = ["ClauseJoinPlan", "JoinProgram", "JoinStep", "compile_join_program"]
