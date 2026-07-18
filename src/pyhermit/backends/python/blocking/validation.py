# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Validated/core blocking and compiled-clause validation.

SPDX-License-Identifier: LGPL-3.0-or-later

The concrete validator is a Python-native port of the pinned validator's two checks:
constraints at the blocked node after copying its blocker, and constraints at the
blocked node's parent after mirroring blocked successors.  It consumes only immutable
compiled clauses and the shared tableau state, so no scheduler or Java object is needed.
"""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Protocol, TypeAlias, runtime_checkable

from pyhermit.backends.python.state import (
    FactRow,
    NodeHandle,
    NodeKind,
    NodeLifecycle,
    TableauSession,
)
from pyhermit.clauses import (
    Atom,
    ClauseProgram,
    DLClause,
    Predicate,
    PredicateKind,
    TermSort,
    Variable,
)
from pyhermit.events import CancellationToken
from pyhermit.exceptions import InternalInvariantError, ResourceLimitError

from .signatures import BlockingSignature, DirectCheckerKind
from .strategy import CoreBlockingMode

_CONCEPT_KINDS = frozenset(
    {
        PredicateKind.CONCEPT,
        PredicateKind.NEGATED_CONCEPT,
        PredicateKind.NOMINAL,
        PredicateKind.NEGATED_NOMINAL,
        PredicateKind.AUTOMATON_STATE,
        PredicateKind.DISJOINT_GUARD,
        PredicateKind.NAMED_INDIVIDUAL,
    }
)
Binding: TypeAlias = dict[Variable, NodeHandle]


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
    """Narrow boundary accepted by :class:`BlockingManager`."""

    def validate_block(
        self,
        session: TableauSession,
        blocked: NodeHandle,
        blocker: NodeHandle,
        signature: BlockingSignature,
    ) -> ValidationDecision: ...


@runtime_checkable
class CancellableBlockingValidator(Protocol):
    """Optional extension for validators that poll inside long clause joins."""

    def validate_block_cancellable(
        self,
        session: TableauSession,
        blocked: NodeHandle,
        blocker: NodeHandle,
        signature: BlockingSignature,
        token: CancellationToken,
    ) -> ValidationDecision: ...


@runtime_checkable
class PassAwareBlockingValidator(Protocol):
    """Optional extension for sharing an immutable snapshot across one pass.

    The manager brackets a validation pass with these methods.  Implementations must
    treat the session as read-only until :meth:`end_validation_pass` is called.
    """

    def begin_validation_pass(
        self,
        session: TableauSession,
        state_digest: str,
        token: CancellationToken,
    ) -> None: ...

    def end_validation_pass(self) -> None: ...


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


@dataclass(frozen=True, slots=True)
class ValidationLimits:
    """Explicit work and cancellation-poll bounds for one direct block."""

    max_matches_per_block: int = 1_000_000
    cancellation_poll_interval: int = 256

    def __post_init__(self) -> None:
        for name in ("max_matches_per_block", "cancellation_poll_interval"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
                raise ValueError(f"{name} must be a positive integer")


@dataclass(frozen=True, slots=True)
class _ClauseShape:
    clause: DLClause
    x: Variable
    y_variables: tuple[Variable, ...]
    z_variables: tuple[Variable, ...]


@dataclass(frozen=True, slots=True)
class _Snapshot:
    rows: tuple[FactRow, ...]
    by_key: Mapping[tuple[int, tuple[NodeHandle, ...]], FactRow]
    by_predicate: Mapping[int, tuple[FactRow, ...]]
    object_nodes: tuple[NodeHandle, ...]
    mirrors: Mapping[NodeHandle, NodeHandle]

    @classmethod
    def from_session(cls, session: TableauSession) -> _Snapshot:
        rows = tuple(
            sorted(
                session.extensions.active_rows(),
                key=lambda row: (row.key.predicate_id, row.key.arguments),
            )
        )
        by_predicate: dict[int, list[FactRow]] = {}
        for row in rows:
            by_predicate.setdefault(row.key.predicate_id, []).append(row)
        active_nodes = tuple(
            node
            for node in sorted(
                session.nodes.existing_nodes(),
                key=lambda value: value.creation_id,
            )
            if node.lifecycle is NodeLifecycle.ACTIVE
        )
        nodes = tuple(node.handle for node in active_nodes if node.kind is not NodeKind.CONCRETE)
        return cls(
            rows,
            MappingProxyType({(row.key.predicate_id, row.key.arguments): row for row in rows}),
            MappingProxyType({key: tuple(values) for key, values in by_predicate.items()}),
            nodes,
            MappingProxyType(
                {
                    node.handle: node.handle if node.blocker is None else node.blocker
                    for node in active_nodes
                }
            ),
        )

    def contains(self, predicate_id: int, arguments: tuple[NodeHandle, ...]) -> bool:
        return (predicate_id, arguments) in self.by_key


@dataclass(frozen=True, slots=True)
class _MatchContext:
    shape: _ClauseShape
    blocked: NodeHandle | None = None
    distinguished_y: Variable | None = None
    mirror_y: bool = False


class _Budget:
    __slots__ = ("_limits", "_steps", "_token")

    def __init__(
        self,
        limits: ValidationLimits,
        token: CancellationToken | None,
    ) -> None:
        self._limits = limits
        self._token = token
        self._steps = 0

    def step(self) -> None:
        self._steps += 1
        if self._steps > self._limits.max_matches_per_block:
            raise ResourceLimitError(
                "blocking validation match limit exceeded",
                limit="blocking_validation_matches",
                observed=self._steps,
                allowed=self._limits.max_matches_per_block,
            )
        if self._token is not None and self._steps % self._limits.cancellation_poll_interval == 0:
            self._token.check()


class CompiledClauseBlockingValidator:
    """Validate provisional core blocks directly against :class:`ClauseProgram`.

    Unsupported non-HT clause shapes conservatively reject provisional blocks.  This
    can only expose more expansion; it can never turn an invalid block into SAT.
    """

    __slots__ = (
        "_concept_predicates",
        "_limits",
        "_object_roles_by_role_id",
        "_prepared_digest",
        "_prepared_session",
        "_prepared_snapshot",
        "_shapes",
        "_unsupported_clause_ids",
        "core_mode",
        "program",
    )

    def __init__(
        self,
        program: ClauseProgram,
        *,
        core_mode: CoreBlockingMode,
        limits: ValidationLimits | None = None,
    ) -> None:
        if not isinstance(program, ClauseProgram):
            raise TypeError("program must be ClauseProgram")
        if not isinstance(core_mode, CoreBlockingMode):
            raise TypeError("core_mode must be CoreBlockingMode")
        if core_mode is CoreBlockingMode.NONE:
            raise ValueError("compiled blocking validation requires a core mode")
        if limits is not None and not isinstance(limits, ValidationLimits):
            raise TypeError("limits must be ValidationLimits or None")
        self.program = program
        self.core_mode = core_mode
        self._limits = limits or ValidationLimits()
        self._prepared_digest: str | None = None
        self._prepared_session: TableauSession | None = None
        self._prepared_snapshot: _Snapshot | None = None
        self._concept_predicates = frozenset(
            predicate.predicate_id
            for predicate in program.predicates.predicates
            if predicate.kind in _CONCEPT_KINDS
        )
        roles: dict[int, list[int]] = {}
        for predicate in program.predicates.predicates:
            if predicate.kind is PredicateKind.OBJECT_ROLE:
                if predicate.role_id is None:
                    raise InternalInvariantError("object-role predicate has no role ID")
                roles.setdefault(predicate.role_id, []).append(predicate.predicate_id)
        self._object_roles_by_role_id = MappingProxyType(
            {key: tuple(sorted(values)) for key, values in roles.items()}
        )
        shapes: list[_ClauseShape] = []
        unsupported: list[int] = []
        for clause in program.clauses:
            outcome = self._shape(clause)
            if outcome is False:
                unsupported.append(clause.clause_id)
            elif isinstance(outcome, _ClauseShape):
                shapes.append(outcome)
        self._shapes = tuple(shapes)
        self._unsupported_clause_ids = tuple(sorted(unsupported))

    @property
    def unsupported_clause_ids(self) -> tuple[int, ...]:
        return self._unsupported_clause_ids

    def begin_validation_pass(
        self,
        session: TableauSession,
        state_digest: str,
        token: CancellationToken,
    ) -> None:
        """Build the expensive fact index once for a manager validation pass."""

        if not isinstance(session, TableauSession):
            raise TypeError("session must be TableauSession")
        if not isinstance(state_digest, str) or not state_digest:
            raise ValueError("state_digest must be a nonempty string")
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        if self._prepared_snapshot is not None:
            raise InternalInvariantError("blocking validator already has an active pass")
        token.check()
        snapshot = _Snapshot.from_session(session)
        token.check()
        self._prepared_session = session
        self._prepared_digest = state_digest
        self._prepared_snapshot = snapshot

    def end_validation_pass(self) -> None:
        """Release pass-local indexes, including after cancellation or failure."""

        self._prepared_snapshot = None
        self._prepared_session = None
        self._prepared_digest = None

    def validate_block(
        self,
        session: TableauSession,
        blocked: NodeHandle,
        blocker: NodeHandle,
        signature: BlockingSignature,
        *,
        token: CancellationToken | None = None,
    ) -> ValidationDecision:
        return self._validate_block(session, blocked, blocker, signature, token)

    def validate_block_cancellable(
        self,
        session: TableauSession,
        blocked: NodeHandle,
        blocker: NodeHandle,
        signature: BlockingSignature,
        token: CancellationToken,
    ) -> ValidationDecision:
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        return self._validate_block(session, blocked, blocker, signature, token)

    def _validate_block(
        self,
        session: TableauSession,
        blocked: NodeHandle,
        blocker: NodeHandle,
        signature: BlockingSignature,
        token: CancellationToken | None,
    ) -> ValidationDecision:
        if not isinstance(session, TableauSession):
            raise TypeError("session must be TableauSession")
        if not isinstance(blocked, NodeHandle) or not isinstance(blocker, NodeHandle):
            raise TypeError("blocked and blocker must be NodeHandle values")
        if not isinstance(signature, BlockingSignature):
            raise TypeError("signature must be BlockingSignature")
        if signature.kind not in {
            DirectCheckerKind.VALIDATED_SINGLE,
            DirectCheckerKind.VALIDATED_PAIRWISE,
        }:
            raise ValueError("compiled validation requires a validated signature")
        if token is not None and not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken or None")
        blocked_node = session.nodes.require_active(blocked)
        session.nodes.require_active(blocker)
        if not blocked_node.directly_blocked or blocked_node.blocker != blocker:
            raise ValueError("blocked must be directly blocked by blocker")
        if token is not None:
            token.check()
        snapshot = self._prepared_snapshot
        if snapshot is not None:
            if self._prepared_session is not session or self._prepared_digest is None:
                raise InternalInvariantError(
                    "blocking validator pass belongs to a different tableau session"
                )
        else:
            snapshot = _Snapshot.from_session(session)
        budget = _Budget(self._limits, token)
        violation = self._first_violation(session, snapshot, blocked, blocker, budget)
        if violation is None and self._unsupported_clause_ids:
            violation = self._unsupported_clause_ids[0]
        if violation is None:
            return ValidationDecision(True)
        repair_rows = self._repair_rows(session, snapshot, blocked, blocker)
        return ValidationDecision(False, repair_rows, (blocked,), (violation,))

    def _shape(self, clause: DLClause) -> _ClauseShape | bool | None:
        predicates = tuple(
            self.program.predicates.predicate(atom.predicate_id)
            for atom in clause.body + clause.head
        )
        if not any(
            predicate.kind in _CONCEPT_KINDS
            or predicate.kind
            in {
                PredicateKind.AT_LEAST_OBJECT,
                PredicateKind.ANNOTATED_EQUALITY,
            }
            for predicate in predicates
        ):
            return None
        x = Variable(0, TermSort.OBJECT)
        variables: set[Variable] = set()
        y_variables: set[Variable] = set()
        unsupported_term = False
        for atom in clause.body + clause.head:
            for argument in atom.arguments:
                if not isinstance(argument, Variable):
                    unsupported_term = True
                else:
                    variables.add(argument)
        if x not in variables:
            return None
        if unsupported_term or any(variable.sort is not TermSort.OBJECT for variable in variables):
            return False
        for atom in clause.body:
            predicate = self.program.predicates.predicate(atom.predicate_id)
            if predicate.kind in _CONCEPT_KINDS:
                if len(atom.arguments) != 1:
                    return False
                continue
            if predicate.kind is not PredicateKind.OBJECT_ROLE or len(atom.arguments) != 2:
                return False
            left, right = atom.arguments
            if not isinstance(left, Variable) or not isinstance(right, Variable):
                return False
            if left != x and right != x:
                return False
            if left != x:
                y_variables.add(left)
            if right != x:
                y_variables.add(right)
        for atom in clause.head:
            predicate = self.program.predicates.predicate(atom.predicate_id)
            if any(
                not isinstance(argument, Variable) or argument.sort is not TermSort.OBJECT
                for argument in atom.arguments
            ):
                return False
            if predicate.kind in {
                PredicateKind.DATA_ROLE,
                PredicateKind.NEGATED_DATA_ROLE,
                PredicateKind.DATA_RANGE,
                PredicateKind.NEGATED_DATA_RANGE,
                PredicateKind.AT_LEAST_DATA,
            }:
                return False
        z_variables = variables - y_variables - {x}
        if not y_variables and not z_variables:
            return None
        return _ClauseShape(
            clause,
            x,
            tuple(sorted(y_variables, key=lambda value: value.index)),
            tuple(sorted(z_variables, key=lambda value: value.index)),
        )

    def _first_violation(
        self,
        session: TableauSession,
        snapshot: _Snapshot,
        blocked: NodeHandle,
        blocker: NodeHandle,
        budget: _Budget,
    ) -> int | None:
        blocked_node = session.nodes.require_active(blocked)
        blocker_node = session.nodes.require_active(blocker)
        parent = blocked_node.parent
        blocker_parent = blocker_node.parent
        if parent is None:
            raise InternalInvariantError("directly blocked tree node has no parent")
        parent_at_least = self._parent_at_least_violation(
            session, snapshot, parent, blocked, budget
        )
        if parent_at_least is not None:
            return parent_at_least
        for shape in self._shapes:
            if self._parent_clause_invalidates(
                session,
                snapshot,
                shape,
                parent,
                blocked,
                budget,
            ):
                return shape.clause.clause_id
        if blocker_parent is not None:
            blocked_at_least = self._blocked_at_least_violation(
                session,
                snapshot,
                blocked,
                blocker,
                parent,
                blocker_parent,
                budget,
            )
            if blocked_at_least is not None:
                return blocked_at_least
        for shape in self._shapes:
            if self._blocked_clause_violation(
                session,
                snapshot,
                shape,
                blocked,
                blocker,
                parent,
                blocker_parent,
                budget,
            ):
                return shape.clause.clause_id
        return None

    def _blocked_clause_violation(
        self,
        session: TableauSession,
        snapshot: _Snapshot,
        shape: _ClauseShape,
        blocked: NodeHandle,
        blocker: NodeHandle,
        parent: NodeHandle,
        blocker_parent: NodeHandle | None,
        budget: _Budget,
    ) -> bool:
        del session
        for distinguished in shape.y_variables:
            context = _MatchContext(shape, blocked, distinguished, False)
            fixed: Binding = {shape.x: blocker, distinguished: parent}
            for binding in self._matches(snapshot, fixed, context, budget):
                if blocker_parent is not None and any(
                    binding.get(variable) == blocker_parent
                    for variable in shape.y_variables
                    if variable != distinguished
                ):
                    continue
                if not self._head_satisfied(snapshot, binding, context):
                    return True
        return False

    def _parent_clause_invalidates(
        self,
        session: TableauSession,
        snapshot: _Snapshot,
        shape: _ClauseShape,
        parent: NodeHandle,
        target: NodeHandle,
        budget: _Budget,
    ) -> bool:
        context = _MatchContext(shape, mirror_y=True)
        for binding in self._matches(snapshot, {shape.x: parent}, context, budget):
            blocked_values = tuple(
                (variable, value)
                for variable in shape.y_variables
                if (value := binding.get(variable)) is not None and self._is_blocked(session, value)
            )
            if not blocked_values or self._head_satisfied(snapshot, binding, context):
                continue
            implicated: list[tuple[int, int, NodeHandle]] = []
            for atom in shape.clause.body:
                predicate = self.program.predicates.predicate(atom.predicate_id)
                if predicate.kind not in _CONCEPT_KINDS:
                    continue
                variable = atom.arguments[0]
                if not isinstance(variable, Variable) or variable not in shape.y_variables:
                    continue
                node = binding[variable]
                blocker = self._mirror(session, node)
                if (
                    blocker != node
                    and snapshot.contains(atom.predicate_id, (blocker,))
                    and not snapshot.contains(atom.predicate_id, (node,))
                ):
                    implicated.append((-variable.index, self._creation_id(session, node), node))
            for atom in shape.clause.head:
                predicate = self.program.predicates.predicate(atom.predicate_id)
                if predicate.kind not in _CONCEPT_KINDS:
                    continue
                variable = atom.arguments[0]
                if not isinstance(variable, Variable) or variable not in shape.y_variables:
                    continue
                node = binding[variable]
                blocker = self._mirror(session, node)
                if (
                    blocker != node
                    and snapshot.contains(atom.predicate_id, (node,))
                    and not snapshot.contains(atom.predicate_id, (blocker,))
                ):
                    implicated.append((-variable.index, self._creation_id(session, node), node))
            if not implicated:
                implicated = [
                    (-variable.index, self._creation_id(session, node), node)
                    for variable, node in blocked_values
                ]
            if min(implicated)[2] == target:
                return True
        return False

    def _matches(
        self,
        snapshot: _Snapshot,
        fixed: Mapping[Variable, NodeHandle],
        context: _MatchContext,
        budget: _Budget,
    ) -> Iterator[Binding]:
        binding = dict(fixed)
        body = context.shape.clause.body
        order = context.shape.clause.join_order or tuple(range(len(body)))

        def visit(position: int) -> Iterator[Binding]:
            if position == len(order):
                yield dict(binding)
                return
            atom = body[order[position]]
            predicate = self.program.predicates.predicate(atom.predicate_id)
            if predicate.kind in _CONCEPT_KINDS:
                variable = atom.arguments[0]
                if not isinstance(variable, Variable):
                    return
                existing = binding.get(variable)
                candidates = snapshot.object_nodes if existing is None else (existing,)
                for candidate in candidates:
                    budget.step()
                    binding[variable] = candidate
                    if self._atom_true(snapshot, atom, binding, context, body=True):
                        yield from visit(position + 1)
                    if existing is None:
                        binding.pop(variable, None)
                return
            rows = snapshot.by_predicate.get(atom.predicate_id, ())
            if (
                context.blocked is not None
                and context.distinguished_y is not None
                and context.shape.x in atom.arguments
                and context.distinguished_y in atom.arguments
            ):
                budget.step()
                if self._atom_true(snapshot, atom, binding, context, body=True):
                    yield from visit(position + 1)
                return
            for row in rows:
                budget.step()
                added: list[Variable] = []
                compatible = True
                for term, value in zip(atom.arguments, row.key.arguments, strict=True):
                    if not isinstance(term, Variable):
                        compatible = False
                        break
                    known = binding.get(term)
                    if known is None:
                        binding[term] = value
                        added.append(term)
                    elif known != value:
                        compatible = False
                        break
                if compatible and self._atom_true(snapshot, atom, binding, context, body=True):
                    yield from visit(position + 1)
                for variable in added:
                    binding.pop(variable, None)

        yield from visit(0)

    def _head_satisfied(
        self,
        snapshot: _Snapshot,
        binding: Mapping[Variable, NodeHandle],
        context: _MatchContext,
    ) -> bool:
        return any(
            self._atom_true(snapshot, atom, binding, context, body=False)
            for atom in context.shape.clause.head
        )

    def _atom_true(
        self,
        snapshot: _Snapshot,
        atom: Atom,
        binding: Mapping[Variable, NodeHandle],
        context: _MatchContext,
        *,
        body: bool,
    ) -> bool:
        predicate = self.program.predicates.predicate(atom.predicate_id)
        arguments: list[NodeHandle] = []
        for term in atom.arguments:
            if not isinstance(term, Variable):
                return False
            value = binding.get(term)
            if value is None:
                return False
            if (
                predicate.kind in _CONCEPT_KINDS
                and context.mirror_y
                and term in context.shape.y_variables
            ):
                value = self._mirror_from_snapshot(snapshot, value)
            arguments.append(value)
        if (
            predicate.kind is PredicateKind.OBJECT_ROLE
            and context.blocked is not None
            and context.distinguished_y is not None
        ):
            for index, term in enumerate(atom.arguments):
                if term == context.shape.x and context.distinguished_y in atom.arguments:
                    arguments[index] = context.blocked
        if predicate.kind in {PredicateKind.EQUALITY, PredicateKind.ANNOTATED_EQUALITY}:
            return len(arguments) >= 2 and arguments[0] == arguments[1]
        if predicate.kind is PredicateKind.INEQUALITY and len(arguments) == 2:
            return snapshot.contains(atom.predicate_id, tuple(arguments))
        del body
        return snapshot.contains(atom.predicate_id, tuple(arguments))

    def _parent_at_least_violation(
        self,
        session: TableauSession,
        snapshot: _Snapshot,
        parent: NodeHandle,
        target: NodeHandle,
        budget: _Budget,
    ) -> int | None:
        for row in snapshot.rows:
            if row.key.arguments != (parent,):
                continue
            predicate = self.program.predicates.predicate(row.key.predicate_id)
            if predicate.kind is not PredicateKind.AT_LEAST_OBJECT:
                continue
            cardinality, filler = self._at_least_parts(predicate)
            successors = self._successors(snapshot, predicate, parent)
            suitable = 0
            candidates: list[NodeHandle] = []
            for successor in successors:
                budget.step()
                mirror = self._mirror(session, successor)
                if snapshot.contains(filler, (mirror,)):
                    suitable += 1
                elif mirror != successor and snapshot.contains(filler, (successor,)):
                    candidates.append(successor)
            if suitable >= cardinality:
                continue
            needed = cardinality - suitable
            selected = tuple(
                sorted(candidates, key=lambda value: self._creation_id(session, value))[:needed]
            )
            if target in selected:
                return len(self.program.clauses) + predicate.predicate_id
        return None

    def _blocked_at_least_violation(
        self,
        session: TableauSession,
        snapshot: _Snapshot,
        blocked: NodeHandle,
        blocker: NodeHandle,
        parent: NodeHandle,
        blocker_parent: NodeHandle,
        budget: _Budget,
    ) -> int | None:
        for row in snapshot.rows:
            if row.key.arguments != (blocker,):
                continue
            predicate = self.program.predicates.predicate(row.key.predicate_id)
            if predicate.kind is not PredicateKind.AT_LEAST_OBJECT:
                continue
            cardinality, filler = self._at_least_parts(predicate)
            blocker_successors = self._successors(snapshot, predicate, blocker)
            if blocker_parent not in blocker_successors or not snapshot.contains(
                filler, (blocker_parent,)
            ):
                continue
            blocked_successors = self._successors(snapshot, predicate, blocked)
            if parent in blocked_successors and snapshot.contains(filler, (parent,)):
                continue
            suitable = 0
            for successor in blocker_successors:
                budget.step()
                if successor != blocker_parent and snapshot.contains(filler, (successor,)):
                    suitable += 1
            if suitable < cardinality:
                return len(self.program.clauses) + predicate.predicate_id
        del session
        return None

    def _successors(
        self,
        snapshot: _Snapshot,
        predicate: Predicate,
        source: NodeHandle,
    ) -> tuple[NodeHandle, ...]:
        if predicate.role_id is None:
            raise InternalInvariantError("at-least predicate has no role ID")
        values: set[NodeHandle] = set()
        for role_predicate_id in self._object_roles_by_role_id.get(predicate.role_id, ()):
            for row in snapshot.by_predicate.get(role_predicate_id, ()):
                if len(row.key.arguments) == 2 and row.key.arguments[0] == source:
                    values.add(row.key.arguments[1])
        return tuple(sorted(values))

    @staticmethod
    def _at_least_parts(predicate: Predicate) -> tuple[int, int]:
        if predicate.cardinality is None or predicate.filler_predicate_id is None:
            raise InternalInvariantError("at-least predicate metadata is incomplete")
        return predicate.cardinality, predicate.filler_predicate_id

    def _repair_rows(
        self,
        session: TableauSession,
        snapshot: _Snapshot,
        blocked: NodeHandle,
        blocker: NodeHandle,
    ) -> tuple[int, ...]:
        pairs = [(blocked, blocker)]
        blocked_parent = session.nodes.require_active(blocked).parent
        blocker_parent = session.nodes.require_active(blocker).parent
        if blocked_parent is not None and blocker_parent is not None:
            pairs.append((blocked_parent, blocker_parent))
        selected: set[int] = set()
        for left, right in pairs:
            left_labels = {
                row.key.predicate_id
                for row in snapshot.rows
                if row.key.arguments == (left,) and row.key.predicate_id in self._concept_predicates
            }
            right_labels = {
                row.key.predicate_id
                for row in snapshot.rows
                if row.key.arguments == (right,)
                and row.key.predicate_id in self._concept_predicates
            }
            difference = left_labels ^ right_labels
            for row in snapshot.rows:
                if (
                    not row.core
                    and row.key.predicate_id in difference
                    and row.key.arguments in {(left,), (right,)}
                ):
                    selected.add(row.row_id)
        return tuple(sorted(selected))

    @staticmethod
    def _is_blocked(session: TableauSession, node: NodeHandle) -> bool:
        return session.nodes.require_active(node).blocker is not None

    @staticmethod
    def _mirror(session: TableauSession, node: NodeHandle) -> NodeHandle:
        blocker = session.nodes.require_active(node).blocker
        return node if blocker is None else blocker

    @staticmethod
    def _mirror_from_snapshot(snapshot: _Snapshot, node: NodeHandle) -> NodeHandle:
        return snapshot.mirrors.get(node, node)

    @staticmethod
    def _creation_id(session: TableauSession, node: NodeHandle) -> int:
        return session.nodes.require_active(node).creation_id


__all__ = [
    "BlockingValidator",
    "CancellableBlockingValidator",
    "CompiledClauseBlockingValidator",
    "PassAwareBlockingValidator",
    "ValidationDecision",
    "ValidationLimits",
    "ValidationPassResult",
]
