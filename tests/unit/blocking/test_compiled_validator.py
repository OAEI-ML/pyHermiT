from __future__ import annotations

import pyowl_core.model as owl
import pytest

from pyhermit.backends.python.blocking.manager import BlockingEvent, BlockingManager
from pyhermit.backends.python.blocking.signatures import (
    BlockingLabels,
    BlockingSignature,
    BlockingVocabulary,
    DirectBlockingChecker,
    ValidatedSingleDirectBlockingChecker,
)
from pyhermit.backends.python.blocking.strategy import (
    BlockingRequirements,
    CoreBlockingMode,
    select_blocking_plan,
)
from pyhermit.backends.python.blocking.validation import (
    CompiledClauseBlockingValidator,
    ValidationLimits,
)
from pyhermit.backends.python.state import DependencySet, NodeHandle, NodeKind, TableauSession
from pyhermit.clauses import ClauseProgram, DLClause, PredicateKind, Variable, compile_normalized
from pyhermit.config import BlockingMode
from pyhermit.events import CancellationSource
from pyhermit.exceptions import ReasonerInterruptedError, ResourceLimitError
from pyhermit.normalize import normalize_axioms

FINGERPRINT = "cd" * 32


def _compile(axiom: owl.SubClassOf) -> ClauseProgram:
    return compile_normalized(normalize_axioms((axiom,), logical_fingerprint=FINGERPRINT))


def _manager(
    program: ClauseProgram,
    session: TableauSession,
) -> tuple[BlockingManager, DirectBlockingChecker]:
    requirements = BlockingRequirements.from_program(
        program,
        has_inverse_roles=False,
        requires_validated_core=True,
    )
    plan = select_blocking_plan(BlockingMode.VALIDATED_ANYWHERE, requirements)
    checker = ValidatedSingleDirectBlockingChecker(
        BlockingVocabulary.from_program(program),
        has_inverses=False,
    )
    manager = BlockingManager(session, checker, plan)
    manager.compute()
    return manager, checker


def _validator(
    program: ClauseProgram,
    *,
    max_matches: int = 1_000_000,
) -> CompiledClauseBlockingValidator:
    return CompiledClauseBlockingValidator(
        program,
        core_mode=CoreBlockingMode.SIMPLE,
        limits=ValidationLimits(
            max_matches_per_block=max_matches,
            cancellation_poll_interval=1,
        ),
    )


def _ht_clause(
    program: ClauseProgram,
    *,
    head_variable: int,
    annotated: bool = False,
) -> DLClause:
    for clause in program.clauses:
        body_kinds = tuple(
            program.predicates.predicate(atom.predicate_id).kind for atom in clause.body
        )
        head_kinds = tuple(
            program.predicates.predicate(atom.predicate_id).kind for atom in clause.head
        )
        if PredicateKind.OBJECT_ROLE not in body_kinds:
            continue
        if annotated:
            if PredicateKind.ANNOTATED_EQUALITY in head_kinds:
                return clause
            continue
        if len(clause.head) != 1 or head_kinds != (PredicateKind.CONCEPT,):
            continue
        argument = clause.head[0].arguments[0]
        if isinstance(argument, Variable) and argument.index == head_variable:
            return clause
    raise AssertionError("compiled HT clause was not found")


def _signature(
    manager: BlockingManager,
    checker: DirectBlockingChecker,
    node: NodeHandle,
) -> BlockingSignature:
    labels = BlockingLabels.from_session(manager.session, checker.vocabulary)
    return checker.signature(manager.session, labels, node)


def test_blocked_x_validation_ports_parent_edge_context_from_pinned_validator() -> None:
    source = owl.Class(owl.IRI("urn:test:blocking:source"))
    filler = owl.Class(owl.IRI("urn:test:blocking:filler"))
    role = owl.ObjectProperty(owl.IRI("urn:test:blocking:role"))
    program = _compile(owl.SubClassOf(source, owl.ObjectAllValuesFrom(role, filler)))
    clause = _ht_clause(program, head_variable=1)
    role_id = next(atom.predicate_id for atom in clause.body if len(atom.arguments) == 2)
    source_id = next(atom.predicate_id for atom in clause.body if len(atom.arguments) == 1)
    filler_id = clause.head[0].predicate_id

    session = TableauSession()
    blocker_parent = session.create_node(NodeKind.NI)
    blocker = session.create_node(NodeKind.TREE, parent=blocker_parent)
    blocked_parent = session.create_node(NodeKind.NI)
    blocked = session.create_node(NodeKind.TREE, parent=blocked_parent)
    for node in (blocker, blocked):
        session.extensions.add(source_id, (node,), DependencySet(), core=True)
    session.extensions.add(role_id, (blocker, blocker_parent), DependencySet())
    session.extensions.add(filler_id, (blocker_parent,), DependencySet())
    session.extensions.add(role_id, (blocked, blocked_parent), DependencySet())

    manager, checker = _manager(program, session)
    assert manager.blocker(blocked) == blocker
    validator = _validator(program)
    decision = validator.validate_block(
        session,
        blocked,
        blocker,
        _signature(manager, checker, blocked),
    )
    assert not decision.valid
    assert decision.violation_ids == (clause.clause_id,)

    session.extensions.add(filler_id, (blocked_parent,), DependencySet())
    assert validator.validate_block(
        session,
        blocked,
        blocker,
        _signature(manager, checker, blocked),
    ).valid


def test_parent_mirroring_invalidates_repairs_and_then_allows_sat() -> None:
    filler = owl.Class(owl.IRI("urn:test:blocking:filler"))
    consequence = owl.Class(owl.IRI("urn:test:blocking:consequence"))
    role = owl.ObjectProperty(owl.IRI("urn:test:blocking:role"))
    program = _compile(owl.SubClassOf(owl.ObjectSomeValuesFrom(role, filler), consequence))
    clause = _ht_clause(program, head_variable=0)
    role_id = next(atom.predicate_id for atom in clause.body if len(atom.arguments) == 2)
    filler_id = next(atom.predicate_id for atom in clause.body if len(atom.arguments) == 1)

    session = TableauSession()
    blocker_parent = session.create_node(NodeKind.NI)
    blocker = session.create_node(NodeKind.TREE, parent=blocker_parent)
    blocked_parent = session.create_node(NodeKind.NI)
    blocked = session.create_node(NodeKind.TREE, parent=blocked_parent)
    filler_row = session.extensions.add(
        filler_id,
        (blocker,),
        DependencySet(),
        core=False,
    )
    session.extensions.add(role_id, (blocked_parent, blocked), DependencySet())

    manager, _checker = _manager(program, session)
    validator = _validator(program)
    result = manager.validation_pass(validator)
    assert not result.valid
    assert result.violation_ids == (clause.clause_id,)
    assert result.promoted_rows == 1
    assert session.extensions.row(filler_row.row_id).core
    assert not manager.is_blocked(blocked)
    assert manager.trace[-1].event is BlockingEvent.INVALIDATED
    assert any(event.event is BlockingEvent.BLOCK_REJECTED for event in manager.trace)

    manager.compute()
    final = manager.validation_pass(validator)
    assert final.valid
    assert manager.ready_for_sat()


def test_parent_at_least_and_annotated_equality_regressions_reject_blocks() -> None:
    source = owl.Class(owl.IRI("urn:test:blocking:source"))
    filler = owl.Class(owl.IRI("urn:test:blocking:filler"))
    role = owl.ObjectProperty(owl.IRI("urn:test:blocking:role"))
    minimum_program = _compile(owl.SubClassOf(source, owl.ObjectMinCardinality(1, role, filler)))
    at_least = next(
        predicate
        for predicate in minimum_program.predicates.predicates
        if predicate.kind is PredicateKind.AT_LEAST_OBJECT
    )
    role_id = next(
        predicate.predicate_id
        for predicate in minimum_program.predicates.predicates
        if predicate.kind is PredicateKind.OBJECT_ROLE and predicate.role_id == at_least.role_id
    )
    assert at_least.filler_predicate_id is not None

    session = TableauSession()
    blocker_parent = session.create_node(NodeKind.NI)
    blocker = session.create_node(NodeKind.TREE, parent=blocker_parent)
    blocked_parent = session.create_node(NodeKind.NI)
    blocked = session.create_node(NodeKind.TREE, parent=blocked_parent)
    session.extensions.add(at_least.predicate_id, (blocked_parent,), DependencySet())
    session.extensions.add(role_id, (blocked_parent, blocked), DependencySet())
    session.extensions.add(
        at_least.filler_predicate_id,
        (blocked,),
        DependencySet(),
    )
    manager, checker = _manager(minimum_program, session)
    decision = _validator(minimum_program).validate_block(
        session,
        blocked,
        blocker,
        _signature(manager, checker, blocked),
    )
    assert not decision.valid
    assert decision.violation_ids[0] >= len(minimum_program.clauses)

    maximum_program = _compile(owl.SubClassOf(source, owl.ObjectMaxCardinality(1, role, filler)))
    clause = _ht_clause(maximum_program, head_variable=0, annotated=True)
    role_id = next(atom.predicate_id for atom in clause.body if len(atom.arguments) == 2)
    source_id = next(
        atom.predicate_id
        for atom in clause.body
        if len(atom.arguments) == 1
        and isinstance(atom.arguments[0], Variable)
        and atom.arguments[0].index == 0
    )
    filler_id = next(
        atom.predicate_id
        for atom in clause.body
        if len(atom.arguments) == 1
        and isinstance(atom.arguments[0], Variable)
        and atom.arguments[0].index != 0
    )
    session = TableauSession()
    blocker_parent = session.create_node(NodeKind.NI)
    blocker = session.create_node(NodeKind.TREE, parent=blocker_parent)
    other_successor = session.create_node(NodeKind.NI)
    blocked_parent = session.create_node(NodeKind.NI)
    blocked = session.create_node(NodeKind.TREE, parent=blocked_parent)
    for node in (blocker, blocked):
        session.extensions.add(source_id, (node,), DependencySet(), core=True)
    for successor in (blocker_parent, other_successor):
        session.extensions.add(role_id, (blocker, successor), DependencySet())
        session.extensions.add(filler_id, (successor,), DependencySet())
    session.extensions.add(role_id, (blocked, blocked_parent), DependencySet())
    session.extensions.add(filler_id, (blocked_parent,), DependencySet())
    manager, checker = _manager(maximum_program, session)
    decision = _validator(maximum_program).validate_block(
        session,
        blocked,
        blocker,
        _signature(manager, checker, blocked),
    )
    assert not decision.valid
    assert decision.violation_ids == (clause.clause_id,)


def test_validation_resource_and_cancellation_bounds_are_operation_safe() -> None:
    filler = owl.Class(owl.IRI("urn:test:blocking:filler"))
    consequence = owl.Class(owl.IRI("urn:test:blocking:consequence"))
    role = owl.ObjectProperty(owl.IRI("urn:test:blocking:role"))
    program = _compile(owl.SubClassOf(owl.ObjectSomeValuesFrom(role, filler), consequence))
    clause = _ht_clause(program, head_variable=0)
    role_id = next(atom.predicate_id for atom in clause.body if len(atom.arguments) == 2)
    filler_id = next(atom.predicate_id for atom in clause.body if len(atom.arguments) == 1)
    session = TableauSession()
    blocker_parent = session.create_node(NodeKind.NI)
    blocker = session.create_node(NodeKind.TREE, parent=blocker_parent)
    blocked_parent = session.create_node(NodeKind.NI)
    blocked = session.create_node(NodeKind.TREE, parent=blocked_parent)
    session.extensions.add(filler_id, (blocker,), DependencySet())
    session.extensions.add(role_id, (blocked_parent, blocked), DependencySet())
    manager, _checker = _manager(program, session)
    session.begin_operation()
    state_before = session.canonical_snapshot()
    blocking_before = manager.canonical_snapshot()

    with pytest.raises(ResourceLimitError, match="match limit"):
        manager.validation_pass(_validator(program, max_matches=1))
    assert session.canonical_snapshot() == state_before
    assert manager.canonical_snapshot() == blocking_before

    source = CancellationSource()
    source.interrupt("compiled validator cancellation")
    with pytest.raises(ReasonerInterruptedError, match="compiled validator cancellation"):
        manager.validation_pass(_validator(program), token=source.token)
    assert session.canonical_snapshot() == state_before
    assert manager.canonical_snapshot() == blocking_before
