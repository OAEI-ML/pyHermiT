from __future__ import annotations

from dataclasses import dataclass

import pytest

from pyhermit.backends.python.blocking import (
    BlockingManager,
    BlockingRequirements,
    BlockingSignature,
    BlockingVocabulary,
    ValidatedSingleDirectBlockingChecker,
    ValidationDecision,
    select_blocking_plan,
)
from pyhermit.backends.python.state import DependencySet, NodeHandle, NodeKind, TableauSession
from pyhermit.config import BlockingMode
from pyhermit.events import CancellationSource
from pyhermit.exceptions import InternalInvariantError, ReasonerInterruptedError

VOCABULARY = BlockingVocabulary(frozenset({1, 2}), frozenset({10}))


@dataclass
class _PromotingValidator:
    blocked: NodeHandle
    row_id: int
    calls: int = 0

    def validate_block(
        self,
        session: TableauSession,
        blocked: NodeHandle,
        blocker: NodeHandle,
        signature: BlockingSignature,
    ) -> ValidationDecision:
        del session, blocker, signature
        self.calls += 1
        if blocked == self.blocked:
            return ValidationDecision(False, (self.row_id,), (blocked,), (99,))
        return ValidationDecision(True)


def _validated() -> tuple[TableauSession, BlockingManager, NodeHandle, int]:
    session = TableauSession()
    root = session.create_node(NodeKind.ROOT)
    blocker = session.create_node(NodeKind.TREE, parent=root)
    blocked = session.create_node(NodeKind.TREE, parent=root)
    for node in (blocker, blocked):
        session.extensions.add(1, (node,), DependencySet(), core=True)
    extra = session.extensions.add(2, (blocked,), DependencySet(), core=False)
    session.nodes.mark_existential(blocked, 5, pending=True)
    plan = select_blocking_plan(
        BlockingMode.VALIDATED_ANYWHERE,
        BlockingRequirements(requires_validated_core=True),
    )
    manager = BlockingManager(
        session,
        ValidatedSingleDirectBlockingChecker(VOCABULARY, has_inverses=False),
        plan,
    )
    manager.compute()
    return session, manager, blocked, extra.row_id


def test_invalid_provisional_block_promotes_core_reschedules_and_reaches_fixed_point() -> None:
    session, manager, blocked, row_id = _validated()
    assert manager.is_directly_blocked(blocked)
    assert not manager.ready_for_sat()
    with pytest.raises(InternalInvariantError, match="before blocking validation"):
        manager.model_found(
            satisfiable=True,
            completed=True,
            has_nominals=True,
            has_additional_ontology=False,
            query_local_axioms=False,
        )

    validator = _PromotingValidator(blocked, row_id)

    def saturate() -> None:
        while (node := session.existential_candidates.pop()) is not None:
            for existential_id in tuple(session.nodes.get(node).unprocessed_existentials):
                session.nodes.mark_existential(node, existential_id, pending=False)

    results = manager.validate_to_fixed_point(validator, saturate)
    assert [result.valid for result in results] == [False, True]
    assert results[0].violation_ids == (99,)
    assert session.extensions.row(row_id).core
    assert not manager.is_blocked(blocked)
    assert manager.ready_for_sat()


def test_validation_cancellation_rolls_back_without_promoting_or_masquerading_as_clash() -> None:
    session, manager, blocked, row_id = _validated()
    session.begin_operation()
    baseline = session.canonical_snapshot()
    source = CancellationSource()
    source.interrupt("cancel validation")
    with pytest.raises(ReasonerInterruptedError, match="cancel validation"):
        manager.validation_pass(_PromotingValidator(blocked, row_id), token=source.token)
    assert session.canonical_snapshot() == baseline
    assert not session.extensions.row(row_id).core
    assert session.clashes.current is None
