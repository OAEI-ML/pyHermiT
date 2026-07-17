from __future__ import annotations

from pyhermit.backends.python.blocking import (
    BlockingManager,
    BlockingRequirements,
    BlockingVocabulary,
    SingleDirectBlockingChecker,
    select_blocking_plan,
)
from pyhermit.backends.python.state import (
    DependencySet,
    NodeHandle,
    NodeKind,
    TableauSession,
)
from pyhermit.config import BlockingMode

VOCABULARY = BlockingVocabulary(frozenset({1, 2, 3}), frozenset({10, 11}))


def _branched_session() -> tuple[TableauSession, NodeHandle, NodeHandle, NodeHandle]:
    session = TableauSession()
    root = session.create_node(NodeKind.ROOT)
    blocker = session.create_node(NodeKind.TREE, parent=root)
    blocked = session.create_node(NodeKind.TREE, parent=root)
    descendant = session.create_node(NodeKind.TREE, parent=blocked)
    for node in (blocker, blocked):
        session.extensions.add(1, (node,), DependencySet())
    session.extensions.add(3, (descendant,), DependencySet())
    session.nodes.mark_existential(descendant, 7, pending=True)
    return session, blocker, blocked, descendant


def test_anywhere_finds_nonancestor_and_indirect_unblocking_reschedules_work() -> None:
    session, blocker, blocked, descendant = _branched_session()
    plan = select_blocking_plan(BlockingMode.ANYWHERE, BlockingRequirements())
    manager = BlockingManager(
        session,
        SingleDirectBlockingChecker(VOCABULARY),
        plan,
    )
    manager.compute()
    assert manager.blocker(blocked) == blocker
    assert manager.is_directly_blocked(blocked)
    assert manager.blocker(descendant) == blocked
    assert not manager.is_directly_blocked(descendant)

    checkpoint = session.trail.checkpoint("label-change")
    outcome = session.extensions.add(2, (blocked,), DependencySet())
    manager.notify_fact_change(outcome.row_id)
    manager.compute()
    assert not manager.is_blocked(blocked)
    assert not manager.is_blocked(descendant)
    assert descendant in session.existential_candidates
    manager.check_invariants()

    session.trail.rollback(checkpoint)
    manager.compute()
    assert manager.blocker(blocked) == blocker
    assert manager.blocker(descendant) == blocked
    assert descendant not in session.existential_candidates


def test_ancestor_mode_does_not_use_a_legal_nonancestor_blocker() -> None:
    session, _blocker, blocked, _descendant = _branched_session()
    plan = select_blocking_plan(BlockingMode.ANCESTOR, BlockingRequirements())
    manager = BlockingManager(
        session,
        SingleDirectBlockingChecker(VOCABULARY),
        plan,
    )
    manager.compute()
    assert not manager.is_blocked(blocked)


def test_unannounced_mutations_merge_prune_and_backtrack_cannot_leave_stale_blocks() -> None:
    session, blocker, blocked, descendant = _branched_session()
    plan = select_blocking_plan(BlockingMode.ANYWHERE, BlockingRequirements())
    manager = BlockingManager(
        session,
        SingleDirectBlockingChecker(VOCABULARY),
        plan,
    )
    manager.compute()
    baseline = manager.canonical_snapshot()
    checkpoint = session.trail.checkpoint("merge-prune")

    # Deliberately omit notification: the digest mismatch must force a safe full pass.
    session.merge_nodes(blocked, blocker, DependencySet())
    manager.compute()
    manager.check_invariants()
    assert not manager.is_blocked(descendant)

    session.trail.rollback(checkpoint)
    manager.compute()
    assert manager.canonical_snapshot() == baseline

    checkpoint = session.trail.checkpoint("prune")
    session.prune_subtree(blocked)
    manager.compute()
    manager.check_invariants()
    session.trail.rollback(checkpoint)
    manager.compute()
    assert manager.canonical_snapshot() == baseline
