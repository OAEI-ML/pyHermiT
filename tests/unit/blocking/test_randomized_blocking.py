from __future__ import annotations

import random

import pytest

from pyhermit.backends.python.blocking import (
    BlockingManager,
    BlockingRequirements,
    BlockingVocabulary,
    SingleDirectBlockingChecker,
    select_blocking_plan,
)
from pyhermit.backends.python.state import (
    Checkpoint,
    DependencySet,
    NodeHandle,
    NodeKind,
    TableauSession,
)
from pyhermit.config import BlockingMode

VOCABULARY = BlockingVocabulary(frozenset(range(1, 7)), frozenset({20, 21}))


def _actual(manager: BlockingManager, nodes: tuple[NodeHandle, ...]) -> tuple[object, ...]:
    return tuple(
        (
            node,
            manager.blocker(node),
            manager.is_directly_blocked(node),
            manager.is_blocked(node),
        )
        for node in nodes
        if manager.session.nodes.get(node).lifecycle.value == "active"
    )


@pytest.mark.parametrize("seed", range(20))
def test_incremental_and_unannounced_changes_match_full_recompute_after_every_step(
    seed: int,
) -> None:
    randomizer = random.Random(seed)
    session = TableauSession()
    root = session.create_node(NodeKind.ROOT)
    created: list[NodeHandle] = []
    for index in range(8):
        parent = root if index < 3 else randomizer.choice(created)
        created.append(session.create_node(NodeKind.TREE, parent=parent))
    nodes = tuple(created)
    for node in nodes:
        session.extensions.add(randomizer.randrange(1, 4), (node,), DependencySet())

    plan = select_blocking_plan(BlockingMode.ANYWHERE, BlockingRequirements())
    manager = BlockingManager(
        session,
        SingleDirectBlockingChecker(VOCABULARY),
        plan,
    )
    manager.compute()
    checkpoints: list[tuple[Checkpoint, tuple[object, ...]]] = []

    for step in range(150):
        action = randomizer.randrange(7)
        if action in (0, 1):
            node = randomizer.choice(nodes)
            outcome = session.extensions.add(
                randomizer.randrange(1, 7),
                (node,),
                DependencySet(),
                core=bool(randomizer.randrange(2)),
            )
            if randomizer.randrange(2):
                manager.notify_fact_change(outcome.row_id)
        elif action == 2:
            active = [row for row in session.extensions.active_rows() if row.key.predicate_id < 20]
            if active:
                row = randomizer.choice(active)
                session.extensions.deactivate(row.row_id)
                if randomizer.randrange(2):
                    manager.notify_fact_change(row)
        elif action == 3:
            active = [row for row in session.extensions.active_rows() if not row.core]
            if active:
                row = randomizer.choice(active)
                session.extensions.set_core(row.row_id)
                if randomizer.randrange(2):
                    manager.notify_fact_change(row)
        elif action == 4:
            child = randomizer.choice(nodes)
            child_parent = session.nodes.get(child).parent
            if child_parent is not None:
                outcome = session.extensions.add(
                    randomizer.choice((20, 21)),
                    (child_parent, child),
                    DependencySet(),
                )
                if randomizer.randrange(2):
                    manager.notify_fact_change(outcome.row_id)
        elif action == 5:
            checkpoints.append(
                (session.trail.checkpoint(f"seed-{seed}-step-{step}"), _actual(manager, nodes))
            )
        elif checkpoints:
            checkpoint, expected = checkpoints.pop()
            session.trail.rollback(checkpoint)
            manager.compute()
            assert _actual(manager, nodes) == expected

        manager.compute()
        reference = manager.reference_assignments()
        assert tuple(
            (
                assignment.node,
                assignment.blocker,
                assignment.directly,
                assignment.blocked,
            )
            for assignment in reference
            if assignment.node in nodes
        ) == _actual(manager, nodes)
        manager.check_invariants()

    while checkpoints:
        checkpoint, expected = checkpoints.pop()
        session.trail.rollback(checkpoint)
        manager.compute()
        assert _actual(manager, nodes) == expected
        manager.check_invariants()
