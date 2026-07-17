from __future__ import annotations

from pyhermit.backends.python.blocking.manager import BlockingEvent, BlockingManager
from pyhermit.backends.python.blocking.signatures import (
    BlockingVocabulary,
    SingleDirectBlockingChecker,
)
from pyhermit.backends.python.blocking.strategy import (
    BlockingRequirements,
    select_blocking_plan,
)
from pyhermit.backends.python.state import DependencySet, NodeKind, TableauSession
from pyhermit.config import BlockingMode


def test_anywhere_index_scales_linearly_over_large_equal_signature_bucket() -> None:
    session = TableauSession()
    root = session.create_node(NodeKind.ROOT)
    nodes = tuple(session.create_node(NodeKind.TREE, parent=root) for _ in range(5_000))
    for node in nodes:
        session.extensions.add(1, (node,), DependencySet())
    vocabulary = BlockingVocabulary(frozenset({1}), frozenset())
    plan = select_blocking_plan(BlockingMode.ANYWHERE, BlockingRequirements())
    manager = BlockingManager(session, SingleDirectBlockingChecker(vocabulary), plan)

    assert manager.compute() == len(nodes) - 1
    assert not manager.is_blocked(nodes[0])
    assert all(manager.blocker(node) == nodes[0] for node in nodes[1:])
    recomputed = tuple(event for event in manager.trace if event.event is BlockingEvent.RECOMPUTED)
    assert len(recomputed) == 1
    # Root plus all tree nodes were visited exactly once by the reference pass.
    assert recomputed[0].details[1] == len(nodes) + 1
