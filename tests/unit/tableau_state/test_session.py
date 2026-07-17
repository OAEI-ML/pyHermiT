from __future__ import annotations

import pytest

from pyhermit.backends.python.state import (
    BranchChoiceKind,
    Clash,
    ClashKind,
    DependencySet,
    NodeKind,
    NodeLifecycle,
    StableQueue,
    TableauSession,
    Trail,
)
from pyhermit.events import CancellationSource
from pyhermit.exceptions import InternalInvariantError, ReasonerInterruptedError


def test_branch_backtrack_restores_every_component_exactly() -> None:
    session = TableauSession()
    named = session.create_node(
        NodeKind.ROOT,
        is_owl_named_individual=True,
        source_individual_id=1,
    )
    other = session.create_node(NodeKind.ROOT)
    session.begin_operation()
    branch = session.push_branch(
        BranchChoiceKind.GROUND_DISJUNCTION,
        (10, 11),
        source_id=4,
        base_dependency=DependencySet(),
    )
    before = session.canonical_snapshot()

    tree = session.create_node(NodeKind.TREE, parent=named)
    session.nodes.mark_existential(tree, 8, pending=True)
    session.extensions.add(3, (tree,), DependencySet.of((branch.level,)), core=True)
    session.delta_rows.enqueue(0, (0,))
    session.existential_candidates.enqueue(tree, (tree.slot, tree.generation))
    session.add_ground_disjunction((20, 21), DependencySet.of((branch.level,)))
    session.install_clash(Clash(ClashKind.BOTTOM, DependencySet.of((branch.level,)), (3,)))
    session.merge_nodes(other, named, DependencySet.of((branch.level,)))
    session.check_invariants()

    session.backtrack_to(branch.level)
    assert session.canonical_snapshot() == before
    session.check_invariants()


def test_merge_and_prune_rewrite_facts_then_restore_on_rollback() -> None:
    session = TableauSession()
    root = session.create_node(NodeKind.ROOT)
    sibling = session.create_node(NodeKind.ROOT)
    child = session.create_node(NodeKind.TREE, parent=root)
    session.extensions.add(1, (sibling,), DependencySet())
    session.extensions.add(2, (sibling, sibling), DependencySet())
    baseline = session.canonical_snapshot()

    checkpoint = session.trail.checkpoint("merge")
    representative = session.merge_nodes(sibling, root, DependencySet())
    assert representative == root
    assert all(sibling not in row.key.arguments for row in session.extensions.active_rows())
    assert session.nodes.get(sibling).lifecycle is NodeLifecycle.MERGED
    session.trail.rollback(checkpoint)
    assert session.canonical_snapshot() == baseline

    checkpoint = session.trail.checkpoint("prune")
    pruned = session.prune_subtree(root)
    assert pruned == (child, root)
    assert session.nodes.get(child).lifecycle is NodeLifecycle.PRUNED
    session.trail.rollback(checkpoint)
    assert session.canonical_snapshot() == baseline


def test_disjunction_take_and_clash_selection_are_deterministic_and_rollback_safe() -> None:
    session = TableauSession()
    disjunction_id = session.add_ground_disjunction((9, 2, 5), DependencySet())
    checkpoint = session.trail.checkpoint("take")
    record = session.take_ground_disjunction()
    assert record is not None and record.disjunction_id == disjunction_id
    assert session.take_ground_disjunction() is None
    session.trail.rollback(checkpoint)
    assert session.take_ground_disjunction() is not None

    session.push_branch(
        BranchChoiceKind.MERGE,
        (1, 2),
        source_id=0,
        base_dependency=DependencySet(),
    )
    larger = Clash(ClashKind.BOTTOM, DependencySet.of((0,)), (1, 2))
    deterministic = Clash(ClashKind.EMPTY_HEAD, DependencySet(), (4,))
    assert session.install_clash(larger)
    assert session.install_clash(deterministic)
    assert session.clashes.current == deterministic
    assert not session.install_clash(larger)


def test_cancellation_is_not_a_clash_and_restores_the_operation_root() -> None:
    session = TableauSession()
    root = session.create_node(NodeKind.ROOT)
    session.begin_operation()
    baseline = session.canonical_snapshot()
    session.create_node(NodeKind.TREE, parent=root)
    session.extensions.add(7, (root,), DependencySet())
    source = CancellationSource()
    source.interrupt("test cancellation")
    with pytest.raises(ReasonerInterruptedError, match="test cancellation"):
        session.poll(source.token)
    assert session.canonical_snapshot() == baseline
    assert session.clashes.current is None


def test_stable_queue_rejects_ambiguous_priorities_and_rolls_back_pop() -> None:
    trail = Trail()
    queue: StableQueue[str] = StableQueue("test", trail)
    queue.enqueue("later", (2, 4))
    queue.enqueue("first", (1, 9))
    with pytest.raises(ValueError, match="uniquely"):
        queue.enqueue("ambiguous", (1, 9))
    checkpoint = trail.checkpoint("pop")
    assert queue.pop() == "first"
    trail.rollback(checkpoint)
    assert queue.values() == ("first", "later")
    queue.check_invariants()


def test_cross_sort_merge_fails_without_partial_state() -> None:
    session = TableauSession()
    root = session.create_node(NodeKind.ROOT)
    data = session.create_node(NodeKind.CONCRETE)
    before = session.canonical_snapshot()
    with pytest.raises(InternalInvariantError, match="object and concrete"):
        session.merge_nodes(root, data, DependencySet())
    assert session.canonical_snapshot() == before
