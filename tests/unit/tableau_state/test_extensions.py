from __future__ import annotations

from pyhermit.backends.python.state import (
    DeltaView,
    DependencyPool,
    DependencySet,
    ExtensionStore,
    NodeArena,
    NodeHandle,
    NodeKind,
    Trail,
)


def _store() -> tuple[Trail, NodeArena, ExtensionStore, tuple[NodeHandle, NodeHandle]]:
    trail = Trail()
    dependencies = DependencyPool()
    nodes = NodeArena(trail, dependencies)
    left = nodes.create(NodeKind.ROOT)
    right = nodes.create(NodeKind.ROOT)
    store = ExtensionStore(trail, nodes, dependencies)
    return trail, nodes, store, (left, right)


def test_support_antichain_preserves_the_derivation_that_survives_backtrack() -> None:
    trail, _nodes, store, handles = _store()
    left, _right = handles
    store.add(1, (left,), DependencySet.of((0, 1)))
    checkpoint = trail.checkpoint("smaller-support")
    outcome = store.add(1, (left,), DependencySet.of((0,)))
    assert outcome.support_changed
    assert store.row(outcome.row_id).supports == (DependencySet.of((0,)),)
    trail.rollback(checkpoint)
    assert store.row(outcome.row_id).supports == (DependencySet.of((0, 1)),)
    store.check_invariants(highest_branch_level=1)


def test_delta_partitions_indexes_deactivation_and_rollback_are_exact() -> None:
    trail, _nodes, store, handles = _store()
    left, right = handles
    first = store.add(2, (left,), DependencySet(), core=True)
    store.register_index((0,))
    assert [row.row_id for row in store.retrieve(2, bindings={0: left})] == [first.row_id]
    store.prepare_next_delta()
    second = store.add(2, (right,), DependencySet())
    store.prepare_next_delta()
    assert {row.row_id for row in store.active_rows(DeltaView.OLD)} == {first.row_id}
    assert {row.row_id for row in store.active_rows(DeltaView.NEW)} == {second.row_id}

    checkpoint = trail.checkpoint("deactivate")
    store.deactivate(first.row_id)
    assert tuple(store.retrieve(2, bindings={0: left})) == ()
    store.check_invariants()
    trail.rollback(checkpoint)
    assert [row.row_id for row in store.retrieve(2, bindings={0: left})] == [first.row_id]
    store.check_invariants()
