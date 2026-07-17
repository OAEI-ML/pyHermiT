from __future__ import annotations

import pytest

from pyhermit.backends.python.state import (
    DependencyPool,
    DependencySet,
    NodeArena,
    NodeKind,
    NodeLifecycle,
    Trail,
)
from pyhermit.exceptions import InternalInvariantError


def _arena() -> tuple[Trail, DependencyPool, NodeArena]:
    trail = Trail()
    dependencies = DependencyPool()
    return trail, dependencies, NodeArena(trail, dependencies)


def test_named_guard_tree_metadata_and_mutations_restore_exactly() -> None:
    trail, _dependencies, arena = _arena()
    root = arena.create(
        NodeKind.ROOT,
        is_owl_named_individual=True,
        source_individual_id=7,
    )
    tree = arena.create(NodeKind.TREE, parent=root)
    before = arena.logical_snapshot()
    checkpoint = trail.checkpoint("mutations")
    arena.set_blocked(tree, root, directly=True)
    arena.mark_existential(tree, 11, pending=True)
    assert arena.get(tree).tree_depth == 1
    assert arena.get(root).is_owl_named_individual
    arena.check_invariants()
    trail.rollback(checkpoint)
    assert arena.logical_snapshot() == before
    arena.check_invariants()

    with pytest.raises(ValueError, match="named-individual"):
        arena.create(NodeKind.TREE, parent=root, is_owl_named_individual=True)


def test_slot_reuse_never_revalidates_stale_handles_even_after_retire_rollback() -> None:
    trail, _dependencies, arena = _arena()
    original = arena.create(NodeKind.ROOT)
    checkpoint = trail.checkpoint("retire-and-reuse")
    arena.retire(original)
    replacement = arena.create(NodeKind.ROOT)
    assert replacement.slot == original.slot
    assert replacement.generation > original.generation
    with pytest.raises(KeyError, match="stale"):
        arena.get(original)

    trail.rollback(checkpoint)
    assert arena.get(original).lifecycle is NodeLifecycle.ACTIVE
    with pytest.raises(KeyError, match="stale"):
        arena.get(replacement)
    arena.check_invariants()

    arena.retire(original)
    later = arena.create(NodeKind.ROOT)
    assert later.generation > replacement.generation


def test_representative_chain_unions_dependencies_and_rolls_back() -> None:
    trail, dependencies, arena = _arena()
    first = arena.create(NodeKind.ROOT)
    second = arena.create(NodeKind.ROOT)
    third = arena.create(NodeKind.ROOT)
    checkpoint = trail.checkpoint("merge-chain")
    arena.merge(first, second, DependencySet.of((0,)))
    arena.merge(second, third, DependencySet.of((1,)))
    representative, support = arena.representative(first)
    assert representative == third
    assert support == dependencies.intern((0, 1))
    arena.check_invariants(highest_branch_level=1)
    trail.rollback(checkpoint)
    assert arena.representative(first) == (first, dependencies.empty)
    assert arena.representative(second) == (second, dependencies.empty)


def test_object_and_concrete_nodes_cannot_merge() -> None:
    _trail, _dependencies, arena = _arena()
    object_node = arena.create(NodeKind.ROOT)
    data_node = arena.create(NodeKind.CONCRETE)
    with pytest.raises(InternalInvariantError, match="object and concrete"):
        arena.merge(object_node, data_node, DependencySet())
