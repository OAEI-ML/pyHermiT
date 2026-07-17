from __future__ import annotations

import pytest
from hypothesis import given
from hypothesis import strategies as st

from pyhermit.backends.python.state import DependencyPool, DependencySet, Trail


@given(
    st.sets(st.integers(min_value=0, max_value=63)),
    st.sets(st.integers(min_value=0, max_value=63)),
)
def test_dependency_bitset_laws(left_values: set[int], right_values: set[int]) -> None:
    left = DependencySet.of(left_values)
    right = DependencySet.of(right_values)
    union = left.union(right)
    assert set(union) == left_values | right_values
    assert left.is_subset_of(union)
    assert right.is_subset_of(union)
    assert left.maximum == (max(left_values) if left_values else None)
    assert left.as_tuple() == tuple(sorted(left_values))


def test_dependency_pool_interns_and_drops_dead_sets() -> None:
    pool = DependencyPool()
    live = pool.intern((1, 3))
    assert pool.intern(DependencySet.of((1, 3))) is live
    pool.intern((2, 5, 8))
    assert len(pool) == 3
    pool.compact((live,))
    assert len(pool) == 2
    assert pool.intern((1, 3)) is live


def test_trail_rolls_back_every_mutation_in_reverse_order() -> None:
    trail = Trail()
    state: list[int] = []
    root = trail.checkpoint("root")
    for value in range(4):
        state.append(value)
        trail.record(f"append.{value}", lambda: state.pop())
    assert trail.rollback(root) == (
        "append.3",
        "append.2",
        "append.1",
        "append.0",
    )
    assert state == []
    with pytest.raises(ValueError, match="future"):
        trail.rollback(type(root)(root.sequence, 1, "unavailable"))
