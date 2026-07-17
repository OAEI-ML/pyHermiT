from __future__ import annotations

from pyhermit.roles.graph import (
    reachability_contains,
    reachability_members,
    transitive_closure,
)


def test_sparse_closure_does_not_allocate_high_dense_singleton_bits() -> None:
    closure = transitive_closure(range(10_000), ())
    assert closure[-1] == (9_999,)
    assert reachability_members(closure[-1]) == (9_999,)
    assert reachability_contains(closure[-1], 9_999)
    assert not reachability_contains(closure[-1], 0)


def test_dense_closure_switches_representation_without_changing_membership() -> None:
    closure = transitive_closure(range(100), ((index, index + 1) for index in range(99)))
    assert isinstance(closure[0], int)
    assert reachability_members(closure[0]) == tuple(range(100))
    assert reachability_contains(closure[50], 99)
    assert not reachability_contains(closure[50], 49)
