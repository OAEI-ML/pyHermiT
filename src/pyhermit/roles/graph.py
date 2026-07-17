"""Small deterministic graph primitives used by role preprocessing.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import heapq
from collections.abc import Iterable, Mapping

Reachability = int | tuple[int, ...]


def transitive_closure(
    nodes: Iterable[int],
    edges: Iterable[tuple[int, int]],
    *,
    reflexive: bool = True,
) -> tuple[Reachability, ...]:
    """Return DAG reachability using a sparse/dense adaptive representation.

    A dense integer bitset is excellent for a genuinely dense hierarchy but is
    quadratic for a large edgeless signature because a high singleton bit still
    occupies all lower machine words.  Singleton and sparse closures therefore stay
    as sorted tuples and switch to bitsets only when the bitset is actually smaller.
    """

    ordered = tuple(sorted(set(nodes)))
    if ordered != tuple(range(len(ordered))):
        raise ValueError("graph node IDs must be dense from zero")
    successors: list[set[int]] = [set() for _ in ordered]
    for source, target in edges:
        if source < 0 or source >= len(ordered) or target < 0 or target >= len(ordered):
            raise ValueError("graph edge endpoint is outside the node domain")
        successors[source].add(target)
    dependencies: dict[int, set[int]] = {node: set() for node in ordered}
    for source, targets in enumerate(successors):
        for target in targets:
            dependencies[target].add(source)
    order = topological_order(len(ordered), dependencies)
    closure: list[Reachability] = [(node,) if reflexive else () for node in ordered]
    for source in reversed(order):
        for target in successors[source]:
            closure[source] = _reachability_union(
                closure[source],
                _reachability_union((target,), closure[target]),
            )
    return tuple(closure)


def reachability_members(value: Reachability) -> tuple[int, ...]:
    if isinstance(value, tuple):
        return value
    if isinstance(value, bool) or value < 0:
        raise ValueError("dense reachability value must be a nonnegative integer")
    members: list[int] = []
    remaining = value
    while remaining:
        least = remaining & -remaining
        members.append(least.bit_length() - 1)
        remaining ^= least
    return tuple(members)


def reachability_contains(value: Reachability, member: int) -> bool:
    if isinstance(member, bool) or not isinstance(member, int) or member < 0:
        raise ValueError("reachability member must be a nonnegative integer")
    if isinstance(value, int):
        return bool(value & (1 << member))
    low = 0
    high = len(value)
    while low < high:
        middle = (low + high) // 2
        candidate = value[middle]
        if candidate < member:
            low = middle + 1
        else:
            high = middle
    return low < len(value) and value[low] == member


def _reachability_union(first: Reachability, second: Reachability) -> Reachability:
    if isinstance(first, int) or isinstance(second, int):
        bits = _as_bits(first) | _as_bits(second)
        return _compact_reachability(bits)
    merged: list[int] = []
    first_offset = 0
    second_offset = 0
    while first_offset < len(first) and second_offset < len(second):
        left = first[first_offset]
        right = second[second_offset]
        if left < right:
            merged.append(left)
            first_offset += 1
        elif right < left:
            merged.append(right)
            second_offset += 1
        else:
            merged.append(left)
            first_offset += 1
            second_offset += 1
    merged.extend(first[first_offset:])
    merged.extend(second[second_offset:])
    sparse = tuple(merged)
    if not sparse:
        return sparse
    dense_bytes = ((sparse[-1] + 30) // 30) * 4
    sparse_bytes = 40 + (8 * len(sparse))
    return _as_bits(sparse) if dense_bytes <= sparse_bytes else sparse


def _as_bits(value: Reachability) -> int:
    if isinstance(value, int):
        return value
    bits = 0
    for member in value:
        bits |= 1 << member
    return bits


def _compact_reachability(bits: int) -> Reachability:
    if not bits:
        return ()
    dense_bytes = ((bits.bit_length() + 29) // 30) * 4
    count = bits.bit_count()
    sparse_bytes = 40 + (8 * count)
    return bits if dense_bytes <= sparse_bytes else reachability_members(bits)


def strongly_connected_components(
    nodes: Iterable[int],
    edges: Iterable[tuple[int, int]],
) -> tuple[tuple[int, ...], ...]:
    """Deterministic Kosaraju SCCs ordered by their least member."""

    ordered = tuple(sorted(set(nodes)))
    if ordered != tuple(range(len(ordered))):
        raise ValueError("graph node IDs must be dense from zero")
    outgoing: list[set[int]] = [set() for _ in ordered]
    incoming: list[set[int]] = [set() for _ in ordered]
    for source, target in edges:
        if source < 0 or source >= len(ordered) or target < 0 or target >= len(ordered):
            raise ValueError("graph edge endpoint is outside the node domain")
        outgoing[source].add(target)
        incoming[target].add(source)

    visited: set[int] = set()
    finish: list[int] = []
    for root in ordered:
        if root in visited:
            continue
        visited.add(root)
        stack: list[tuple[int, int, tuple[int, ...]]] = [(root, 0, tuple(sorted(outgoing[root])))]
        while stack:
            node, offset, adjacent = stack[-1]
            if offset < len(adjacent):
                successor = adjacent[offset]
                stack[-1] = (node, offset + 1, adjacent)
                if successor not in visited:
                    visited.add(successor)
                    stack.append((successor, 0, tuple(sorted(outgoing[successor]))))
                continue
            finish.append(node)
            stack.pop()

    assigned: set[int] = set()
    components: list[tuple[int, ...]] = []
    for root in reversed(finish):
        if root in assigned:
            continue
        component: list[int] = []
        pending = [root]
        assigned.add(root)
        while pending:
            node = pending.pop()
            component.append(node)
            for predecessor in sorted(incoming[node], reverse=True):
                if predecessor not in assigned:
                    assigned.add(predecessor)
                    pending.append(predecessor)
        components.append(tuple(sorted(component)))
    return tuple(sorted(components, key=lambda value: value[0]))


def topological_order(
    node_count: int,
    dependencies: Mapping[int, frozenset[int] | set[int]],
) -> tuple[int, ...]:
    """Order nodes so every dependency precedes its consumer."""

    if isinstance(node_count, bool) or not isinstance(node_count, int) or node_count < 0:
        raise ValueError("node_count must be a nonnegative integer")
    remaining = [set(dependencies.get(node, ())) - {node} for node in range(node_count)]
    dependents: list[set[int]] = [set() for _ in range(node_count)]
    for consumer, values in enumerate(remaining):
        if any(value < 0 or value >= node_count for value in values):
            raise ValueError("dependency is outside the node domain")
        for dependency in values:
            dependents[dependency].add(consumer)
    ready = [node for node, values in enumerate(remaining) if not values]
    heapq.heapify(ready)
    result: list[int] = []
    while ready:
        node = heapq.heappop(ready)
        result.append(node)
        for consumer in sorted(dependents[node]):
            values = remaining[consumer]
            values.remove(node)
            if not values:
                heapq.heappush(ready, consumer)
    if len(result) != node_count:
        raise ValueError("dependency graph contains a cycle")
    return tuple(result)


def shortest_cycle(
    node_count: int,
    edges: Iterable[tuple[int, int]],
) -> tuple[int, ...] | None:
    """Return the lexicographically least shortest directed cycle, if any."""

    adjacency: list[set[int]] = [set() for _ in range(node_count)]
    for source, target in edges:
        adjacency[source].add(target)
    candidates: list[tuple[int, ...]] = []
    for start in range(node_count):
        queue: list[tuple[int, tuple[int, ...]]] = [(start, (start,))]
        seen = {start}
        offset = 0
        while offset < len(queue):
            node, path = queue[offset]
            offset += 1
            for successor in sorted(adjacency[node]):
                if successor == start:
                    candidates.append((*path, start))
                    queue = []
                    break
                if successor not in seen:
                    seen.add(successor)
                    queue.append((successor, (*path, successor)))
    if not candidates:
        return None
    return min(candidates, key=lambda value: (len(value), value))


__all__ = [
    "Reachability",
    "reachability_contains",
    "reachability_members",
    "shortest_cycle",
    "strongly_connected_components",
    "topological_order",
    "transitive_closure",
]
