"""Deterministic SCC collapse and exact quotient-DAG transitive reduction.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from collections.abc import Callable, Iterable, Mapping
from typing import TypeVar

from pyhermit.backends.protocol import Hierarchy

from .model import HierarchyIndex

T = TypeVar("T")
CanonicalKey = Callable[[T], bytes]


def build_hierarchy(
    elements: Iterable[T],
    relations: Iterable[tuple[T, T]],
    *,
    top: T,
    bottom: T,
    key: CanonicalKey[T],
) -> HierarchyIndex[T]:
    """Collapse a subordinate-to-superior relation into a canonical hierarchy."""

    values = frozenset(elements)
    if top not in values or bottom not in values:
        raise ValueError("top and bottom must occur in elements")
    if not callable(key):
        raise TypeError("key must be callable")
    semantic_edges = set(relations)
    if any(
        child not in values or parent not in values
        for child, parent in semantic_edges
    ):
        raise ValueError("relations must reference only classified elements")
    scc_edges = set(semantic_edges)
    for value in values:
        scc_edges.add((value, value))
        scc_edges.add((bottom, value))
        scc_edges.add((value, top))

    successors: dict[T, set[T]] = {value: set() for value in values}
    for child, parent in scc_edges:
        successors[child].add(parent)
    components = _strongly_connected_components(successors, key)
    members = {index: set(component) for index, component in enumerate(components)}
    component_by_member = {
        member: component_id for component_id, component in members.items() for member in component
    }
    bottom_component = component_by_member[bottom]
    top_component = component_by_member[top]
    # Structural bottom<=x<=top edges are required for SCC/equivalence detection,
    # but carrying every one into the quotient makes reduction quadratic.  Retain
    # only caller-provided semantic edges, then connect the quotient's minima and
    # maxima to the distinguished bounds.
    quotient = {
        (component_by_member[child], component_by_member[parent])
        for child, parent in semantic_edges
        if component_by_member[child] != component_by_member[parent]
        and component_by_member[child] != bottom_component
        and component_by_member[parent] != top_component
    }
    component_ids = frozenset(members)
    has_incoming = {parent for _child, parent in quotient}
    has_outgoing = {child for child, _parent in quotient}
    for component_id in component_ids:
        if component_id not in {bottom_component, top_component}:
            if component_id not in has_incoming:
                quotient.add((bottom_component, component_id))
            if component_id not in has_outgoing:
                quotient.add((component_id, top_component))
    if bottom_component != top_component and not quotient:
        quotient.add((bottom_component, top_component))
    return hierarchy_from_partition(
        members,
        quotient,
        top_node=top_component,
        bottom_node=bottom_component,
        key=key,
    )


def hierarchy_from_partition(
    members: Mapping[int, set[T] | frozenset[T]],
    edges: Iterable[tuple[int, int]],
    *,
    top_node: int,
    bottom_node: int,
    key: CanonicalKey[T],
) -> HierarchyIndex[T]:
    """Canonicalize a validated mutable partition into the public hierarchy value."""

    if not members or any(not values for values in members.values()):
        raise ValueError("hierarchy partition must contain nonempty nodes")
    if top_node not in members or bottom_node not in members:
        raise ValueError("top and bottom must reference partition nodes")
    ordered_old_ids = tuple(
        sorted(
            members,
            key=lambda node_id: tuple(sorted(key(value) for value in members[node_id])),
        )
    )
    new_id = {old_id: index for index, old_id in enumerate(ordered_old_ids)}
    nodes = tuple(frozenset(members[old_id]) for old_id in ordered_old_ids)
    materialized_edges = set(edges)
    if any(
        child not in new_id or parent not in new_id
        for child, parent in materialized_edges
    ):
        raise ValueError("hierarchy edge references an absent partition node")
    remapped = {
        (new_id[child], new_id[parent])
        for child, parent in materialized_edges
        if child != parent
    }
    reduced = _transitive_reduction(remapped, len(nodes))
    hierarchy = Hierarchy(
        nodes=nodes,
        edges=frozenset(reduced),
        top_node=new_id[top_node],
        bottom_node=new_id[bottom_node],
    )
    return HierarchyIndex(
        hierarchy,
        {
            member: node_id
            for node_id, node in enumerate(hierarchy.nodes)
            for member in node
        },
    )


def relation_closure(
    elements: Iterable[T],
    relations: Iterable[tuple[T, T]],
) -> frozenset[tuple[T, T]]:
    """Return the reflexive transitive closure of subordinate-to-superior pairs."""

    values = tuple(elements)
    successors: dict[T, set[T]] = {value: {value} for value in values}
    for child, parent in relations:
        if child not in successors or parent not in successors:
            raise ValueError("relations must reference only closure elements")
        successors[child].add(parent)
    for pivot in values:
        pivot_successors = successors[pivot]
        for child in values:
            if pivot in successors[child]:
                successors[child].update(pivot_successors)
    return frozenset(
        (child, parent) for child, parents in successors.items() for parent in parents
    )


def _strongly_connected_components(
    successors: Mapping[T, set[T]],
    key: CanonicalKey[T],
) -> tuple[frozenset[T], ...]:
    # Iterative Kosaraju avoids Python's recursion ceiling on deep biomedical
    # taxonomies while preserving a deterministic traversal order.
    ordered_successors = {
        value: tuple(sorted(values, key=key)) for value, values in successors.items()
    }
    visited: set[T] = set()
    finish_order: list[T] = []
    for start in sorted(successors, key=key):
        if start in visited:
            continue
        visited.add(start)
        stack: list[tuple[T, int]] = [(start, 0)]
        while stack:
            value, offset = stack[-1]
            adjacent = ordered_successors[value]
            if offset < len(adjacent):
                successor = adjacent[offset]
                stack[-1] = (value, offset + 1)
                if successor not in visited:
                    visited.add(successor)
                    stack.append((successor, 0))
                continue
            finish_order.append(value)
            stack.pop()

    predecessors: dict[T, set[T]] = {value: set() for value in successors}
    for child, parents in successors.items():
        for parent in parents:
            predecessors[parent].add(child)
    ordered_predecessors = {
        value: tuple(sorted(values, key=key)) for value, values in predecessors.items()
    }
    components: list[frozenset[T]] = []
    assigned: set[T] = set()
    for start in reversed(finish_order):
        if start in assigned:
            continue
        component: set[T] = set()
        stack = [(start, 0)]
        assigned.add(start)
        while stack:
            value, offset = stack[-1]
            adjacent = ordered_predecessors[value]
            if offset < len(adjacent):
                predecessor = adjacent[offset]
                stack[-1] = (value, offset + 1)
                if predecessor not in assigned:
                    assigned.add(predecessor)
                    stack.append((predecessor, 0))
                continue
            component.add(value)
            stack.pop()
        components.append(frozenset(component))
    return tuple(
        sorted(
            components,
            key=lambda component: tuple(sorted(key(value) for value in component)),
        )
    )


def _transitive_reduction(
    edges: set[tuple[int, int]],
    node_count: int,
) -> frozenset[tuple[int, int]]:
    successors: dict[int, set[int]] = {node: set() for node in range(node_count)}
    for child, parent in edges:
        if child not in successors or parent not in successors:
            raise ValueError("hierarchy edge references an absent node")
        successors[child].add(parent)
    _require_acyclic(successors)
    for edge in sorted(edges):
        successors[edge[0]].remove(edge[1])
        if not _reachable(successors, edge[0], edge[1]):
            successors[edge[0]].add(edge[1])
    return frozenset(
        (child, parent)
        for child, parents in successors.items()
        for parent in parents
    )


def _reachable(
    successors: Mapping[int, set[int]],
    start: int,
    target: int,
) -> bool:
    if start not in successors or target not in successors:
        raise ValueError("hierarchy edge references an absent node")
    frontier = list(successors[start])
    seen = {start}
    while frontier:
        current = frontier.pop()
        if current == target:
            return True
        if current in seen:
            continue
        seen.add(current)
        frontier.extend(successors[current] - seen)
    return False


def _require_acyclic(successors: Mapping[int, set[int]]) -> None:
    incoming = {node: 0 for node in successors}
    for parents in successors.values():
        for parent in parents:
            incoming[parent] += 1
    frontier = [node for node, count in incoming.items() if count == 0]
    visited = 0
    while frontier:
        child = frontier.pop()
        visited += 1
        for parent in successors[child]:
            incoming[parent] -= 1
            if incoming[parent] == 0:
                frontier.append(parent)
    if visited != len(successors):
        raise ValueError("hierarchy quotient relation must be acyclic")


__all__ = [
    "CanonicalKey",
    "build_hierarchy",
    "hierarchy_from_partition",
    "relation_closure",
]
