"""Immutable indexed hierarchy helpers shared by classification services.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Generic, TypeVar

from pyhermit.backends.protocol import Hierarchy

T = TypeVar("T")


@dataclass(frozen=True, slots=True)
class HierarchyIndex(Generic[T]):
    """A validated hierarchy plus its immutable member-to-node index."""

    hierarchy: Hierarchy[T]
    by_member: Mapping[T, int]

    def __post_init__(self) -> None:
        if not isinstance(self.hierarchy, Hierarchy):
            raise TypeError("hierarchy must be Hierarchy")
        index = dict(self.by_member)
        expected = {
            member: node_id for node_id, node in enumerate(self.hierarchy.nodes) for member in node
        }
        if index != expected:
            raise ValueError("member index must exactly cover the hierarchy partition")
        object.__setattr__(self, "by_member", MappingProxyType(index))

    @property
    def top(self) -> frozenset[T]:
        return self.hierarchy.nodes[self.hierarchy.top_node]

    @property
    def bottom(self) -> frozenset[T]:
        return self.hierarchy.nodes[self.hierarchy.bottom_node]

    def node_id(self, member: T) -> int:
        try:
            return self.by_member[member]
        except KeyError as error:
            raise KeyError("member is outside this hierarchy") from error

    def node(self, member: T) -> frozenset[T]:
        return self.hierarchy.nodes[self.node_id(member)]

    def direct_supernodes(self, node_id: int) -> frozenset[int]:
        self._require_node(node_id)
        return frozenset(parent for child, parent in self.hierarchy.edges if child == node_id)

    def direct_subnodes(self, node_id: int) -> frozenset[int]:
        self._require_node(node_id)
        return frozenset(child for child, parent in self.hierarchy.edges if parent == node_id)

    def supernodes(self, node_id: int, *, direct: bool) -> frozenset[int]:
        return self.direct_supernodes(node_id) if direct else self.hierarchy.ancestors(node_id)

    def subnodes(self, node_id: int, *, direct: bool) -> frozenset[int]:
        return self.direct_subnodes(node_id) if direct else self.hierarchy.descendants(node_id)

    def groups(self, node_ids: frozenset[int]) -> frozenset[frozenset[T]]:
        return frozenset(self.hierarchy.nodes[node_id] for node_id in node_ids)

    def _require_node(self, node_id: int) -> None:
        if (
            isinstance(node_id, bool)
            or not isinstance(node_id, int)
            or not 0 <= node_id < len(self.hierarchy.nodes)
        ):
            raise IndexError("hierarchy node index out of range")


__all__ = ["HierarchyIndex"]
