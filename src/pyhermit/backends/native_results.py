"""Construct requested public results from opaque, native-validated cache owners.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import importlib
from collections.abc import Iterator, Mapping
from typing import TYPE_CHECKING, Any, TypeVar, cast

if TYPE_CHECKING:
    from pyhermit.hierarchy.model import HierarchyIndex

from pyhermit.backends.protocol import Hierarchy, HierarchyIds, RealizationIds
from pyhermit.exceptions import BackendMismatchError

_T = TypeVar("_T")


def _owner(value: object, name: str) -> Any:
    module = importlib.import_module("pyhermit._native")
    if type(value) is not getattr(module, name, None):
        raise BackendMismatchError("result requires an opaque native-issued owner")
    return value


def hierarchy_ids(owner: object) -> HierarchyIds:
    owner = _owner(owner, "_NativeHierarchyResult")
    nodes, edges, top, bottom = cast(Any, owner).rows()
    result = object.__new__(HierarchyIds)
    for key, value in (
        ("nodes", tuple(map(tuple, nodes))),
        ("edges", tuple(map(tuple, edges))),
        ("top_node", top),
        ("bottom_node", bottom),
        ("_native_owner", owner),
    ):
        object.__setattr__(result, key, value)
    return result


def realization_ids(owner: object) -> RealizationIds:
    owner = _owner(owner, "_NativeRealizationResult")
    groups, direct, objects, data, different = cast(Any, owner).rows()
    result = object.__new__(RealizationIds)
    for key, value in (
        ("same_as", tuple(map(tuple, groups))),
        ("direct_types", tuple((group, tuple(ids)) for group, ids in direct)),
        ("object_targets", tuple((group, prop, tuple(ids)) for group, prop, ids in objects)),
        ("data_targets", tuple((group, prop, tuple(ids)) for group, prop, ids in data)),
        ("different_from", tuple(map(tuple, different))),
        ("_native_owner", owner),
    ):
        object.__setattr__(result, key, value)
    return result


def matches(value: HierarchyIds | RealizationIds, symbols: Mapping[int, object]) -> bool:
    from .native_context import _NativeDomainMapping

    if value._native_owner is None:
        return False
    name = (
        "_NativeHierarchyResult" if isinstance(value, HierarchyIds) else "_NativeRealizationResult"
    )
    owner = _owner(value._native_owner, name)
    if type(symbols) is not _NativeDomainMapping or not owner.matches(
        symbols._owner, symbols._domain
    ):
        raise BackendMismatchError("native result belongs to another program or symbol domain")
    return True


def mapped_hierarchy(
    value: HierarchyIds | Hierarchy[_T],
    nodes: tuple[frozenset[_T], ...],
    symbols: Mapping[int, _T] | None = None,
) -> Hierarchy[_T]:
    # Called only after matching a native owner to its exact symbol domain.
    owner = _owner(value._native_owner, "_NativeHierarchyResult")
    result = object.__new__(Hierarchy)
    for key, item in (
        ("nodes", nodes),
        ("edges", frozenset(value.edges)),
        ("top_node", value.top_node),
        ("bottom_node", value.bottom_node),
        ("_native_owner", owner),
        (
            "_native_symbols",
            symbols if symbols is not None else getattr(value, "_native_symbols", None),
        ),
    ):
        object.__setattr__(result, key, item)
    return result


def require_same_hierarchy(value: RealizationIds, hierarchy: Hierarchy[_T]) -> None:
    owner = _owner(value._native_owner, "_NativeRealizationResult")
    other = _owner(hierarchy._native_owner, "_NativeHierarchyResult")
    if not owner.matches_hierarchy(other):
        raise BackendMismatchError("native realization belongs to another class hierarchy")


def hierarchy_related(
    value: Hierarchy[_T], node: int, *, upward: bool, direct: bool
) -> frozenset[int]:
    owner = _owner(value._native_owner, "_NativeHierarchyResult")
    return frozenset(owner.related(node, upward, direct))


class _NativeHierarchyMembers(Mapping[_T, int]):
    def __init__(self, hierarchy: Hierarchy[_T]) -> None:
        self._hierarchy = hierarchy
        self._owner = _owner(hierarchy._native_owner, "_NativeHierarchyResult")
        from .native_context import _NativeDomainMapping

        if type(hierarchy._native_symbols) is not _NativeDomainMapping:
            raise BackendMismatchError("native hierarchy lost its matching symbol owner")
        self._symbols = hierarchy._native_symbols

    def __getitem__(self, member: _T) -> int:
        try:
            identifier = self._symbols.native_id(cast(Any, member))
        except (ValueError, AttributeError):
            # Public inverse top/bottom aliases share their named property's node.
            import pyowl_core.model as owl

            for builtin, node in (
                (owl.OWL_TOP_OBJECT_PROPERTY, self._hierarchy.top_node),
                (owl.OWL_BOTTOM_OBJECT_PROPERTY, self._hierarchy.bottom_node),
            ):
                if self._symbols._domain == "object_property" and member == owl.inverse_property(
                    builtin
                ):
                    return node
            raise KeyError(member) from None
        node = self._owner.member_node(identifier)
        if node is None:
            raise KeyError(member)
        return cast(int, node)

    def __iter__(self) -> Iterator[_T]:
        return (member for node in self._hierarchy.nodes for member in node)

    def __len__(self) -> int:
        return len(self._symbols) + (2 if self._symbols._domain == "object_property" else 0)


def hierarchy_index(value: Hierarchy[_T]) -> HierarchyIndex[_T]:
    from pyhermit.hierarchy.model import HierarchyIndex

    result = object.__new__(HierarchyIndex)
    object.__setattr__(result, "hierarchy", value)
    object.__setattr__(result, "by_member", _NativeHierarchyMembers(value))
    return result


def hierarchy_reaches(value: Hierarchy[_T], child: int, parent: int) -> bool:
    owner = _owner(value._native_owner, "_NativeHierarchyResult")
    return cast(bool, owner.reaches(child, parent))
