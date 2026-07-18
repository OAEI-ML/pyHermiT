"""Exact mapping from domain-scoped native IDs to retained pyowl-core values.

SPDX-License-Identifier: LGPL-3.0-or-later

The compact native results intentionally contain integers only.  This module performs the
single coarse mapping back to objects already retained by the Python runtime; it never parses,
reconstructs, or copies an ontology model.  IDs are resolved in their explicit symbol domain so
overlapping dense identifiers (for example class ``0`` and object-role ``0``) cannot be confused.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import NoReturn, TypeVar

import pyowl_core.model as owl

from pyhermit.backends.protocol import Hierarchy, HierarchyIds, RealizationIds
from pyhermit.clauses import ClauseProgram, SymbolKind
from pyhermit.exceptions import BackendMismatchError

_T = TypeVar("_T", bound=owl.StructuralNode)


@dataclass(frozen=True, slots=True)
class MappedRealization:
    """Native realization values resolved against one mapped class taxonomy."""

    same_as: tuple[frozenset[owl.NamedIndividual], ...]
    direct_types: tuple[tuple[int, frozenset[int]], ...]
    object_targets: tuple[
        tuple[int, owl.ObjectPropertyExpression, frozenset[int]], ...
    ]
    data_targets: tuple[tuple[int, owl.DataProperty, frozenset[owl.Literal]], ...]
    different_from: frozenset[tuple[int, int]]


class CompiledResultMapper:
    """Domain-aware immutable lookup tables over one retained compiled program."""

    __slots__ = (
        "_classes",
        "_data_properties",
        "_individuals",
        "_object_properties",
        "_source_literals",
    )

    def __init__(
        self,
        program: ClauseProgram,
        *,
        signature: Iterable[owl.Entity],
        source_literals: Iterable[owl.Literal],
    ) -> None:
        if not isinstance(program, ClauseProgram):
            raise TypeError("program must be ClauseProgram")
        signature_values = tuple(signature)
        if not all(isinstance(value, owl.Entity) for value in signature_values):
            raise TypeError("signature must contain exact pyowl-core Entity values")
        literal_values = tuple(source_literals)
        if not all(isinstance(value, owl.Literal) for value in literal_values):
            raise TypeError("source_literals must contain exact pyowl-core Literal values")

        classes = {
            owl.OWL_THING,
            owl.OWL_NOTHING,
            *(value for value in signature_values if isinstance(value, owl.Class)),
        }
        source_object_properties = {
            value
            for value in signature_values
            if isinstance(value, owl.ObjectProperty)
            and value not in (owl.OWL_TOP_OBJECT_PROPERTY, owl.OWL_BOTTOM_OBJECT_PROPERTY)
        }
        object_properties: set[owl.ObjectPropertyExpression] = {
            owl.OWL_TOP_OBJECT_PROPERTY,
            owl.OWL_BOTTOM_OBJECT_PROPERTY,
            *source_object_properties,
        }
        object_properties.update(
            owl.inverse_property(value) for value in source_object_properties
        )
        data_properties = {
            owl.OWL_TOP_DATA_PROPERTY,
            owl.OWL_BOTTOM_DATA_PROPERTY,
            *(value for value in signature_values if isinstance(value, owl.DataProperty)),
        }
        individuals = {
            value for value in signature_values if isinstance(value, owl.NamedIndividual)
        }

        self._classes = _domain_lookup(
            program,
            SymbolKind.CLASS_EXPRESSION,
            classes,
            "class",
        )
        self._object_properties = _domain_lookup(
            program,
            SymbolKind.OBJECT_ROLE,
            object_properties,
            "object property",
        )
        self._data_properties = _domain_lookup(
            program,
            SymbolKind.DATA_PROPERTY,
            data_properties,
            "data property",
        )
        self._individuals = _domain_lookup(
            program,
            SymbolKind.INDIVIDUAL,
            individuals,
            "named individual",
        )
        self._source_literals = _domain_lookup(
            program,
            SymbolKind.SOURCE_LITERAL,
            literal_values,
            "source literal",
        )

    @property
    def class_ids(self) -> Mapping[int, owl.Class]:
        return self._classes

    @property
    def object_property_ids(self) -> Mapping[int, owl.ObjectPropertyExpression]:
        return self._object_properties

    @property
    def data_property_ids(self) -> Mapping[int, owl.DataProperty]:
        return self._data_properties

    @property
    def individual_ids(self) -> Mapping[int, owl.NamedIndividual]:
        return self._individuals

    @property
    def source_literal_ids(self) -> Mapping[int, owl.Literal]:
        return self._source_literals

    def class_id(self, value: owl.Class) -> int:
        return _reverse_id(self._classes, value, "class")

    def object_property_id(self, value: owl.ObjectPropertyExpression) -> int:
        if value == owl.inverse_property(owl.OWL_TOP_OBJECT_PROPERTY):
            value = owl.OWL_TOP_OBJECT_PROPERTY
        elif value == owl.inverse_property(owl.OWL_BOTTOM_OBJECT_PROPERTY):
            value = owl.OWL_BOTTOM_OBJECT_PROPERTY
        return _reverse_id(self._object_properties, value, "object property")

    def data_property_id(self, value: owl.DataProperty) -> int:
        return _reverse_id(self._data_properties, value, "data property")

    def individual_id(self, value: owl.NamedIndividual) -> int:
        return _reverse_id(self._individuals, value, "named individual")

    def source_literal_id(self, value: owl.Literal) -> int:
        return _reverse_id(self._source_literals, value, "source literal")

    def class_hierarchy(self, value: HierarchyIds) -> Hierarchy[owl.Class]:
        return _map_hierarchy(
            value,
            self._classes,
            owl.OWL_THING,
            owl.OWL_NOTHING,
            "class",
        )

    def object_property_hierarchy(
        self,
        value: HierarchyIds,
    ) -> Hierarchy[owl.ObjectPropertyExpression]:
        hierarchy = _map_hierarchy(
            value,
            self._object_properties,
            owl.OWL_TOP_OBJECT_PROPERTY,
            owl.OWL_BOTTOM_OBJECT_PROPERTY,
            "object-property",
        )
        nodes = list(hierarchy.nodes)
        nodes[hierarchy.top_node] = nodes[hierarchy.top_node] | frozenset(
            (owl.inverse_property(owl.OWL_TOP_OBJECT_PROPERTY),)
        )
        nodes[hierarchy.bottom_node] = nodes[hierarchy.bottom_node] | frozenset(
            (owl.inverse_property(owl.OWL_BOTTOM_OBJECT_PROPERTY),)
        )
        return Hierarchy(
            tuple(nodes),
            hierarchy.edges,
            hierarchy.top_node,
            hierarchy.bottom_node,
        )

    def data_property_hierarchy(
        self,
        value: HierarchyIds,
    ) -> Hierarchy[owl.DataProperty]:
        return _map_hierarchy(
            value,
            self._data_properties,
            owl.OWL_TOP_DATA_PROPERTY,
            owl.OWL_BOTTOM_DATA_PROPERTY,
            "data-property",
        )

    def realization(
        self,
        value: RealizationIds,
        class_hierarchy: Hierarchy[owl.Class],
    ) -> MappedRealization:
        """Resolve a result whose object targets are canonical same-as group IDs."""

        if not isinstance(value, RealizationIds):
            raise TypeError("value must be RealizationIds")
        if not isinstance(class_hierarchy, Hierarchy):
            raise TypeError("class_hierarchy must be Hierarchy")
        groups = tuple(
            frozenset(
                _lookup(self._individuals, identifier, "realization individual")
                for identifier in group
            )
            for group in value.same_as
        )
        observed_individuals = frozenset(
            identifier for group in value.same_as for identifier in group
        )
        if observed_individuals != frozenset(self._individuals):
            _fail(
                "native realization same-as partition does not cover exactly the named individuals",
                "realization_partition_mismatch",
            )
        _canonical_rows(value.direct_types, "direct-type")
        direct_types: list[tuple[int, frozenset[int]]] = []
        for group_id, type_nodes in value.direct_types:
            _require_group(group_id, groups, "direct type")
            if any(node_id >= len(class_hierarchy.nodes) for node_id in type_nodes):
                _fail(
                    "native realization direct type references an absent class node",
                    "realization_class_node_missing",
                )
            direct_types.append((group_id, frozenset(type_nodes)))

        _canonical_rows(value.object_targets, "object-target")
        object_targets: list[
            tuple[int, owl.ObjectPropertyExpression, frozenset[int]]
        ] = []
        for group_id, property_id, targets in value.object_targets:
            _require_group(group_id, groups, "object-property subject")
            if any(target >= len(groups) for target in targets):
                _fail(
                    "native realization object target is not a same-as group ID",
                    "realization_object_group_missing",
                )
            object_targets.append(
                (
                    group_id,
                    _lookup(
                        self._object_properties,
                        property_id,
                        "realization object property",
                    ),
                    frozenset(targets),
                )
            )

        _canonical_rows(value.data_targets, "data-target")
        data_targets: list[
            tuple[int, owl.DataProperty, frozenset[owl.Literal]]
        ] = []
        for group_id, property_id, targets in value.data_targets:
            _require_group(group_id, groups, "data-property subject")
            data_targets.append(
                (
                    group_id,
                    _lookup(
                        self._data_properties,
                        property_id,
                        "realization data property",
                    ),
                    frozenset(
                        _lookup(
                            self._source_literals,
                            target,
                            "realization source literal",
                        )
                        for target in targets
                    ),
                )
            )
        return MappedRealization(
            groups,
            tuple(direct_types),
            tuple(object_targets),
            tuple(data_targets),
            frozenset(value.different_from),
        )


def _domain_lookup(
    program: ClauseProgram,
    kind: SymbolKind,
    values: Iterable[_T],
    label: str,
) -> Mapping[int, _T]:
    by_key = {
        bytes.fromhex(value.key_hex): value.identifier
        for value in program.symbols.domain(kind).values
    }
    result: dict[int, _T] = {}
    for value in values:
        identifier = by_key.get(value.canonical_bytes())
        if identifier is None:
            _fail(
                f"retained {label} is absent from compiled {kind.value} symbols",
                "compiled_symbol_missing",
            )
        retained = result.get(identifier)
        if retained is not None and retained != value:
            _fail(
                f"compiled {kind.value} ID aliases distinct retained {label} values",
                "compiled_symbol_alias",
            )
        result[identifier] = value
    return MappingProxyType(dict(sorted(result.items())))


def _reverse_id(values: Mapping[int, _T], value: _T, label: str) -> int:
    for identifier, candidate in values.items():
        if candidate == value:
            return identifier
    raise ValueError(f"{label} is not retained by this compiled runtime")


def _map_hierarchy(
    value: HierarchyIds,
    symbols: Mapping[int, _T],
    top: _T,
    bottom: _T,
    label: str,
) -> Hierarchy[_T]:
    if not isinstance(value, HierarchyIds):
        raise TypeError("value must be HierarchyIds")
    observed = frozenset(member for node in value.nodes for member in node)
    if observed != frozenset(symbols):
        _fail(
            f"native {label} hierarchy does not cover exactly its compiled domain",
            "hierarchy_partition_mismatch",
        )
    nodes = tuple(
        frozenset(_lookup(symbols, member, f"{label} hierarchy member") for member in node)
        for node in value.nodes
    )
    if top not in nodes[value.top_node] or bottom not in nodes[value.bottom_node]:
        _fail(
            f"native {label} hierarchy top/bottom nodes do not contain the built-ins",
            "hierarchy_boundary_mismatch",
        )
    return Hierarchy(nodes, frozenset(value.edges), value.top_node, value.bottom_node)


def _lookup(values: Mapping[int, _T], identifier: int, label: str) -> _T:
    try:
        return values[identifier]
    except KeyError as error:
        raise _mismatch(
            f"native {label} ID is absent from the retained compiled domain",
            "native_result_symbol_missing",
        ) from error


def _canonical_rows(rows: tuple[tuple[object, ...], ...], label: str) -> None:
    if rows != tuple(sorted(set(rows))):
        _fail(
            f"native realization {label} rows are not sorted and unique",
            "realization_rows_noncanonical",
        )


def _require_group(group_id: int, groups: tuple[object, ...], label: str) -> None:
    if group_id >= len(groups):
        _fail(
            f"native realization {label} references an absent same-as group",
            "realization_group_missing",
        )


def _mismatch(message: str, reason: str) -> BackendMismatchError:
    return BackendMismatchError(message, context={"reason": reason})


def _fail(message: str, reason: str) -> NoReturn:
    raise _mismatch(message, reason)


__all__ = ["CompiledResultMapper", "MappedRealization"]
