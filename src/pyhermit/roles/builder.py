# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Compile core OWL property axioms into one deterministic private role model.

SPDX-License-Identifier: LGPL-3.0-or-later

Source-guided behavior: pinned HermiT ``ObjectPropertyInclusionManager``,
``BuiltInPropertyManager``, and ``graph/Graph`` at commit
37ec30aced32ac81ebecc5e33fad255ddefcb4c3.
"""

from __future__ import annotations

import hashlib
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from typing import Protocol, TypeVar

from pyowl_core.model import (
    OWL_BOTTOM_DATA_PROPERTY,
    OWL_BOTTOM_OBJECT_PROPERTY,
    OWL_TOP_DATA_PROPERTY,
    OWL_TOP_OBJECT_PROPERTY,
    AxiomNode,
    DataProperty,
    EquivalentDataProperties,
    EquivalentObjectProperties,
    InverseObjectProperties,
    ObjectInverseOf,
    ObjectProperty,
    ObjectPropertyChain,
    ObjectPropertyExpression,
    SubDataPropertyOf,
    SubObjectPropertyOf,
    SymmetricObjectProperty,
    TransitiveObjectProperty,
    inverse_property,
    walk,
)

from pyhermit.exceptions import ReasonerInterruptedError

from .automata import AutomatonProduction, build_role_automata
from .graph import (
    reachability_members,
    shortest_cycle,
    strongly_connected_components,
    transitive_closure,
)
from .model import (
    ComplexRoleInclusion,
    DataRoleInclusion,
    RegularityViolation,
    RoleAxiomGraph,
    RoleBuildLimits,
    RoleComponent,
    RoleInclusion,
)

_BUILTIN_TOP_TRANSITIVITY = hashlib.sha256(
    b"pyhermit:role-model:builtin-top-transitivity:v1"
).hexdigest()
_TOP_OBJECT_IRI = OWL_TOP_OBJECT_PROPERTY.iri.value
_BOTTOM_OBJECT_IRI = OWL_BOTTOM_OBJECT_PROPERTY.iri.value


@dataclass(frozen=True, slots=True)
class _RawInclusion:
    sub: bytes
    sup: bytes
    provenance: str | None
    builtin: bool


@dataclass(frozen=True, slots=True)
class _RawDataInclusion:
    sub: bytes
    sup: bytes
    provenance: str | None
    builtin: bool


@dataclass(frozen=True, slots=True)
class _RawChain:
    chain: tuple[bytes, ...]
    sup: bytes
    provenance: str
    inverse_generated: bool


def canonical_object_role(role: ObjectPropertyExpression) -> ObjectPropertyExpression:
    """Normalize the self-inverse built-ins without wrapping other core values."""

    if not isinstance(role, (ObjectProperty, ObjectInverseOf)):
        raise TypeError("role must be a pyowl_core object property expression")
    if isinstance(role, ObjectInverseOf) and role.property.iri.value in {
        _TOP_OBJECT_IRI,
        _BOTTOM_OBJECT_IRI,
    }:
        return role.property
    return role


def inverse_object_role(role: ObjectPropertyExpression) -> ObjectPropertyExpression:
    canonical = canonical_object_role(role)
    if isinstance(canonical, ObjectProperty) and canonical.iri.value in {
        _TOP_OBJECT_IRI,
        _BOTTOM_OBJECT_IRI,
    }:
        return canonical
    return canonical_object_role(inverse_property(canonical))


def _object_identity(role: ObjectPropertyExpression) -> tuple[str, bool]:
    """Return the canonical semantic identity without serializing the role."""

    canonical = canonical_object_role(role)
    if isinstance(canonical, ObjectInverseOf):
        return (canonical.property.iri.value, True)
    return (canonical.iri.value, False)


def build_role_axiom_graph(
    axioms: Iterable[AxiomNode],
    *,
    limits: RoleBuildLimits | None = None,
    require_regular: bool = False,
    cancelled: Callable[[], bool] | None = None,
) -> RoleAxiomGraph:
    """Build the shared role/profile/clausification graph in one canonical pass."""

    selected_limits = limits or RoleBuildLimits()
    if not isinstance(selected_limits, RoleBuildLimits):
        raise TypeError("limits must be RoleBuildLimits or None")
    if not isinstance(require_regular, bool):
        raise TypeError("require_regular must be bool")
    if cancelled is not None and not callable(cancelled):
        raise TypeError("cancelled must be callable or None")

    def checkpoint() -> None:
        if cancelled is not None and cancelled():
            raise ReasonerInterruptedError("role preprocessing cancelled")

    supplied_values: list[AxiomNode] = []
    for index, axiom in enumerate(axioms):
        if index & 0x3F == 0:
            checkpoint()
        supplied_values.append(axiom)
    supplied = tuple(supplied_values)
    if not all(isinstance(axiom, AxiomNode) for axiom in supplied):
        raise TypeError("axioms must contain pyowl_core AxiomNode values")
    encoded_items: list[tuple[bytes, AxiomNode]] = []
    for index, axiom in enumerate(supplied):
        if index & 0x3F == 0:
            checkpoint()
        encoded_items.append((axiom.canonical_bytes(), axiom))
    encoded_values = tuple(sorted(encoded_items, key=lambda item: item[0]))
    checkpoint()
    values = tuple(axiom for _encoded, axiom in encoded_values)

    object_values: dict[bytes, ObjectPropertyExpression] = {}
    data_values: dict[bytes, DataProperty] = {}
    simple: dict[tuple[bytes, bytes], _RawInclusion] = {}
    data_simple: dict[tuple[bytes, bytes], _RawDataInclusion] = {}
    chains: dict[tuple[tuple[bytes, ...], bytes, bool], _RawChain] = {}
    object_key_cache: dict[tuple[str, bool], bytes] = {}

    def object_key(role: ObjectPropertyExpression) -> bytes:
        canonical = canonical_object_role(role)
        identity = _object_identity(canonical)
        known = object_key_cache.get(identity)
        if known is None:
            known = canonical.canonical_bytes()
            object_key_cache[identity] = known
        return known

    def retain_object(role: ObjectPropertyExpression) -> bytes:
        canonical = canonical_object_role(role)
        key = object_key(canonical)
        object_values[key] = canonical
        inverse = inverse_object_role(canonical)
        object_values[object_key(inverse)] = inverse
        if len(object_values) > selected_limits.max_object_roles:
            raise ValueError("object role limit exceeded")
        return key

    def retain_data(property: DataProperty) -> bytes:
        if not isinstance(property, DataProperty):
            raise TypeError("property must be a pyowl_core DataProperty")
        key = property.canonical_bytes()
        data_values[key] = property
        if len(data_values) > selected_limits.max_data_properties:
            raise ValueError("data property limit exceeded")
        return key

    def add_simple(
        sub: ObjectPropertyExpression,
        sup: ObjectPropertyExpression,
        provenance: str | None,
        *,
        builtin: bool = False,
    ) -> None:
        sub_key = retain_object(sub)
        sup_key = retain_object(sup)
        candidate = _RawInclusion(sub_key, sup_key, provenance, builtin)
        _retain_preferred(simple, (sub_key, sup_key), candidate)
        inverse_sub = inverse_object_role(sub)
        inverse_sup = inverse_object_role(sup)
        inverse_sub_key = retain_object(inverse_sub)
        inverse_sup_key = retain_object(inverse_sup)
        inverse_candidate = _RawInclusion(
            inverse_sub_key,
            inverse_sup_key,
            provenance,
            builtin,
        )
        _retain_preferred(
            simple,
            (inverse_sub_key, inverse_sup_key),
            inverse_candidate,
        )

    def add_data_simple(
        sub: DataProperty,
        sup: DataProperty,
        provenance: str | None,
        *,
        builtin: bool = False,
    ) -> None:
        sub_key = retain_data(sub)
        sup_key = retain_data(sup)
        candidate = _RawDataInclusion(sub_key, sup_key, provenance, builtin)
        _retain_preferred(data_simple, (sub_key, sup_key), candidate)

    def add_chain(
        chain: tuple[ObjectPropertyExpression, ...],
        sup: ObjectPropertyExpression,
        provenance: str,
        *,
        inverse_generated: bool = False,
    ) -> None:
        chain_keys = tuple(retain_object(role) for role in chain)
        sup_key = retain_object(sup)
        record = _RawChain(chain_keys, sup_key, provenance, inverse_generated)
        chains[(chain_keys, sup_key, inverse_generated)] = record
        inverse_chain = tuple(inverse_object_role(role) for role in reversed(chain))
        inverse_sup = inverse_object_role(sup)
        inverse_keys = tuple(retain_object(role) for role in inverse_chain)
        inverse_sup_key = retain_object(inverse_sup)
        if inverse_keys != chain_keys or inverse_sup_key != sup_key:
            inverse_record = _RawChain(inverse_keys, inverse_sup_key, provenance, True)
            chains[(inverse_keys, inverse_sup_key, True)] = inverse_record
        if len(chains) > selected_limits.max_chain_axioms:
            raise ValueError("complex role inclusion limit exceeded")

    retain_object(OWL_TOP_OBJECT_PROPERTY)
    retain_object(OWL_BOTTOM_OBJECT_PROPERTY)
    retain_data(OWL_TOP_DATA_PROPERTY)
    retain_data(OWL_BOTTOM_DATA_PROPERTY)

    for index, (encoded_axiom, axiom) in enumerate(encoded_values):
        if index & 0x3F == 0:
            checkpoint()
        provenance = hashlib.sha256(encoded_axiom).hexdigest()
        for node in walk(axiom):
            if isinstance(node, (ObjectProperty, ObjectInverseOf)):
                retain_object(node)
            elif isinstance(node, DataProperty):
                retain_data(node)
        if isinstance(axiom, SubObjectPropertyOf):
            if isinstance(axiom.sub_property, ObjectPropertyChain):
                add_chain(
                    tuple(axiom.sub_property.properties),
                    axiom.super_property,
                    provenance,
                )
            else:
                add_simple(axiom.sub_property, axiom.super_property, provenance)
        elif isinstance(axiom, EquivalentObjectProperties):
            object_properties = tuple(axiom.properties)
            first_object_property = object_properties[0]
            for other_object_property in object_properties[1:]:
                add_simple(first_object_property, other_object_property, provenance)
                add_simple(other_object_property, first_object_property, provenance)
        elif isinstance(axiom, InverseObjectProperties):
            inverse_second = inverse_object_role(axiom.second)
            add_simple(axiom.first, inverse_second, provenance)
            add_simple(inverse_second, axiom.first, provenance)
        elif isinstance(axiom, SymmetricObjectProperty):
            inverse = inverse_object_role(axiom.property)
            add_simple(axiom.property, inverse, provenance)
            add_simple(inverse, axiom.property, provenance)
        elif isinstance(axiom, TransitiveObjectProperty):
            add_chain((axiom.property, axiom.property), axiom.property, provenance)
        elif isinstance(axiom, SubDataPropertyOf):
            add_data_simple(axiom.sub_property, axiom.super_property, provenance)
        elif isinstance(axiom, EquivalentDataProperties):
            axiom_data_properties = tuple(axiom.properties)
            first_data_property = axiom_data_properties[0]
            for other_data_property in axiom_data_properties[1:]:
                add_data_simple(first_data_property, other_data_property, provenance)
                add_data_simple(other_data_property, first_data_property, provenance)

    object_roles = tuple(object_values[key] for key in sorted(object_values))
    object_id = {key: index for index, key in enumerate(sorted(object_values))}
    data_properties = tuple(data_values[key] for key in sorted(data_values))
    data_id = {key: index for index, key in enumerate(sorted(data_values))}
    checkpoint()

    top_object = object_id[OWL_TOP_OBJECT_PROPERTY.canonical_bytes()]
    bottom_object = object_id[OWL_BOTTOM_OBJECT_PROPERTY.canonical_bytes()]
    top_data = data_id[OWL_TOP_DATA_PROPERTY.canonical_bytes()]
    bottom_data = data_id[OWL_BOTTOM_DATA_PROPERTY.canonical_bytes()]

    add_chain(
        (OWL_TOP_OBJECT_PROPERTY, OWL_TOP_OBJECT_PROPERTY),
        OWL_TOP_OBJECT_PROPERTY,
        _BUILTIN_TOP_TRANSITIVITY,
    )

    simple_records = tuple(
        RoleInclusion(
            object_id[value.sub],
            object_id[value.sup],
            value.provenance,
            value.builtin,
        )
        for value in sorted(
            simple.values(),
            key=lambda item: (item.sub, item.sup, item.builtin, item.provenance or ""),
        )
    )
    data_records = tuple(
        DataRoleInclusion(
            data_id[value.sub],
            data_id[value.sup],
            value.provenance,
            value.builtin,
        )
        for value in sorted(
            data_simple.values(),
            key=lambda item: (item.sub, item.sup, item.builtin, item.provenance or ""),
        )
    )
    chain_records = tuple(
        ComplexRoleInclusion(
            tuple(object_id[key] for key in value.chain),
            object_id[value.sup],
            value.provenance,
            value.inverse_generated,
        )
        for value in sorted(
            chains.values(),
            key=lambda item: (
                item.sup,
                item.chain,
                item.inverse_generated,
                item.provenance,
            ),
        )
    )

    object_sccs = strongly_connected_components(
        range(len(object_roles)),
        ((value.sub_role_id, value.super_role_id) for value in simple_records),
    )
    object_component_by_role = _component_map(len(object_roles), object_sccs)
    object_components = tuple(
        RoleComponent(index, members) for index, members in enumerate(object_sccs)
    )
    object_component_edges = {
        (
            object_component_by_role[value.sub_role_id],
            object_component_by_role[value.super_role_id],
        )
        for value in simple_records
        if object_component_by_role[value.sub_role_id]
        != object_component_by_role[value.super_role_id]
    }
    object_super = transitive_closure(range(len(object_components)), object_component_edges)

    data_sccs = strongly_connected_components(
        range(len(data_properties)),
        ((value.sub_property_id, value.super_property_id) for value in data_records),
    )
    data_component_by_property = _component_map(len(data_properties), data_sccs)
    data_component_edges = {
        (
            data_component_by_property[value.sub_property_id],
            data_component_by_property[value.super_property_id],
        )
        for value in data_records
        if data_component_by_property[value.sub_property_id]
        != data_component_by_property[value.super_property_id]
    }
    data_super = transitive_closure(range(len(data_sccs)), data_component_edges)

    inverse_ids = tuple(object_id[object_key(inverse_object_role(role))] for role in object_roles)
    violations, dependencies = _regularity(
        chain_records,
        simple_records,
        object_component_by_role,
        inverse_ids,
        len(object_components),
        top_object,
    )
    checkpoint()
    seeds = {object_component_by_role[inclusion.super_role_id] for inclusion in chain_records} | {
        object_component_by_role[top_object],
        object_component_by_role[bottom_object],
    }
    non_simple = frozenset(
        component for seed in seeds for component in reachability_members(object_super[seed])
    )

    productions = tuple(
        AutomatonProduction(
            object_component_by_role[inclusion.super_role_id],
            tuple(object_component_by_role[role_id] for role_id in inclusion.chain_role_ids),
        )
        for inclusion in chain_records
    )
    subrole_dependencies: dict[int, set[int]] = {
        component: set() for component in range(len(object_components))
    }
    for dependency, consumer in object_component_edges:
        subrole_dependencies[consumer].add(dependency)
    top_component = object_component_by_role[top_object]
    selected_automata = {top_component}
    pending_components = [component for component in non_simple if component != top_component]
    while pending_components:
        component = pending_components.pop()
        if component in selected_automata:
            continue
        selected_automata.add(component)
        pending_components.extend(dependencies.get(component, ()))
    automata = (
        {}
        if violations
        else build_role_automata(
            component_count=len(object_components),
            component_members=tuple(component.member_role_ids for component in object_components),
            dependencies=dependencies,
            subrole_dependencies={
                component: frozenset(values) for component, values in subrole_dependencies.items()
            },
            productions=productions,
            selected_components=frozenset(selected_automata),
            top_component=top_component,
            all_role_ids=tuple(range(len(object_roles))),
            limits=selected_limits,
        )
    )
    graph = RoleAxiomGraph(
        object_roles=object_roles,
        data_properties=data_properties,
        object_components=object_components,
        data_components=data_sccs,
        object_component_by_role=object_component_by_role,
        data_component_by_property=data_component_by_property,
        object_super_components=object_super,
        data_super_components=data_super,
        simple_inclusions=simple_records,
        data_inclusions=data_records,
        complex_inclusions=chain_records,
        non_simple_components=non_simple,
        regularity_violations=violations,
        automata=automata,
        inverse_role_ids=inverse_ids,
        top_object_role_id=top_object,
        bottom_object_role_id=bottom_object,
        top_data_property_id=top_data,
        bottom_data_property_id=bottom_data,
        source_axiom_count=len(values),
    )
    checkpoint()
    if require_regular:
        graph.require_regular()
    return graph


class _RawEdge(Protocol):
    @property
    def builtin(self) -> bool: ...

    @property
    def provenance(self) -> str | None: ...


RawEdgeT = TypeVar("RawEdgeT", bound=_RawEdge)


def _retain_preferred(
    target: dict[tuple[bytes, bytes], RawEdgeT],
    key: tuple[bytes, bytes],
    candidate: RawEdgeT,
) -> None:
    known = target.get(key)
    if known is None or _record_order(candidate) < _record_order(known):
        target[key] = candidate


def _record_order(value: _RawEdge) -> tuple[bool, str]:
    return (value.builtin, value.provenance or "")


def _component_map(size: int, components: tuple[tuple[int, ...], ...]) -> tuple[int, ...]:
    mapping = [-1] * size
    for component, members in enumerate(components):
        for member in members:
            mapping[member] = component
    if any(value < 0 for value in mapping):
        raise RuntimeError("SCC decomposition omitted a role")
    return tuple(mapping)


def _regularity(
    chains: tuple[ComplexRoleInclusion, ...],
    simple: tuple[RoleInclusion, ...],
    component_by_role: tuple[int, ...],
    inverse_ids: tuple[int, ...],
    component_count: int,
    top_role_id: int,
) -> tuple[tuple[RegularityViolation, ...], dict[int, frozenset[int]]]:
    violations: list[RegularityViolation] = []
    dependency_edges = {
        (
            component_by_role[inclusion.sub_role_id],
            component_by_role[inclusion.super_role_id],
        )
        for inclusion in simple
        if component_by_role[inclusion.sub_role_id] != component_by_role[inclusion.super_role_id]
    }
    edge_sources: dict[tuple[int, int], ComplexRoleInclusion] = {}
    for inclusion in chains:
        target = component_by_role[inclusion.super_role_id]
        if inclusion.super_role_id == top_role_id:
            continue
        inverse_target = component_by_role[inverse_ids[inclusion.super_role_id]]
        components = tuple(component_by_role[role] for role in inclusion.chain_role_ids)
        target_positions = tuple(
            index for index, component in enumerate(components) if component == target
        )
        for position, component in enumerate(components):
            if component == inverse_target and inverse_target != target:
                violations.append(
                    RegularityViolation(
                        "RIA_INVERSE_RECURSION",
                        "a complex subproperty chain contains the inverse of its super role",
                        inclusion.super_role_id,
                        inclusion.chain_role_ids,
                        inclusion.provenance_sha256,
                        position,
                    )
                )
        valid_recursive = (
            not target_positions
            or target_positions == (0,)
            or target_positions == (len(components) - 1,)
            or (len(components) == 2 and target_positions == (0, 1))
        )
        if not valid_recursive:
            violations.append(
                RegularityViolation(
                    "RIA_NON_REGULAR_RECURSION",
                    "the super role occurs outside a legal chain boundary pattern",
                    inclusion.super_role_id,
                    inclusion.chain_role_ids,
                    inclusion.provenance_sha256,
                    target_positions[0] if target_positions else None,
                )
            )
        for component in components:
            if component == target:
                continue
            dependency_edges.add((component, target))
            edge_sources.setdefault((component, target), inclusion)

    cycle = shortest_cycle(component_count, dependency_edges)
    if cycle is not None:
        source = next(
            (
                edge_sources[(cycle[index], cycle[index + 1])]
                for index in range(len(cycle) - 1)
                if (cycle[index], cycle[index + 1]) in edge_sources
            ),
            chains[0] if chains else None,
        )
        if source is not None:
            violations.append(
                RegularityViolation(
                    "RIA_DEPENDENCY_CYCLE",
                    "complex role inclusions create a strict dependency cycle",
                    source.super_role_id,
                    source.chain_role_ids,
                    source.provenance_sha256,
                    component_cycle=cycle,
                )
            )
    dependencies: dict[int, set[int]] = {component: set() for component in range(component_count)}
    for dependency, consumer in dependency_edges:
        if dependency != consumer:
            dependencies[consumer].add(dependency)
    return (
        tuple(
            sorted(
                set(violations),
                key=lambda value: (
                    value.code,
                    value.super_role_id,
                    value.chain_role_ids,
                    value.position if value.position is not None else -1,
                    value.provenance_sha256,
                ),
            )
        ),
        {key: frozenset(value) for key, value in dependencies.items()},
    )


__all__ = [
    "build_role_axiom_graph",
    "canonical_object_role",
    "inverse_object_role",
]
