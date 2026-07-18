"""Native result IDs map through exact compiled symbol domains without reparsing."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import pyowl_core.model as owl
import pytest

from pyhermit.backends.native_mapping import CompiledResultMapper
from pyhermit.backends.protocol import HierarchyIds, RealizationIds
from pyhermit.clauses import compile_normalized
from pyhermit.datatypes import XSD_INTEGER
from pyhermit.exceptions import BackendMismatchError
from pyhermit.normalize import normalize_axioms


def _runtime() -> tuple[
    CompiledResultMapper,
    owl.Class,
    owl.ObjectProperty,
    owl.DataProperty,
    owl.NamedIndividual,
    owl.NamedIndividual,
    owl.Literal,
]:
    class_ = owl.Class(owl.IRI("urn:test:mapping:C"))
    object_property = owl.ObjectProperty(owl.IRI("urn:test:mapping:p"))
    data_property = owl.DataProperty(owl.IRI("urn:test:mapping:d"))
    left = owl.NamedIndividual(owl.IRI("urn:test:mapping:left"))
    right = owl.NamedIndividual(owl.IRI("urn:test:mapping:right"))
    literal = owl.Literal("1", owl.Datatype(owl.IRI(XSD_INTEGER)))
    axioms = (
        owl.Declaration(class_),
        owl.Declaration(object_property),
        owl.Declaration(data_property),
        owl.Declaration(left),
        owl.Declaration(right),
        owl.ClassAssertion(class_, left),
        owl.ObjectPropertyAssertion(object_property, left, right),
        owl.DataPropertyAssertion(data_property, left, literal),
    )
    normalized = normalize_axioms(axioms, logical_fingerprint="ab" * 32)
    program = compile_normalized(normalized)
    signature = (class_, object_property, data_property, left, right)
    return (
        CompiledResultMapper(program, signature=signature, source_literals=(literal,)),
        class_,
        object_property,
        data_property,
        left,
        right,
        literal,
    )


def _class_ids(mapper: CompiledResultMapper, class_: owl.Class) -> HierarchyIds:
    members = (
        (mapper.class_id(owl.OWL_NOTHING),),
        (mapper.class_id(class_),),
        (mapper.class_id(owl.OWL_THING),),
    )
    nodes = tuple(sorted(members))
    bottom = nodes.index(members[0])
    middle = nodes.index(members[1])
    top = nodes.index(members[2])
    return HierarchyIds(
        nodes,
        tuple(sorted(((bottom, middle), (middle, top)))),
        top,
        bottom,
    )


def test_maps_hierarchies_in_their_explicit_symbol_domains() -> None:
    mapper, class_, object_property, *_rest = _runtime()
    raw = _class_ids(mapper, class_)

    mapped = mapper.class_hierarchy(raw)

    assert class_ in mapped.nodes[
        next(index for index, node in enumerate(raw.nodes) if mapper.class_id(class_) in node)
    ]
    assert owl.OWL_THING in mapped.nodes[mapped.top_node]
    assert owl.OWL_NOTHING in mapped.nodes[mapped.bottom_node]
    with pytest.raises(BackendMismatchError):
        mapper.class_hierarchy(HierarchyIds(((999,),), (), 0, 0))

    object_members = (
        (mapper.object_property_id(owl.OWL_BOTTOM_OBJECT_PROPERTY),),
        (mapper.object_property_id(object_property),),
        (mapper.object_property_id(owl.inverse_property(object_property)),),
        (mapper.object_property_id(owl.OWL_TOP_OBJECT_PROPERTY),),
    )
    object_nodes = tuple(sorted(object_members))
    object_bottom = object_nodes.index(object_members[0])
    object_middle = object_nodes.index(object_members[1])
    inverse_middle = object_nodes.index(object_members[2])
    object_top = object_nodes.index(object_members[3])
    object_hierarchy = mapper.object_property_hierarchy(
        HierarchyIds(
            object_nodes,
            tuple(
                sorted(
                    (
                        (object_bottom, object_middle),
                        (object_bottom, inverse_middle),
                        (object_middle, object_top),
                        (inverse_middle, object_top),
                    )
                )
            ),
            object_top,
            object_bottom,
        )
    )
    assert owl.inverse_property(owl.OWL_TOP_OBJECT_PROPERTY) in object_hierarchy.nodes[
        object_hierarchy.top_node
    ]
    assert mapper.object_property_id(
        owl.inverse_property(owl.OWL_BOTTOM_OBJECT_PROPERTY)
    ) == mapper.object_property_id(owl.OWL_BOTTOM_OBJECT_PROPERTY)


def test_maps_realization_groups_properties_literals_and_class_nodes() -> None:
    mapper, class_, object_property, data_property, left, right, literal = _runtime()
    raw_hierarchy = _class_ids(mapper, class_)
    hierarchy = mapper.class_hierarchy(raw_hierarchy)
    individual_groups = tuple(
        sorted(
            (
                (mapper.individual_id(left),),
                (mapper.individual_id(right),),
            )
        )
    )
    left_group = next(
        index
        for index, group in enumerate(individual_groups)
        if mapper.individual_id(left) in group
    )
    right_group = 1 - left_group
    class_node = next(
        index for index, node in enumerate(raw_hierarchy.nodes) if mapper.class_id(class_) in node
    )
    raw = RealizationIds(
        individual_groups,
        ((left_group, (class_node,)),),
        (
            (
                left_group,
                mapper.object_property_id(object_property),
                (right_group,),
            ),
        ),
        (
            (
                left_group,
                mapper.data_property_id(data_property),
                (mapper.source_literal_id(literal),),
            ),
        ),
        (tuple(sorted((left_group, right_group))),),
    )

    mapped = mapper.realization(raw, hierarchy)

    assert mapped.same_as[left_group] == frozenset((left,))
    assert mapped.direct_types == ((left_group, frozenset((class_node,))),)
    assert mapped.object_targets == (
        (left_group, object_property, frozenset((right_group,))),
    )
    assert mapped.data_targets == ((left_group, data_property, frozenset((literal,))),)
    assert mapped.different_from == frozenset((tuple(sorted((left_group, right_group))),))


def test_rejects_incomplete_partitions() -> None:
    mapper, class_, _object_property, _data_property, left, _right, _literal = _runtime()
    hierarchy = mapper.class_hierarchy(_class_ids(mapper, class_))
    incomplete = RealizationIds(((mapper.individual_id(left),),))
    with pytest.raises(BackendMismatchError) as partition_error:
        mapper.realization(incomplete, hierarchy)
    assert partition_error.value.context["reason"] == "realization_partition_mismatch"
