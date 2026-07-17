from __future__ import annotations

import itertools

from pyowl_core import (
    IRI,
    OWL_BOTTOM_DATA_PROPERTY,
    OWL_BOTTOM_OBJECT_PROPERTY,
    OWL_TOP_DATA_PROPERTY,
    OWL_TOP_OBJECT_PROPERTY,
    CanonicalSet,
    DataProperty,
    EquivalentDataProperties,
    EquivalentObjectProperties,
    InverseObjectProperties,
    ObjectInverseOf,
    ObjectProperty,
    ObjectPropertyChain,
    SubDataPropertyOf,
    SubObjectPropertyOf,
    TransitiveObjectProperty,
)

from pyhermit.roles import (
    BuiltinRoleSemantics,
    build_role_axiom_graph,
    inverse_object_role,
)


def object_property(name: str) -> ObjectProperty:
    return ObjectProperty(IRI(f"urn:test:{name}"))


def data_property(name: str) -> DataProperty:
    return DataProperty(IRI(f"urn:test:{name}"))


def test_empty_hierarchy_has_exact_nonmaterializing_builtins() -> None:
    graph = build_role_axiom_graph(())
    assert graph.regular
    assert graph.source_axiom_count == 0
    assert graph.builtin_object_semantics(OWL_TOP_OBJECT_PROPERTY) is (
        BuiltinRoleSemantics.UNIVERSAL
    )
    assert graph.builtin_object_semantics(OWL_BOTTOM_OBJECT_PROPERTY) is (
        BuiltinRoleSemantics.EMPTY
    )
    assert graph.builtin_data_semantics(OWL_TOP_DATA_PROPERTY) is (BuiltinRoleSemantics.UNIVERSAL)
    assert graph.builtin_data_semantics(OWL_BOTTOM_DATA_PROPERTY) is (BuiltinRoleSemantics.EMPTY)
    assert not graph.is_simple(OWL_TOP_OBJECT_PROPERTY)
    assert not graph.is_simple(OWL_BOTTOM_OBJECT_PROPERTY)
    assert graph.accepts(OWL_TOP_OBJECT_PROPERTY, (OWL_TOP_OBJECT_PROPERTY,))
    assert graph.slow_accepts(OWL_TOP_OBJECT_PROPERTY, (OWL_TOP_OBJECT_PROPERTY,))
    assert graph.accepts(
        OWL_BOTTOM_OBJECT_PROPERTY,
        (OWL_TOP_OBJECT_PROPERTY, OWL_BOTTOM_OBJECT_PROPERTY),
    )
    assert graph.slow_accepts(
        OWL_BOTTOM_OBJECT_PROPERTY,
        (OWL_TOP_OBJECT_PROPERTY, OWL_BOTTOM_OBJECT_PROPERTY),
    )


def test_simple_hierarchy_closure_and_inverse_edges_are_exact() -> None:
    child = object_property("child")
    parent = object_property("parent")
    ancestor = object_property("ancestor")
    graph = build_role_axiom_graph(
        (
            SubObjectPropertyOf(child, parent),
            SubObjectPropertyOf(parent, ancestor),
        )
    )
    assert graph.is_sub_object_role(child, ancestor)
    assert graph.is_sub_object_role(inverse_object_role(child), inverse_object_role(ancestor))
    assert not graph.is_sub_object_role(ancestor, child)
    assert graph.accepts(ancestor, (child,))
    assert graph.slow_accepts(ancestor, (child,))


def test_equivalent_inverse_and_symmetric_components_are_canonical() -> None:
    first = object_property("first")
    second = object_property("second")
    third = object_property("third")
    graph = build_role_axiom_graph(
        (
            EquivalentObjectProperties(CanonicalSet((first, second))),
            InverseObjectProperties(second, third),
        )
    )
    equivalents = graph.equivalent_object_roles(first)
    assert first in equivalents
    assert second in equivalents
    assert ObjectInverseOf(third) in equivalents
    assert graph.inverse_id(graph.inverse_id(graph.object_role_id(first))) == (
        graph.object_role_id(first)
    )


def test_data_property_scc_and_builtin_closure_are_separate() -> None:
    first = data_property("first")
    second = data_property("second")
    third = data_property("third")
    graph = build_role_axiom_graph(
        (
            EquivalentDataProperties(CanonicalSet((first, second))),
            SubDataPropertyOf(second, third),
        )
    )
    assert set(graph.equivalent_data_properties(first)) == {first, second}
    assert graph.is_sub_data_property(first, third)
    assert graph.is_sub_data_property(OWL_BOTTOM_DATA_PROPERTY, first)
    assert graph.is_sub_data_property(first, OWL_TOP_DATA_PROPERTY)
    assert not graph.is_sub_data_property(third, first)


def test_non_simple_status_propagates_to_inverse_and_superroles_only() -> None:
    first = object_property("first")
    second = object_property("second")
    complex_role = object_property("complex")
    super_role = object_property("super")
    graph = build_role_axiom_graph(
        (
            SubObjectPropertyOf(ObjectPropertyChain((first, second)), complex_role),
            SubObjectPropertyOf(complex_role, super_role),
        )
    )
    assert graph.is_simple(first)
    assert graph.is_simple(second)
    assert not graph.is_simple(complex_role)
    assert not graph.is_simple(inverse_object_role(complex_role))
    assert not graph.is_simple(super_role)
    assert not graph.is_simple(OWL_TOP_OBJECT_PROPERTY)


def test_explicit_transitivity_marks_exact_role_family_non_simple() -> None:
    role = object_property("transitive")
    graph = build_role_axiom_graph((TransitiveObjectProperty(role),))
    assert not graph.is_simple(role)
    assert not graph.is_simple(inverse_object_role(role))


def test_all_source_orders_produce_identical_ids_components_and_nfas() -> None:
    first = object_property("first")
    second = object_property("second")
    third = object_property("third")
    axioms = (
        SubObjectPropertyOf(first, second),
        SubObjectPropertyOf(second, third),
        EquivalentObjectProperties(CanonicalSet((first, inverse_object_role(first)))),
    )
    snapshots = {
        build_role_axiom_graph(permutation).canonical_snapshot()
        for permutation in itertools.permutations(axioms)
    }
    assert len(snapshots) == 1
