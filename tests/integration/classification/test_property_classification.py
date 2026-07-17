from __future__ import annotations

from typing import Any

import pyowl_core.model as owl


def _class(name: str) -> owl.Class:
    return owl.Class(owl.IRI(f"urn:test:property-classification:{name}"))


def _object(name: str) -> owl.ObjectProperty:
    return owl.ObjectProperty(owl.IRI(f"urn:test:property-classification:{name}"))


def _data(name: str) -> owl.DataProperty:
    return owl.DataProperty(owl.IRI(f"urn:test:property-classification:{name}"))


def test_object_property_hierarchy_inverses_disjointness_domains_and_ranges(
    make_classification: Any,
) -> None:
    p, q, equivalent, disjoint = (_object(name) for name in ("p", "q", "eq", "d"))
    domain, range_ = _class("Domain"), _class("Range")
    service = make_classification(
        (
            owl.SubObjectPropertyOf(p, q),
            owl.EquivalentObjectProperties(owl.CanonicalSet((q, equivalent))),
            owl.DisjointObjectProperties(owl.CanonicalSet((p, disjoint))),
            owl.ObjectPropertyDomain(p, domain),
            owl.ObjectPropertyRange(p, range_),
        )
    ).classification

    hierarchy = service.object_property_hierarchy()
    assert p in {member for node in hierarchy.nodes for member in node}
    assert owl.inverse_property(p) in {member for node in hierarchy.nodes for member in node}
    assert service.equivalent_object_properties(q) == frozenset((q, equivalent))
    assert frozenset((q, equivalent)) in service.super_object_properties(p, direct=True)
    assert service.inverse_object_properties(p) >= frozenset((owl.inverse_property(p),))
    assert any(disjoint in group for group in service.disjoint_object_properties(p))
    assert any(domain in group for group in service.object_property_domains(p))
    assert any(range_ in group for group in service.object_property_ranges(p))
    assert service.disjoint_object_properties(owl.OWL_BOTTOM_OBJECT_PROPERTY) >= frozenset(
        (service.equivalent_object_properties(owl.OWL_BOTTOM_OBJECT_PROPERTY),)
    )


def test_semantic_object_property_inclusion_is_not_only_asserted_closure(
    make_classification: Any,
) -> None:
    p, q = _object("semantic-p"), _object("semantic-q")
    individual = owl.NamedIndividual(owl.IRI("urn:test:property-classification:only"))
    singleton_domain = owl.ObjectOneOf(owl.CanonicalSet((individual,)))
    service = make_classification(
        (
            owl.EquivalentClasses(owl.CanonicalSet((owl.OWL_THING, singleton_domain))),
            owl.ObjectPropertyAssertion(q, individual, individual),
        )
    ).classification

    # In the forced singleton domain, every possible p-edge is the asserted q-edge.
    assert any(q in group for group in service.super_object_properties(p))


def test_data_property_hierarchy_disjointness_domain_and_semantic_inclusion(
    make_classification: Any,
) -> None:
    p, q, disjoint = (_data(name) for name in ("p", "q", "d"))
    domain = _class("DataDomain")
    individual = owl.NamedIndividual(owl.IRI("urn:test:property-classification:data-only"))
    literal = owl.Literal("one", owl.XSD_STRING)
    singleton_domain = owl.ObjectOneOf(owl.CanonicalSet((individual,)))
    singleton_value = owl.DataOneOf(owl.CanonicalSet((literal,)))
    service = make_classification(
        (
            owl.DisjointDataProperties(owl.CanonicalSet((p, disjoint))),
            owl.DataPropertyDomain(p, domain),
            owl.EquivalentClasses(owl.CanonicalSet((owl.OWL_THING, singleton_domain))),
            owl.DataPropertyRange(p, singleton_value),
            owl.DataPropertyAssertion(q, individual, literal),
        )
    ).classification

    assert any(q in group for group in service.super_data_properties(p))
    assert any(disjoint in group for group in service.disjoint_data_properties(p))
    assert any(domain in group for group in service.data_property_domains(p))
    assert service.disjoint_data_properties(owl.OWL_BOTTOM_DATA_PROPERTY) >= frozenset(
        (service.equivalent_data_properties(owl.OWL_BOTTOM_DATA_PROPERTY),)
    )
