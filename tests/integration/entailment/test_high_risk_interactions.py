from __future__ import annotations

import pyowl_core.model as owl

from pyhermit.datatypes import XSD_INTEGER, XSD_STRING


def test_property_chain_entailment_uses_ordered_shared_witnesses(make_service) -> None:  # type: ignore[no-untyped-def]
    first = owl.ObjectProperty(owl.IRI("urn:test:interactions:first"))
    second = owl.ObjectProperty(owl.IRI("urn:test:interactions:second"))
    implied = owl.ObjectProperty(owl.IRI("urn:test:interactions:implied"))
    chain = owl.SubObjectPropertyOf(
        owl.ObjectPropertyChain((first, second)),
        implied,
    )

    assert make_service((chain,), force_reductions=True).service.entails(chain)
    assert not make_service((), force_reductions=True).service.entails(chain)


def test_nary_class_and_individual_axioms_check_every_required_pair(make_service) -> None:  # type: ignore[no-untyped-def]
    first = owl.Class(owl.IRI("urn:test:interactions:A"))
    second = owl.Class(owl.IRI("urn:test:interactions:B"))
    third = owl.Class(owl.IRI("urn:test:interactions:C"))
    classes = owl.CanonicalSet((first, second, third))
    equivalent = owl.EquivalentClasses(classes)
    disjoint = owl.DisjointClasses(classes)

    assert make_service(
        (
            owl.EquivalentClasses(owl.CanonicalSet((first, second))),
            owl.EquivalentClasses(owl.CanonicalSet((second, third))),
        ),
        force_reductions=True,
    ).service.entails(equivalent)
    assert make_service(
        tuple(
            owl.DisjointClasses(owl.CanonicalSet(pair))
            for pair in ((first, second), (first, third), (second, third))
        ),
        force_reductions=True,
    ).service.entails(disjoint)

    people = tuple(
        owl.NamedIndividual(owl.IRI(f"urn:test:interactions:i{index}")) for index in range(3)
    )
    same = owl.SameIndividual(owl.CanonicalSet(people))
    different = owl.DifferentIndividuals(owl.CanonicalSet(people))
    assert make_service(
        (
            owl.SameIndividual(owl.CanonicalSet((people[0], people[1]))),
            owl.SameIndividual(owl.CanonicalSet((people[1], people[2]))),
        ),
        force_reductions=True,
    ).service.entails(same)
    assert make_service((different,), force_reductions=True).service.entails(different)


def test_positive_and_negative_assertions_propagate_through_subproperties(make_service) -> None:  # type: ignore[no-untyped-def]
    sub = owl.ObjectProperty(owl.IRI("urn:test:interactions:sub"))
    sup = owl.ObjectProperty(owl.IRI("urn:test:interactions:sup"))
    first = owl.NamedIndividual(owl.IRI("urn:test:interactions:first-individual"))
    second = owl.NamedIndividual(owl.IRI("urn:test:interactions:second-individual"))
    positive = make_service(
        (
            owl.SubObjectPropertyOf(sub, sup),
            owl.ObjectPropertyAssertion(sub, first, second),
        ),
        force_reductions=True,
    ).service
    negative = make_service(
        (
            owl.SubObjectPropertyOf(sub, sup),
            owl.NegativeObjectPropertyAssertion(sup, first, second),
        ),
        force_reductions=True,
    ).service

    assert positive.entails(owl.ObjectPropertyAssertion(sup, first, second))
    assert negative.entails(owl.NegativeObjectPropertyAssertion(sub, first, second))


def test_data_subproperty_and_datatype_definition_interactions(make_service) -> None:  # type: ignore[no-untyped-def]
    sub = owl.DataProperty(owl.IRI("urn:test:interactions:data-sub"))
    sup = owl.DataProperty(owl.IRI("urn:test:interactions:data-sup"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:interactions:subject"))
    integer = owl.Datatype(owl.IRI(XSD_INTEGER))
    string = owl.Datatype(owl.IRI(XSD_STRING))
    literal = owl.Literal("7", integer)
    custom = owl.Datatype(owl.IRI("urn:test:interactions:custom-integer"))
    service = make_service(
        (
            owl.SubDataPropertyOf(sub, sup),
            owl.DataPropertyAssertion(sub, individual, literal),
            owl.DatatypeDefinition(custom, integer),
        ),
        force_reductions=True,
    ).service

    assert service.entails(owl.DataPropertyAssertion(sup, individual, literal))
    assert service.entails(owl.DatatypeDefinition(custom, integer))
    assert not service.entails(owl.DatatypeDefinition(custom, string))


def test_characteristic_reductions_detect_interactions_not_just_asserted_axioms(
    make_service,
) -> None:  # type: ignore[no-untyped-def]
    role = owl.ObjectProperty(owl.IRI("urn:test:interactions:role"))
    inverse = owl.ObjectInverseOf(role)
    service = make_service(
        (
            owl.SymmetricObjectProperty(role),
            owl.TransitiveObjectProperty(role),
        ),
        force_reductions=True,
    ).service

    assert service.entails(owl.InverseObjectProperties(role, role))
    assert service.entails(owl.TransitiveObjectProperty(inverse))
