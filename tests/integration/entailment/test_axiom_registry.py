from __future__ import annotations

import pyowl_core.model as owl
import pytest

from pyhermit.datatypes import XSD_INTEGER
from pyhermit.services import ENTAILMENT_REDUCTION_TYPES


def logical_axioms() -> tuple[owl.LogicalAxiom, ...]:
    first = owl.Class(owl.IRI("urn:test:entailment:First"))
    second = owl.Class(owl.IRI("urn:test:entailment:Second"))
    third = owl.Class(owl.IRI("urn:test:entailment:Third"))
    role = owl.ObjectProperty(owl.IRI("urn:test:entailment:role"))
    other_role = owl.ObjectProperty(owl.IRI("urn:test:entailment:other-role"))
    data = owl.DataProperty(owl.IRI("urn:test:entailment:data"))
    other_data = owl.DataProperty(owl.IRI("urn:test:entailment:other-data"))
    datatype = owl.Datatype(owl.IRI("urn:test:entailment:datatype"))
    integer = owl.Datatype(owl.IRI(XSD_INTEGER))
    first_individual = owl.NamedIndividual(owl.IRI("urn:test:entailment:first"))
    second_individual = owl.NamedIndividual(owl.IRI("urn:test:entailment:second"))
    literal = owl.Literal("1", integer)
    classes = owl.CanonicalSet((first, second, third))
    roles = owl.CanonicalSet((role, other_role))
    data_roles = owl.CanonicalSet((data, other_data))
    individuals = owl.CanonicalSet((first_individual, second_individual))
    return (
        owl.SubClassOf(first, owl.ObjectSomeValuesFrom(role, second)),
        owl.EquivalentClasses(classes),
        owl.DisjointClasses(classes),
        owl.DisjointUnion(first, owl.CanonicalSet((second, third))),
        owl.SubObjectPropertyOf(role, other_role),
        owl.EquivalentObjectProperties(roles),
        owl.DisjointObjectProperties(roles),
        owl.InverseObjectProperties(role, other_role),
        owl.ObjectPropertyDomain(role, first),
        owl.ObjectPropertyRange(role, second),
        owl.FunctionalObjectProperty(role),
        owl.InverseFunctionalObjectProperty(role),
        owl.ReflexiveObjectProperty(role),
        owl.IrreflexiveObjectProperty(role),
        owl.SymmetricObjectProperty(role),
        owl.AsymmetricObjectProperty(role),
        owl.TransitiveObjectProperty(role),
        owl.SubDataPropertyOf(data, other_data),
        owl.EquivalentDataProperties(data_roles),
        owl.DisjointDataProperties(data_roles),
        owl.DataPropertyDomain(data, first),
        owl.DataPropertyRange(data, integer),
        owl.FunctionalDataProperty(data),
        owl.DatatypeDefinition(datatype, integer),
        owl.HasKey(first, owl.CanonicalSet((role,)), owl.CanonicalSet((data,))),
        owl.SameIndividual(individuals),
        owl.DifferentIndividuals(individuals),
        owl.ClassAssertion(owl.ObjectSomeValuesFrom(role, second), first_individual),
        owl.ObjectPropertyAssertion(role, first_individual, second_individual),
        owl.NegativeObjectPropertyAssertion(role, first_individual, second_individual),
        owl.DataPropertyAssertion(data, first_individual, literal),
        owl.NegativeDataPropertyAssertion(data, first_individual, literal),
    )


def test_registry_exactly_covers_every_core_logical_axiom_type(make_service) -> None:  # type: ignore[no-untyped-def]
    service = make_service().service
    assert frozenset(owl.LOGICAL_AXIOM_TYPES) == ENTAILMENT_REDUCTION_TYPES
    assert all(service.supports_entailment(value) for value in owl.LOGICAL_AXIOM_TYPES)
    assert not service.supports_entailment(owl.Declaration)
    with pytest.raises(TypeError, match="must be a type"):
        service.supports_entailment("SubClassOf")  # type: ignore[arg-type]


@pytest.mark.parametrize("axiom", logical_axioms(), ids=lambda value: type(value).__name__)
def test_each_axiom_family_has_positive_forced_reduction_and_open_world_negative(
    make_service,  # type: ignore[no-untyped-def]
    axiom: owl.LogicalAxiom,
) -> None:
    positive = make_service((axiom,), force_reductions=True).service
    negative = make_service((), force_reductions=True).service

    assert positive.entails(axiom)
    assert not negative.entails(axiom)
