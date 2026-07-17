from __future__ import annotations

import pyowl_core.model as owl
import pytest


def _anonymous(name: str) -> owl.AnonymousIndividual:
    return owl.AnonymousIndividual(b"q" * 32, name.encode())


def test_anonymous_individual_tree_rolls_up_against_named_root(make_service) -> None:  # type: ignore[no-untyped-def]
    member = owl.Class(owl.IRI("urn:test:anonymous:Member"))
    missing = owl.Class(owl.IRI("urn:test:anonymous:Missing"))
    role = owl.ObjectProperty(owl.IRI("urn:test:anonymous:role"))
    named = owl.NamedIndividual(owl.IRI("urn:test:anonymous:named"))
    target = owl.NamedIndividual(owl.IRI("urn:test:anonymous:target"))
    service = make_service(
        (
            owl.ObjectPropertyAssertion(role, named, target),
            owl.ClassAssertion(member, target),
        ),
        force_reductions=True,
    ).service
    blank = _anonymous("child")

    assert service.entails_all(
        (
            owl.ObjectPropertyAssertion(role, named, blank),
            owl.ClassAssertion(member, blank),
        )
    )
    assert not service.entails_all(
        (
            owl.ObjectPropertyAssertion(role, named, blank),
            owl.ClassAssertion(missing, blank),
        )
    )


def test_unconnected_anonymous_component_checks_entailed_existence(make_service) -> None:  # type: ignore[no-untyped-def]
    member = owl.Class(owl.IRI("urn:test:anonymous:Exists"))
    named = owl.NamedIndividual(owl.IRI("urn:test:anonymous:witness"))
    query = owl.ClassAssertion(member, _anonymous("root"))

    assert make_service((owl.ClassAssertion(member, named),)).service.entails(query)
    assert not make_service().service.entails(query)


def test_invalid_anonymous_cycle_and_multiple_named_edges_are_rejected(make_service) -> None:  # type: ignore[no-untyped-def]
    role = owl.ObjectProperty(owl.IRI("urn:test:anonymous:role"))
    first = _anonymous("first")
    second = _anonymous("second")
    third = _anonymous("third")
    named_a = owl.NamedIndividual(owl.IRI("urn:test:anonymous:a"))
    named_b = owl.NamedIndividual(owl.IRI("urn:test:anonymous:b"))
    service = make_service().service

    with pytest.raises(ValueError, match="cycle"):
        service.entails_all(
            (
                owl.ObjectPropertyAssertion(role, first, second),
                owl.ObjectPropertyAssertion(role, second, third),
                owl.ObjectPropertyAssertion(role, third, first),
            )
        )
    with pytest.raises(ValueError, match="more than one named"):
        service.entails_all(
            (
                owl.ObjectPropertyAssertion(role, named_a, first),
                owl.ObjectPropertyAssertion(role, first, named_b),
            )
        )


def test_has_key_uses_named_guard_and_shared_values(make_service) -> None:  # type: ignore[no-untyped-def]
    keyed = owl.Class(owl.IRI("urn:test:key:Class"))
    role = owl.ObjectProperty(owl.IRI("urn:test:key:role"))
    key = owl.HasKey(keyed, owl.CanonicalSet((role,)), owl.CanonicalSet())
    first = owl.NamedIndividual(owl.IRI("urn:test:key:first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:key:second"))
    value = owl.NamedIndividual(owl.IRI("urn:test:key:value"))
    service = make_service(
        (
            key,
            owl.ClassAssertion(keyed, first),
            owl.ClassAssertion(keyed, second),
            owl.ObjectPropertyAssertion(role, first, value),
            owl.ObjectPropertyAssertion(role, second, value),
        ),
        force_reductions=True,
    ).service

    assert service.entails(key)
    assert service.entails(owl.SameIndividual(owl.CanonicalSet((first, second))))
    # Satisfiability uses an anonymous ROOT and therefore cannot activate HasKey's
    # named-individual guard by itself.
    assert service.is_satisfiable(keyed)
