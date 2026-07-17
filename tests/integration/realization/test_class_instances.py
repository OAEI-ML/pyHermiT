from __future__ import annotations

import random
from typing import Any, cast

import pyowl_core.model as owl

from pyhermit.config import IndividualGrouping, ReasonerConfig


def _class(name: str) -> owl.Class:
    return owl.Class(owl.IRI(f"urn:test:realization:class:{name}"))


def _individual(name: str) -> owl.NamedIndividual:
    return owl.NamedIndividual(owl.IRI(f"urn:test:realization:individual:{name}"))


def test_type_closure_direct_instances_and_naive_entailment_agree(
    make_realization: Any,
) -> None:
    a, b, equivalent = (_class(name) for name in ("A", "B", "EquivalentB"))
    first, second = (_individual(name) for name in ("first", "second"))
    harness = make_realization(
        (
            owl.SubClassOf(a, b),
            owl.EquivalentClasses(owl.CanonicalSet((b, equivalent))),
            owl.ClassAssertion(a, first),
            owl.ClassAssertion(b, second),
        )
    )
    service = harness.realization

    assert service.types(first, direct=True) == frozenset((frozenset((a,)),))
    assert frozenset((b, equivalent)) in service.types(first)
    assert service.has_type(first, b)
    assert not service.has_type(first, b, direct=True)
    assert service.instances(a, direct=True) == frozenset((first,))
    assert service.instances(b) == frozenset((first, second))
    assert service.instances(b, direct=True) == frozenset((second,))

    for expression in (a, b, equivalent, owl.OWL_THING, owl.OWL_NOTHING):
        expected = frozenset(
            individual
            for individual in (first, second)
            if harness.entailment.entails(owl.ClassAssertion(expression, individual))
        )
        assert service.instances(expression) == expected


def test_same_as_grouping_substitution_and_different_are_exact(
    make_realization: Any,
) -> None:
    a = _class("SameType")
    first, alias, other = (_individual(name) for name in ("first", "alias", "other"))
    axioms = (
        owl.SameIndividual(owl.CanonicalSet((first, alias))),
        owl.DifferentIndividuals(owl.CanonicalSet((first, other))),
        owl.ClassAssertion(a, first),
    )
    flat = make_realization(axioms).realization
    grouped = make_realization(
        axioms,
        config=ReasonerConfig(individual_grouping=IndividualGrouping.BY_SAME_AS),
    ).realization

    assert flat.same_individuals(alias) == frozenset((first, alias))
    assert flat.has_type(alias, a)
    assert flat.different_individuals(alias) == frozenset((other,))
    assert grouped.instances(a) == frozenset((frozenset((first, alias)),))
    assert grouped.different_individuals(alias) == frozenset((frozenset((other,)),))
    assert all(
        isinstance(group, frozenset)
        for group in cast(frozenset[frozenset[owl.NamedIndividual]], grouped.instances(a))
    )


def test_complex_expression_direct_semantics_use_strict_named_subclasses(
    make_realization: Any,
) -> None:
    a, b = _class("ComplexA"), _class("ComplexB")
    first, second = _individual("complex-first"), _individual("complex-second")
    expression = owl.ObjectUnionOf(owl.CanonicalSet((a, b)))
    service = make_realization(
        (
            owl.ClassAssertion(a, first),
            owl.ClassAssertion(expression, second),
        )
    ).realization

    assert service.instances(expression) == frozenset((first, second))
    assert service.instances(expression, direct=True) == frozenset((second,))
    assert not service.has_type(first, expression, direct=True)
    assert service.has_type(second, expression, direct=True)


def test_generated_realization_matches_naive_entailment_oracle(
    make_realization: Any,
) -> None:
    rng = random.Random(20260717)
    classes = tuple(_class(f"Generated{index}") for index in range(6))
    individuals = tuple(_individual(f"generated-{index}") for index in range(4))
    axioms: list[owl.AxiomNode] = [
        owl.SubClassOf(classes[index], classes[index + 1])
        for index in range(len(classes) - 1)
    ]
    axioms.extend(
        owl.SubClassOf(classes[left], classes[right])
        for left in range(len(classes))
        for right in range(left + 2, len(classes))
        if rng.random() < 0.3
    )
    axioms.extend(
        owl.ClassAssertion(classes[rng.randrange(len(classes))], individual)
        for individual in individuals
    )
    harness = make_realization(axioms)

    for expression in (*classes, owl.OWL_THING, owl.OWL_NOTHING):
        expected_instances = frozenset(
            individual
            for individual in individuals
            if harness.entailment.entails(owl.ClassAssertion(expression, individual))
        )
        assert harness.realization.instances(expression) == expected_instances
    for individual in individuals:
        returned = {
            member
            for group in harness.realization.types(individual)
            for member in group
        }
        expected_types = {
            expression
            for expression in (*classes, owl.OWL_THING, owl.OWL_NOTHING)
            if harness.entailment.entails(owl.ClassAssertion(expression, individual))
        }
        assert returned == expected_types
