from __future__ import annotations

from typing import Any

import pyowl_core.model as owl
import pytest

from pyhermit.config import FreshEntityPolicy, ReasonerConfig
from pyhermit.exceptions import (
    FreshEntityError,
    InconsistentOntologyError,
    ReasonerInterruptedError,
)


def _class(name: str) -> owl.Class:
    return owl.Class(owl.IRI(f"urn:test:realization:edge-class:{name}"))


def _individual(name: str) -> owl.NamedIndividual:
    return owl.NamedIndividual(owl.IRI(f"urn:test:realization:edge-individual:{name}"))


def test_fresh_individual_builtins_and_disallow_policy(make_realization: Any) -> None:
    known = _individual("known")
    fresh = _individual("fresh")
    allowed = make_realization((owl.Declaration(known),)).realization

    assert allowed.same_individuals(fresh) == frozenset((fresh,))
    assert allowed.types(fresh, direct=True) == frozenset((frozenset((owl.OWL_THING,)),))
    assert allowed.object_property_values(
        fresh,
        owl.OWL_TOP_OBJECT_PROPERTY,
    ) == frozenset((known, fresh))

    disallowed = make_realization(
        (owl.Declaration(known),),
        config=ReasonerConfig(fresh_entities=FreshEntityPolicy.DISALLOW),
    ).realization
    with pytest.raises(FreshEntityError):
        disallowed.same_individuals(fresh)


def test_inconsistent_ontology_rejects_realization_answers(make_realization: Any) -> None:
    individual = _individual("inconsistent")
    service = make_realization(
        (owl.ClassAssertion(owl.OWL_NOTHING, individual),)
    ).realization

    with pytest.raises(InconsistentOntologyError):
        service.types(individual)


def test_cancellation_does_not_publish_partial_cache_and_repeat_is_cached(
    make_realization: Any,
) -> None:
    a = _class("Cancel")
    individual = _individual("cancel")
    state = {"cancelled": False}
    harness = make_realization(
        (owl.ClassAssertion(a, individual),),
        cancelled=lambda: state["cancelled"],
    )

    state["cancelled"] = True
    with pytest.raises(ReasonerInterruptedError):
        harness.realization.instances(a)
    state["cancelled"] = False
    first = harness.realization.instances(a)
    query_count = len(harness.temporary_queries)
    second = harness.realization.instances(a)

    assert first == second == frozenset((individual,))
    assert len(harness.temporary_queries) == query_count
    assert harness.realization.statistics.cache_hits > 0


def test_ordinary_large_abox_does_not_allocate_quadratic_same_as_candidates(
    make_realization: Any,
) -> None:
    individuals = tuple(_individual(f"ordinary-{index}") for index in range(250))
    service = make_realization(
        tuple(owl.Declaration(individual) for individual in individuals)
    ).realization

    assert service.same_individuals(individuals[125]) == frozenset((individuals[125],))
    # One built-in type assertion validates the public query.  With no nominal,
    # key, functional-role, or max-cardinality equality source, no O(n^2)
    # same-as entailment candidates are generated.
    assert service.statistics.entailment_tests == 1
