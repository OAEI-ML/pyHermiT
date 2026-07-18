from __future__ import annotations

from typing import Any

import pyowl_core.model as owl
import pytest

from pyhermit.backends.native_mapping import MappedRealization
from pyhermit.config import FreshEntityPolicy, ReasonerConfig
from pyhermit.exceptions import (
    BackendMismatchError,
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


def test_coarse_realization_seeds_all_public_caches_atomically(
    make_realization: Any,
) -> None:
    class_ = _class("coarse")
    first, second = (_individual(name) for name in ("coarse-first", "coarse-second"))
    object_property = owl.ObjectProperty(owl.IRI("urn:test:realization:coarse-object"))
    data_property = owl.DataProperty(owl.IRI("urn:test:realization:coarse-data"))
    integer = owl.Datatype(owl.IRI("http://www.w3.org/2001/XMLSchema#integer"))
    literal = owl.Literal("1", integer)
    harness = make_realization(
        (
            owl.Declaration(class_),
            owl.ObjectPropertyAssertion(object_property, first, second),
            owl.DataPropertyAssertion(data_property, first, literal),
        )
    )
    hierarchy = harness.classification.class_hierarchy()
    class_node = next(
        node_id for node_id, node in enumerate(hierarchy.nodes) if class_ in node
    )
    groups = (frozenset((first,)), frozenset((second,)))
    calls = 0

    def coarse() -> MappedRealization:
        nonlocal calls
        calls += 1
        return MappedRealization(
            groups,
            ((0, frozenset((class_node,))), (1, frozenset((hierarchy.top_node,)))),
            ((0, object_property, frozenset((1,))),),
            ((0, data_property, frozenset((literal,))),),
            frozenset(((0, 1),)),
        )

    service = harness.realization
    service._install_coarse_provider(coarse)

    assert service.same_individuals(first) == frozenset((first,))
    assert service.types(first, direct=True) == frozenset((frozenset((class_,)),))
    assert service.instances(class_) == frozenset((first,))
    assert service.object_property_values(first, object_property) == frozenset((second,))
    assert service.object_property_values(
        first, owl.OWL_TOP_OBJECT_PROPERTY
    ) == frozenset((first, second))
    assert service.data_property_values(first, data_property) == frozenset((literal,))
    assert service.data_property_values(
        first, owl.OWL_TOP_DATA_PROPERTY
    ) == frozenset((literal,))
    assert service.different_individuals(first) == frozenset((second,))
    assert calls == 1


def test_coarse_realization_failure_publishes_no_partial_partition(
    make_realization: Any,
) -> None:
    first = _individual("coarse-failure")
    service = make_realization((owl.Declaration(first),)).realization
    calls = 0

    def invalid() -> MappedRealization:
        nonlocal calls
        calls += 1
        return MappedRealization((), (), (), (), frozenset())

    service._install_coarse_provider(invalid)
    with pytest.raises(BackendMismatchError):
        service.same_individuals(first)
    with pytest.raises(BackendMismatchError):
        service.same_individuals(first)
    assert calls == 2
