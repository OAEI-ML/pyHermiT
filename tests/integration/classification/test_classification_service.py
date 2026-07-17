from __future__ import annotations

from typing import Any

import pyowl_core.model as owl
import pytest

from pyhermit.config import ReasonerConfig
from pyhermit.events import ProgressEvent
from pyhermit.exceptions import ReasonerInterruptedError
from pyhermit.services import ClassificationDomain


def _class(name: str) -> owl.Class:
    return owl.Class(owl.IRI(f"urn:test:classification:{name}"))


def test_class_hierarchy_equivalence_unsatisfiable_isolated_and_navigation(
    make_classification: Any,
) -> None:
    a, b, c, dead, isolated = (_class(name) for name in ("A", "B", "C", "Dead", "I"))
    service = make_classification(
        (
            owl.SubClassOf(a, b),
            owl.EquivalentClasses(owl.CanonicalSet((b, c))),
            owl.SubClassOf(dead, owl.OWL_NOTHING),
            owl.Declaration(isolated),
        )
    ).classification

    hierarchy = service.class_hierarchy()
    by_member = {
        member: node_id for node_id, node in enumerate(hierarchy.nodes) for member in node
    }
    assert by_member[b] == by_member[c]
    assert hierarchy.nodes[hierarchy.bottom_node] == frozenset((owl.OWL_NOTHING, dead))
    assert isolated in by_member
    assert service.equivalent_classes(b) == frozenset((b, c))
    assert service.superclasses(a, direct=True) == frozenset((frozenset((b, c)),))
    assert frozenset((owl.OWL_THING,)) in service.superclasses(a)
    assert frozenset((a,)) in service.subclasses(b)
    assert service.unsatisfiable_classes() == frozenset((owl.OWL_NOTHING, dead))
    assert service.disjoint_classes(dead) >= frozenset(
        (frozenset((owl.OWL_NOTHING, dead)),)
    )


def test_complex_bottom_expression_is_disjoint_with_bottom_node(
    make_classification: Any,
) -> None:
    a = _class("Contradiction")
    contradiction = owl.ObjectIntersectionOf(
        owl.CanonicalSet((a, owl.ObjectComplementOf(a)))
    )
    service = make_classification((owl.Declaration(a),)).classification

    assert service.disjoint_classes(contradiction) >= frozenset(
        (frozenset((owl.OWL_NOTHING,)),)
    )


def test_nonasserted_semantic_subsumption_and_complex_query_position(
    make_classification: Any,
) -> None:
    a, b, domain = (_class(name) for name in ("A", "B", "Domain"))
    role = owl.ObjectProperty(owl.IRI("urn:test:classification:role"))
    existential = owl.ObjectSomeValuesFrom(role, b)
    service = make_classification(
        (
            owl.EquivalentClasses(owl.CanonicalSet((a, existential))),
            owl.ObjectPropertyDomain(role, domain),
        )
    ).classification

    assert frozenset((domain,)) in service.superclasses(a)
    assert service.equivalent_classes(existential) == frozenset((a,))
    assert service.superclasses(existential, direct=True) == service.superclasses(a, direct=True)
    assert service.subclasses(existential, direct=True) == service.subclasses(a, direct=True)


def test_deterministic_quasi_and_slow_modes_are_identical(
    make_classification: Any,
) -> None:
    classes = tuple(_class(f"G{i}") for i in range(5))
    axioms = tuple(owl.SubClassOf(classes[index], classes[index + 1]) for index in range(4))
    deterministic = make_classification(axioms).classification
    quasi = make_classification(
        axioms,
        config=ReasonerConfig(force_quasi_order_classification=True),
    ).classification

    assert deterministic.class_hierarchy() == quasi.class_hierarchy()
    assert (
        deterministic.class_hierarchy()
        == deterministic.classify_slow(ClassificationDomain.CLASSES).hierarchy.hierarchy
    )
    assert deterministic.statistics(ClassificationDomain.CLASSES) is not None
    assert quasi.statistics(ClassificationDomain.CLASSES).mode.value == "quasi_order"


def test_cancelled_classification_never_publishes_partial_cache(
    make_classification: Any,
) -> None:
    a, b = _class("CancelA"), _class("CancelB")
    state = {"cancelled": True}
    service = make_classification(
        (owl.DisjointClasses(owl.CanonicalSet((a, b))),),
        cancelled=lambda: state["cancelled"],
    ).classification

    with pytest.raises(ReasonerInterruptedError):
        service.class_hierarchy()
    assert service.statistics(ClassificationDomain.CLASSES) is None
    state["cancelled"] = False
    assert service.class_hierarchy().nodes
    assert service.statistics(ClassificationDomain.CLASSES) is not None


def test_classification_cache_is_atomic_and_progress_is_observable(
    make_classification: Any,
) -> None:
    a, b = _class("ProgressA"), _class("ProgressB")
    events: list[ProgressEvent] = []
    harness = make_classification(
        (owl.SubClassOf(a, b),),
        config=ReasonerConfig(progress=events.append),
    )

    first = harness.classification.class_hierarchy()
    query_count = len(harness.temporary_queries)
    second = harness.classification.class_hierarchy()

    assert second is first
    assert len(harness.temporary_queries) == query_count
    classification_events = [
        event for event in events if event.kind.startswith("classification-")
    ]
    assert [event.kind for event in classification_events] == [
        "classification-started",
        "classification-completed",
    ]
    assert classification_events[0].operation_id == classification_events[1].operation_id
    assert classification_events[1].completed == classification_events[1].total
    assert classification_events[1].details["semantic_tests"] == 0
