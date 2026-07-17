from __future__ import annotations

import pytest
from pyowl_core import (
    IRI,
    OWL_TOP_OBJECT_PROPERTY,
    ObjectProperty,
    ObjectPropertyChain,
    SubObjectPropertyOf,
)

from pyhermit.roles import (
    RoleRegularityError,
    build_role_axiom_graph,
    inverse_object_role,
)


def prop(name: str) -> ObjectProperty:
    return ObjectProperty(IRI(f"urn:test:{name}"))


def test_internal_recursive_occurrence_has_stable_detailed_violation() -> None:
    target = prop("target")
    left = prop("left")
    right = prop("right")
    graph = build_role_axiom_graph(
        (
            SubObjectPropertyOf(
                ObjectPropertyChain((left, target, right)),
                target,
            ),
        )
    )
    assert not graph.regular
    violation = next(
        item for item in graph.regularity_violations if item.code == "RIA_NON_REGULAR_RECURSION"
    )
    assert violation.position == 1
    assert len(violation.provenance_sha256) == 64
    assert not graph.automata


def test_inverse_super_role_in_chain_is_rejected() -> None:
    target = prop("target")
    other = prop("other")
    graph = build_role_axiom_graph(
        (
            SubObjectPropertyOf(
                ObjectPropertyChain((inverse_object_role(target), other)),
                target,
            ),
        )
    )
    assert {item.code for item in graph.regularity_violations} >= {"RIA_INVERSE_RECURSION"}


def test_strict_complex_dependency_cycle_is_rejected_with_witness() -> None:
    first = prop("first")
    second = prop("second")
    guard = prop("guard")
    graph = build_role_axiom_graph(
        (
            SubObjectPropertyOf(ObjectPropertyChain((second, guard)), first),
            SubObjectPropertyOf(ObjectPropertyChain((first, guard)), second),
        )
    )
    violation = next(
        item for item in graph.regularity_violations if item.code == "RIA_DEPENDENCY_CYCLE"
    )
    assert violation.component_cycle[0] == violation.component_cycle[-1]


def test_strict_mode_raises_structured_error_without_hiding_report() -> None:
    target = prop("target")
    other = prop("other")
    axiom = SubObjectPropertyOf(
        ObjectPropertyChain((other, target, other)),
        target,
    )
    with pytest.raises(RoleRegularityError) as caught:
        build_role_axiom_graph((axiom,), require_regular=True)
    assert caught.value.violations
    assert "RIA_NON_REGULAR_RECURSION" in str(caught.value)


def test_any_chain_into_top_object_property_is_regular_by_w3c_rule() -> None:
    first = prop("first")
    second = prop("second")
    graph = build_role_axiom_graph(
        (
            SubObjectPropertyOf(
                ObjectPropertyChain((OWL_TOP_OBJECT_PROPERTY, first, second)),
                OWL_TOP_OBJECT_PROPERTY,
            ),
        )
    )
    assert graph.regular
    assert graph.accepts(OWL_TOP_OBJECT_PROPERTY, (second, first, second))
