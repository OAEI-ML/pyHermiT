from __future__ import annotations

import hashlib

from pyowl_core import (
    IRI,
    CanonicalSet,
    EquivalentObjectProperties,
    ObjectProperty,
    ObjectPropertyChain,
    SubObjectPropertyOf,
    TransitiveObjectProperty,
)

from pyhermit.roles import build_role_axiom_graph


def test_role_model_trace_is_frozen() -> None:
    role = lambda name: ObjectProperty(IRI(f"urn:wpr:{name}"))  # noqa: E731
    target, first, second, equivalent = (role(name) for name in "rstu")
    graph = build_role_axiom_graph(
        (
            EquivalentObjectProperties(CanonicalSet((first, equivalent))),
            SubObjectPropertyOf(
                ObjectPropertyChain((first, second)),
                target,
            ),
            TransitiveObjectProperty(target),
        )
    )
    snapshot = graph.canonical_snapshot().encode("utf-8")
    assert hashlib.sha256(snapshot).hexdigest() == (
        "f173ca9ac322670b5adb7a4894062e3a55f97bb1b0c1bd0bb5e9882927cce409"
    )
    assert (
        len(graph.object_roles),
        len(graph.object_components),
        len(graph.simple_inclusions),
        len(graph.complex_inclusions),
        len(graph.automata),
    ) == (10, 8, 4, 5, 8)
    assert sum(value.state_count for value in graph.automata.values()) == 26
    assert sum(len(value.transitions) for value in graph.automata.values()) == 36
