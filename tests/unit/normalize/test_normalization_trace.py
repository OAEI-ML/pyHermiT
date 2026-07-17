from __future__ import annotations

import hashlib

from pyowl_core import (
    IRI,
    CanonicalSet,
    Class,
    EquivalentClasses,
    ObjectIntersectionOf,
    ObjectProperty,
    ObjectPropertyDomain,
    ObjectSomeValuesFrom,
    ObjectUnionOf,
    SubClassOf,
)

from pyhermit.normalize import normalize_axioms


def test_normalization_trace_is_frozen() -> None:
    first = Class(IRI("urn:trace:A"))
    second = Class(IRI("urn:trace:B"))
    third = Class(IRI("urn:trace:C"))
    role = ObjectProperty(IRI("urn:trace:p"))
    normalized = normalize_axioms(
        (
            EquivalentClasses(
                CanonicalSet(
                    (
                        first,
                        ObjectUnionOf(CanonicalSet((second, third))),
                    )
                )
            ),
            SubClassOf(
                ObjectIntersectionOf(CanonicalSet((first, ObjectSomeValuesFrom(role, second)))),
                third,
            ),
            ObjectPropertyDomain(
                role,
                ObjectUnionOf(CanonicalSet((first, second))),
            ),
        ),
        logical_fingerprint="56" * 32,
    )
    snapshot = normalized.canonical_snapshot().encode("utf-8")
    assert hashlib.sha256(snapshot).hexdigest() == (
        "818ae79befd1a7879380dd1cf9db76bebd144405a31fc45ac0f182f506f6fd64"
    )
    assert (len(normalized.records), len(normalized.definitions), normalized.expression_steps) == (
        9,
        5,
        16,
    )
