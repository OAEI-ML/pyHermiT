from __future__ import annotations

from collections.abc import Iterable

import pyowl_core.model as owl
import pytest

from pyhermit.backends.python.tableau import PythonTableau
from pyhermit.clauses import compile_normalized
from pyhermit.config import ReasonerConfig
from pyhermit.events import CancellationSource
from pyhermit.normalize import normalize_axioms

FINGERPRINT = "e6" * 32


def _satisfiable(axioms: Iterable[owl.AxiomNode]) -> bool:
    program = compile_normalized(
        normalize_axioms(tuple(axioms), logical_fingerprint=FINGERPRINT)
    )
    token = CancellationSource().token
    return PythonTableau(program, ReasonerConfig(), token).run(token).satisfiable


def _interaction_cases() -> tuple[tuple[str, tuple[owl.AxiomNode, ...]], ...]:
    first_class = owl.Class(owl.IRI("urn:test:tableau:interaction:A"))
    second_class = owl.Class(owl.IRI("urn:test:tableau:interaction:B"))
    third_class = owl.Class(owl.IRI("urn:test:tableau:interaction:C"))
    first_role = owl.ObjectProperty(owl.IRI("urn:test:tableau:interaction:r"))
    second_role = owl.ObjectProperty(owl.IRI("urn:test:tableau:interaction:s"))
    super_role = owl.ObjectProperty(owl.IRI("urn:test:tableau:interaction:u"))
    first = owl.NamedIndividual(owl.IRI("urn:test:tableau:interaction:a"))
    second = owl.NamedIndividual(owl.IRI("urn:test:tableau:interaction:b"))
    third = owl.NamedIndividual(owl.IRI("urn:test:tableau:interaction:c"))
    return (
        (
            "role-chain-negative-assertion",
            (
                owl.SubObjectPropertyOf(
                    owl.ObjectPropertyChain((first_role, second_role)),
                    super_role,
                ),
                owl.ObjectPropertyAssertion(first_role, first, second),
                owl.ObjectPropertyAssertion(second_role, second, third),
                owl.NegativeObjectPropertyAssertion(super_role, first, third),
            ),
        ),
        (
            "universal-role-filler",
            (
                owl.SubClassOf(
                    first_class,
                    owl.ObjectAllValuesFrom(first_role, second_class),
                ),
                owl.ClassAssertion(first_class, first),
                owl.ObjectPropertyAssertion(first_role, first, second),
                owl.ClassAssertion(owl.ObjectComplementOf(second_class), second),
            ),
        ),
        (
            "same-and-different",
            (
                owl.SameIndividual(owl.CanonicalSet((first, second))),
                owl.DifferentIndividuals(owl.CanonicalSet((first, second))),
            ),
        ),
        (
            "key-equality-and-difference",
            (
                owl.HasKey(
                    first_class,
                    owl.CanonicalSet((first_role,)),
                    owl.CanonicalSet(()),
                ),
                owl.ClassAssertion(first_class, first),
                owl.ClassAssertion(first_class, second),
                owl.ObjectPropertyAssertion(first_role, first, third),
                owl.ObjectPropertyAssertion(first_role, second, third),
                owl.DifferentIndividuals(owl.CanonicalSet((first, second))),
            ),
        ),
        (
            "nominal-and-negative-label",
            (
                owl.SubClassOf(
                    owl.ObjectOneOf(owl.CanonicalSet((first,))),
                    first_class,
                ),
                owl.ClassAssertion(owl.ObjectComplementOf(first_class), first),
            ),
        ),
        (
            "minimum-maximum-cardinality",
            (
                owl.SubClassOf(
                    first_class,
                    owl.ObjectMinCardinality(2, first_role, second_class),
                ),
                owl.SubClassOf(
                    first_class,
                    owl.ObjectMaxCardinality(1, first_role, second_class),
                ),
                owl.ClassAssertion(first_class, first),
            ),
        ),
        (
            "exhausted-disjunction",
            (
                owl.SubClassOf(
                    first_class,
                    owl.ObjectUnionOf(owl.CanonicalSet((second_class, third_class))),
                ),
                owl.SubClassOf(second_class, owl.OWL_NOTHING),
                owl.SubClassOf(third_class, owl.OWL_NOTHING),
                owl.ClassAssertion(first_class, first),
            ),
        ),
    )


@pytest.mark.parametrize(
    ("_name", "axioms"),
    _interaction_cases(),
    ids=lambda value: value if isinstance(value, str) else None,
)
def test_rule_family_interactions_reach_root_unsatisfiability(
    _name: str,
    axioms: tuple[owl.AxiomNode, ...],
) -> None:
    assert not _satisfiable(axioms)


def test_key_merge_without_explicit_difference_remains_satisfiable() -> None:
    member = owl.Class(owl.IRI("urn:test:tableau:key-sat-member"))
    role = owl.ObjectProperty(owl.IRI("urn:test:tableau:key-sat-role"))
    first = owl.NamedIndividual(owl.IRI("urn:test:tableau:key-sat-first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:tableau:key-sat-second"))
    shared = owl.NamedIndividual(owl.IRI("urn:test:tableau:key-sat-shared"))
    assert _satisfiable(
        (
            owl.HasKey(member, owl.CanonicalSet((role,)), owl.CanonicalSet(())),
            owl.ClassAssertion(member, first),
            owl.ClassAssertion(member, second),
            owl.ObjectPropertyAssertion(role, first, shared),
            owl.ObjectPropertyAssertion(role, second, shared),
        )
    )
