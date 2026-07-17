from __future__ import annotations

from collections.abc import Iterable

import pyowl_core.model as owl

from pyhermit.backends.python.state import NodeLifecycle
from pyhermit.backends.python.tableau import PythonTableau
from pyhermit.clauses import PredicateKind, SymbolKind, compile_normalized
from pyhermit.config import BlockingMode, ExistentialMode, ReasonerConfig
from pyhermit.datatypes import XSD_INTEGER
from pyhermit.events import CancellationSource
from pyhermit.normalize import normalize_axioms

FINGERPRINT = "c4" * 32


def _tableau(
    axioms: Iterable[owl.AxiomNode],
    *,
    config: ReasonerConfig | None = None,
) -> PythonTableau:
    program = compile_normalized(normalize_axioms(tuple(axioms), logical_fingerprint=FINGERPRINT))
    token = CancellationSource().token
    return PythonTableau(program, config or ReasonerConfig(), token)


def test_empty_and_deterministic_horn_ontologies_reach_sat_fixed_points() -> None:
    empty = _tableau(())
    assert empty.run(CancellationSource().token).satisfiable
    assert len(empty.session.nodes.active_handles()) == 1

    source = owl.Class(owl.IRI("urn:test:tableau:horn-source"))
    target = owl.Class(owl.IRI("urn:test:tableau:horn-target"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:tableau:horn-i"))
    tableau = _tableau(
        (
            owl.SubClassOf(source, target),
            owl.ClassAssertion(source, individual),
        )
    )
    result = tableau.run(CancellationSource().token)
    assert result.satisfiable
    target_symbol = next(
        value.identifier
        for value in tableau.program.symbols.domain(SymbolKind.CLASS_EXPRESSION).values
        if value.display == f"class:{target.iri.value}"
    )
    target_predicate = next(
        value.predicate_id
        for value in tableau.program.predicates.predicates
        if value.kind is PredicateKind.CONCEPT and value.symbol_id == target_symbol
    )
    assert tuple(tableau.session.extensions.retrieve(target_predicate))


def test_positive_negative_concept_clash_is_unsatisfiable() -> None:
    source = owl.Class(owl.IRI("urn:test:tableau:clash-source"))
    target = owl.Class(owl.IRI("urn:test:tableau:clash-target"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:tableau:clash-i"))
    tableau = _tableau(
        (
            owl.SubClassOf(source, target),
            owl.SubClassOf(source, owl.ObjectComplementOf(target)),
            owl.ClassAssertion(source, individual),
        )
    )
    assert not tableau.run(CancellationSource().token).satisfiable


def test_cyclic_existential_terminates_by_anywhere_blocking() -> None:
    member = owl.Class(owl.IRI("urn:test:tableau:cycle-member"))
    role = owl.ObjectProperty(owl.IRI("urn:test:tableau:cycle-role"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:tableau:cycle-i"))
    tableau = _tableau(
        (
            owl.SubClassOf(member, owl.ObjectSomeValuesFrom(role, member)),
            owl.ClassAssertion(member, individual),
        )
    )
    result = tableau.run(CancellationSource().token)
    assert result.satisfiable
    active = tuple(
        value
        for value in tableau.session.nodes.existing_nodes()
        if value.lifecycle is NodeLifecycle.ACTIVE
    )
    assert len(active) <= 4
    assert any(value.blocker is not None for value in active)


def test_disjunction_clash_backtracks_to_the_satisfiable_choice() -> None:
    source = owl.Class(owl.IRI("urn:test:tableau:branch-source"))
    bad = owl.Class(owl.IRI("urn:test:tableau:branch-0-bad"))
    good = owl.Class(owl.IRI("urn:test:tableau:branch-1-good"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:tableau:branch-i"))
    tableau = _tableau(
        (
            owl.SubClassOf(
                source,
                owl.ObjectUnionOf(owl.CanonicalSet((bad, good))),
            ),
            owl.SubClassOf(bad, owl.OWL_NOTHING),
            owl.ClassAssertion(source, individual),
        )
    )
    result = tableau.run(CancellationSource().token)
    assert result.satisfiable
    assert result.statistics.disjunction_actions >= 1


def test_object_max_cardinality_and_explicit_difference_are_unsatisfiable() -> None:
    member = owl.Class(owl.IRI("urn:test:tableau:max-member"))
    filler = owl.Class(owl.IRI("urn:test:tableau:max-filler"))
    role = owl.ObjectProperty(owl.IRI("urn:test:tableau:max-role"))
    root = owl.NamedIndividual(owl.IRI("urn:test:tableau:max-root"))
    first = owl.NamedIndividual(owl.IRI("urn:test:tableau:max-first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:tableau:max-second"))
    tableau = _tableau(
        (
            owl.SubClassOf(member, owl.ObjectMaxCardinality(1, role, filler)),
            owl.ClassAssertion(member, root),
            owl.ObjectPropertyAssertion(role, root, first),
            owl.ObjectPropertyAssertion(role, root, second),
            owl.ClassAssertion(filler, first),
            owl.ClassAssertion(filler, second),
            owl.DifferentIndividuals(owl.CanonicalSet((first, second))),
        )
    )
    assert not tableau.run(CancellationSource().token).satisfiable


def test_datatype_range_checks_fixed_values() -> None:
    role = owl.DataProperty(owl.IRI("urn:test:tableau:data-role"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:tableau:data-i"))
    valid = _tableau(
        (
            owl.DataPropertyRange(role, owl.XSD_STRING),
            owl.DataPropertyAssertion(
                role,
                individual,
                owl.Literal("valid", owl.XSD_STRING),
            ),
        )
    )
    assert valid.run(CancellationSource().token).satisfiable

    invalid = _tableau(
        (
            owl.DataPropertyRange(role, owl.XSD_STRING),
            owl.DataPropertyAssertion(
                role,
                individual,
                owl.Literal("1", owl.Datatype(owl.IRI(XSD_INTEGER))),
            ),
        )
    )
    assert not invalid.run(CancellationSource().token).satisfiable


def test_individual_reuse_and_creation_order_have_identical_sat_results() -> None:
    source = owl.Class(owl.IRI("urn:test:tableau:reuse-source"))
    filler = owl.Class(owl.IRI("urn:test:tableau:reuse-filler"))
    role = owl.ObjectProperty(owl.IRI("urn:test:tableau:reuse-role"))
    first = owl.NamedIndividual(owl.IRI("urn:test:tableau:reuse-first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:tableau:reuse-second"))
    axioms = (
        owl.SubClassOf(source, owl.ObjectSomeValuesFrom(role, filler)),
        owl.ClassAssertion(source, first),
        owl.ClassAssertion(source, second),
    )
    creation = _tableau(axioms)
    reuse = _tableau(
        axioms,
        config=ReasonerConfig(existentials=ExistentialMode.INDIVIDUAL_REUSE),
    )
    assert creation.run(CancellationSource().token).satisfiable
    assert reuse.run(CancellationSource().token).satisfiable
    assert len(reuse.session.nodes.active_handles()) < len(creation.session.nodes.active_handles())


def test_every_blocking_mode_agrees_and_validated_mode_reaches_a_checked_fixed_point() -> None:
    member = owl.Class(owl.IRI("urn:test:tableau:blocking-mode-member"))
    role = owl.ObjectProperty(owl.IRI("urn:test:tableau:blocking-mode-role"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:tableau:blocking-mode-i"))
    axioms = (
        owl.SubClassOf(member, owl.ObjectSomeValuesFrom(role, member)),
        owl.ClassAssertion(member, individual),
    )
    results: dict[BlockingMode, bool] = {}
    for mode in BlockingMode:
        tableau = _tableau(axioms, config=ReasonerConfig(blocking=mode))
        results[mode] = tableau.run(CancellationSource().token).satisfiable
        assert tableau.blocking.ready_for_sat()
    assert set(results.values()) == {True}


def test_source_inverse_usage_selects_pairwise_but_internal_inverse_closure_does_not() -> None:
    member = owl.Class(owl.IRI("urn:test:tableau:blocking-selection-member"))
    role = owl.ObjectProperty(owl.IRI("urn:test:tableau:blocking-selection-role"))
    forward = _tableau((owl.SubClassOf(member, owl.ObjectSomeValuesFrom(role, member)),))
    inverse = _tableau(
        (
            owl.SubClassOf(
                member,
                owl.ObjectSomeValuesFrom(owl.ObjectInverseOf(role), member),
            ),
        )
    )
    assert forward.blocking.checker.kind.value == "single"
    assert inverse.blocking.checker.kind.value == "pairwise"
