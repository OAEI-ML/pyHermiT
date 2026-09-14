"""Public query answers remain exact across isolated native request sequences."""

from __future__ import annotations

from collections.abc import Callable
from functools import partial
from typing import cast

import pyowl_core as core
import pyowl_core.model as owl
import pytest

from pyhermit import Reasoner, ReasonerConfig
from pyhermit.backends import native_context
from pyhermit.config import BackendName
from pyhermit.exceptions import FeatureNotImplementedError
from pyhermit.services import checks

pytest.importorskip("pyhermit._native")

BASE = "urn:test:native-reuse#"
SOURCE = f"""Prefix(:=<{BASE}>) Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<urn:test:native-reuse>
 Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
 Declaration(ObjectProperty(:p)) Declaration(ObjectProperty(:q)) Declaration(DataProperty(:d))
 Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:c))
 SubClassOf(:A :B) DisjointClasses(:B :C) SubObjectPropertyOf(:p :q)
 SubClassOf(:A ObjectSomeValuesFrom(:p :B))
 ClassAssertion(:A :a) SameIndividual(:a :b) DifferentIndividuals(:a :c)
 ObjectPropertyAssertion(:p :a :c) DataPropertyAssertion(:d :a "known"^^xsd:string)
)""".encode()
A, B, C = (owl.Class(owl.IRI(BASE + name)) for name in ("A", "B", "C"))
P, Q = (owl.ObjectProperty(owl.IRI(BASE + name)) for name in ("p", "q"))
D = owl.DataProperty(owl.IRI(BASE + "d"))
LEFT, ALIAS, OTHER = (owl.NamedIndividual(owl.IRI(BASE + name)) for name in ("a", "b", "c"))
LITERAL = owl.Literal("known", owl.XSD_STRING)


def snapshot() -> core.OntologySnapshot:
    return core.load_snapshot(
        SOURCE,
        options=core.LoadOptions(
            backend=core.BackendPreference.NATIVE, imports=core.ImportPolicy.IGNORE
        ),
    )


def fresh_answer(operation: Callable[[Reasoner], bool]) -> bool:
    with Reasoner(snapshot(), config=ReasonerConfig(backend=BackendName.PYTHON)) as reasoner:
        return operation(reasoner)


def forbid_old_query_path(patch: pytest.MonkeyPatch) -> None:
    def forbidden(*args: object, **kwargs: object) -> object:
        raise AssertionError("strict native query entered an old overlay/compiler/domain scan")

    patch.setattr(Reasoner, "_temporary_encoded_check", forbidden)
    patch.setattr(Reasoner, "_temporary_check", forbidden)
    patch.setattr(checks, "normalize_query", forbidden)
    patch.setattr(checks, "compile_query_program", forbidden)
    patch.setattr(native_context._NativeDomainMapping, "__iter__", forbidden)


def expressions() -> tuple[owl.ClassExpression, ...]:
    return (
        owl.ObjectIntersectionOf(owl.CanonicalSet((A, owl.ObjectComplementOf(B)))),
        owl.ObjectIntersectionOf(owl.CanonicalSet((A, B))),
        owl.ObjectIntersectionOf(owl.CanonicalSet((A, C))),
        owl.ObjectOneOf(owl.CanonicalSet((LEFT, ALIAS))),
        owl.ObjectIntersectionOf(
            owl.CanonicalSet(
                (
                    owl.ObjectOneOf(owl.CanonicalSet((LEFT,))),
                    owl.ObjectOneOf(owl.CanonicalSet((OTHER,))),
                )
            )
        ),
        owl.ObjectSomeValuesFrom(Q, B),
        owl.ObjectIntersectionOf(owl.CanonicalSet((A, owl.DataHasValue(D, LITERAL)))),
        owl.ObjectIntersectionOf(
            owl.CanonicalSet(
                (
                    owl.ObjectOneOf(owl.CanonicalSet((LEFT,))),
                    owl.ObjectComplementOf(owl.DataHasValue(D, LITERAL)),
                )
            )
        ),
    )


def test_generic_satisfiability_matches_fresh_oracles_and_repeated_sequences(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    probes = expressions()
    expected = tuple(fresh_answer(partial(Reasoner.is_satisfiable, expression=e)) for e in probes)
    assert any(expected) and not all(expected)
    source = snapshot()
    with monkeypatch.context() as patch:
        forbid_old_query_path(patch)
        with Reasoner(source, config=ReasonerConfig(require_native_pipeline=True)) as reasoner:
            assert tuple(reasoner.is_satisfiable(e) for e in probes) == expected
            assert tuple(reasoner.is_satisfiable(probes[i]) for i in (1, 0, 1)) == (
                expected[1],
                expected[0],
                expected[1],
            )
            held = reasoner.class_hierarchy()
            saved_nodes = held.nodes
            assert tuple(reasoner.is_satisfiable(e) for e in reversed(probes)) == tuple(
                reversed(expected)
            )
            assert held.nodes == saved_nodes
            assert reasoner.is_consistent()
        assert held.nodes == saved_nodes


def test_complex_entailment_conjunctions_preserve_partition_and_order(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    axioms = (
        owl.ClassAssertion(
            owl.ObjectIntersectionOf(owl.CanonicalSet((B, owl.ObjectComplementOf(C)))), LEFT
        ),
        owl.ClassAssertion(
            owl.ObjectSomeValuesFrom(Q, owl.ObjectOneOf(owl.CanonicalSet((OTHER,)))), LEFT
        ),
        owl.ClassAssertion(owl.ObjectOneOf(owl.CanonicalSet((ALIAS,))), LEFT),
        owl.ClassAssertion(owl.DataHasValue(D, LITERAL), LEFT),
        owl.ClassAssertion(owl.ObjectIntersectionOf(owl.CanonicalSet((A, C))), OTHER),
    )
    expected = tuple(fresh_answer(partial(Reasoner.entails, axiom=a)) for a in axioms)
    assert expected[:4] == (True, True, True, True)
    assert expected[-1] is False
    source = snapshot()
    with monkeypatch.context() as patch:
        forbid_old_query_path(patch)
        with Reasoner(source, config=ReasonerConfig(require_native_pipeline=True)) as reasoner:
            assert tuple(reasoner.entails(a) for a in axioms) == expected
            for width in (1, 2, len(axioms)):
                for start in range(0, len(axioms), width):
                    part = axioms[start : start + width]
                    assert reasoner.entails_all(part) == all(expected[start : start + width])
            assert reasoner.entails_all(reversed(axioms)) is False
            assert reasoner.entails_all(axioms[:4]) is True
            assert reasoner.entails(axioms[-1]) is False
            assert reasoner.entails_all(axioms[:4]) is True
            assert reasoner.is_consistent()


def test_delta_answers_equal_independently_compiled_full_native_reductions(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # This oracle creates and parses a complete ontology containing each reduction;
    # it does not call the query compiler or reuse an optimized query session.
    probes = expressions()[:5]
    expected = []
    for expression in probes:
        source = snapshot()
        document = source.root
        witness = owl.AnonymousIndividual(b"q" * 32, b"independent-full-query")
        combined = core.OntologyDocument(
            ontology_id=document.ontology_id,
            document_iri=document.document_iri,
            direct_imports=document.direct_imports,
            ontology_annotations=owl.CanonicalSet(document.ontology_annotations),
            axioms=owl.CanonicalSet((*document.axioms, owl.ClassAssertion(expression, witness))),
            extension_components=owl.CanonicalSet(document.extension_components),
            provenance=document.provenance,
        )
        encoded = core.render_document(combined, format=core.DocumentFormat.FUNCTIONAL)
        full = core.load_snapshot(
            encoded,
            options=core.LoadOptions(
                backend=core.BackendPreference.NATIVE, imports=core.ImportPolicy.IGNORE
            ),
        )
        with Reasoner(full, config=ReasonerConfig(backend=BackendName.NATIVE)) as oracle:
            expected.append(oracle.is_consistent())
            diagnostics = oracle.diagnostics()
            assert diagnostics["ingestion_path"] == "encoded-native"
            assert diagnostics["native_query_delta_loads"] == 0
    with monkeypatch.context() as patch:
        forbid_old_query_path(patch)
        with Reasoner(snapshot(), config=ReasonerConfig(require_native_pipeline=True)) as reused:
            before = reused.diagnostics()
            actual = [reused.is_satisfiable(expression) for expression in probes]
            after = reused.diagnostics()
            assert actual == expected
            assert cast(int, after["native_query_delta_loads"]) > cast(
                int, before["native_query_delta_loads"]
            )
            assert (
                after["native_query_full_program_loads"]
                == before["native_query_full_program_loads"]
            )
            assert cast(int, after["native_query_local_rule_plans"]) > cast(
                int, before["native_query_local_rule_plans"]
            )
            assert cast(int, after["native_query_peak_local_records"]) > 0


def test_inverse_strategy_expansion_rejects_before_install_and_default_rebuilds(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    expression = owl.ObjectAllValuesFrom(owl.ObjectInverseOf(P), A)
    expected = fresh_answer(lambda reasoner: reasoner.is_satisfiable(expression))
    with Reasoner(snapshot(), config=ReasonerConfig(backend=BackendName.NATIVE)) as default:
        assert default.is_satisfiable(expression) == expected
    with monkeypatch.context() as patch:
        forbid_old_query_path(patch)
        with Reasoner(snapshot(), config=ReasonerConfig(require_native_pipeline=True)) as strict:
            strict.is_consistent()
            before = strict.diagnostics()
            with pytest.raises(FeatureNotImplementedError) as caught:
                strict.is_satisfiable(expression)
            assert caught.value.feature_id == "native_query_delta_ineligible"
            after = strict.diagnostics()
            assert cast(int, after["native_query_delta_loads"]) == cast(
                int, before["native_query_delta_loads"]
            )
            assert (
                after["native_query_full_program_loads"]
                == before["native_query_full_program_loads"]
            )
            assert strict.is_consistent()
            assert strict.is_satisfiable(owl.ObjectIntersectionOf(owl.CanonicalSet((A, B))))
