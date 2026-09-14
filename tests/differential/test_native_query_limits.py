"""Actual native batch rejection does not publish prefixes or bypass resource limits."""

from __future__ import annotations

import json
from collections.abc import Iterator

import pyowl_core.model as owl
import pytest
from tests.differential.test_native_query_reuse import LEFT, A, C, P, Q, snapshot

from pyhermit import Reasoner, ReasonerConfig
from pyhermit.backends.native import NativeBackendSession
from pyhermit.backends.native_queries import serialize_query
from pyhermit.exceptions import FeatureNotImplementedError, ResourceLimitError
from pyhermit.services.checks import EncodedQueryExecutor, QueryPlan


def test_native_batch_failure_does_not_publish_a_successful_prefix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("strict query failure reached a full rebuild")

    monkeypatch.setattr(Reasoner, "_temporary_encoded_check", forbidden)
    with Reasoner(snapshot(), config=ReasonerConfig(require_native_pipeline=True)) as reasoner:
        executor = reasoner._runtime.executor
        first = QueryPlan(
            (owl.ClassAssertion(owl.ObjectIntersectionOf(owl.CanonicalSet((A, C))), LEFT),)
        )
        unsupported = QueryPlan(
            (owl.ClassAssertion(owl.ObjectAllValuesFrom(P, owl.ObjectSomeValuesFrom(Q, A)), LEFT),)
        )
        assert reasoner.is_consistent()
        before = reasoner.diagnostics()["native_query_delta_loads"]
        assert isinstance(before, int)
        with pytest.raises(FeatureNotImplementedError, match="nested existential"):
            executor.check_many((first, unsupported))
        failed = reasoner.diagnostics()["native_query_delta_loads"]
        assert isinstance(failed, int)
        assert failed == before + 1
        assert not executor.check(first).satisfiable
        assert reasoner.diagnostics()["native_query_delta_loads"] == failed + 1
        assert reasoner.is_consistent()
        assert reasoner.diagnostics()["native_query_fallback_rebuilds"] == 0


def test_query_iterator_is_bounded_before_native_work() -> None:
    with Reasoner(snapshot(), config=ReasonerConfig(require_native_pipeline=True)) as reasoner:
        count = 0
        plan = QueryPlan((owl.ClassAssertion(A, LEFT),))

        def endless() -> Iterator[QueryPlan]:
            nonlocal count
            while True:
                count += 1
                yield plan

        with pytest.raises(ResourceLimitError, match="item limit"):
            reasoner._runtime.executor.check_many(endless())
        assert count == 4097
        assert reasoner.diagnostics()["native_query_delta_loads"] == 0
        assert reasoner.is_consistent()


def test_native_byte_and_local_domain_limits_preserve_the_session() -> None:
    with Reasoner(snapshot(), config=ReasonerConfig(require_native_pipeline=True)) as reasoner:
        session = reasoner._runtime.session
        assert isinstance(session, NativeBackendSession)
        call = session.check_assertions_many
        with pytest.raises(ResourceLimitError):
            call((b" " * (1024 * 1024 + 1),))
        with pytest.raises(ResourceLimitError):
            call((b" " * (1024 * 1024),) * 17)
        executor = reasoner._runtime.executor
        assert isinstance(executor, EncodedQueryExecutor)
        context = executor.service_context
        request = json.loads(serialize_query((owl.ClassAssertion(A, LEFT),), context))
        request["individual_count"] = 65_537
        with pytest.raises(ResourceLimitError, match="local domain"):
            call((json.dumps(request).encode(),))
        assert reasoner.diagnostics()["native_query_delta_loads"] == 0
        assert reasoner.diagnostics()["native_query_fallback_rebuilds"] == 0
        assert reasoner.is_consistent()


def test_public_entailment_iterator_and_reduction_fanout_are_bounded() -> None:
    with Reasoner(snapshot(), config=ReasonerConfig(require_native_pipeline=True)) as reasoner:
        count = 0
        axiom = owl.ClassAssertion(A, LEFT)

        def endless() -> Iterator[owl.LogicalAxiom]:
            nonlocal count
            while True:
                count += 1
                yield axiom

        with pytest.raises(ResourceLimitError, match="item limit"):
            reasoner.entails_all(endless())
        assert count == 4097
        classes = tuple(owl.Class(owl.IRI(f"urn:query:local:{i}")) for i in range(100))
        with pytest.raises(ResourceLimitError, match="plan limit"):
            reasoner.entails(owl.DisjointClasses(owl.CanonicalSet(classes)))
        assert reasoner.diagnostics()["native_query_delta_loads"] == 0


def test_actual_query_local_work_is_independent_of_unrelated_base_growth() -> None:
    import pyowl_core as core

    measured = []
    for unrelated in (4, 128):
        extra = " ".join(
            f"SubClassOf(<urn:unrelated:{i}> <urn:unrelated:{i + 1}>)" for i in range(unrelated)
        )
        declarations = " ".join(
            f"Declaration(Class(<urn:unrelated:{i}>))" for i in range(unrelated + 1)
        )
        source = core.load_snapshot(
            (
                "Ontology(<urn:query-growth> Declaration(Class(<urn:base:A>)) "
                "Declaration(Class(<urn:base:B>)) SubClassOf(<urn:base:A> <urn:base:B>) "
                + declarations
                + " "
                + extra
                + ")"
            ).encode(),
            options=core.LoadOptions(backend=core.BackendPreference.NATIVE),
        )
        a = owl.Class(owl.IRI("urn:base:A"))
        b = owl.Class(owl.IRI("urn:base:B"))
        expression = owl.ObjectIntersectionOf(owl.CanonicalSet((a, owl.ObjectComplementOf(b))))
        with Reasoner(source, config=ReasonerConfig(require_native_pipeline=True)) as reasoner:
            assert not reasoner.is_satisfiable(expression)
            report = reasoner.diagnostics()
            assert report["native_query_delta_loads"] == 1
            assert report["native_query_full_program_loads"] == 0
            assert report["native_query_fallback_rebuilds"] == 0
            plans = report["native_query_local_rule_plans"]
            assert isinstance(plans, int) and plans > 0
            measured.append((plans, report["native_query_peak_local_records"]))
    assert measured[0] == measured[1]
