from __future__ import annotations

import pyowl_core.model as owl
import pytest

import pyhermit.services.checks as checks_module
from pyhermit.clauses import compile_query_program
from pyhermit.config import FreshEntityPolicy
from pyhermit.exceptions import (
    FreshEntityError,
    InconsistentOntologyError,
    ReasonerTimeoutError,
)
from pyhermit.normalize import normalize_query
from pyhermit.services import QueryPlan


def test_consistency_satisfiability_subsumption_and_open_world(make_service) -> None:  # type: ignore[no-untyped-def]
    first = owl.Class(owl.IRI("urn:test:services:First"))
    second = owl.Class(owl.IRI("urn:test:services:Second"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:services:i"))
    harness = make_service(
        (
            owl.SubClassOf(first, second),
            owl.ClassAssertion(first, individual),
        )
    )
    service = harness.service

    assert service.is_consistent()
    assert service.is_satisfiable(first)
    assert not service.is_satisfiable(owl.OWL_NOTHING)
    assert service.is_subclass(first, second)
    assert not service.is_subclass(second, first)
    assert service.entails(owl.ClassAssertion(second, individual))
    assert not service.entails(owl.ClassAssertion(owl.ObjectComplementOf(second), individual))


def test_inconsistent_policy_and_empty_conjunction(make_service) -> None:  # type: ignore[no-untyped-def]
    cls = owl.Class(owl.IRI("urn:test:services:Contradiction"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:services:i"))
    service = make_service(
        (
            owl.ClassAssertion(cls, individual),
            owl.ClassAssertion(owl.ObjectComplementOf(cls), individual),
        )
    ).service

    assert not service.is_consistent()
    assert service.entails_all(())
    with pytest.raises(InconsistentOntologyError):
        service.is_satisfiable(cls)
    with pytest.raises(InconsistentOntologyError):
        service.entails(owl.ClassAssertion(cls, individual))


def test_entails_all_snapshots_one_shot_iterable_before_backend_work(make_service) -> None:  # type: ignore[no-untyped-def]
    cls = owl.Class(owl.IRI("urn:test:services:Snapshot"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:services:i"))
    harness = make_service((owl.ClassAssertion(cls, individual),))

    def broken():  # type: ignore[no-untyped-def]
        yield owl.ClassAssertion(cls, individual)
        raise RuntimeError("iteration failed")

    with pytest.raises(RuntimeError, match="iteration failed"):
        harness.service.entails_all(broken())
    assert harness.temporary_queries == []


def test_fresh_entity_policy_and_defined_signature(make_service) -> None:  # type: ignore[no-untyped-def]
    known = owl.Class(owl.IRI("urn:test:services:Known"))
    fresh = owl.Class(owl.IRI("urn:test:services:Fresh"))
    service = make_service(
        (owl.Declaration(known),),
        fresh_entities=FreshEntityPolicy.DISALLOW,
    ).service

    assert service.is_defined(known)
    assert service.is_defined(owl.OWL_THING)
    assert not service.is_defined(fresh)
    with pytest.raises(FreshEntityError, match="Fresh"):
        service.is_satisfiable(fresh)


def test_builtins_and_negative_assertions_preserve_open_world_semantics(make_service) -> None:  # type: ignore[no-untyped-def]
    role = owl.ObjectProperty(owl.IRI("urn:test:services:role"))
    first = owl.NamedIndividual(owl.IRI("urn:test:services:first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:services:second"))
    service = make_service().service

    assert service.entails(owl.ObjectPropertyAssertion(owl.OWL_TOP_OBJECT_PROPERTY, first, second))
    assert service.entails(
        owl.NegativeObjectPropertyAssertion(owl.OWL_BOTTOM_OBJECT_PROPERTY, first, second)
    )
    assert not service.entails(owl.ObjectPropertyAssertion(role, first, second))
    assert not service.entails(owl.NegativeObjectPropertyAssertion(role, first, second))


def test_fast_and_forced_reduction_paths_agree(make_service) -> None:  # type: ignore[no-untyped-def]
    first = owl.Class(owl.IRI("urn:test:services:First"))
    second = owl.Class(owl.IRI("urn:test:services:Second"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:services:i"))
    axioms = (
        owl.SubClassOf(first, second),
        owl.ClassAssertion(first, individual),
    )
    queries = (
        owl.SubClassOf(first, second),
        owl.SubClassOf(second, first),
        owl.ClassAssertion(first, individual),
        owl.ClassAssertion(second, individual),
    )
    fast = make_service(axioms).service
    slow = make_service(axioms, force_reductions=True).service

    assert tuple(fast.entails(value) for value in queries) == tuple(
        slow.entails(value) for value in queries
    )


def test_query_compilation_is_cached_without_reserializing_permanent_program(
    make_service,  # type: ignore[no-untyped-def]
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cls = owl.Class(owl.IRI("urn:test:services:Cached"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:services:i"))
    harness = make_service((owl.ClassAssertion(cls, individual),), force_reductions=True)
    executor = harness.service._executor
    plan = QueryPlan(
        (owl.ClassAssertion(owl.ObjectComplementOf(cls), individual),),
        ("cache-probe",),
    )
    calls = 0
    original = checks_module.normalize_query

    def counted(*args, **kwargs):  # type: ignore[no-untyped-def]
        nonlocal calls
        calls += 1
        return original(*args, **kwargs)

    monkeypatch.setattr(checks_module, "normalize_query", counted)
    monkeypatch.setattr(
        type(harness.program),
        "canonical_bytes",
        lambda _self: (_ for _ in ()).throw(AssertionError("permanent program reserialized")),
    )
    assert not executor.check(plan).satisfiable
    assert not executor.check(plan).satisfiable
    assert calls == 1


def test_reusable_query_context_is_canonically_equal_and_shares_validated_prefix(
    make_service,  # type: ignore[no-untyped-def]
) -> None:
    first = owl.Class(owl.IRI("urn:test:services:ContextFirst"))
    second = owl.Class(owl.IRI("urn:test:services:ContextSecond"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:services:context-i"))
    harness = make_service(
        (
            owl.SubClassOf(first, second),
            owl.ClassAssertion(first, individual),
        ),
        force_reductions=True,
    )
    executor = harness.service._executor
    query = normalize_query(
        executor.normalized,
        (owl.ClassAssertion(second, individual),),
    )

    standalone = compile_query_program(harness.program, executor.normalized, query)
    optimized = compile_query_program(
        harness.program,
        executor.normalized,
        query,
        permanent_program_sha256=executor.permanent_program_sha256,
        verify_immutable=False,
        query_context=executor._query_context,
    )

    assert optimized.canonical_bytes() == standalone.canonical_bytes()
    assert optimized.program is not None
    cutoff = optimized.first_local_predicate_id
    assert all(
        retained is permanent
        for retained, permanent in zip(
            optimized.program.predicates.predicates[:cutoff],
            harness.program.predicates.predicates,
            strict=True,
        )
    )


def test_temporary_failures_are_never_recoded_as_false(make_service) -> None:  # type: ignore[no-untyped-def]
    first = owl.NamedIndividual(owl.IRI("urn:test:services:first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:services:second"))
    timeout = ReasonerTimeoutError("deadline expired")
    service = make_service(temporary_error=timeout, force_reductions=True).service
    query = owl.SameIndividual(owl.CanonicalSet((first, second)))

    with pytest.raises(ReasonerTimeoutError, match="deadline expired"):
        service.entails(query)
