from __future__ import annotations

import dataclasses
import hashlib

import pyowl_core.model as owl
import pytest

from pyhermit.backends.protocol import BackendFactory, CompiledOntology, DeltaOutcome
from pyhermit.backends.python.session import (
    PythonBackendFactory,
    PythonBackendSession,
    combine_query_program,
)
from pyhermit.clauses import (
    ClauseProgram,
    CompiledDelta,
    CompiledQuery,
    DeltaCompatibility,
    SymbolKind,
    compile_normalized,
    compile_query_program,
)
from pyhermit.config import ReasonerConfig
from pyhermit.events import CancellationSource, ProgressEvent
from pyhermit.exceptions import (
    BackendMismatchError,
    DisposedReasonerError,
    ReasonerInterruptedError,
)
from pyhermit.normalize import NormalizedOntology, normalize_axioms, normalize_query

FINGERPRINT = "d5" * 32


@dataclasses.dataclass
class _Fingerprint:
    digest: bytes
    algorithm: str = "sha256"
    schema: int = 2

    @property
    def hex(self) -> str:
        return self.digest.hex()


def _permanent() -> tuple[NormalizedOntology, ClauseProgram, owl.Class, owl.NamedIndividual]:
    member = owl.Class(owl.IRI("urn:test:backend-session:member"))
    first = owl.NamedIndividual(owl.IRI("urn:test:backend-session:first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:backend-session:second"))
    normalized = normalize_axioms(
        (
            owl.ClassAssertion(member, first),
            owl.ClassAssertion(owl.ObjectComplementOf(member), second),
        ),
        logical_fingerprint=FINGERPRINT,
    )
    return normalized, compile_normalized(normalized), member, first


def _compiled(program: ClauseProgram) -> CompiledOntology:
    fingerprint = _Fingerprint(b"s" * 32)
    named = tuple(
        value.identifier
        for value in program.symbols.domain(SymbolKind.INDIVIDUAL).values
        if value.display.startswith("named_individual:")
    )
    return CompiledOntology(
        schema_version=1,
        ontology_fingerprint="5" * 64,
        source_structural_fingerprint=fingerprint,
        source_logical_fingerprint=fingerprint,
        source_signature_fingerprint=fingerprint,
        core_package_version="0.2.0",
        core_api_version=(0, 2),
        core_model_schema_version=2,
        core_wire_format_version=(1, 2),
        core_adapter_protocol_version=1,
        symbols=program.symbols,
        clauses=program.clauses,
        positive_facts=program.positive_facts,
        negative_facts=program.negative_facts,
        ground_disjunctions=program.ground_disjunctions,
        role_model=program.role_model,
        datatype_model=program.datatype_model,
        expressivity=program.expressivity,
        declared_entities=(),
        named_individuals=named,
        provenance=program.provenance,
    )


def _contradicting_query(
    normalized: NormalizedOntology,
    program: ClauseProgram,
    member: owl.Class,
    individual: owl.NamedIndividual,
) -> CompiledQuery:
    return compile_query_program(
        program,
        normalized,
        normalize_query(
            normalized,
            (owl.ClassAssertion(owl.ObjectComplementOf(member), individual),),
        ),
    )


def test_factory_satisfies_protocol_and_reports_complete_python_tableau() -> None:
    factory: BackendFactory = PythonBackendFactory()
    assert factory.info.name == "python"
    assert factory.info.accelerated is False
    assert "satisfiability" in factory.info.complete_features


def test_query_checks_are_isolated_and_preserve_permanent_canonical_bytes() -> None:
    normalized, program, member, individual = _permanent()
    query = _contradicting_query(normalized, program, member, individual)
    before = program.canonical_bytes()
    events: list[ProgressEvent] = []
    session = PythonBackendSession(
        _compiled(program),
        ReasonerConfig(progress=events.append),
        CancellationSource().token,
    )

    assert session.check().satisfiable
    assert not session.check(query).satisfiable
    assert session.check().satisfiable
    assert tuple(value.satisfiable for value in session.check_many((query, query))) == (
        False,
        False,
    )
    assert program.canonical_bytes() == before
    assert session.ontology_fingerprint == "5" * 64
    assert [value.kind for value in events].count("reasoning-completed") == 5
    assert all(value.operation_id.startswith("python-check-") for value in events)


def test_session_checks_do_not_reserialize_the_permanent_program(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    normalized, program, member, individual = _permanent()
    query = _contradicting_query(normalized, program, member, individual)
    session = PythonBackendSession(
        _compiled(program),
        ReasonerConfig(),
        CancellationSource().token,
    )

    def repeated_serialization(_program: ClauseProgram) -> bytes:
        raise AssertionError("session check repeated permanent canonical serialization")

    monkeypatch.setattr(ClauseProgram, "canonical_bytes", repeated_serialization)
    assert session.check().satisfiable
    assert not session.check(query).satisfiable


def test_branch_heavy_unsatisfiable_query_cannot_leak_choices_into_the_session() -> None:
    source_class = owl.Class(owl.IRI("urn:test:backend-session:branch-source"))
    first_choice = owl.Class(owl.IRI("urn:test:backend-session:branch-first"))
    second_choice = owl.Class(owl.IRI("urn:test:backend-session:branch-second"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:backend-session:branch-i"))
    normalized = normalize_axioms(
        (
            owl.SubClassOf(
                source_class,
                owl.ObjectUnionOf(owl.CanonicalSet((first_choice, second_choice))),
            ),
            owl.SubClassOf(first_choice, owl.OWL_NOTHING),
            owl.SubClassOf(second_choice, owl.OWL_NOTHING),
            owl.ClassAssertion(owl.OWL_THING, individual),
        ),
        logical_fingerprint=FINGERPRINT,
    )
    program = compile_normalized(normalized)
    query = compile_query_program(
        program,
        normalized,
        normalize_query(normalized, (owl.ClassAssertion(source_class, individual),)),
    )
    assert not query.requires_rebuild
    session = PythonBackendSession(
        _compiled(program),
        ReasonerConfig(),
        CancellationSource().token,
    )
    assert session.check().satisfiable
    result = session.check(query)
    assert not result.satisfiable
    assert result.statistics.branches >= 1
    assert result.statistics.backtracks >= 1
    assert session.check().satisfiable


def test_overlay_combination_is_deterministic_and_retains_provenance() -> None:
    normalized, program, member, individual = _permanent()
    query = _contradicting_query(normalized, program, member, individual)
    first = combine_query_program(program, query)
    second = combine_query_program(program, query)
    assert first.canonical_bytes() == second.canonical_bytes()
    assert len(first.negative_facts) > len(program.negative_facts)
    assert all(value.provenance_ids for value in first.clauses)
    assert all(value.provenance_ids for value in first.positive_facts + first.negative_facts)
    assert tuple(value.clause_id for value in first.clauses) == tuple(range(len(first.clauses)))


def test_query_hash_and_prefix_mismatches_fail_before_tableau_execution() -> None:
    normalized, program, member, individual = _permanent()
    query = _contradicting_query(normalized, program, member, individual)
    wrong_hash = dataclasses.replace(query, permanent_program_sha256="0" * 64)
    with pytest.raises(BackendMismatchError, match="different permanent ontology"):
        combine_query_program(program, wrong_hash)

    wrong_boundary = dataclasses.replace(
        query,
        first_local_predicate_id=query.first_local_predicate_id - 1,
    )
    with pytest.raises(BackendMismatchError, match="prefix boundary"):
        combine_query_program(program, wrong_boundary)


def test_rebuild_query_is_an_explicit_boundary_outcome() -> None:
    normalized, program, member, individual = _permanent()
    compiled = _contradicting_query(normalized, program, member, individual)
    rebuild = dataclasses.replace(
        compiled,
        requires_rebuild=True,
        program=None,
        reason="test full rebuild",
    )
    session = PythonBackendSession(
        _compiled(program),
        ReasonerConfig(),
        CancellationSource().token,
    )
    with pytest.raises(BackendMismatchError, match="temporary full rebuild"):
        session.check(rebuild)
    assert session.check().satisfiable


def test_interruption_cannot_publish_a_partial_answer_or_mutate_permanent_ir() -> None:
    _normalized, program, _member, _individual = _permanent()
    source = CancellationSource()
    session = PythonBackendSession(_compiled(program), ReasonerConfig(), source.token)
    before = program.canonical_bytes()
    source.interrupt("fault injection")
    with pytest.raises(ReasonerInterruptedError, match="fault injection"):
        session.check()
    assert program.canonical_bytes() == before


def test_delta_fallback_reset_and_idempotent_close_follow_backend_lifecycle() -> None:
    _normalized, program, _member, _individual = _permanent()
    session = PythonBackendSession(
        _compiled(program),
        ReasonerConfig(),
        CancellationSource().token,
    )
    digest = hashlib.sha256(program.canonical_bytes()).hexdigest()
    no_op = CompiledDelta(
        digest,
        digest,
        DeltaCompatibility.DECLARATION_ONLY,
        (),
        (),
    )
    rebuild = dataclasses.replace(no_op, result_program_sha256="f" * 64)
    assert session.apply_delta(no_op) is DeltaOutcome.APPLIED_INCREMENTALLY
    assert session.apply_delta(rebuild) is DeltaOutcome.REBUILD_REQUIRED
    session.reset_query_state()
    session.close()
    session.close()
    with pytest.raises(DisposedReasonerError):
        session.check()
    with pytest.raises(DisposedReasonerError):
        session.reset_query_state()
