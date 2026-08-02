from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass, field

import pyowl_core.model as owl
import pytest

from pyhermit.backends.protocol import CheckResult, CompiledOntology
from pyhermit.backends.python.session import PythonBackendSession
from pyhermit.backends.python.tableau import PythonTableau
from pyhermit.clauses import ClauseProgram, SymbolKind, compile_normalized
from pyhermit.config import FreshEntityPolicy, ReasonerConfig
from pyhermit.events import CancellationSource
from pyhermit.normalize import normalize_axioms
from pyhermit.services import CompiledQueryExecutor, EntailmentService


@dataclass(frozen=True, slots=True)
class _Fingerprint:
    digest: bytes
    algorithm: str = "sha256"
    schema: int = 2

    @property
    def hex(self) -> str:
        return self.digest.hex()


def _compiled(program: ClauseProgram) -> CompiledOntology:
    fingerprint = _Fingerprint(b"e" * 32)
    named = tuple(
        value.identifier
        for value in program.symbols.domain(SymbolKind.INDIVIDUAL).values
        if value.display.startswith("named_individual:")
    )
    return CompiledOntology(
        schema_version=1,
        ontology_fingerprint="e" * 64,
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


@dataclass(slots=True)
class ServiceHarness:
    service: EntailmentService
    program: ClauseProgram
    session: PythonBackendSession
    temporary_queries: list[tuple[owl.AxiomNode, ...]] = field(default_factory=list)


@pytest.fixture
def make_service():  # type: ignore[no-untyped-def]
    def make(
        axioms: Iterable[owl.AxiomNode] = (),
        *,
        force_reductions: bool = False,
        fresh_entities: FreshEntityPolicy = FreshEntityPolicy.ALLOW,
        temporary_error: Exception | None = None,
    ) -> ServiceHarness:
        source = tuple(axioms)
        fingerprint = owl.structural_hexdigest(
            owl.EquivalentClasses(
                owl.CanonicalSet(
                    (
                        owl.Class(owl.IRI("urn:test:entailment:fingerprint-a")),
                        owl.Class(owl.IRI("urn:test:entailment:fingerprint-b")),
                    )
                )
            )
        )
        normalized = normalize_axioms(source, logical_fingerprint=fingerprint)
        program = compile_normalized(normalized)
        config = ReasonerConfig()
        cancellation = CancellationSource().token
        session = PythonBackendSession(_compiled(program), config, cancellation)
        temporary_queries: list[tuple[owl.AxiomNode, ...]] = []

        def temporary(extra: tuple[owl.AxiomNode, ...]) -> CheckResult:
            temporary_queries.append(extra)
            if temporary_error is not None:
                raise temporary_error
            full = normalize_axioms(
                source + extra,
                logical_fingerprint="f0" * 32,
            )
            tableau = PythonTableau(compile_normalized(full), config, cancellation)
            return CheckResult(tableau.run(cancellation).satisfiable)

        executor = CompiledQueryExecutor(
            normalized,
            program,
            session,
            temporary_check=temporary,
        )
        service = EntailmentService(
            executor,
            fresh_entities=fresh_entities,
            force_reductions=force_reductions,
        )
        return ServiceHarness(service, program, session, temporary_queries)

    return make
