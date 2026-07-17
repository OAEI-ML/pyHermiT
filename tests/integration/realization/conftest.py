from __future__ import annotations

from collections.abc import Callable, Iterable
from dataclasses import dataclass, field
from typing import cast

import pyowl_core.model as owl
import pytest

from pyhermit.backends.protocol import CheckResult, CompiledOntology
from pyhermit.backends.python.session import PythonBackendSession
from pyhermit.backends.python.tableau import PythonTableau
from pyhermit.clauses import ClauseProgram, SymbolKind, compile_normalized
from pyhermit.config import ReasonerConfig
from pyhermit.events import CancellationSource
from pyhermit.normalize import normalize_axioms
from pyhermit.services import (
    ClassificationService,
    CompiledQueryExecutor,
    EntailmentService,
    TemporaryQueryChecker,
)
from pyhermit.services.realization import RealizationService


@dataclass(slots=True)
class _Fingerprint:
    digest: bytes
    algorithm: str = "sha256"
    schema: int = 1

    @property
    def hex(self) -> str:
        return self.digest.hex()


def _compiled(program: ClauseProgram) -> CompiledOntology:
    fingerprint = _Fingerprint(b"r" * 32)
    named = tuple(
        value.identifier
        for value in program.symbols.domain(SymbolKind.INDIVIDUAL).values
        if value.display.startswith("named_individual:")
    )
    return CompiledOntology(
        schema_version=1,
        ontology_fingerprint="d" * 64,
        source_structural_fingerprint=fingerprint,
        source_logical_fingerprint=fingerprint,
        source_signature_fingerprint=fingerprint,
        core_package_version="0.1.0",
        core_api_version=(0, 1),
        core_model_schema_version=1,
        core_wire_format_version=(1, 0),
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
class RealizationHarness:
    realization: RealizationService
    classification: ClassificationService
    entailment: EntailmentService
    temporary_queries: list[tuple[owl.AxiomNode, ...]] = field(default_factory=list)


@pytest.fixture
def make_realization() -> Callable[..., RealizationHarness]:
    def make(
        axioms: Iterable[owl.AxiomNode] = (),
        *,
        config: ReasonerConfig | None = None,
        cancelled: Callable[[], bool] | None = None,
    ) -> RealizationHarness:
        source = tuple(axioms)
        normalized = normalize_axioms(source, logical_fingerprint="d1" * 32)
        program = compile_normalized(normalized)
        selected_config = ReasonerConfig() if config is None else config
        token = CancellationSource().token
        session = PythonBackendSession(_compiled(program), selected_config, token)
        temporary_queries: list[tuple[owl.AxiomNode, ...]] = []

        def temporary(extra: tuple[owl.AxiomNode, ...]) -> CheckResult:
            temporary_queries.append(extra)
            full = normalize_axioms(source + extra, logical_fingerprint="d2" * 32)
            tableau = PythonTableau(compile_normalized(full), selected_config, token)
            return CheckResult(tableau.run(token).satisfiable)

        executor = CompiledQueryExecutor(
            normalized,
            program,
            session,
            temporary_check=cast(TemporaryQueryChecker, temporary),
            cancelled=cancelled,
        )
        entailment = EntailmentService(
            executor,
            fresh_entities=selected_config.fresh_entities,
        )
        classification = ClassificationService(
            entailment,
            config=selected_config,
            cancelled=cancelled,
        )
        realization = RealizationService(
            entailment,
            classification,
            config=selected_config,
            cancelled=cancelled,
        )
        return RealizationHarness(
            realization,
            classification,
            entailment,
            temporary_queries,
        )

    return make
