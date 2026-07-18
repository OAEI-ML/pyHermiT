"""Isolated backend sessions over the complete pure-Python tableau.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import hashlib
import json
import time
from collections.abc import Sequence
from typing import TypeAlias, TypeVar

from pyhermit import __version__
from pyhermit.backends.protocol import (
    COMPILED_IR_SCHEMA_VERSION,
    BackendInfo,
    CheckResult,
    CompiledOntology,
    DeltaOutcome,
    HierarchyIds,
    RealizationIds,
    ReasoningStatistics,
)
from pyhermit.clauses import (
    Atom,
    ClauseProgram,
    CompiledDelta,
    CompiledQuery,
    DataConstant,
    DatatypeModelIR,
    DLClause,
    Expressivity,
    GroundAtom,
    GroundDisjunctionIR,
    IndividualTerm,
    PredicateRegistry,
    ProvenanceEntry,
    ProvenanceTable,
    RoleModelIR,
    SymbolKind,
    SymbolTable,
)
from pyhermit.config import ReasonerConfig
from pyhermit.core import CoreVersionInfo, current_core_versions, require_core_compatibility
from pyhermit.events import CancellationToken, ProgressEvent
from pyhermit.exceptions import (
    BackendMismatchError,
    DisposedReasonerError,
    FeatureNotImplementedError,
)

from .state import NodeLifecycle
from .tableau import PythonTableau

_GroundTerm: TypeAlias = IndividualTerm | DataConstant
_FactIdentity: TypeAlias = tuple[int, tuple[_GroundTerm, ...]]
_ClauseIdentity: TypeAlias = tuple[tuple[Atom, ...], tuple[Atom, ...], tuple[int, ...]]
_RecordT = TypeVar("_RecordT")


def clause_program_from_compiled(ontology: CompiledOntology) -> ClauseProgram:
    """Recover the one concrete private program carried by a compiled envelope."""

    if not isinstance(ontology, CompiledOntology):
        raise TypeError("ontology must be CompiledOntology")
    if not isinstance(ontology.symbols, SymbolTable):
        raise BackendMismatchError("compiled ontology has no concrete SymbolTable")
    predicates = ontology.symbols.predicates
    if not isinstance(predicates, PredicateRegistry):
        raise BackendMismatchError("compiled ontology SymbolTable has no predicate registry")
    clauses = _concrete_tuple(ontology.clauses, DLClause, "clauses")
    positive = _concrete_tuple(ontology.positive_facts, GroundAtom, "positive facts")
    negative = _concrete_tuple(ontology.negative_facts, GroundAtom, "negative facts")
    disjunctions = _concrete_tuple(
        ontology.ground_disjunctions,
        GroundDisjunctionIR,
        "ground disjunctions",
    )
    if not isinstance(ontology.role_model, RoleModelIR):
        raise BackendMismatchError("compiled ontology has no concrete role model")
    if not isinstance(ontology.datatype_model, DatatypeModelIR):
        raise BackendMismatchError("compiled ontology has no concrete datatype model")
    if not isinstance(ontology.expressivity, Expressivity):
        raise BackendMismatchError("compiled ontology has no concrete expressivity record")
    if not isinstance(ontology.provenance, ProvenanceTable):
        raise BackendMismatchError("compiled ontology has no concrete provenance table")
    return ClauseProgram(
        symbols=ontology.symbols,
        predicates=predicates,
        clauses=clauses,
        positive_facts=positive,
        negative_facts=negative,
        ground_disjunctions=disjunctions,
        role_model=ontology.role_model,
        datatype_model=ontology.datatype_model,
        expressivity=ontology.expressivity,
        provenance=ontology.provenance,
    )


def combine_query_program(permanent: ClauseProgram, query: CompiledQuery) -> ClauseProgram:
    """Combine a prefix-compatible query overlay without mutating either input."""

    if not isinstance(permanent, ClauseProgram):
        raise TypeError("permanent must be ClauseProgram")
    if not isinstance(query, CompiledQuery):
        raise TypeError("query must be the concrete clauses.CompiledQuery")
    expected = hashlib.sha256(permanent.canonical_bytes()).hexdigest()
    return _combine_query_program(permanent, query, expected)


def _combine_query_program(
    permanent: ClauseProgram,
    query: CompiledQuery,
    permanent_sha256: str,
) -> ClauseProgram:
    expected = permanent_sha256
    if query.permanent_program_sha256 != expected:
        raise BackendMismatchError(
            "compiled query belongs to a different permanent ontology",
            context={
                "actual": query.permanent_program_sha256,
                "expected": expected,
            },
        )
    if query.requires_rebuild:
        raise BackendMismatchError(
            "compiled query requires a temporary full rebuild before backend execution",
            context={"query_hash": query.query_hash, "reason": query.reason},
        )
    overlay = query.program
    if overlay is None:
        raise BackendMismatchError("incremental compiled query has no overlay program")
    _validate_overlay_prefix(permanent, overlay, query)

    provenance, permanent_ids, overlay_ids = _merge_provenance(
        permanent.provenance,
        overlay.provenance,
    )
    clauses = _merge_clauses(((permanent.clauses, permanent_ids), (overlay.clauses, overlay_ids)))
    positive = _merge_facts(
        ((permanent.positive_facts, permanent_ids), (overlay.positive_facts, overlay_ids))
    )
    negative = _merge_facts(
        ((permanent.negative_facts, permanent_ids), (overlay.negative_facts, overlay_ids))
    )
    disjunctions = _merge_disjunctions(
        (
            (permanent.ground_disjunctions, permanent_ids),
            (overlay.ground_disjunctions, overlay_ids),
        )
    )
    return ClauseProgram(
        symbols=overlay.symbols,
        predicates=overlay.predicates,
        clauses=clauses,
        positive_facts=positive,
        negative_facts=negative,
        ground_disjunctions=disjunctions,
        role_model=overlay.role_model,
        datatype_model=overlay.datatype_model,
        expressivity=overlay.expressivity,
        provenance=provenance,
    )


class PythonBackendSession:
    """Reusable control plane whose individual tableau runs are fully isolated."""

    __slots__ = (
        "_cancellation",
        "_closed",
        "_config",
        "_fingerprint",
        "_last_tableau",
        "_operation_sequence",
        "_permanent",
        "_permanent_sha256",
    )

    def __init__(
        self,
        ontology: CompiledOntology,
        config: ReasonerConfig,
        cancellation: CancellationToken,
    ) -> None:
        if not isinstance(ontology, CompiledOntology):
            raise TypeError("ontology must be CompiledOntology")
        if not isinstance(config, ReasonerConfig):
            raise TypeError("config must be ReasonerConfig")
        if not isinstance(cancellation, CancellationToken):
            raise TypeError("cancellation must be CancellationToken")
        _validate_core_envelope(ontology)
        cancellation.check()
        permanent = clause_program_from_compiled(ontology)
        self._permanent = permanent
        self._permanent_sha256 = hashlib.sha256(permanent.canonical_bytes()).hexdigest()
        self._fingerprint = ontology.ontology_fingerprint
        self._config = config
        self._cancellation = cancellation
        self._last_tableau: PythonTableau | None = None
        self._operation_sequence = 0
        self._closed = False

    @property
    def ontology_fingerprint(self) -> str:
        self._require_open()
        return self._fingerprint

    def check(self, query: object = None) -> CheckResult:
        self._require_open()
        token = self._cancellation
        token.check()
        concrete: CompiledQuery | None
        if query is None:
            concrete = None
            program = self._permanent
        else:
            concrete = _concrete_query(query)
            program = _combine_query_program(
                self._permanent,
                concrete,
                self._permanent_sha256,
            )

        self._operation_sequence += 1
        operation_id = f"python-check-{self._operation_sequence}"
        self._emit_progress(operation_id, "reasoning-started", 0, 1, 0.0)
        started = time.perf_counter()
        tableau: PythonTableau | None = None
        try:
            tableau = PythonTableau(program, self._config, token)
            run = tableau.run(token)
            token.check()
            elapsed = time.perf_counter() - started
            statistics = _statistics(tableau, run.statistics, elapsed)
            self._last_tableau = tableau
            self._emit_progress(
                operation_id,
                "reasoning-completed",
                1,
                1,
                elapsed,
                satisfiable=run.satisfiable,
                query_hash=None if concrete is None else concrete.query_hash,
            )
            return CheckResult(run.satisfiable, statistics)
        except Exception:
            self._last_tableau = None
            raise

    def check_many(self, queries: object) -> tuple[CheckResult, ...]:
        self._require_open()
        if isinstance(queries, (str, bytes)) or not isinstance(queries, Sequence):
            raise TypeError("queries must be a sequence of compiled queries")
        return tuple(self.check(query) for query in queries)

    def classify_classes(self) -> HierarchyIds:
        self._require_open()
        raise FeatureNotImplementedError(
            "class taxonomy construction is delivered by WP13",
            feature_id="class-classification",
        )

    def classify_object_properties(self) -> HierarchyIds:
        self._require_open()
        raise FeatureNotImplementedError(
            "object-property taxonomy construction is delivered by WP14",
            feature_id="object-property-classification",
        )

    def classify_data_properties(self) -> HierarchyIds:
        self._require_open()
        raise FeatureNotImplementedError(
            "data-property taxonomy construction is delivered by WP14",
            feature_id="data-property-classification",
        )

    def realize(self) -> RealizationIds:
        self._require_open()
        raise FeatureNotImplementedError(
            "realization is delivered by WP15",
            feature_id="realization",
        )

    def apply_delta(self, delta: object) -> DeltaOutcome:
        self._require_open()
        if not isinstance(delta, CompiledDelta):
            raise TypeError("delta must be the concrete clauses.CompiledDelta")
        if delta.base_program_sha256 != self._permanent_sha256:
            raise BackendMismatchError(
                "compiled delta belongs to a different permanent program",
                context={
                    "actual": delta.base_program_sha256,
                    "expected": self._permanent_sha256,
                },
            )
        if (
            delta.result_program_sha256 == delta.base_program_sha256
            and not delta.fact_additions
            and not delta.fact_removals
        ):
            return DeltaOutcome.APPLIED_INCREMENTALLY
        return DeltaOutcome.REBUILD_REQUIRED

    def reset_query_state(self) -> None:
        self._require_open()
        self._last_tableau = None

    def close(self) -> None:
        self._last_tableau = None
        self._closed = True

    def _require_open(self) -> None:
        if self._closed:
            raise DisposedReasonerError("pure-Python backend session is closed")

    def _emit_progress(
        self,
        operation_id: str,
        kind: str,
        completed: int,
        total: int,
        elapsed: float,
        *,
        satisfiable: bool | None = None,
        query_hash: str | None = None,
    ) -> None:
        callback = self._config.progress
        if callback is None:
            return
        callback(
            ProgressEvent(
                version=1,
                operation_id=operation_id,
                kind=kind,
                completed=completed,
                total=total,
                elapsed_seconds=elapsed,
                details={"query_hash": query_hash, "satisfiable": satisfiable},
            )
        )


class PythonBackendFactory:
    """Side-effect-free factory for complete pure-Python backend sessions."""

    __slots__ = ("_info",)

    def __init__(self) -> None:
        core = require_core_compatibility()
        self._info = BackendInfo(
            name="python",
            package_version=__version__,
            ir_schema_version=COMPILED_IR_SCHEMA_VERSION,
            implementation_version="python-tableau-v1",
            core_package_version=core.package_version,
            core_api_version=core.api_version,
            core_model_schema_version=core.model_schema_version,
            core_wire_format_version=core.wire_format_version,
            core_adapter_protocol_version=core.adapter_protocol_version,
            complete_features=frozenset(
                {
                    "blocking",
                    "classification",
                    "datatypes",
                    "full_reasoner",
                    "incremental_updates",
                    "nominals",
                    "query-overlays",
                    "realization",
                    "satisfiability",
                }
            ),
            accelerated=False,
        )

    @property
    def info(self) -> BackendInfo:
        return self._info

    def create_session(
        self,
        ontology: CompiledOntology,
        config: ReasonerConfig,
        cancellation: CancellationToken,
    ) -> PythonBackendSession:
        return PythonBackendSession(ontology, config, cancellation)


def _concrete_tuple(
    values: tuple[object, ...],
    expected: type[_RecordT],
    name: str,
) -> tuple[_RecordT, ...]:
    if not all(isinstance(value, expected) for value in values):
        raise BackendMismatchError(f"compiled ontology {name} use an incompatible IR record")
    return tuple(value for value in values if isinstance(value, expected))


def _concrete_query(value: object) -> CompiledQuery:
    if type(value) is not CompiledQuery:
        raise TypeError("query must be the concrete clauses.CompiledQuery or None")
    return value


def _validate_core_envelope(ontology: CompiledOntology) -> None:
    require_core_compatibility(
        CoreVersionInfo(
            ontology.core_package_version,
            ontology.core_api_version,
            ontology.core_model_schema_version,
            ontology.core_wire_format_version,
            ontology.core_adapter_protocol_version,
        )
    )
    current = current_core_versions()
    if ontology.core_wire_format_version[0] != current.wire_format_version[0]:
        raise BackendMismatchError("compiled ontology core wire major is incompatible")


def _validate_overlay_prefix(
    permanent: ClauseProgram,
    overlay: ClauseProgram,
    query: CompiledQuery,
) -> None:
    if query.first_local_predicate_id != len(permanent.predicates.predicates):
        raise BackendMismatchError("query predicate prefix boundary does not match the ontology")
    if overlay.predicates.predicates[: query.first_local_predicate_id] != (
        permanent.predicates.predicates
    ):
        raise BackendMismatchError("query predicate prefix differs from the permanent registry")
    boundaries = dict(query.first_local_symbols)
    for kind in SymbolKind:
        permanent_values = permanent.symbols.domain(kind).values
        cutoff = boundaries.get(kind.value)
        if cutoff != len(permanent_values):
            raise BackendMismatchError(
                f"query {kind.value} prefix boundary does not match the ontology"
            )
        if overlay.symbols.domain(kind).values[:cutoff] != permanent_values:
            raise BackendMismatchError(
                f"query {kind.value} symbol prefix differs from the permanent table"
            )
    if overlay.role_model != permanent.role_model:
        raise BackendMismatchError("incremental query changed the permanent role model")


def _merge_provenance(
    permanent: ProvenanceTable,
    overlay: ProvenanceTable,
) -> tuple[ProvenanceTable, tuple[int, ...], tuple[int, ...]]:
    keys = tuple(
        sorted(
            {
                (entry.source_sha256, entry.generated)
                for table in (permanent, overlay)
                for entry in table.entries
            }
        )
    )
    identifiers = {key: identifier for identifier, key in enumerate(keys)}
    table = ProvenanceTable(
        tuple(
            ProvenanceEntry(identifier, source_sha256, generated)
            for identifier, (source_sha256, generated) in enumerate(keys)
        )
    )

    def remap(source: ProvenanceTable) -> tuple[int, ...]:
        return tuple(
            identifiers[(entry.source_sha256, entry.generated)] for entry in source.entries
        )

    return table, remap(permanent), remap(overlay)


def _remap_ids(values: tuple[int, ...], mapping: tuple[int, ...]) -> tuple[int, ...]:
    try:
        return tuple(sorted({mapping[value] for value in values}))
    except IndexError as error:
        raise BackendMismatchError("compiled overlay has dangling provenance IDs") from error


def _merge_facts(
    sources: tuple[tuple[tuple[GroundAtom, ...], tuple[int, ...]], ...],
) -> tuple[GroundAtom, ...]:
    grouped: dict[_FactIdentity, set[int]] = {}
    for facts, mapping in sources:
        for fact in facts:
            key = (fact.predicate_id, fact.arguments)
            grouped.setdefault(key, set()).update(_remap_ids(fact.provenance_ids, mapping))
    values = tuple(
        GroundAtom(predicate_id, arguments, tuple(sorted(provenance)))
        for (predicate_id, arguments), provenance in grouped.items()
    )
    return tuple(sorted(values, key=lambda value: value.canonical_bytes()))


def _clause_identity_bytes(identity: _ClauseIdentity) -> bytes:
    body, head, join_order = identity
    temporary = DLClause(0, body, head, (0,), join_order)
    return json.dumps(
        temporary.identity_payload(),
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")


def _merge_clauses(
    sources: tuple[tuple[tuple[DLClause, ...], tuple[int, ...]], ...],
) -> tuple[DLClause, ...]:
    grouped: dict[_ClauseIdentity, set[int]] = {}
    for clauses, mapping in sources:
        for clause in clauses:
            key = (clause.body, clause.head, clause.join_order)
            grouped.setdefault(key, set()).update(_remap_ids(clause.provenance_ids, mapping))
    ordered = sorted(grouped, key=_clause_identity_bytes)
    return tuple(
        DLClause(identifier, body, head, tuple(sorted(grouped[key])), join_order)
        for identifier, key in enumerate(ordered)
        for body, head, join_order in (key,)
    )


def _merge_disjunctions(
    sources: tuple[tuple[tuple[GroundDisjunctionIR, ...], tuple[int, ...]], ...],
) -> tuple[GroundDisjunctionIR, ...]:
    grouped: dict[tuple[_FactIdentity, ...], tuple[set[int], dict[_FactIdentity, set[int]]]] = {}
    for disjunctions, mapping in sources:
        for disjunction in disjunctions:
            rows = {
                (fact.predicate_id, fact.arguments): set(_remap_ids(fact.provenance_ids, mapping))
                for fact in disjunction.disjuncts
            }
            key = tuple(sorted(rows, key=_fact_identity_bytes))
            outer, disjunct_provenance = grouped.setdefault(key, (set(), {}))
            outer.update(_remap_ids(disjunction.provenance_ids, mapping))
            for identity, provenance in rows.items():
                disjunct_provenance.setdefault(identity, set()).update(provenance)

    prepared: list[tuple[bytes, tuple[GroundAtom, ...], tuple[int, ...]]] = []
    for key, (outer, disjunct_provenance) in grouped.items():
        disjuncts = tuple(
            GroundAtom(predicate_id, arguments, tuple(sorted(disjunct_provenance[identity])))
            for identity in key
            for predicate_id, arguments in (identity,)
        )
        temporary = GroundDisjunctionIR(0, disjuncts, tuple(sorted(outer)))
        prepared.append((temporary.canonical_bytes(), disjuncts, tuple(sorted(outer))))
    prepared.sort(key=lambda item: item[0])
    return tuple(
        GroundDisjunctionIR(identifier, disjuncts, provenance)
        for identifier, (_key, disjuncts, provenance) in enumerate(prepared)
    )


def _fact_identity_bytes(identity: _FactIdentity) -> bytes:
    predicate_id, arguments = identity
    return GroundAtom(predicate_id, arguments, (0,)).canonical_bytes()


def _statistics(
    tableau: PythonTableau,
    run: object,
    elapsed: float,
) -> ReasoningStatistics:
    from .tableau import TableauRunStatistics

    if not isinstance(run, TableauRunStatistics):
        raise TypeError("run must be TableauRunStatistics")
    nodes = tableau.session.nodes.existing_nodes()
    return ReasoningStatistics(
        elapsed_seconds=elapsed,
        nodes=len(nodes),
        facts=len(tableau.session.extensions.active_rows()),
        branches=run.disjunction_actions,
        backtracks=run.backtracks,
        merges=sum(value.lifecycle is NodeLifecycle.MERGED for value in nodes),
        datatype_checks=run.datatype_checks,
    )


__all__ = [
    "PythonBackendFactory",
    "PythonBackendSession",
    "clause_program_from_compiled",
    "combine_query_program",
]
