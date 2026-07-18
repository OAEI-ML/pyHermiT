"""Deterministic clausification of normalized OWL into the private DL-clause IR.

The translation follows the structural shapes of pinned HermiT while keeping IDs
and generated guards independent of input/hash iteration order.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import hashlib
import itertools
import json
import re
from collections.abc import Callable, Iterable, Iterator, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import cast

import pyowl_core.model as owl

from pyhermit.backends.protocol import (
    COMPILED_IR_SCHEMA_VERSION,
    CompiledOntology,
    EntityRef,
    FingerprintLike,
)
from pyhermit.config import ReasonerConfig
from pyhermit.core import CapturedOntology, compiler_cache_key
from pyhermit.datatypes import (
    SUPPORTED_DATATYPES,
    CompiledLiteral,
    compile_datatype_semantic_model,
    compile_literal,
    compile_literal_semantic_payload,
)
from pyhermit.exceptions import ReasonerInterruptedError, ResourceLimitError
from pyhermit.normalize import (
    DataRangeInclusion,
    NormalizedFamily,
    NormalizedOntology,
    NormalizedQuery,
    NormalizedRecord,
    normalize_view,
)
from pyhermit.roles import RoleAxiomGraph, build_role_axiom_graph

from .model import (
    Atom,
    ClauseProgram,
    CompilationLimits,
    CompiledDelta,
    CompiledQuery,
    DataConstant,
    DatatypeModelIR,
    DeltaCompatibility,
    DeltaFactIR,
    DLClause,
    Expressivity,
    GroundAtom,
    GroundDisjunctionIR,
    IndividualTerm,
    LiteralIdentityIR,
    Predicate,
    PredicateKind,
    PredicateRegistry,
    ProvenanceEntry,
    ProvenanceTable,
    RoleAutomatonIR,
    RoleModelIR,
    RoleTransitionIR,
    SymbolDomain,
    SymbolKind,
    SymbolTable,
    SymbolValue,
    Term,
    TermSort,
    Variable,
)

_BUILTIN_PROVENANCE = hashlib.sha256(b"pyhermit:clausification:builtins:v1").hexdigest()
_NEGATIVE_KINDS = frozenset(
    {
        PredicateKind.NEGATED_CONCEPT,
        PredicateKind.NEGATED_NOMINAL,
        PredicateKind.NEGATED_OBJECT_ROLE,
        PredicateKind.NEGATED_DATA_ROLE,
        PredicateKind.NEGATED_DATA_RANGE,
    }
)
CLAUSIFICATION_HANDLER_TABLE: Mapping[type[object], str] = MappingProxyType(
    {
        owl.SubClassOf: "subclass",
        owl.DisjointClasses: "disjoint_classes",
        owl.SubObjectPropertyOf: "sub_object_property",
        owl.EquivalentObjectProperties: "equivalent_object_properties",
        owl.DisjointObjectProperties: "disjoint_object_properties",
        owl.InverseObjectProperties: "inverse_object_properties",
        owl.ObjectPropertyDomain: "object_property_domain",
        owl.ObjectPropertyRange: "object_property_range",
        owl.FunctionalObjectProperty: "functional_object_property",
        owl.InverseFunctionalObjectProperty: "inverse_functional_object_property",
        owl.ReflexiveObjectProperty: "reflexive_object_property",
        owl.IrreflexiveObjectProperty: "irreflexive_object_property",
        owl.SymmetricObjectProperty: "symmetric_object_property",
        owl.AsymmetricObjectProperty: "asymmetric_object_property",
        owl.TransitiveObjectProperty: "transitive_object_property",
        owl.SubDataPropertyOf: "sub_data_property",
        owl.EquivalentDataProperties: "equivalent_data_properties",
        owl.DisjointDataProperties: "disjoint_data_properties",
        owl.DataPropertyDomain: "data_property_domain",
        owl.DataPropertyRange: "data_property_range",
        owl.FunctionalDataProperty: "functional_data_property",
        owl.DatatypeDefinition: "datatype_definition",
        DataRangeInclusion: "data_range_inclusion",
        owl.HasKey: "has_key",
        owl.SameIndividual: "same_individual",
        owl.DifferentIndividuals: "different_individuals",
        owl.ClassAssertion: "class_assertion",
        owl.ObjectPropertyAssertion: "object_property_assertion",
        owl.NegativeObjectPropertyAssertion: "negative_object_property_assertion",
        owl.DataPropertyAssertion: "data_property_assertion",
        owl.NegativeDataPropertyAssertion: "negative_data_property_assertion",
    }
)


@dataclass(frozen=True, slots=True)
class _PredicateSpec:
    kind: PredicateKind
    argument_sorts: tuple[TermSort, ...]
    symbol_id: int | None = None
    role_id: int | None = None
    cardinality: int | None = None
    filler: _PredicateSpec | None = None
    annotation: tuple[int, ...] = ()
    internal_key: str | None = None


@dataclass(frozen=True, slots=True)
class _AtomSpec:
    predicate: _PredicateSpec
    arguments: tuple[Term, ...]


@dataclass(frozen=True, slots=True)
class _ClauseSpec:
    body: tuple[_AtomSpec, ...]
    head: tuple[_AtomSpec, ...]
    provenance_ids: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class _FactSpec:
    atom: _AtomSpec
    provenance_ids: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class _SymbolIndex:
    table: SymbolTable
    by_kind: Mapping[SymbolKind, Mapping[bytes, int]]
    individuals: tuple[owl.Individual, ...]
    data_ranges: tuple[owl.DataRange, ...]
    source_literals: tuple[owl.Literal, ...]
    compiled_literals: dict[bytes, CompiledLiteral | None]

    def identifier(self, kind: SymbolKind, value: owl.StructuralNode) -> int:
        try:
            return self.by_kind[kind][value.canonical_bytes()]
        except KeyError as error:
            raise ValueError(f"missing {kind.value} symbol during clausification") from error


@dataclass(frozen=True, slots=True)
class _OverlayIndex(Mapping[bytes, int]):
    local: Mapping[bytes, int]
    permanent: Mapping[bytes, int]

    def __getitem__(self, key: bytes) -> int:
        try:
            return self.local[key]
        except KeyError:
            return self.permanent[key]

    def __iter__(self) -> Iterator[bytes]:
        yield from self.local
        yield from (key for key in self.permanent if key not in self.local)

    def __len__(self) -> int:
        return len(self.local) + sum(key not in self.local for key in self.permanent)


@dataclass(frozen=True, slots=True)
class QueryCompilationContext:
    """Reusable permanent indexes for O(query-size) overlay preparation."""

    normalized_digest: str
    permanent_program_sha256: str
    role_model: RoleAxiomGraph
    domain_by_kind: Mapping[SymbolKind, Mapping[bytes, int]]
    by_kind: Mapping[SymbolKind, Mapping[bytes, int]]
    individuals: tuple[owl.Individual, ...]
    data_ranges: tuple[owl.DataRange, ...]
    source_literals: tuple[owl.Literal, ...]
    predicate_specs: tuple[_PredicateSpec, ...]
    predicate_set: frozenset[_PredicateSpec]


def prepare_query_compilation(
    permanent_program: ClauseProgram,
    permanent_normalized: NormalizedOntology,
    *,
    permanent_program_sha256: str | None = None,
    cancelled: Callable[[], bool] | None = None,
) -> QueryCompilationContext:
    """Index immutable permanent objects once for repeated query compilation."""

    if not isinstance(permanent_program, ClauseProgram):
        raise TypeError("permanent_program must be ClauseProgram")
    if not isinstance(permanent_normalized, NormalizedOntology):
        raise TypeError("permanent_normalized must be NormalizedOntology")
    if cancelled is not None and not callable(cancelled):
        raise TypeError("cancelled must be callable or None")
    if permanent_program_sha256 is not None and (
        not isinstance(permanent_program_sha256, str)
        or re.fullmatch(r"[0-9a-f]{64}", permanent_program_sha256) is None
    ):
        raise ValueError("permanent_program_sha256 must be a lowercase SHA-256 digest or None")
    digest = permanent_program_sha256
    if digest is None:
        digest = hashlib.sha256(permanent_program.canonical_bytes()).hexdigest()
    _raise_if_cancelled(cancelled)
    roles = build_role_axiom_graph(
        _role_source_axioms(permanent_normalized, cancelled),
        cancelled=cancelled,
    )
    nodes = _normalized_nodes(permanent_normalized, cancelled=cancelled)
    individual_nodes = {
        node.canonical_bytes(): node
        for node in itertools.chain(permanent_normalized.declared_entities, nodes)
        if isinstance(node, (owl.NamedIndividual, owl.AnonymousIndividual))
    }
    data_range_nodes = {
        node.canonical_bytes(): node
        for node in itertools.chain(
            (owl.RDFS_LITERAL,),
            permanent_normalized.declared_entities,
            nodes,
        )
        if isinstance(node, owl.DATA_RANGE_TYPES)
    }
    literal_nodes = {
        node.canonical_bytes(): node for node in nodes if isinstance(node, owl.Literal)
    }
    domain_by_kind: dict[SymbolKind, Mapping[bytes, int]] = {}
    for kind in SymbolKind:
        domain = permanent_program.symbols.domain(kind)
        domain_by_kind[kind] = MappingProxyType(
            {bytes.fromhex(value.key_hex): value.identifier for value in domain.values}
        )
    by_kind = dict(domain_by_kind)
    source_literals = tuple(
        literal_nodes[bytes.fromhex(value.key_hex)]
        for value in permanent_program.symbols.domain(SymbolKind.SOURCE_LITERAL).values
    )
    data_ranges = tuple(
        cast(owl.DataRange, data_range_nodes[bytes.fromhex(value.key_hex)])
        for value in permanent_program.symbols.domain(SymbolKind.DATA_RANGE).values
    )
    individuals = tuple(
        individual_nodes[bytes.fromhex(value.key_hex)]
        for value in permanent_program.symbols.domain(SymbolKind.INDIVIDUAL).values
    )
    by_kind[SymbolKind.DATA_VALUE] = MappingProxyType(
        {
            source_literals[value.source_literal_id].canonical_bytes(): value.data_identity_id
            for value in permanent_program.datatype_model.literal_identities
        }
    )
    predicate_specs = _predicate_specs_from_registry(permanent_program.predicates)
    return QueryCompilationContext(
        normalized_digest=permanent_normalized.digest,
        permanent_program_sha256=digest,
        role_model=roles,
        domain_by_kind=MappingProxyType(domain_by_kind),
        by_kind=MappingProxyType(by_kind),
        individuals=individuals,
        data_ranges=data_ranges,
        source_literals=source_literals,
        predicate_specs=predicate_specs,
        predicate_set=frozenset(predicate_specs),
    )


class _CompilationState:
    def __init__(
        self,
        normalized: NormalizedOntology | NormalizedQuery,
        roles: RoleAxiomGraph,
        symbols: _SymbolIndex,
        provenance: ProvenanceTable,
        provenance_ids: dict[tuple[tuple[str, ...], bool], int],
        provenance_by_sha: dict[str, tuple[int, ...]],
        limits: CompilationLimits,
        cancelled: Callable[[], bool] | None,
    ) -> None:
        self.normalized = normalized
        self.roles = roles
        self.symbols = symbols
        self.provenance = provenance
        self.provenance_ids = provenance_ids
        self.provenance_by_sha = provenance_by_sha
        self.role_provenance = {
            hashlib.sha256(record.statement.canonical_bytes()).hexdigest(): (
                provenance_ids[(record.provenance_sha256, record.generated)],
            )
            for record in normalized.records
            if isinstance(record.statement, owl.AxiomNode)
            and record.family in {NormalizedFamily.OBJECT_PROPERTY, NormalizedFamily.DATA_PROPERTY}
        }
        self.limits = limits
        self.cancelled = cancelled
        self.predicates: set[_PredicateSpec] = set()
        self.clauses: list[_ClauseSpec] = []
        self.facts: list[_FactSpec] = []
        self.atom_count = 0
        self._nominal_semantics: set[_PredicateSpec] = set()
        self._automaton_semantics: set[tuple[int, _PredicateSpec, tuple[int, ...]]] = set()

    def checkpoint(self) -> None:
        if self.cancelled is not None and self.cancelled():
            raise ReasonerInterruptedError("ontology clausification cancelled")

    def provenance_for(self, record: NormalizedRecord) -> tuple[int, ...]:
        key = (record.provenance_sha256, record.generated)
        try:
            return (self.provenance_ids[key],)
        except KeyError as error:
            raise RuntimeError("normalized record provenance was not indexed") from error

    def provenance_for_sha(self, source_sha256: str | None) -> tuple[int, ...]:
        if source_sha256 is None:
            return self.provenance_by_sha[_BUILTIN_PROVENANCE]
        try:
            return self.provenance_by_sha[source_sha256]
        except KeyError:
            known = self.role_provenance.get(source_sha256)
            if known is not None:
                return known
            return self.provenance_by_sha[_BUILTIN_PROVENANCE]

    def retain_predicate(self, predicate: _PredicateSpec) -> _PredicateSpec:
        self.predicates.add(predicate)
        if len(self.predicates) > self.limits.max_predicates:
            raise ResourceLimitError(
                "compiled predicate limit exceeded",
                limit="max_predicates",
                observed=len(self.predicates),
                allowed=self.limits.max_predicates,
            )
        if predicate.filler is not None:
            self.retain_predicate(predicate.filler)
        return predicate

    def atom(self, predicate: _PredicateSpec, *arguments: Term) -> _AtomSpec:
        if self.atom_count & 0x3FF == 0:
            self.checkpoint()
        self.retain_predicate(predicate)
        self.atom_count += 1
        if self.atom_count > self.limits.max_atoms:
            raise ResourceLimitError(
                "compiled atom limit exceeded",
                limit="max_atoms",
                observed=self.atom_count,
                allowed=self.limits.max_atoms,
            )
        return _AtomSpec(predicate, tuple(arguments))

    def add_clause(
        self,
        body: Iterable[_AtomSpec],
        head: Iterable[_AtomSpec],
        provenance_ids: tuple[int, ...],
    ) -> None:
        if len(self.clauses) & 0x3FF == 0:
            self.checkpoint()
        self.clauses.append(_ClauseSpec(tuple(body), tuple(head), provenance_ids))
        if len(self.clauses) > self.limits.max_clauses:
            raise ResourceLimitError(
                "compiled clause limit exceeded",
                limit="max_clauses",
                observed=len(self.clauses),
                allowed=self.limits.max_clauses,
            )

    def add_fact(self, atom: _AtomSpec, provenance_ids: tuple[int, ...]) -> None:
        self.facts.append(_FactSpec(atom, provenance_ids))


def compile_normalized(
    normalized: NormalizedOntology,
    *,
    role_model: RoleAxiomGraph | None = None,
    limits: CompilationLimits | None = None,
    cancelled: Callable[[], bool] | None = None,
) -> ClauseProgram:
    """Compile one immutable normalized ontology into validated private IR."""

    if not isinstance(normalized, NormalizedOntology):
        raise TypeError("normalized must be NormalizedOntology")
    selected_limits = limits or CompilationLimits()
    if not isinstance(selected_limits, CompilationLimits):
        raise TypeError("limits must be CompilationLimits or None")
    if cancelled is not None and not callable(cancelled):
        raise TypeError("cancelled must be callable or None")
    _raise_if_cancelled(cancelled)
    roles = role_model or build_role_axiom_graph(
        _role_source_axioms(normalized, cancelled),
        cancelled=cancelled,
    )
    if not isinstance(roles, RoleAxiomGraph):
        raise TypeError("role_model must be RoleAxiomGraph or None")
    roles.require_regular()
    _raise_if_cancelled(cancelled)
    symbols = _build_symbol_index(
        normalized,
        roles,
        selected_limits,
        cancelled=cancelled,
    )
    provenance, provenance_ids, provenance_by_sha = _build_provenance(
        normalized.records,
        cancelled=cancelled,
    )
    state = _CompilationState(
        normalized,
        roles,
        symbols,
        provenance,
        provenance_ids,
        provenance_by_sha,
        selected_limits,
        cancelled,
    )
    _compile_role_graph(state)
    for record in normalized.records:
        state.checkpoint()
        _compile_record(state, record)
    _emit_builtin_facts_and_clashes(state)
    _emit_complement_clashes(state)
    _emit_pending_nominal_semantics(state)
    _retain_runtime_predicates(state)
    state.checkpoint()
    registry, predicate_ids = _freeze_predicates(state.predicates, cancelled=cancelled)
    clauses, positive, negative, disjunctions = _freeze_rules(state, registry, predicate_ids)
    table = SymbolTable(symbols.table.domains, registry)
    state.checkpoint()
    datatype_model = _freeze_datatype_model(symbols, normalized, cancelled=cancelled)
    program = ClauseProgram(
        symbols=table,
        predicates=registry,
        clauses=clauses,
        positive_facts=positive,
        negative_facts=negative,
        ground_disjunctions=disjunctions,
        role_model=_freeze_role_model(roles),
        datatype_model=datatype_model,
        expressivity=_derive_expressivity(
            normalized,
            roles,
            registry,
            clauses,
            datatype_model,
            cancelled=cancelled,
        ),
        provenance=provenance,
    )
    return program


def compile_query_program(
    permanent_program: ClauseProgram,
    permanent_normalized: NormalizedOntology,
    query: NormalizedQuery,
    *,
    role_model: RoleAxiomGraph | None = None,
    limits: CompilationLimits | None = None,
    cancelled: Callable[[], bool] | None = None,
    permanent_program_sha256: str | None = None,
    verify_immutable: bool = True,
    query_context: QueryCompilationContext | None = None,
) -> CompiledQuery:
    """Compile a safe query overlay while preserving every permanent byte and ID."""

    if not isinstance(permanent_program, ClauseProgram):
        raise TypeError("permanent_program must be ClauseProgram")
    if not isinstance(permanent_normalized, NormalizedOntology):
        raise TypeError("permanent_normalized must be NormalizedOntology")
    if not isinstance(query, NormalizedQuery):
        raise TypeError("query must be NormalizedQuery")
    if query.permanent_normalization_digest != permanent_normalized.digest:
        raise ValueError("query was normalized against a different permanent ontology")
    if query_context is not None:
        if not isinstance(query_context, QueryCompilationContext):
            raise TypeError("query_context must be QueryCompilationContext or None")
        if query_context.normalized_digest != permanent_normalized.digest:
            raise ValueError("query context belongs to a different normalized ontology")
    selected_limits = limits or CompilationLimits()
    if not isinstance(selected_limits, CompilationLimits):
        raise TypeError("limits must be CompilationLimits or None")
    contextual_digest = None if query_context is None else query_context.permanent_program_sha256
    if (
        permanent_program_sha256 is not None
        and contextual_digest is not None
        and permanent_program_sha256 != contextual_digest
    ):
        raise ValueError("permanent_program_sha256 disagrees with query_context")
    selected_permanent_digest = permanent_program_sha256 or contextual_digest
    if selected_permanent_digest is not None and (
        not isinstance(selected_permanent_digest, str)
        or re.fullmatch(r"[0-9a-f]{64}", selected_permanent_digest) is None
    ):
        raise ValueError("permanent_program_sha256 must be a lowercase SHA-256 digest or None")
    if not isinstance(verify_immutable, bool):
        raise TypeError("verify_immutable must be bool")
    before = permanent_program.canonical_bytes() if verify_immutable else None
    computed_digest = hashlib.sha256(before).hexdigest() if before is not None else None
    if (
        selected_permanent_digest is not None
        and computed_digest is not None
        and selected_permanent_digest != computed_digest
    ):
        raise ValueError("permanent_program_sha256 does not match permanent_program")
    permanent_digest = selected_permanent_digest or computed_digest
    if permanent_digest is None:
        # The fast service path always supplies a digest computed once at construction.
        raise ValueError("permanent_program_sha256 is required when verify_immutable is false")
    first_local_symbols = tuple(
        (domain.kind.value, len(domain.values)) for domain in permanent_program.symbols.domains
    )
    first_local_predicate = len(permanent_program.predicates.predicates)
    _raise_if_cancelled(cancelled)
    roles = role_model or (
        query_context.role_model
        if query_context is not None
        else build_role_axiom_graph(
            _role_source_axioms(permanent_normalized, cancelled),
            cancelled=cancelled,
        )
    )
    if query.requires_rebuild:
        return CompiledQuery(
            permanent_digest,
            query.query_hash,
            first_local_predicate,
            first_local_symbols,
            True,
            None,
            "normalization classified the query as strategy- or schema-changing",
        )
    missing_role = _first_missing_query_role(query, roles)
    if missing_role is not None:
        return CompiledQuery(
            permanent_digest,
            query.query_hash,
            first_local_predicate,
            first_local_symbols,
            True,
            None,
            f"query role is outside the permanent role model: {missing_role}",
        )
    symbols = _build_symbol_index(
        query,
        roles,
        selected_limits,
        base_table=permanent_program.symbols,
        seed_nodes=(
            ()
            if query_context is not None
            else _normalized_nodes(permanent_normalized, cancelled=cancelled)
        ),
        query_context=query_context,
        cancelled=cancelled,
    )
    provenance, provenance_ids, provenance_by_sha = _build_provenance(
        query.records,
        cancelled=cancelled,
    )
    state = _CompilationState(
        query,
        roles,
        symbols,
        provenance,
        provenance_ids,
        provenance_by_sha,
        selected_limits,
        cancelled,
    )
    base_specs = (
        query_context.predicate_specs
        if query_context is not None
        else _predicate_specs_from_registry(permanent_program.predicates)
    )
    base_set = query_context.predicate_set if query_context is not None else frozenset(base_specs)
    state.predicates.update(base_specs)
    for record in query.records:
        state.checkpoint()
        _compile_record(state, record)
    first_local_individual = dict(first_local_symbols)[SymbolKind.INDIVIDUAL.value]
    _emit_builtin_facts_and_clashes(
        state,
        first_local_individual_id=first_local_individual,
    )
    _emit_complement_clashes(state, base_predicates=base_set)
    _emit_pending_nominal_semantics(state)
    _retain_runtime_predicates(state)
    registry, predicate_ids = _freeze_predicates(
        state.predicates,
        permanent_program.predicates,
        base_specs=base_specs,
        base_set=base_set,
        cancelled=cancelled,
    )
    clauses, positive, negative, disjunctions = _freeze_rules(
        state,
        registry,
        predicate_ids,
    )
    table = SymbolTable(symbols.table.domains, registry)
    datatype_model = _freeze_datatype_model(
        symbols,
        query,
        base_model=permanent_program.datatype_model,
        base_definitions=tuple(
            record.statement
            for record in permanent_normalized.records
            if isinstance(record.statement, owl.DatatypeDefinition)
        ),
        first_local_symbols=dict(first_local_symbols),
        cancelled=cancelled,
    )
    query_expressivity = _derive_expressivity(
        query,
        roles,
        registry,
        clauses,
        datatype_model,
        cancelled=cancelled,
    )
    merged_expressivity = _merge_expressivity(
        permanent_program.expressivity,
        query_expressivity,
    )
    program = ClauseProgram(
        symbols=table,
        predicates=registry,
        clauses=clauses,
        positive_facts=positive,
        negative_facts=negative,
        ground_disjunctions=disjunctions,
        role_model=permanent_program.role_model,
        datatype_model=datatype_model,
        expressivity=merged_expressivity,
        provenance=provenance,
    )
    if before is not None and permanent_program.canonical_bytes() != before:
        raise RuntimeError("query compilation mutated the permanent compiled IR")
    expanded_strategy = _strategy_expansions(
        permanent_program.expressivity,
        merged_expressivity,
    )
    if expanded_strategy:
        return CompiledQuery(
            permanent_digest,
            query.query_hash,
            first_local_predicate,
            first_local_symbols,
            True,
            None,
            "query requires additional backend strategy features: " + ", ".join(expanded_strategy),
        )
    return CompiledQuery(
        permanent_digest,
        query.query_hash,
        first_local_predicate,
        first_local_symbols,
        False,
        program,
    )


def compile_delta_plan(
    base_program: ClauseProgram,
    result_program: ClauseProgram,
    *,
    additions: Iterable[owl.AxiomNode] = (),
    removals: Iterable[owl.AxiomNode] = (),
) -> CompiledDelta:
    """Conservatively classify a core delta without mutating either compiled revision."""

    if not isinstance(base_program, ClauseProgram) or not isinstance(result_program, ClauseProgram):
        raise TypeError("base_program and result_program must be ClauseProgram")
    added = tuple(additions)
    removed = tuple(removals)
    if not all(isinstance(value, owl.AxiomNode) for value in added + removed):
        raise TypeError("delta additions/removals must contain AxiomNode values")
    values = added + removed
    reasons: list[str] = []
    if not values:
        if base_program.canonical_bytes() == result_program.canonical_bytes():
            compatibility = DeltaCompatibility.DECLARATION_ONLY
            reasons.append("empty delta has no private reasoning mutation")
        else:
            compatibility = DeltaCompatibility.REBUILD_REQUIRED
            reasons.append("empty source delta does not explain the compiled-program change")
    elif all(_declaration_or_annotation(value) for value in values):
        if _private_program_shape_equal(
            base_program,
            result_program,
            allow_entity_domain_change=True,
            allow_fact_change=False,
        ):
            compatibility = DeltaCompatibility.DECLARATION_ONLY
            reasons.append("only declaration/signature metadata changed")
        else:
            compatibility = DeltaCompatibility.REBUILD_REQUIRED
            reasons.append("declared metadata delta also changed private reasoning IR")
    elif all(_incremental_assertion(value) for value in values):
        missing = tuple(
            value for value in values if not _assertion_uses_existing_symbols(base_program, value)
        )
        if missing:
            compatibility = DeltaCompatibility.REBUILD_REQUIRED
            reasons.extend(
                sorted(
                    {
                        f"{type(value).__name__} introduces a fresh compiled symbol"
                        for value in missing
                    }
                )
            )
        elif _private_program_shape_equal(
            base_program,
            result_program,
            allow_entity_domain_change=False,
            allow_fact_change=True,
        ):
            compatibility = DeltaCompatibility.ASSERTION_ONLY
            reasons.append("only existing-predicate atomic assertion rows changed")
        else:
            compatibility = DeltaCompatibility.REBUILD_REQUIRED
            reasons.append("assertion delta changed schema, clauses, or backend strategy")
    else:
        compatibility = DeltaCompatibility.REBUILD_REQUIRED
        reasons.extend(
            sorted(
                {
                    f"{type(value).__name__} changes normalized schema or strategy state"
                    for value in values
                    if not _declaration_or_annotation(value) and not _incremental_assertion(value)
                }
            )
        )
        if any(_declaration_or_annotation(value) for value in values):
            reasons.append("metadata and logical changes cannot share the assertion-only path")
    fact_additions: tuple[DeltaFactIR, ...] = ()
    fact_removals: tuple[DeltaFactIR, ...] = ()
    if compatibility is DeltaCompatibility.ASSERTION_ONLY:
        base_facts = set(_delta_fact_rows(base_program))
        result_facts = set(_delta_fact_rows(result_program))
        fact_additions = tuple(
            sorted(result_facts - base_facts, key=lambda value: value.canonical_bytes())
        )
        fact_removals = tuple(
            sorted(base_facts - result_facts, key=lambda value: value.canonical_bytes())
        )
    return CompiledDelta(
        base_program_sha256=hashlib.sha256(base_program.canonical_bytes()).hexdigest(),
        result_program_sha256=hashlib.sha256(result_program.canonical_bytes()).hexdigest(),
        compatibility=compatibility,
        addition_sha256=tuple(
            hashlib.sha256(value.canonical_bytes()).hexdigest() for value in added
        ),
        removal_sha256=tuple(
            hashlib.sha256(value.canonical_bytes()).hexdigest() for value in removed
        ),
        fact_additions=fact_additions,
        fact_removals=fact_removals,
        reasons=tuple(reasons),
    )


def _delta_fact_rows(program: ClauseProgram) -> tuple[DeltaFactIR, ...]:
    return tuple(
        DeltaFactIR(value.predicate_id, value.arguments, negative)
        for values, negative in (
            (program.positive_facts, False),
            (program.negative_facts, True),
        )
        for value in values
    )


def _private_program_shape_equal(
    base: ClauseProgram,
    result: ClauseProgram,
    *,
    allow_entity_domain_change: bool,
    allow_fact_change: bool,
) -> bool:
    kinds = tuple(
        kind
        for kind in SymbolKind
        if not (allow_entity_domain_change and kind is SymbolKind.ENTITY)
    )
    if any(base.symbols.domain(kind) != result.symbols.domain(kind) for kind in kinds):
        return False
    if base.predicates != result.predicates:
        return False
    if (
        base.role_model != result.role_model
        or base.datatype_model != result.datatype_model
        or base.expressivity != result.expressivity
    ):
        return False
    base_clauses = tuple(
        json.dumps(
            value.identity_payload(),
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        )
        for value in base.clauses
    )
    result_clauses = tuple(
        json.dumps(
            value.identity_payload(),
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        )
        for value in result.clauses
    )
    if base_clauses != result_clauses:
        return False

    def fact_identities(
        program: ClauseProgram,
    ) -> tuple[tuple[bool, int, tuple[Term, ...]], ...]:
        return tuple(
            sorted(
                (
                    negative,
                    value.predicate_id,
                    cast(tuple[Term, ...], value.arguments),
                )
                for values, negative in (
                    (program.positive_facts, False),
                    (program.negative_facts, True),
                )
                for value in values
            )
        )

    def disjunction_identities(
        program: ClauseProgram,
    ) -> tuple[tuple[tuple[int, tuple[Term, ...]], ...], ...]:
        return tuple(
            tuple(
                (value.predicate_id, cast(tuple[Term, ...], value.arguments))
                for value in disjunction.disjuncts
            )
            for disjunction in program.ground_disjunctions
        )

    if disjunction_identities(base) != disjunction_identities(result):
        return False
    return allow_fact_change or fact_identities(base) == fact_identities(result)


def _assertion_uses_existing_symbols(
    base: ClauseProgram,
    assertion: owl.AxiomNode,
) -> bool:
    required: list[tuple[SymbolKind, bytes]] = []
    for node in owl.walk(assertion):
        if isinstance(node, owl.Entity):
            required.append((SymbolKind.ENTITY, node.canonical_bytes()))
        if isinstance(node, owl.Class):
            required.append((SymbolKind.CLASS_EXPRESSION, node.canonical_bytes()))
        elif isinstance(node, (owl.ObjectProperty, owl.ObjectInverseOf)):
            required.append((SymbolKind.OBJECT_ROLE, node.canonical_bytes()))
        elif isinstance(node, owl.DataProperty):
            required.append((SymbolKind.DATA_PROPERTY, node.canonical_bytes()))
        elif isinstance(node, (owl.NamedIndividual, owl.AnonymousIndividual)):
            required.append((SymbolKind.INDIVIDUAL, node.canonical_bytes()))
        elif isinstance(node, owl.Literal):
            required.append((SymbolKind.SOURCE_LITERAL, node.canonical_bytes()))
    available = {
        kind: {bytes.fromhex(value.key_hex) for value in base.symbols.domain(kind).values}
        for kind in SymbolKind
    }
    return all(encoded in available[kind] for kind, encoded in required)


def _declaration_or_annotation(value: owl.AxiomNode) -> bool:
    return isinstance(
        value,
        (
            owl.Declaration,
            owl.AnnotationAssertion,
            owl.SubAnnotationPropertyOf,
            owl.AnnotationPropertyDomain,
            owl.AnnotationPropertyRange,
        ),
    )


def _incremental_assertion(value: owl.AxiomNode) -> bool:
    if isinstance(
        value,
        (
            owl.ObjectPropertyAssertion,
            owl.NegativeObjectPropertyAssertion,
            owl.DataPropertyAssertion,
            owl.NegativeDataPropertyAssertion,
        ),
    ):
        return True
    if not isinstance(value, owl.ClassAssertion):
        return False
    expression = value.class_expression
    return isinstance(expression, owl.Class) or (
        isinstance(expression, owl.ObjectComplementOf) and isinstance(expression.operand, owl.Class)
    )


def compile_captured(
    captured: CapturedOntology,
    config: ReasonerConfig,
    *,
    limits: CompilationLimits | None = None,
    cancelled: Callable[[], bool] | None = None,
) -> CompiledOntology:
    """Compile a captured core view without flattening or copying its public model."""

    return compile_captured_bundle(
        captured,
        config,
        limits=limits,
        cancelled=cancelled,
    )[2]


def compile_captured_bundle(
    captured: CapturedOntology,
    config: ReasonerConfig,
    *,
    limits: CompilationLimits | None = None,
    cancelled: Callable[[], bool] | None = None,
) -> tuple[NormalizedOntology, ClauseProgram, CompiledOntology]:
    """Compile once and retain every immutable layer needed by a reasoner session."""

    if not isinstance(captured, CapturedOntology):
        raise TypeError("captured must be CapturedOntology")
    if not isinstance(config, ReasonerConfig):
        raise TypeError("config must be ReasonerConfig")
    normalized = normalize_view(captured.view, cancelled=cancelled)
    program = compile_normalized(normalized, limits=limits, cancelled=cancelled)
    entity_domain = program.symbols.domain(SymbolKind.ENTITY)
    declared_keys = {value.canonical_bytes() for value in normalized.declared_entities}
    declared_entities = tuple(
        EntityRef(
            kind=_entity_kind_from_display(value.display),
            iri=_entity_iri_from_display(value.display),
            entity_id=value.identifier,
        )
        for value in entity_domain.values
        if bytes.fromhex(value.key_hex) in declared_keys
    )
    individual_domain = program.symbols.domain(SymbolKind.INDIVIDUAL)
    named = tuple(
        value.identifier
        for value in individual_domain.values
        if value.display.startswith("named_individual:")
    )
    compiled = CompiledOntology(
        schema_version=COMPILED_IR_SCHEMA_VERSION,
        ontology_fingerprint=compiler_cache_key(captured, config),
        source_structural_fingerprint=cast(
            FingerprintLike,
            captured.structural_fingerprint,
        ),
        source_logical_fingerprint=cast(FingerprintLike, captured.logical_fingerprint),
        source_signature_fingerprint=cast(
            FingerprintLike,
            captured.signature_fingerprint,
        ),
        core_package_version=captured.core_package_version,
        core_api_version=captured.core_api_version,
        core_model_schema_version=captured.core_model_schema_version,
        core_wire_format_version=captured.core_wire_format_version,
        core_adapter_protocol_version=captured.core_adapter_protocol_version,
        symbols=program.symbols,
        clauses=program.clauses,
        positive_facts=program.positive_facts,
        negative_facts=program.negative_facts,
        ground_disjunctions=program.ground_disjunctions,
        role_model=program.role_model,
        datatype_model=program.datatype_model,
        expressivity=program.expressivity,
        declared_entities=tuple(
            sorted(declared_entities, key=lambda value: (value.kind, value.iri))
        ),
        named_individuals=named,
        provenance=program.provenance,
    )
    return normalized, program, compiled


def _raise_if_cancelled(cancelled: Callable[[], bool] | None) -> None:
    if cancelled is not None and cancelled():
        raise ReasonerInterruptedError("ontology clausification cancelled")


def _owl_statements(
    records: tuple[NormalizedRecord, ...],
    *,
    cancelled: Callable[[], bool] | None = None,
) -> tuple[owl.AxiomNode, ...]:
    statements: list[owl.AxiomNode] = []
    for index, record in enumerate(records):
        if index & 0x3F == 0:
            _raise_if_cancelled(cancelled)
        if isinstance(record.statement, owl.AxiomNode):
            statements.append(record.statement)
    _raise_if_cancelled(cancelled)
    return tuple(statements)


def _role_source_axioms(
    normalized: NormalizedOntology,
    cancelled: Callable[[], bool] | None,
) -> tuple[owl.AxiomNode, ...]:
    statements = list(_owl_statements(normalized.records, cancelled=cancelled))
    known = {value.canonical_bytes() for value in statements}
    for index, entity in enumerate(normalized.declared_entities):
        if index & 0x3F == 0:
            _raise_if_cancelled(cancelled)
        declaration = owl.Declaration(entity)
        encoded = declaration.canonical_bytes()
        if encoded not in known:
            known.add(encoded)
            statements.append(declaration)
    _raise_if_cancelled(cancelled)
    return tuple(statements)


def _normalized_nodes(
    normalized: NormalizedOntology | NormalizedQuery,
    *,
    cancelled: Callable[[], bool] | None = None,
    include_declared_entities: bool = True,
) -> tuple[owl.StructuralNode, ...]:
    values: list[owl.StructuralNode] = []
    if include_declared_entities:
        values.extend(getattr(normalized, "declared_entities", ()))
    for index, record in enumerate(normalized.records):
        if index & 0x3F == 0:
            _raise_if_cancelled(cancelled)
        if isinstance(record.statement, DataRangeInclusion):
            values.extend(owl.walk(record.statement.sub_range))
            values.extend(owl.walk(record.statement.super_range))
        else:
            values.extend(owl.walk(record.statement))
    for index, definition in enumerate(normalized.definitions):
        if index & 0x3F == 0:
            _raise_if_cancelled(cancelled)
        values.extend(owl.walk(definition.symbol))
        values.extend(owl.walk(definition.expression))
    _raise_if_cancelled(cancelled)
    return tuple(values)


def _first_missing_query_role(
    query: NormalizedQuery,
    roles: RoleAxiomGraph,
) -> str | None:
    for node in _normalized_nodes(query):
        try:
            if isinstance(node, (owl.ObjectProperty, owl.ObjectInverseOf)):
                roles.object_role_id(node)
            elif isinstance(node, owl.DataProperty):
                roles.data_property_id(node)
        except KeyError:
            return _display(node)
    return None


def _merge_expressivity(first: Expressivity, second: Expressivity) -> Expressivity:
    return Expressivity(
        inverse_roles=first.inverse_roles or second.inverse_roles,
        nominals=first.nominals or second.nominals,
        datatypes=first.datatypes or second.datatypes,
        unknown_datatypes=first.unknown_datatypes or second.unknown_datatypes,
        complex_roles=first.complex_roles or second.complex_roles,
        number_restrictions=first.number_restrictions or second.number_restrictions,
        keys=first.keys or second.keys,
        non_horn=first.non_horn or second.non_horn,
        bottom_properties=first.bottom_properties or second.bottom_properties,
        abox=first.abox or second.abox,
    )


def _strategy_expansions(
    permanent: Expressivity,
    combined: Expressivity,
) -> tuple[str, ...]:
    strategy_fields = (
        "inverse_roles",
        "nominals",
        "datatypes",
        "unknown_datatypes",
        "complex_roles",
        "number_restrictions",
        "keys",
        "non_horn",
        "bottom_properties",
    )
    return tuple(
        name for name in strategy_fields if not getattr(permanent, name) and getattr(combined, name)
    )


def _build_provenance(
    records: tuple[NormalizedRecord, ...],
    *,
    cancelled: Callable[[], bool] | None = None,
) -> tuple[
    ProvenanceTable,
    dict[tuple[tuple[str, ...], bool], int],
    dict[str, tuple[int, ...]],
]:
    retained: set[tuple[tuple[str, ...], bool]] = {((_BUILTIN_PROVENANCE,), True)}
    for index, record in enumerate(records):
        if index & 0xFF == 0:
            _raise_if_cancelled(cancelled)
        retained.add((record.provenance_sha256, record.generated))
    keys = tuple(sorted(retained))
    entries = tuple(
        ProvenanceEntry(index, source, generated) for index, (source, generated) in enumerate(keys)
    )
    identifiers = {key: index for index, key in enumerate(keys)}
    by_sha: dict[str, list[int]] = {}
    for index, (sources, _generated) in enumerate(keys):
        for source in sources:
            by_sha.setdefault(source, []).append(index)
    return (
        ProvenanceTable(entries),
        identifiers,
        {source: tuple(values) for source, values in by_sha.items()},
    )


def _build_symbol_index(
    normalized: NormalizedOntology | NormalizedQuery,
    roles: RoleAxiomGraph,
    limits: CompilationLimits,
    *,
    base_table: SymbolTable | None = None,
    seed_nodes: tuple[owl.StructuralNode, ...] = (),
    query_context: QueryCompilationContext | None = None,
    cancelled: Callable[[], bool] | None = None,
) -> _SymbolIndex:
    if base_table is not None and not isinstance(base_table, SymbolTable):
        raise TypeError("base_table must be SymbolTable or None")
    if query_context is not None and base_table is None:
        raise ValueError("query_context requires base_table")
    retained: dict[SymbolKind, dict[bytes, tuple[str, bool, bool]]] = {
        kind: {} for kind in SymbolKind
    }
    query_symbols = {
        definition.symbol.canonical_bytes()
        for definition in normalized.definitions
        if definition.query_local
    }
    generated_symbols = {
        definition.symbol.canonical_bytes() for definition in normalized.definitions
    }

    def retain(kind: SymbolKind, node: owl.StructuralNode, display: str | None = None) -> None:
        encoded = node.canonical_bytes()
        retained[kind][encoded] = (
            display or _display(node),
            encoded in generated_symbols,
            encoded in query_symbols,
        )

    if base_table is None or query_context is None:
        for builtin_class in (owl.OWL_THING, owl.OWL_NOTHING):
            retain(SymbolKind.ENTITY, builtin_class, _display_entity(builtin_class))
            retain(SymbolKind.CLASS_EXPRESSION, builtin_class)
        retain(SymbolKind.ENTITY, owl.RDFS_LITERAL, _display_entity(owl.RDFS_LITERAL))
        retain(SymbolKind.DATA_RANGE, owl.RDFS_LITERAL)
        for role in roles.object_roles:
            retain(SymbolKind.OBJECT_ROLE, role)
        for property in roles.data_properties:
            retain(SymbolKind.DATA_PROPERTY, property)
    for entity in getattr(normalized, "declared_entities", ()):
        retain(SymbolKind.ENTITY, entity, _display_entity(entity))
        if isinstance(entity, owl.Class):
            retain(SymbolKind.CLASS_EXPRESSION, entity)
        elif isinstance(entity, owl.Datatype):
            retain(SymbolKind.DATA_RANGE, entity)
        elif isinstance(entity, owl.ObjectProperty):
            retain(SymbolKind.OBJECT_ROLE, entity)
        elif isinstance(entity, owl.DataProperty):
            retain(SymbolKind.DATA_PROPERTY, entity)
        elif isinstance(entity, owl.NamedIndividual):
            retain(SymbolKind.INDIVIDUAL, entity)
    nodes: list[owl.StructuralNode] = list(seed_nodes)
    for index, record in enumerate(normalized.records):
        if index & 0x3F == 0:
            _raise_if_cancelled(cancelled)
        statement = record.statement
        if isinstance(statement, DataRangeInclusion):
            nodes.extend(owl.walk(statement.sub_range))
            nodes.extend(owl.walk(statement.super_range))
        else:
            nodes.extend(owl.walk(statement))
    for index, definition in enumerate(normalized.definitions):
        if index & 0x3F == 0:
            _raise_if_cancelled(cancelled)
        nodes.extend(owl.walk(definition.symbol))
        nodes.extend(owl.walk(definition.expression))
    for index, node in enumerate(nodes):
        if index & 0xFF == 0:
            _raise_if_cancelled(cancelled)
        if isinstance(node, owl.Entity):
            retain(SymbolKind.ENTITY, node, _display_entity(node))
        if isinstance(node, owl.CLASS_EXPRESSION_TYPES):
            retain(SymbolKind.CLASS_EXPRESSION, node)
        if isinstance(node, owl.DATA_RANGE_TYPES):
            retain(SymbolKind.DATA_RANGE, node)
        if isinstance(node, (owl.ObjectProperty, owl.ObjectInverseOf)):
            retain(SymbolKind.OBJECT_ROLE, node)
        if isinstance(node, owl.DataProperty):
            retain(SymbolKind.DATA_PROPERTY, node)
        if isinstance(node, (owl.NamedIndividual, owl.AnonymousIndividual)):
            retain(SymbolKind.INDIVIDUAL, node)
        if isinstance(node, owl.Literal):
            retain(SymbolKind.SOURCE_LITERAL, node)
    literal_nodes = {
        node.canonical_bytes(): node for node in nodes if isinstance(node, owl.Literal)
    }
    compiled_literals: dict[bytes, CompiledLiteral | None] = {}
    data_value_key_by_source: dict[bytes, bytes] = {}
    for index, (source_key, literal) in enumerate(literal_nodes.items()):
        if index & 0x3F == 0:
            _raise_if_cancelled(cancelled)
        if literal.datatype.iri.value in SUPPORTED_DATATYPES:
            compiled = compile_literal(literal)
            identity_payload = json.dumps(
                compiled.data_identity.as_tagged(),
                ensure_ascii=False,
                separators=(",", ":"),
            ).encode("utf-8")
            identity_key = b"pyhermit:data-identity:v1\0" + identity_payload
        else:
            compiled = None
            identity_key = b"pyhermit:unsupported-data-identity:v1\0" + source_key
        compiled_literals[source_key] = compiled
        data_value_key_by_source[source_key] = identity_key
        retained[SymbolKind.DATA_VALUE][identity_key] = (
            f"data-value:{hashlib.sha256(identity_key).hexdigest()}",
            False,
            False,
        )
    domains: list[SymbolDomain] = []
    indexes: dict[SymbolKind, Mapping[bytes, int]] = {}
    source_literals: list[owl.Literal] = []
    individuals: list[owl.Individual] = []
    data_ranges: list[owl.DataRange] = []
    data_range_nodes = {
        node.canonical_bytes(): node
        for node in itertools.chain(
            (owl.RDFS_LITERAL,),
            getattr(normalized, "declared_entities", ()),
            nodes,
        )
        if isinstance(node, owl.DATA_RANGE_TYPES)
    }
    for kind in sorted(SymbolKind, key=lambda value: value.value):
        _raise_if_cancelled(cancelled)
        values = retained[kind]
        base_values = () if base_table is None else base_table.domain(kind).values
        base_keys: Mapping[bytes, int] | set[bytes]
        if query_context is None:
            base_keys = {bytes.fromhex(value.key_hex) for value in base_values}
        else:
            base_keys = query_context.domain_by_kind[kind]
        new_values = tuple(
            sorted(
                (
                    (encoded, metadata)
                    for encoded, metadata in values.items()
                    if encoded not in base_keys
                ),
                key=lambda item: item[0],
            )
        )
        total_count = len(base_values) + len(new_values)
        if total_count > limits.max_symbols_per_domain:
            raise ResourceLimitError(
                f"compiled {kind.value} symbol limit exceeded",
                limit="max_symbols_per_domain",
                observed=total_count,
                allowed=limits.max_symbols_per_domain,
            )
        combined_values = tuple(base_values) + tuple(
            SymbolValue(
                len(base_values) + index,
                encoded.hex(),
                display,
                generated,
                query_local or base_table is not None,
            )
            for index, (encoded, (display, generated, query_local)) in enumerate(new_values)
        )
        if query_context is None:
            domain_index: Mapping[bytes, int] = {
                bytes.fromhex(value.key_hex): value.identifier for value in combined_values
            }
        else:
            domain_index = _OverlayIndex(
                {
                    encoded: len(base_values) + index
                    for index, (encoded, _metadata) in enumerate(new_values)
                },
                query_context.domain_by_kind[kind],
            )
        indexes[kind] = domain_index
        if kind is SymbolKind.DATA_VALUE:
            local_source_ids = {
                source_key: domain_index[identity_key]
                for source_key, identity_key in data_value_key_by_source.items()
            }
            indexes[kind] = (
                local_source_ids
                if query_context is None
                else _OverlayIndex(local_source_ids, query_context.by_kind[kind])
            )
        domains.append(
            SymbolDomain(
                kind,
                combined_values,
            )
        )
        if kind is SymbolKind.SOURCE_LITERAL:
            if query_context is None:
                source_literals = [
                    literal_nodes[bytes.fromhex(value.key_hex)] for value in combined_values
                ]
            else:
                source_literals = list(query_context.source_literals)
                source_literals.extend(
                    literal_nodes[bytes.fromhex(value.key_hex)]
                    for value in combined_values[len(base_values) :]
                )
        if kind is SymbolKind.DATA_RANGE:
            if query_context is None:
                data_ranges = [
                    cast(owl.DataRange, data_range_nodes[bytes.fromhex(value.key_hex)])
                    for value in combined_values
                ]
            else:
                data_ranges = list(query_context.data_ranges)
                data_ranges.extend(
                    cast(owl.DataRange, data_range_nodes[bytes.fromhex(value.key_hex)])
                    for value in combined_values[len(base_values) :]
                )
        if kind is SymbolKind.INDIVIDUAL:
            by_key_individual = {
                node.canonical_bytes(): node
                for node in itertools.chain(getattr(normalized, "declared_entities", ()), nodes)
                if isinstance(node, (owl.NamedIndividual, owl.AnonymousIndividual))
            }
            if query_context is None:
                individuals = [
                    by_key_individual[bytes.fromhex(value.key_hex)] for value in combined_values
                ]
            else:
                individuals = list(query_context.individuals)
                individuals.extend(
                    by_key_individual[bytes.fromhex(value.key_hex)]
                    for value in combined_values[len(base_values) :]
                )
    return _SymbolIndex(
        SymbolTable(tuple(domains)),
        indexes,
        tuple(individuals),
        tuple(data_ranges),
        tuple(source_literals),
        compiled_literals,
    )


def _display(node: owl.StructuralNode) -> str:
    if isinstance(node, owl.Entity):
        return _display_entity(node)
    if isinstance(node, owl.ObjectInverseOf):
        return f"inverse_object_property:{node.property.iri.value}"
    if isinstance(node, owl.AnonymousIndividual):
        return f"anonymous:{node.document_scope.hex()}:{node.local_key.hex()}"
    if isinstance(node, owl.Literal):
        language = "" if node.language is None else f"@{node.language}"
        return f"literal:{node.lexical_form!r}^^{node.datatype.iri.value}{language}"
    digest = hashlib.sha256(node.canonical_bytes()).hexdigest()
    return f"{type(node).__name__}:{digest}"


def _display_entity(entity: owl.Entity) -> str:
    return f"{entity.kind.value}:{entity.iri.value}"


def _entity_kind_from_display(display: str) -> str:
    return display.split(":", 1)[0]


def _entity_iri_from_display(display: str) -> str:
    return display.split(":", 1)[1]


def _object_role_predicate(
    state: _CompilationState,
    role: owl.ObjectPropertyExpression,
    *,
    negative: bool = False,
) -> _PredicateSpec:
    return _PredicateSpec(
        PredicateKind.NEGATED_OBJECT_ROLE if negative else PredicateKind.OBJECT_ROLE,
        (TermSort.OBJECT, TermSort.OBJECT),
        role_id=state.roles.object_role_id(role),
    )


def _data_role_predicate(
    state: _CompilationState,
    property: owl.DataProperty,
    *,
    negative: bool = False,
) -> _PredicateSpec:
    return _PredicateSpec(
        PredicateKind.NEGATED_DATA_ROLE if negative else PredicateKind.DATA_ROLE,
        (TermSort.OBJECT, TermSort.DATA),
        role_id=state.roles.data_property_id(property),
    )


def _class_predicate(
    state: _CompilationState,
    expression: owl.ClassExpression,
    *,
    negative: bool = False,
) -> _PredicateSpec:
    if isinstance(expression, owl.ObjectComplementOf):
        return _class_predicate(state, expression.operand, negative=not negative)
    symbol_id = state.symbols.identifier(SymbolKind.CLASS_EXPRESSION, expression)
    if isinstance(expression, owl.ObjectOneOf):
        individual_ids = tuple(
            state.symbols.identifier(SymbolKind.INDIVIDUAL, value)
            for value in expression.individuals
        )
        predicate = _PredicateSpec(
            PredicateKind.NEGATED_NOMINAL if negative else PredicateKind.NOMINAL,
            (TermSort.OBJECT,),
            symbol_id=symbol_id,
            annotation=individual_ids,
        )
        state._nominal_semantics.add(predicate)
        return predicate
    if not isinstance(expression, owl.Class):
        raise TypeError(f"expected a normalized class literal, got {type(expression).__name__}")
    return _PredicateSpec(
        PredicateKind.NEGATED_CONCEPT if negative else PredicateKind.CONCEPT,
        (TermSort.OBJECT,),
        symbol_id=symbol_id,
    )


def _data_predicate(
    state: _CompilationState,
    data_range: owl.DataRange,
    *,
    negative: bool = False,
    arity: int = 1,
) -> _PredicateSpec:
    if isinstance(data_range, owl.DataComplementOf):
        return _data_predicate(
            state,
            data_range.operand,
            negative=not negative,
            arity=arity,
        )
    if isinstance(arity, bool) or not isinstance(arity, int) or arity < 1:
        raise ValueError("data-range predicate arity must be positive")
    if not isinstance(data_range, (owl.Datatype, owl.DatatypeRestriction, owl.DataOneOf)):
        raise TypeError(f"expected a normalized data literal, got {type(data_range).__name__}")
    return _PredicateSpec(
        PredicateKind.NEGATED_DATA_RANGE if negative else PredicateKind.DATA_RANGE,
        (TermSort.DATA,) * arity,
        symbol_id=state.symbols.identifier(SymbolKind.DATA_RANGE, data_range),
    )


def _equality(sort: TermSort, *, inequality: bool = False) -> _PredicateSpec:
    return _PredicateSpec(
        PredicateKind.INEQUALITY if inequality else PredicateKind.EQUALITY,
        (sort, sort),
    )


def _named_predicate() -> _PredicateSpec:
    return _PredicateSpec(
        PredicateKind.NAMED_INDIVIDUAL,
        (TermSort.OBJECT,),
        internal_key="named-individual",
    )


def _ordering_predicate(sort: TermSort) -> _PredicateSpec:
    return _PredicateSpec(
        PredicateKind.ORDERING_GUARD,
        (sort, sort),
        internal_key=f"canonical-{sort.value}-order",
    )


def _annotated_equality(
    state: _CompilationState,
    cardinality: int,
    role: owl.ObjectPropertyExpression,
    filler: owl.ClassExpression,
) -> _PredicateSpec:
    if cardinality < 1:
        raise ValueError("annotated equality requires a positive at-most cardinality")
    return _PredicateSpec(
        PredicateKind.ANNOTATED_EQUALITY,
        (TermSort.OBJECT, TermSort.OBJECT, TermSort.OBJECT),
        role_id=state.roles.object_role_id(role),
        cardinality=cardinality,
        filler=_class_predicate(state, filler),
    )


def _at_least_object(
    state: _CompilationState,
    cardinality: int,
    role: owl.ObjectPropertyExpression,
    filler: owl.ClassExpression,
    *,
    negative_filler: bool = False,
) -> _PredicateSpec:
    if cardinality < 1:
        raise ValueError("at-least cardinality must be positive")
    return _PredicateSpec(
        PredicateKind.AT_LEAST_OBJECT,
        (TermSort.OBJECT,),
        role_id=state.roles.object_role_id(role),
        cardinality=cardinality,
        filler=_class_predicate(state, filler, negative=negative_filler),
    )


def _at_least_data(
    state: _CompilationState,
    cardinality: int,
    properties: tuple[owl.DataProperty, ...],
    filler: owl.DataRange,
    *,
    negative_filler: bool = False,
) -> _PredicateSpec:
    if cardinality < 1:
        raise ValueError("at-least cardinality must be positive")
    if not properties:
        raise ValueError("data at-least requires at least one property")
    role_ids = tuple(state.roles.data_property_id(value) for value in properties)
    return _PredicateSpec(
        PredicateKind.AT_LEAST_DATA,
        (TermSort.OBJECT,),
        role_id=role_ids[0],
        cardinality=cardinality,
        filler=_data_predicate(
            state,
            filler,
            negative=negative_filler,
            arity=len(properties),
        ),
        annotation=role_ids,
    )


def _individual_term(state: _CompilationState, value: owl.Individual) -> IndividualTerm:
    return IndividualTerm(state.symbols.identifier(SymbolKind.INDIVIDUAL, value))


def _data_term(state: _CompilationState, value: owl.Literal) -> DataConstant:
    source_id = state.symbols.identifier(SymbolKind.SOURCE_LITERAL, value)
    identity_id = state.symbols.identifier(SymbolKind.DATA_VALUE, value)
    return DataConstant(source_id, identity_id)


_ROLE_GRAPH_ONLY_TYPES = frozenset(
    {
        owl.SubObjectPropertyOf,
        owl.EquivalentObjectProperties,
        owl.InverseObjectProperties,
        owl.SymmetricObjectProperty,
        owl.TransitiveObjectProperty,
        owl.SubDataPropertyOf,
        owl.EquivalentDataProperties,
    }
)


def _compile_record(state: _CompilationState, record: NormalizedRecord) -> None:
    statement = record.statement
    provenance = state.provenance_for(record)
    constructor = type(statement)
    if constructor not in CLAUSIFICATION_HANDLER_TABLE:
        raise RuntimeError(
            f"normalized constructor {constructor.__name__} is outside the closed handler table"
        )
    if constructor in _ROLE_GRAPH_ONLY_TYPES:
        return
    if isinstance(statement, owl.SubClassOf):
        _compile_class_inclusion(
            state,
            statement.sub_class,
            statement.super_class,
            provenance,
        )
        return
    if isinstance(statement, owl.DisjointClasses):
        _compile_disjoint_classes(state, tuple(statement.expressions), provenance)
        return
    if isinstance(statement, owl.DisjointObjectProperties):
        _compile_disjoint_object_roles(state, tuple(statement.properties), provenance)
        return
    if isinstance(statement, owl.ObjectPropertyDomain):
        x = Variable(0, TermSort.OBJECT)
        y = Variable(1, TermSort.OBJECT)
        body = (state.atom(_object_role_predicate(state, statement.property), x, y),)
        _compile_class_consequent(state, body, (), statement.domain, x, provenance)
        return
    if isinstance(statement, owl.ObjectPropertyRange):
        x = Variable(0, TermSort.OBJECT)
        y = Variable(1, TermSort.OBJECT)
        body = (state.atom(_object_role_predicate(state, statement.property), x, y),)
        _compile_class_consequent(state, body, (), statement.range, y, provenance)
        return
    if isinstance(statement, owl.FunctionalObjectProperty):
        _compile_object_functionality(state, statement.property, False, provenance)
        return
    if isinstance(statement, owl.InverseFunctionalObjectProperty):
        _compile_object_functionality(state, statement.property, True, provenance)
        return
    if isinstance(statement, owl.ReflexiveObjectProperty):
        x = Variable(0, TermSort.OBJECT)
        thing = _class_predicate(state, owl.OWL_THING)
        state.add_clause(
            (state.atom(thing, x),),
            (state.atom(_object_role_predicate(state, statement.property), x, x),),
            provenance,
        )
        return
    if isinstance(statement, owl.IrreflexiveObjectProperty):
        x = Variable(0, TermSort.OBJECT)
        state.add_clause(
            (state.atom(_object_role_predicate(state, statement.property), x, x),),
            (),
            provenance,
        )
        return
    if isinstance(statement, owl.AsymmetricObjectProperty):
        x = Variable(0, TermSort.OBJECT)
        y = Variable(1, TermSort.OBJECT)
        role = _object_role_predicate(state, statement.property)
        state.add_clause(
            (state.atom(role, x, y), state.atom(role, y, x)),
            (),
            provenance,
        )
        return
    if isinstance(statement, owl.DisjointDataProperties):
        _compile_disjoint_data_roles(state, tuple(statement.properties), provenance)
        return
    if isinstance(statement, owl.DataPropertyDomain):
        x = Variable(0, TermSort.OBJECT)
        y = Variable(1, TermSort.DATA)
        body = (state.atom(_data_role_predicate(state, statement.property), x, y),)
        _compile_class_consequent(state, body, (), statement.domain, x, provenance)
        return
    if isinstance(statement, owl.DataPropertyRange):
        x = Variable(0, TermSort.OBJECT)
        y = Variable(1, TermSort.DATA)
        state.add_clause(
            (state.atom(_data_role_predicate(state, statement.property), x, y),),
            (state.atom(_data_predicate(state, statement.range), y),),
            provenance,
        )
        return
    if isinstance(statement, owl.FunctionalDataProperty):
        x = Variable(0, TermSort.OBJECT)
        first = Variable(1, TermSort.DATA)
        second = Variable(2, TermSort.DATA)
        role = _data_role_predicate(state, statement.property)
        state.add_clause(
            (state.atom(role, x, first), state.atom(role, x, second)),
            (state.atom(_equality(TermSort.DATA), first, second),),
            provenance,
        )
        return
    if isinstance(statement, DataRangeInclusion):
        _compile_data_inclusion(
            state,
            statement.sub_range,
            statement.super_range,
            provenance,
        )
        return
    if isinstance(statement, owl.DatatypeDefinition):
        _compile_data_inclusion(state, statement.datatype, statement.data_range, provenance)
        _compile_data_inclusion(state, statement.data_range, statement.datatype, provenance)
        return
    if isinstance(statement, owl.HasKey):
        _compile_key(state, statement, provenance)
        return
    if isinstance(statement, owl.SameIndividual):
        _compile_same_individuals(state, tuple(statement.individuals), provenance)
        return
    if isinstance(statement, owl.DifferentIndividuals):
        _compile_different_individuals(state, tuple(statement.individuals), provenance)
        return
    if isinstance(statement, owl.ClassAssertion):
        _compile_class_assertion(state, statement, provenance)
        return
    if isinstance(statement, owl.ObjectPropertyAssertion):
        state.add_fact(
            state.atom(
                _object_role_predicate(state, statement.property),
                _individual_term(state, statement.source),
                _individual_term(state, statement.target),
            ),
            provenance,
        )
        return
    if isinstance(statement, owl.NegativeObjectPropertyAssertion):
        state.add_fact(
            state.atom(
                _object_role_predicate(state, statement.property, negative=True),
                _individual_term(state, statement.source),
                _individual_term(state, statement.target),
            ),
            provenance,
        )
        return
    if isinstance(statement, owl.DataPropertyAssertion):
        state.add_fact(
            state.atom(
                _data_role_predicate(state, statement.property),
                _individual_term(state, statement.source),
                _data_term(state, statement.value),
            ),
            provenance,
        )
        return
    if isinstance(statement, owl.NegativeDataPropertyAssertion):
        state.add_fact(
            state.atom(
                _data_role_predicate(state, statement.property, negative=True),
                _individual_term(state, statement.source),
                _data_term(state, statement.value),
            ),
            provenance,
        )
        return
    raise RuntimeError(
        f"normalized constructor {type(statement).__name__} has no clausification handler"
    )


def _compile_role_graph(state: _CompilationState) -> None:
    x = Variable(0, TermSort.OBJECT)
    y = Variable(1, TermSort.OBJECT)
    data = Variable(1, TermSort.DATA)
    for role_id, inverse_id in enumerate(state.roles.inverse_role_ids):
        if role_id > inverse_id:
            continue
        role = state.roles.object_roles[role_id]
        inverse = state.roles.object_roles[inverse_id]
        provenance = state.provenance_for_sha(None)
        state.add_clause(
            (state.atom(_object_role_predicate(state, role), x, y),),
            (state.atom(_object_role_predicate(state, inverse), y, x),),
            provenance,
        )
        if role_id != inverse_id:
            state.add_clause(
                (state.atom(_object_role_predicate(state, inverse), x, y),),
                (state.atom(_object_role_predicate(state, role), y, x),),
                provenance,
            )
    for object_inclusion in state.roles.simple_inclusions:
        if object_inclusion.sub_role_id == object_inclusion.super_role_id:
            continue
        state.add_clause(
            (
                state.atom(
                    _object_role_predicate(
                        state,
                        state.roles.object_roles[object_inclusion.sub_role_id],
                    ),
                    x,
                    y,
                ),
            ),
            (
                state.atom(
                    _object_role_predicate(
                        state,
                        state.roles.object_roles[object_inclusion.super_role_id],
                    ),
                    x,
                    y,
                ),
            ),
            state.provenance_for_sha(object_inclusion.provenance_sha256),
        )
    for data_inclusion in state.roles.data_inclusions:
        if data_inclusion.sub_property_id == data_inclusion.super_property_id:
            continue
        state.add_clause(
            (
                state.atom(
                    _data_role_predicate(
                        state,
                        state.roles.data_properties[data_inclusion.sub_property_id],
                    ),
                    x,
                    data,
                ),
            ),
            (
                state.atom(
                    _data_role_predicate(
                        state,
                        state.roles.data_properties[data_inclusion.super_property_id],
                    ),
                    x,
                    data,
                ),
            ),
            state.provenance_for_sha(data_inclusion.provenance_sha256),
        )
    for complex_inclusion in state.roles.complex_inclusions:
        variables = tuple(
            Variable(index, TermSort.OBJECT)
            for index in range(len(complex_inclusion.chain_role_ids) + 1)
        )
        body = tuple(
            state.atom(
                _object_role_predicate(state, state.roles.object_roles[role_id]),
                variables[index],
                variables[index + 1],
            )
            for index, role_id in enumerate(complex_inclusion.chain_role_ids)
        )
        head = (
            state.atom(
                _object_role_predicate(
                    state,
                    state.roles.object_roles[complex_inclusion.super_role_id],
                ),
                variables[0],
                variables[-1],
            ),
        )
        state.add_clause(
            body,
            head,
            state.provenance_for_sha(complex_inclusion.provenance_sha256),
        )
    bottom_object = state.roles.object_roles[state.roles.bottom_object_role_id]
    state.add_clause(
        (state.atom(_object_role_predicate(state, bottom_object), x, y),),
        (),
        state.provenance_for_sha(None),
    )
    bottom_data = state.roles.data_properties[state.roles.bottom_data_property_id]
    state.add_clause(
        (state.atom(_data_role_predicate(state, bottom_data), x, data),),
        (),
        state.provenance_for_sha(None),
    )


def _compile_class_inclusion(
    state: _CompilationState,
    sub_class: owl.ClassExpression,
    super_class: owl.ClassExpression,
    provenance: tuple[int, ...],
) -> None:
    if isinstance(sub_class, owl.ObjectUnionOf):
        for operand in sub_class.operands:
            _compile_class_inclusion(state, operand, super_class, provenance)
        return
    if isinstance(super_class, owl.ObjectIntersectionOf):
        for operand in super_class.operands:
            _compile_class_inclusion(state, sub_class, operand, provenance)
        return
    x = Variable(0, TermSort.OBJECT)
    body, head = _compile_class_antecedent(state, sub_class, x)
    if not body:
        body = (state.atom(_class_predicate(state, owl.OWL_THING), x),)
    _compile_class_consequent(state, body, head, super_class, x, provenance)


def _compile_class_antecedent(
    state: _CompilationState,
    expression: owl.ClassExpression,
    root: Variable | IndividualTerm,
) -> tuple[tuple[_AtomSpec, ...], tuple[_AtomSpec, ...]]:
    if isinstance(expression, (owl.Class, owl.ObjectOneOf, owl.ObjectComplementOf)):
        return ((state.atom(_class_predicate(state, expression), root),), ())
    if isinstance(expression, owl.ObjectIntersectionOf):
        return (
            tuple(
                state.atom(_class_predicate(state, operand), root)
                for operand in expression.operands
            ),
            (),
        )
    if isinstance(expression, owl.ObjectSomeValuesFrom):
        target = Variable(1, TermSort.OBJECT)
        return (
            (
                state.atom(_object_role_predicate(state, expression.property), root, target),
                state.atom(_class_predicate(state, expression.filler), target),
            ),
            (),
        )
    if isinstance(expression, owl.ObjectAllValuesFrom):
        return (
            (),
            (
                state.atom(
                    _at_least_object(
                        state,
                        1,
                        expression.property,
                        expression.filler,
                        negative_filler=True,
                    ),
                    root,
                ),
            ),
        )
    if isinstance(expression, owl.ObjectHasSelf):
        return (
            (state.atom(_object_role_predicate(state, expression.property), root, root),),
            (),
        )
    if isinstance(expression, owl.ObjectMinCardinality):
        if expression.cardinality == 0:
            return ((state.atom(_class_predicate(state, owl.OWL_THING), root),), ())
        return (
            (
                state.atom(
                    _at_least_object(
                        state,
                        expression.cardinality,
                        expression.property,
                        expression.filler,
                    ),
                    root,
                ),
            ),
            (),
        )
    if isinstance(expression, owl.ObjectMaxCardinality):
        return (
            (),
            (
                state.atom(
                    _at_least_object(
                        state,
                        expression.cardinality + 1,
                        expression.property,
                        expression.filler,
                    ),
                    root,
                ),
            ),
        )
    if isinstance(expression, owl.DataSomeValuesFrom):
        targets = tuple(
            Variable(index + 1, TermSort.DATA) for index in range(len(expression.properties))
        )
        return (
            (
                *(
                    state.atom(_data_role_predicate(state, property), root, target)
                    for property, target in zip(
                        expression.properties,
                        targets,
                        strict=True,
                    )
                ),
                state.atom(
                    _data_predicate(state, expression.filler, arity=len(targets)),
                    *targets,
                ),
            ),
            (),
        )
    if isinstance(expression, owl.DataAllValuesFrom):
        return (
            (),
            (
                state.atom(
                    _at_least_data(
                        state,
                        1,
                        tuple(expression.properties),
                        expression.filler,
                        negative_filler=True,
                    ),
                    root,
                ),
            ),
        )
    if isinstance(expression, owl.DataMinCardinality):
        if expression.cardinality == 0:
            return ((state.atom(_class_predicate(state, owl.OWL_THING), root),), ())
        return (
            (
                state.atom(
                    _at_least_data(
                        state,
                        expression.cardinality,
                        (expression.property,),
                        expression.filler,
                    ),
                    root,
                ),
            ),
            (),
        )
    if isinstance(expression, owl.DataMaxCardinality):
        return (
            (),
            (
                state.atom(
                    _at_least_data(
                        state,
                        expression.cardinality + 1,
                        (expression.property,),
                        expression.filler,
                    ),
                    root,
                ),
            ),
        )
    raise RuntimeError(f"unhandled normalized class antecedent {type(expression).__name__}")


def _compile_class_consequent(
    state: _CompilationState,
    body: tuple[_AtomSpec, ...],
    head: tuple[_AtomSpec, ...],
    expression: owl.ClassExpression,
    root: Variable | IndividualTerm,
    provenance: tuple[int, ...],
) -> None:
    if isinstance(expression, (owl.Class, owl.ObjectOneOf, owl.ObjectComplementOf)):
        state.add_clause(
            body,
            (*head, state.atom(_class_predicate(state, expression), root)),
            provenance,
        )
        return
    if isinstance(expression, owl.ObjectUnionOf):
        state.add_clause(
            body,
            head
            + tuple(
                state.atom(_class_predicate(state, operand), root)
                for operand in expression.operands
            ),
            provenance,
        )
        return
    if isinstance(expression, owl.ObjectIntersectionOf):
        for operand in expression.operands:
            _compile_class_consequent(state, body, head, operand, root, provenance)
        return
    if isinstance(expression, owl.ObjectSomeValuesFrom):
        state.add_clause(
            body,
            (
                *head,
                state.atom(
                    _at_least_object(state, 1, expression.property, expression.filler),
                    root,
                ),
            ),
            provenance,
        )
        return
    if isinstance(expression, owl.ObjectAllValuesFrom):
        _compile_object_universal(
            state,
            body,
            head,
            root,
            expression.property,
            expression.filler,
            provenance,
        )
        return
    if isinstance(expression, owl.ObjectHasSelf):
        state.add_clause(
            body,
            (
                *head,
                state.atom(_object_role_predicate(state, expression.property), root, root),
            ),
            provenance,
        )
        return
    if isinstance(expression, owl.ObjectMinCardinality):
        if expression.cardinality == 0:
            return
        state.add_clause(
            body,
            (
                *head,
                state.atom(
                    _at_least_object(
                        state,
                        expression.cardinality,
                        expression.property,
                        expression.filler,
                    ),
                    root,
                ),
            ),
            provenance,
        )
        return
    if isinstance(expression, owl.ObjectMaxCardinality):
        _compile_object_at_most(
            state,
            body,
            head,
            root,
            expression.cardinality,
            expression.property,
            expression.filler,
            provenance,
        )
        return
    if isinstance(expression, owl.DataSomeValuesFrom):
        state.add_clause(
            body,
            (
                *head,
                state.atom(
                    _at_least_data(
                        state,
                        1,
                        tuple(expression.properties),
                        expression.filler,
                    ),
                    root,
                ),
            ),
            provenance,
        )
        return
    if isinstance(expression, owl.DataAllValuesFrom):
        first_fresh = _fresh_variable_index(body, head, root)
        targets = tuple(
            Variable(first_fresh + index, TermSort.DATA)
            for index in range(len(expression.properties))
        )
        extra_body = tuple(
            state.atom(_data_role_predicate(state, property), root, target)
            for property, target in zip(expression.properties, targets, strict=True)
        )
        state.add_clause(
            body + extra_body,
            (
                *head,
                state.atom(
                    _data_predicate(state, expression.filler, arity=len(targets)),
                    *targets,
                ),
            ),
            provenance,
        )
        return
    if isinstance(expression, owl.DataMinCardinality):
        if expression.cardinality == 0:
            return
        state.add_clause(
            body,
            (
                *head,
                state.atom(
                    _at_least_data(
                        state,
                        expression.cardinality,
                        (expression.property,),
                        expression.filler,
                    ),
                    root,
                ),
            ),
            provenance,
        )
        return
    if isinstance(expression, owl.DataMaxCardinality):
        _compile_data_at_most(
            state,
            body,
            head,
            root,
            expression.cardinality,
            expression.property,
            expression.filler,
            provenance,
        )
        return
    raise RuntimeError(f"unhandled normalized class consequent {type(expression).__name__}")


def _fresh_variable_index(
    body: tuple[_AtomSpec, ...],
    head: tuple[_AtomSpec, ...],
    root: Variable | IndividualTerm,
) -> int:
    indices = [
        argument.index
        for atom in body + head
        for argument in atom.arguments
        if isinstance(argument, Variable)
    ]
    if isinstance(root, Variable):
        indices.append(root.index)
    return max(indices, default=-1) + 1


def _compile_object_at_most(
    state: _CompilationState,
    body: tuple[_AtomSpec, ...],
    head: tuple[_AtomSpec, ...],
    root: Variable | IndividualTerm,
    cardinality: int,
    role: owl.ObjectPropertyExpression,
    filler: owl.ClassExpression,
    provenance: tuple[int, ...],
) -> None:
    first_fresh = _fresh_variable_index(body, head, root)
    targets = tuple(
        Variable(first_fresh + index, TermSort.OBJECT) for index in range(cardinality + 1)
    )
    role_predicate = _object_role_predicate(state, role)
    filler_predicate = _class_predicate(state, filler)
    extra_body = tuple(
        atom
        for target in targets
        for atom in (
            state.atom(role_predicate, root, target),
            state.atom(filler_predicate, target),
        )
    )
    if len(targets) > 2:
        extra_body += tuple(
            state.atom(_ordering_predicate(TermSort.OBJECT), left, right)
            for left, right in itertools.pairwise(targets)
        )
    if cardinality == 0:
        equalities: tuple[_AtomSpec, ...] = ()
    else:
        annotated_equality = _annotated_equality(state, cardinality, role, filler)
        equalities = tuple(
            state.atom(annotated_equality, left, right, root)
            for left, right in itertools.combinations(targets, 2)
        )
    state.add_clause(body + extra_body, head + equalities, provenance)


def _compile_data_at_most(
    state: _CompilationState,
    body: tuple[_AtomSpec, ...],
    head: tuple[_AtomSpec, ...],
    root: Variable | IndividualTerm,
    cardinality: int,
    property: owl.DataProperty,
    filler: owl.DataRange,
    provenance: tuple[int, ...],
) -> None:
    first_fresh = _fresh_variable_index(body, head, root)
    targets = tuple(
        Variable(first_fresh + index, TermSort.DATA) for index in range(cardinality + 1)
    )
    role_predicate = _data_role_predicate(state, property)
    filler_predicate = _data_predicate(state, filler)
    extra_body = tuple(
        atom
        for target in targets
        for atom in (
            state.atom(role_predicate, root, target),
            state.atom(filler_predicate, target),
        )
    )
    equalities = tuple(
        state.atom(_equality(TermSort.DATA), left, right)
        for left, right in itertools.combinations(targets, 2)
    )
    state.add_clause(body + extra_body, head + equalities, provenance)


def _compile_data_inclusion(
    state: _CompilationState,
    sub_range: owl.DataRange,
    super_range: owl.DataRange,
    provenance: tuple[int, ...],
) -> None:
    if isinstance(sub_range, owl.DataUnionOf):
        for operand in sub_range.operands:
            _compile_data_inclusion(state, operand, super_range, provenance)
        return
    if isinstance(super_range, owl.DataIntersectionOf):
        for operand in super_range.operands:
            _compile_data_inclusion(state, sub_range, operand, provenance)
        return
    value = Variable(0, TermSort.DATA)
    if isinstance(sub_range, owl.DataIntersectionOf):
        body = tuple(
            state.atom(_data_predicate(state, operand), value) for operand in sub_range.operands
        )
    elif isinstance(
        sub_range,
        (owl.Datatype, owl.DatatypeRestriction, owl.DataOneOf, owl.DataComplementOf),
    ):
        body = (state.atom(_data_predicate(state, sub_range), value),)
    else:
        raise RuntimeError(f"unhandled normalized data antecedent {type(sub_range).__name__}")
    if isinstance(super_range, owl.DataUnionOf):
        head = tuple(
            state.atom(_data_predicate(state, operand), value) for operand in super_range.operands
        )
    elif isinstance(
        super_range,
        (owl.Datatype, owl.DatatypeRestriction, owl.DataOneOf, owl.DataComplementOf),
    ):
        head = (state.atom(_data_predicate(state, super_range), value),)
    else:
        raise RuntimeError(f"unhandled normalized data consequent {type(super_range).__name__}")
    state.add_clause(body, head, provenance)


def _compile_object_universal(
    state: _CompilationState,
    body: tuple[_AtomSpec, ...],
    head: tuple[_AtomSpec, ...],
    root: Variable | IndividualTerm,
    role: owl.ObjectPropertyExpression,
    filler: owl.ClassExpression,
    provenance: tuple[int, ...],
) -> None:
    role_id = state.roles.object_role_id(role)
    component = state.roles.object_component_by_role[role_id]
    automaton = state.roles.automata.get(component)
    if automaton is None:
        target = Variable(_fresh_variable_index(body, head, root), TermSort.OBJECT)
        state.add_clause(
            (*body, state.atom(_object_role_predicate(state, role), root, target)),
            (*head, state.atom(_class_predicate(state, filler), target)),
            provenance,
        )
        return
    filler_predicate = _class_predicate(state, filler)
    automaton_key = hashlib.sha256(
        b"pyhermit:universal-automaton:v1\0"
        + component.to_bytes(4, "big")
        + _predicate_spec_key(filler_predicate)
    ).hexdigest()

    def state_predicate(state_id: int) -> _PredicateSpec:
        return _PredicateSpec(
            PredicateKind.AUTOMATON_STATE,
            (TermSort.OBJECT,),
            annotation=(component, state_id),
            internal_key=automaton_key,
        )

    state.add_clause(
        body,
        (*head, state.atom(state_predicate(automaton.initial_state), root)),
        provenance,
    )
    semantic_key = (component, filler_predicate, provenance)
    if semantic_key in state._automaton_semantics:
        return
    state._automaton_semantics.add(semantic_key)
    source = Variable(0, TermSort.OBJECT)
    target = Variable(1, TermSort.OBJECT)
    for transition in automaton.transitions:
        transition_body = [state.atom(state_predicate(transition.source_state), source)]
        transition_head: tuple[_AtomSpec, ...]
        if transition.role_id is None:
            transition_head = (state.atom(state_predicate(transition.target_state), source),)
        else:
            transition_body.append(
                state.atom(
                    _object_role_predicate(
                        state,
                        state.roles.object_roles[transition.role_id],
                    ),
                    source,
                    target,
                )
            )
            transition_head = (state.atom(state_predicate(transition.target_state), target),)
        state.add_clause(tuple(transition_body), transition_head, provenance)
    for final_state in automaton.final_states:
        state.add_clause(
            (state.atom(state_predicate(final_state), source),),
            (state.atom(filler_predicate, source),),
            provenance,
        )


def _compile_disjoint_classes(
    state: _CompilationState,
    expressions: tuple[owl.ClassExpression, ...],
    provenance: tuple[int, ...],
) -> None:
    x = Variable(0, TermSort.OBJECT)
    digest = hashlib.sha256(
        b"pyhermit:linear-disjoint-classes:v1\0"
        + b"".join(value.canonical_bytes() for value in expressions)
    ).hexdigest()
    previous: _PredicateSpec | None = None
    for index, expression in enumerate(expressions):
        current = _PredicateSpec(
            PredicateKind.DISJOINT_GUARD,
            (TermSort.OBJECT,),
            annotation=(index,),
            internal_key=digest,
        )
        member = state.atom(_class_predicate(state, expression), x)
        if previous is not None:
            state.add_clause(
                (state.atom(previous, x), member),
                (),
                provenance,
            )
            state.add_clause(
                (state.atom(previous, x),),
                (state.atom(current, x),),
                provenance,
            )
        state.add_clause((member,), (state.atom(current, x),), provenance)
        previous = current


def _compile_disjoint_object_roles(
    state: _CompilationState,
    properties: tuple[owl.ObjectPropertyExpression, ...],
    provenance: tuple[int, ...],
) -> None:
    x = Variable(0, TermSort.OBJECT)
    y = Variable(1, TermSort.OBJECT)
    for first, second in itertools.combinations(properties, 2):
        state.add_clause(
            (
                state.atom(_object_role_predicate(state, first), x, y),
                state.atom(_object_role_predicate(state, second), x, y),
            ),
            (),
            provenance,
        )


def _compile_disjoint_data_roles(
    state: _CompilationState,
    properties: tuple[owl.DataProperty, ...],
    provenance: tuple[int, ...],
) -> None:
    x = Variable(0, TermSort.OBJECT)
    y = Variable(1, TermSort.DATA)
    for first, second in itertools.combinations(properties, 2):
        state.add_clause(
            (
                state.atom(_data_role_predicate(state, first), x, y),
                state.atom(_data_role_predicate(state, second), x, y),
            ),
            (),
            provenance,
        )


def _compile_object_functionality(
    state: _CompilationState,
    role: owl.ObjectPropertyExpression,
    inverse: bool,
    provenance: tuple[int, ...],
) -> None:
    root = Variable(0, TermSort.OBJECT)
    first = Variable(1, TermSort.OBJECT)
    second = Variable(2, TermSort.OBJECT)
    predicate = _object_role_predicate(state, role)
    if inverse:
        first_atom = state.atom(predicate, first, root)
        second_atom = state.atom(predicate, second, root)
    else:
        first_atom = state.atom(predicate, root, first)
        second_atom = state.atom(predicate, root, second)
    state.add_clause(
        (first_atom, second_atom),
        (state.atom(_equality(TermSort.OBJECT), first, second),),
        provenance,
    )


def _compile_key(
    state: _CompilationState,
    statement: owl.HasKey,
    provenance: tuple[int, ...],
) -> None:
    left = Variable(0, TermSort.OBJECT)
    right = Variable(1, TermSort.OBJECT)
    head: list[_AtomSpec] = [state.atom(_equality(TermSort.OBJECT), left, right)]
    body: list[_AtomSpec] = [
        state.atom(_class_predicate(state, statement.class_expression), left),
        state.atom(_class_predicate(state, statement.class_expression), right),
        state.atom(_named_predicate(), left),
        state.atom(_named_predicate(), right),
        state.atom(_ordering_predicate(TermSort.OBJECT), left, right),
    ]
    next_index = 2
    for object_property in statement.object_properties:
        target = Variable(next_index, TermSort.OBJECT)
        next_index += 1
        predicate = _object_role_predicate(state, object_property)
        body.extend(
            (
                state.atom(predicate, left, target),
                state.atom(predicate, right, target),
                state.atom(_named_predicate(), target),
            )
        )
    for data_property in statement.data_properties:
        left_target = Variable(next_index, TermSort.DATA)
        right_target = Variable(next_index + 1, TermSort.DATA)
        next_index += 2
        predicate = _data_role_predicate(state, data_property)
        body.extend(
            (
                state.atom(predicate, left, left_target),
                state.atom(predicate, right, right_target),
            )
        )
        head.append(
            state.atom(
                _equality(TermSort.DATA, inequality=True),
                left_target,
                right_target,
            )
        )
    state.add_clause(tuple(body), tuple(head), provenance)


def _compile_same_individuals(
    state: _CompilationState,
    individuals: tuple[owl.Individual, ...],
    provenance: tuple[int, ...],
) -> None:
    first = _individual_term(state, individuals[0])
    for individual in individuals[1:]:
        state.add_fact(
            state.atom(
                _equality(TermSort.OBJECT),
                first,
                _individual_term(state, individual),
            ),
            provenance,
        )


def _compile_different_individuals(
    state: _CompilationState,
    individuals: tuple[owl.Individual, ...],
    provenance: tuple[int, ...],
) -> None:
    for first, second in itertools.combinations(individuals, 2):
        state.add_fact(
            state.atom(
                _equality(TermSort.OBJECT, inequality=True),
                _individual_term(state, first),
                _individual_term(state, second),
            ),
            provenance,
        )


def _compile_class_assertion(
    state: _CompilationState,
    statement: owl.ClassAssertion,
    provenance: tuple[int, ...],
) -> None:
    individual = _individual_term(state, statement.individual)
    expression = statement.class_expression
    if isinstance(expression, (owl.Class, owl.ObjectOneOf, owl.ObjectComplementOf)):
        state.add_fact(state.atom(_class_predicate(state, expression), individual), provenance)
        return
    _compile_class_consequent(state, (), (), expression, individual, provenance)


def _emit_builtin_facts_and_clashes(
    state: _CompilationState,
    *,
    first_local_individual_id: int = 0,
) -> None:
    provenance = state.provenance_for_sha(None)
    thing = _class_predicate(state, owl.OWL_THING)
    nothing = _class_predicate(state, owl.OWL_NOTHING)
    variable = Variable(0, TermSort.OBJECT)
    state.add_clause((state.atom(nothing, variable),), (), provenance)
    named = _named_predicate()
    for individual in state.symbols.individuals:
        term = _individual_term(state, individual)
        if term.individual_id < first_local_individual_id:
            continue
        state.add_fact(state.atom(thing, term), provenance)
        if isinstance(individual, owl.NamedIndividual):
            state.add_fact(state.atom(named, term), provenance)


def _emit_pending_nominal_semantics(state: _CompilationState) -> None:
    provenance = state.provenance_for_sha(None)
    variable = Variable(0, TermSort.OBJECT)
    positive_by_symbol = {
        predicate.symbol_id: predicate
        for predicate in state._nominal_semantics
        if predicate.kind is PredicateKind.NOMINAL
    }
    negative_by_symbol = {
        predicate.symbol_id: predicate
        for predicate in state._nominal_semantics
        if predicate.kind is PredicateKind.NEGATED_NOMINAL
    }
    for predicate in tuple(state._nominal_semantics):
        individual_terms = tuple(IndividualTerm(value) for value in predicate.annotation)
        if predicate.kind is PredicateKind.NOMINAL:
            state.add_clause(
                (state.atom(predicate, variable),),
                tuple(
                    state.atom(_equality(TermSort.OBJECT), variable, value)
                    for value in individual_terms
                ),
                provenance,
            )
            for value in individual_terms:
                state.add_clause(
                    (state.atom(_equality(TermSort.OBJECT), variable, value),),
                    (state.atom(predicate, variable),),
                    provenance,
                )
        else:
            for value in individual_terms:
                state.add_clause(
                    (state.atom(predicate, variable),),
                    (state.atom(_equality(TermSort.OBJECT, inequality=True), variable, value),),
                    provenance,
                )
        positive = positive_by_symbol.get(predicate.symbol_id)
        negative = negative_by_symbol.get(predicate.symbol_id)
        if positive is not None and negative is not None:
            state.add_clause(
                (state.atom(positive, variable), state.atom(negative, variable)),
                (),
                provenance,
            )


def _emit_complement_clashes(
    state: _CompilationState,
    *,
    base_predicates: set[_PredicateSpec] | frozenset[_PredicateSpec] | None = None,
) -> None:
    provenance = state.provenance_for_sha(None)
    opposite_kinds = {
        PredicateKind.NEGATED_CONCEPT: PredicateKind.CONCEPT,
        PredicateKind.NEGATED_NOMINAL: PredicateKind.NOMINAL,
        PredicateKind.NEGATED_DATA_RANGE: PredicateKind.DATA_RANGE,
    }
    # A counterpart is required only when normalized input actually mentions a
    # complement.  Manufacturing a negative predicate for every positive class
    # would preserve truth conditions, but it would also turn otherwise Horn
    # ontologies into exponentially branching programs.
    for predicate in tuple(state.predicates):
        opposite_kind = opposite_kinds.get(predicate.kind)
        if opposite_kind is None:
            continue
        opposite = _PredicateSpec(
            kind=opposite_kind,
            argument_sorts=predicate.argument_sorts,
            symbol_id=predicate.symbol_id,
            role_id=predicate.role_id,
            annotation=predicate.annotation,
            internal_key=predicate.internal_key,
        )
        state.retain_predicate(opposite)
        if opposite.kind in {PredicateKind.NOMINAL, PredicateKind.NEGATED_NOMINAL}:
            state._nominal_semantics.add(opposite)
    by_identity: dict[
        tuple[str, int | None, int | None, tuple[TermSort, ...]],
        dict[bool, _PredicateSpec],
    ] = {}
    positive_kinds = {
        PredicateKind.CONCEPT: PredicateKind.NEGATED_CONCEPT,
        PredicateKind.NOMINAL: PredicateKind.NEGATED_NOMINAL,
        PredicateKind.OBJECT_ROLE: PredicateKind.NEGATED_OBJECT_ROLE,
        PredicateKind.DATA_ROLE: PredicateKind.NEGATED_DATA_ROLE,
        PredicateKind.DATA_RANGE: PredicateKind.NEGATED_DATA_RANGE,
    }
    negative_to_positive = {negative: positive for positive, negative in positive_kinds.items()}
    for predicate in tuple(state.predicates):
        if predicate.kind in positive_kinds:
            base_kind = predicate.kind
            is_negative = False
        elif predicate.kind in negative_to_positive:
            base_kind = negative_to_positive[predicate.kind]
            is_negative = True
        else:
            continue
        identity = (
            base_kind.value,
            predicate.symbol_id,
            predicate.role_id,
            predicate.argument_sorts,
        )
        by_identity.setdefault(identity, {})[is_negative] = predicate
    for pair in by_identity.values():
        if set(pair) != {False, True}:
            continue
        if base_predicates is not None and all(
            predicate in base_predicates for predicate in pair.values()
        ):
            continue
        arguments = tuple(
            Variable(index, sort) for index, sort in enumerate(pair[False].argument_sorts)
        )
        state.add_clause(
            (
                state.atom(pair[False], *arguments),
                state.atom(pair[True], *arguments),
            ),
            (),
            provenance,
        )
        positive = pair[False]
        negative = pair[True]
        if positive.kind in {PredicateKind.CONCEPT, PredicateKind.NOMINAL}:
            variable = Variable(0, TermSort.OBJECT)
            state.add_clause(
                (state.atom(_class_predicate(state, owl.OWL_THING), variable),),
                (state.atom(positive, variable), state.atom(negative, variable)),
                provenance,
            )
        elif positive.kind is PredicateKind.DATA_RANGE:
            variable = Variable(0, TermSort.DATA)
            state.add_clause(
                (state.atom(_data_predicate(state, owl.RDFS_LITERAL), variable),),
                (state.atom(positive, variable), state.atom(negative, variable)),
                provenance,
            )


def _retain_runtime_predicates(state: _CompilationState) -> None:
    """Retain extension predicates needed only by runtime-created consequences."""

    predicates = tuple(state.predicates)
    for predicate in predicates:
        if predicate.kind is PredicateKind.AT_LEAST_OBJECT:
            state.retain_predicate(
                _PredicateSpec(
                    PredicateKind.OBJECT_ROLE,
                    (TermSort.OBJECT, TermSort.OBJECT),
                    role_id=predicate.role_id,
                )
            )
        elif predicate.kind is PredicateKind.AT_LEAST_DATA:
            for role_id in predicate.annotation:
                state.retain_predicate(
                    _PredicateSpec(
                        PredicateKind.DATA_ROLE,
                        (TermSort.OBJECT, TermSort.DATA),
                        role_id=role_id,
                    )
                )
    if any(
        predicate.kind is PredicateKind.AT_LEAST_OBJECT
        and predicate.cardinality is not None
        and predicate.cardinality > 1
        for predicate in predicates
    ):
        state.retain_predicate(_equality(TermSort.OBJECT, inequality=True))
    if any(
        (
            predicate.kind is PredicateKind.AT_LEAST_DATA
            and predicate.cardinality is not None
            and predicate.cardinality > 1
        )
        or predicate.kind is PredicateKind.NEGATED_DATA_ROLE
        for predicate in predicates
    ):
        state.retain_predicate(_equality(TermSort.DATA, inequality=True))


def _predicate_spec_key(predicate: _PredicateSpec) -> bytes:
    payload = {
        "annotation": list(predicate.annotation),
        "argument_sorts": [value.value for value in predicate.argument_sorts],
        "cardinality": predicate.cardinality,
        "filler": (
            None
            if predicate.filler is None
            else hashlib.sha256(_predicate_spec_key(predicate.filler)).hexdigest()
        ),
        "internal_key": predicate.internal_key,
        "kind": predicate.kind.value,
        "role_id": predicate.role_id,
        "symbol_id": predicate.symbol_id,
    }
    return json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8")


def _freeze_predicates(
    predicates: set[_PredicateSpec],
    base_registry: PredicateRegistry | None = None,
    *,
    base_specs: tuple[_PredicateSpec, ...] | None = None,
    base_set: frozenset[_PredicateSpec] | None = None,
    cancelled: Callable[[], bool] | None = None,
) -> tuple[PredicateRegistry, dict[_PredicateSpec, int]]:
    _raise_if_cancelled(cancelled)
    if base_registry is None:
        if base_specs is not None or base_set is not None:
            raise ValueError("base_specs and base_set require base_registry")
        selected_base_specs: tuple[_PredicateSpec, ...] = ()
        selected_base_set: frozenset[_PredicateSpec] = frozenset()
    else:
        selected_base_specs = (
            _predicate_specs_from_registry(base_registry) if base_specs is None else base_specs
        )
        if len(selected_base_specs) != len(base_registry.predicates):
            raise ValueError("base_specs must align with base_registry")
        selected_base_set = frozenset(selected_base_specs) if base_set is None else base_set
        if len(selected_base_set) != len(selected_base_specs):
            raise ValueError("base predicate specs must be structurally unique")
    local_specs = tuple(
        sorted(
            (predicate for predicate in predicates if predicate not in selected_base_set),
            key=_predicate_spec_key,
        )
    )
    ordered = selected_base_specs + local_specs
    identifiers = {predicate: index for index, predicate in enumerate(ordered)}
    _raise_if_cancelled(cancelled)
    first_local = len(selected_base_specs)
    values = tuple(
        Predicate(
            predicate_id=index,
            kind=predicate.kind,
            argument_sorts=predicate.argument_sorts,
            symbol_id=predicate.symbol_id,
            role_id=predicate.role_id,
            cardinality=predicate.cardinality,
            filler_predicate_id=(
                None if predicate.filler is None else identifiers[predicate.filler]
            ),
            annotation=predicate.annotation,
            internal_key=predicate.internal_key,
        )
        for index, predicate in enumerate(local_specs, start=first_local)
    )
    _raise_if_cancelled(cancelled)
    registry = (
        PredicateRegistry(values)
        if base_registry is None
        else PredicateRegistry._from_validated_extension(base_registry, values)
    )
    return registry, identifiers


def _predicate_specs_from_registry(
    registry: PredicateRegistry,
) -> tuple[_PredicateSpec, ...]:
    cache: dict[int, _PredicateSpec] = {}

    def decode(predicate_id: int) -> _PredicateSpec:
        known = cache.get(predicate_id)
        if known is not None:
            return known
        value = registry.predicate(predicate_id)
        filler = None if value.filler_predicate_id is None else decode(value.filler_predicate_id)
        result = _PredicateSpec(
            kind=value.kind,
            argument_sorts=value.argument_sorts,
            symbol_id=value.symbol_id,
            role_id=value.role_id,
            cardinality=value.cardinality,
            filler=filler,
            annotation=value.annotation,
            internal_key=value.internal_key,
        )
        cache[predicate_id] = result
        return result

    return tuple(decode(value.predicate_id) for value in registry.predicates)


def _freeze_rules(
    state: _CompilationState,
    registry: PredicateRegistry,
    predicate_ids: dict[_PredicateSpec, int],
) -> tuple[
    tuple[DLClause, ...],
    tuple[GroundAtom, ...],
    tuple[GroundAtom, ...],
    tuple[GroundDisjunctionIR, ...],
]:
    merged_facts: dict[tuple[int, tuple[Term, ...]], set[int]] = {}
    for index, fact in enumerate(state.facts):
        if index & 0xFF == 0:
            state.checkpoint()
        atom = _freeze_atom(fact.atom, predicate_ids, registry)
        merged_facts.setdefault((atom.predicate_id, atom.arguments), set()).update(
            fact.provenance_ids
        )

    merged_clauses: dict[
        tuple[tuple[Atom, ...], tuple[Atom, ...]],
        set[int],
    ] = {}
    ground_disjunction_specs: list[tuple[tuple[Atom, ...], tuple[int, ...]]] = []
    for index, raw in enumerate(state.clauses):
        if index & 0xFF == 0:
            state.checkpoint()
        body, head = _freeze_clause_atoms(
            raw,
            predicate_ids,
            registry,
            cancelled=state.cancelled,
        )
        if set(body).intersection(head):
            continue
        if (
            not body
            and head
            and all(
                not isinstance(argument, Variable) for atom in head for argument in atom.arguments
            )
        ):
            if len(head) == 1:
                atom = head[0]
                merged_facts.setdefault((atom.predicate_id, atom.arguments), set()).update(
                    raw.provenance_ids
                )
            else:
                ground_disjunction_specs.append((head, raw.provenance_ids))
            continue
        merged_clauses.setdefault((body, head), set()).update(raw.provenance_ids)

    clause_specs = tuple(
        sorted(
            (
                (
                    body,
                    head,
                    tuple(sorted(provenance)),
                )
                for (body, head), provenance in merged_clauses.items()
            ),
            key=lambda value: _rule_key(value[0], value[1]),
        )
    )
    state.checkpoint()
    clauses = tuple(
        DLClause(
            index,
            body,
            head,
            provenance,
            _plan_join_order(body, registry),
        )
        for index, (body, head, provenance) in enumerate(clause_specs)
    )

    positive: list[GroundAtom] = []
    negative: list[GroundAtom] = []
    for index, ((predicate_id, arguments), provenance) in enumerate(merged_facts.items()):
        if index & 0xFF == 0:
            state.checkpoint()
        ground_fact = GroundAtom(
            predicate_id,
            cast(tuple[IndividualTerm | DataConstant, ...], arguments),
            tuple(sorted(provenance)),
        )
        destination = (
            negative if registry.predicate(predicate_id).kind in _NEGATIVE_KINDS else positive
        )
        destination.append(ground_fact)
    positive_values = tuple(sorted(positive, key=lambda value: value.canonical_bytes()))
    negative_values = tuple(sorted(negative, key=lambda value: value.canonical_bytes()))

    merged_disjunctions: dict[
        tuple[tuple[int, tuple[IndividualTerm | DataConstant, ...]], ...],
        set[int],
    ] = {}
    for index, (atoms, disjunction_provenance) in enumerate(ground_disjunction_specs):
        if index & 0xFF == 0:
            state.checkpoint()
        identities = tuple(
            sorted(
                (
                    (
                        atom.predicate_id,
                        cast(tuple[IndividualTerm | DataConstant, ...], atom.arguments),
                    )
                    for atom in atoms
                ),
                key=lambda value: (value[0], tuple(_term_key(term) for term in value[1])),
            )
        )
        merged_disjunctions.setdefault(identities, set()).update(disjunction_provenance)
    ordered_disjunctions = tuple(
        sorted(
            merged_disjunctions.items(),
            key=lambda item: item[0],
        )
    )
    disjunctions = tuple(
        GroundDisjunctionIR(
            index,
            tuple(
                sorted(
                    (
                        GroundAtom(predicate_id, arguments, tuple(sorted(provenance)))
                        for predicate_id, arguments in identities
                    ),
                    key=lambda value: value.canonical_bytes(),
                )
            ),
            tuple(sorted(provenance)),
        )
        for index, (identities, provenance) in enumerate(ordered_disjunctions)
    )
    return clauses, positive_values, negative_values, disjunctions


def _freeze_clause_atoms(
    clause: _ClauseSpec,
    predicate_ids: dict[_PredicateSpec, int],
    registry: PredicateRegistry,
    *,
    cancelled: Callable[[], bool] | None = None,
) -> tuple[tuple[Atom, ...], tuple[Atom, ...]]:
    _raise_if_cancelled(cancelled)
    raw_body = tuple(_freeze_atom(value, predicate_ids, registry) for value in clause.body)
    raw_head = tuple(_freeze_atom(value, predicate_ids, registry) for value in clause.head)
    body = tuple(sorted(set(raw_body), key=_alpha_skeleton_key))
    head = tuple(sorted(set(raw_head), key=_alpha_skeleton_key))
    variable_count = len(
        {
            (argument.index, argument.sort)
            for atom in body + head
            for argument in atom.arguments
            if isinstance(argument, Variable)
        }
    )
    seen: set[tuple[tuple[Atom, ...], tuple[Atom, ...]]] = set()
    for _pass in range(max(2, variable_count + 2)):
        _raise_if_cancelled(cancelled)
        state = (body, head)
        if state in seen:
            raise RuntimeError("alpha-canonical clause ordering did not converge")
        seen.add(state)
        variable_map: dict[tuple[int, TermSort], int] = {}
        for index, atom in enumerate(body + head):
            if index & 0xFF == 0:
                _raise_if_cancelled(cancelled)
            for argument in atom.arguments:
                if not isinstance(argument, Variable):
                    continue
                key = (argument.index, argument.sort)
                if key not in variable_map:
                    variable_map[key] = len(variable_map)

        renamed_body = tuple(
            sorted(
                {_rename_atom(value, variable_map, registry) for value in body},
                key=lambda value: value.canonical_bytes(),
            )
        )
        renamed_head = tuple(
            sorted(
                {_rename_atom(value, variable_map, registry) for value in head},
                key=lambda value: value.canonical_bytes(),
            )
        )
        first_occurrence = tuple(
            dict.fromkeys(
                argument.index
                for atom in renamed_body + renamed_head
                for argument in atom.arguments
                if isinstance(argument, Variable)
            )
        )
        if (renamed_body, renamed_head) == state and first_occurrence == tuple(
            range(variable_count)
        ):
            return renamed_body, renamed_head
        body, head = renamed_body, renamed_head
    raise RuntimeError("alpha-canonical clause ordering exceeded its bounded passes")


def _plan_join_order(body: tuple[Atom, ...], registry: PredicateRegistry) -> tuple[int, ...]:
    """Build a deterministic connected greedy join plan over canonical body atoms."""

    remaining = set(range(len(body)))
    bound: set[tuple[int, TermSort]] = set()
    result: list[int] = []
    filters = {
        PredicateKind.EQUALITY,
        PredicateKind.INEQUALITY,
        PredicateKind.ORDERING_GUARD,
    }
    while remaining:

        def rank(index: int) -> tuple[int, int, int, int, bytes]:
            atom = body[index]
            predicate = registry.predicate(atom.predicate_id)
            variables = {
                (argument.index, argument.sort)
                for argument in atom.arguments
                if isinstance(argument, Variable)
            }
            shared = len(variables & bound)
            new = len(variables - bound)
            is_unready_filter = int(predicate.kind in filters and new > 0)
            # Prefer ready filters, then connected/selective atoms, while the
            # canonical bytes provide a total stable tie-break independent of hash order.
            return (
                is_unready_filter,
                0 if shared else 1,
                new,
                len(atom.arguments),
                atom.canonical_bytes(),
            )

        selected = min(remaining, key=rank)
        result.append(selected)
        remaining.remove(selected)
        bound.update(
            (argument.index, argument.sort)
            for argument in body[selected].arguments
            if isinstance(argument, Variable)
        )
    return tuple(result)


def _freeze_atom(
    atom: _AtomSpec,
    predicate_ids: dict[_PredicateSpec, int],
    registry: PredicateRegistry,
) -> Atom:
    return _canonicalize_symmetric_atom(
        Atom(predicate_ids[atom.predicate], atom.arguments),
        registry,
    )


def _canonicalize_symmetric_atom(atom: Atom, registry: PredicateRegistry) -> Atom:
    predicate = registry.predicate(atom.predicate_id)
    if predicate.kind is PredicateKind.ANNOTATED_EQUALITY:
        left, right, root = atom.arguments
        if _term_key(right) < _term_key(left):
            return Atom(atom.predicate_id, (right, left, root))
        return atom
    if predicate.kind not in {
        PredicateKind.EQUALITY,
        PredicateKind.INEQUALITY,
        PredicateKind.ORDERING_GUARD,
    }:
        return atom
    left, right = atom.arguments
    if _term_key(right) < _term_key(left):
        return Atom(atom.predicate_id, (right, left))
    return atom


def _rename_atom(
    atom: Atom,
    variable_map: Mapping[tuple[int, TermSort], int],
    registry: PredicateRegistry,
) -> Atom:
    arguments = tuple(
        Variable(variable_map[(value.index, value.sort)], value.sort)
        if isinstance(value, Variable)
        else value
        for value in atom.arguments
    )
    return _canonicalize_symmetric_atom(Atom(atom.predicate_id, arguments), registry)


def _term_key(term: Term) -> tuple[str, int, int]:
    if isinstance(term, Variable):
        return (f"0:{term.sort.value}", term.index, 0)
    if isinstance(term, IndividualTerm):
        return ("1:object", term.individual_id, 0)
    return ("2:data", term.data_identity_id, term.source_literal_id)


def _alpha_skeleton_key(atom: Atom) -> tuple[int, tuple[tuple[str, int, int], ...]]:
    return (
        atom.predicate_id,
        tuple(
            (f"0:{value.sort.value}", 0, value.index)
            if isinstance(value, Variable)
            else _term_key(value)
            for value in atom.arguments
        ),
    )


def _rule_key(body: tuple[Atom, ...], head: tuple[Atom, ...]) -> bytes:
    payload = {
        "body": [json.loads(value.canonical_bytes()) for value in body],
        "head": [json.loads(value.canonical_bytes()) for value in head],
    }
    return json.dumps(payload, separators=(",", ":"), sort_keys=True).encode("utf-8")


def _freeze_role_model(roles: RoleAxiomGraph) -> RoleModelIR:
    automata = tuple(
        RoleAutomatonIR(
            component_id=component,
            state_count=automaton.state_count,
            initial_state=automaton.initial_state,
            final_states=automaton.final_states,
            transitions=tuple(
                sorted(
                    (
                        RoleTransitionIR(
                            transition.source_state,
                            transition.target_state,
                            transition.role_id,
                        )
                        for transition in automaton.transitions
                    ),
                    key=lambda value: value.canonical_bytes(),
                )
            ),
        )
        for component, automaton in sorted(roles.automata.items())
    )
    return RoleModelIR(
        object_role_count=len(roles.object_roles),
        data_property_count=len(roles.data_properties),
        inverse_role_ids=roles.inverse_role_ids,
        simple_inclusions=tuple(
            sorted({(value.sub_role_id, value.super_role_id) for value in roles.simple_inclusions})
        ),
        data_inclusions=tuple(
            sorted(
                {
                    (value.sub_property_id, value.super_property_id)
                    for value in roles.data_inclusions
                }
            )
        ),
        complex_inclusions=tuple(
            sorted(
                {(value.chain_role_ids, value.super_role_id) for value in roles.complex_inclusions}
            )
        ),
        non_simple_components=tuple(sorted(roles.non_simple_components)),
        automata=automata,
        top_object_role_id=roles.top_object_role_id,
        bottom_object_role_id=roles.bottom_object_role_id,
        top_data_property_id=roles.top_data_property_id,
        bottom_data_property_id=roles.bottom_data_property_id,
    )


def _freeze_datatype_model(
    symbols: _SymbolIndex,
    normalized: NormalizedOntology | NormalizedQuery,
    *,
    base_model: DatatypeModelIR | None = None,
    base_definitions: tuple[owl.DatatypeDefinition, ...] = (),
    first_local_symbols: Mapping[str, int] | None = None,
    cancelled: Callable[[], bool] | None = None,
) -> DatatypeModelIR:
    if base_model is not None and first_local_symbols is not None:
        unchanged_domains = all(
            len(symbols.table.domain(kind).values) == first_local_symbols.get(kind.value)
            for kind in (
                SymbolKind.DATA_RANGE,
                SymbolKind.SOURCE_LITERAL,
                SymbolKind.DATA_VALUE,
            )
        )
        has_local_definition = any(
            isinstance(record.statement, owl.DatatypeDefinition) for record in normalized.records
        )
        if unchanged_domains and not has_local_definition:
            return base_model
    identities: list[LiteralIdentityIR] = list(
        () if base_model is None else base_model.literal_identities
    )
    unknown_datatypes = set(() if base_model is None else base_model.unknown_datatype_ids)
    for index, literal in enumerate(symbols.source_literals):
        if base_model is not None and index < len(base_model.literal_identities):
            continue
        if index & 0x3F == 0:
            _raise_if_cancelled(cancelled)
        source_key = literal.canonical_bytes()
        compiled = symbols.compiled_literals[source_key]
        if compiled is None:
            comparison_payload = b"pyhermit:datatype-comparison:unsupported:v1\0" + source_key
            unknown_datatypes.add(symbols.identifier(SymbolKind.DATA_RANGE, literal.datatype))
        else:
            comparison_payload = json.dumps(
                compiled.comparison.as_tagged(),
                ensure_ascii=False,
                separators=(",", ":"),
            ).encode("utf-8")
        semantic_literal = compile_literal_semantic_payload(
            literal if compiled is None else compiled,
            allow_opaque=True,
        )
        identities.append(
            LiteralIdentityIR(
                source_literal_id=index,
                data_identity_id=symbols.identifier(SymbolKind.DATA_VALUE, literal),
                comparison_key=hashlib.sha256(comparison_payload).hexdigest(),
                semantic_payload_json=semantic_literal.canonical_bytes().decode("utf-8"),
            )
        )
    definitions = list(() if base_model is None else base_model.datatype_definitions)
    for index, record in enumerate(normalized.records):
        if index & 0x3F == 0:
            _raise_if_cancelled(cancelled)
        if not isinstance(record.statement, owl.DatatypeDefinition):
            continue
        definitions.append(
            (
                symbols.identifier(SymbolKind.DATA_RANGE, record.statement.datatype),
                symbols.identifier(SymbolKind.DATA_RANGE, record.statement.data_range),
            )
        )
    unknown_datatypes.update(
        _unknown_data_range_ids(
            symbols,
            normalized,
            base_model,
            cancelled=cancelled,
        )
    )
    definition_axioms = base_definitions + tuple(
        record.statement
        for record in normalized.records
        if isinstance(record.statement, owl.DatatypeDefinition)
    )
    defined_iris = {value.datatype.iri.value for value in definition_axioms}
    opaque_iris = tuple(
        sorted(
            {
                node.iri.value
                for data_range in symbols.data_ranges
                for node in owl.walk(data_range)
                if isinstance(node, owl.Datatype)
                and node.iri.value not in SUPPORTED_DATATYPES
                and node.iri.value not in defined_iris
            }
            | {
                node.iri.value
                for definition in definition_axioms
                for node in owl.walk(definition.data_range)
                if isinstance(node, owl.Datatype)
                and node.iri.value not in SUPPORTED_DATATYPES
                and node.iri.value not in defined_iris
            }
        )
    )
    semantic_model = compile_datatype_semantic_model(
        symbols.data_ranges,
        definitions=definition_axioms,
        opaque_datatype_iris=opaque_iris,
    )
    return DatatypeModelIR(
        literal_identities=tuple(identities),
        datatype_definitions=tuple(sorted(set(definitions))),
        unknown_datatype_ids=tuple(sorted(unknown_datatypes)),
        semantic_payload_json=semantic_model.canonical_bytes().decode("utf-8"),
    )


def _unknown_data_range_ids(
    symbols: _SymbolIndex,
    normalized: NormalizedOntology | NormalizedQuery,
    base_model: DatatypeModelIR | None = None,
    *,
    cancelled: Callable[[], bool] | None = None,
) -> set[int]:
    definitions = {
        record.statement.datatype.iri.value: record.statement.data_range
        for record in normalized.records
        if isinstance(record.statement, owl.DatatypeDefinition)
    }
    base_defined_ids = {
        value[0] for value in (() if base_model is None else base_model.datatype_definitions)
    }
    base_unknown_ids = set(() if base_model is None else base_model.unknown_datatype_ids)
    cache: dict[bytes, bool] = {}

    def is_unknown(data_range: owl.DataRange, stack: frozenset[str] = frozenset()) -> bool:
        if len(cache) & 0x3F == 0:
            _raise_if_cancelled(cancelled)
        encoded = data_range.canonical_bytes()
        known = cache.get(encoded)
        if known is not None:
            return known
        if isinstance(data_range, owl.Datatype):
            iri = data_range.iri.value
            identifier = symbols.identifier(SymbolKind.DATA_RANGE, data_range)
            if iri in SUPPORTED_DATATYPES:
                result = False
            elif identifier in base_defined_ids:
                result = identifier in base_unknown_ids
            elif iri not in definitions or iri in stack:
                result = True
            else:
                result = is_unknown(definitions[iri], stack | {iri})
        elif isinstance(data_range, (owl.DataIntersectionOf, owl.DataUnionOf)):
            result = any(is_unknown(value, stack) for value in data_range.operands)
        elif isinstance(data_range, owl.DataComplementOf):
            result = is_unknown(data_range.operand, stack)
        elif isinstance(data_range, owl.DataOneOf):
            result = any(is_unknown(value.datatype, stack) for value in data_range.values)
        elif isinstance(data_range, owl.DatatypeRestriction):
            result = is_unknown(data_range.datatype, stack) or any(
                is_unknown(value.value.datatype, stack) for value in data_range.restrictions
            )
        else:  # pragma: no cover - closed by pyowl-core's DATA_RANGE_TYPES
            raise AssertionError(f"unhandled data range {type(data_range).__name__}")
        cache[encoded] = result
        return result

    result: set[int] = set()
    for index, node in enumerate(
        _normalized_nodes(
            normalized,
            cancelled=cancelled,
            include_declared_entities=False,
        )
    ):
        if index & 0xFF == 0:
            _raise_if_cancelled(cancelled)
        if isinstance(node, owl.DATA_RANGE_TYPES) and is_unknown(cast(owl.DataRange, node)):
            result.add(symbols.identifier(SymbolKind.DATA_RANGE, node))
    return result


def _derive_expressivity(
    normalized: NormalizedOntology | NormalizedQuery,
    roles: RoleAxiomGraph,
    registry: PredicateRegistry,
    clauses: tuple[DLClause, ...],
    datatype_model: DatatypeModelIR,
    *,
    cancelled: Callable[[], bool] | None = None,
) -> Expressivity:
    nodes: list[owl.StructuralNode] = []
    abox = False
    keys = False
    bottom_properties = False
    for index, record in enumerate(normalized.records):
        if index & 0x3F == 0:
            _raise_if_cancelled(cancelled)
        abox = abox or record.family is NormalizedFamily.ASSERTION
        keys = keys or record.family is NormalizedFamily.KEY
        if isinstance(record.statement, DataRangeInclusion):
            current = tuple(owl.walk(record.statement.sub_range)) + tuple(
                owl.walk(record.statement.super_range)
            )
        else:
            current = tuple(owl.walk(record.statement))
        nodes.extend(current)
        for node_index, node in enumerate(current):
            if node_index & 0xFF == 0:
                _raise_if_cancelled(cancelled)
            if isinstance(node, (owl.ObjectProperty, owl.DataProperty)) and node.iri.value in {
                owl.OWL_BOTTOM_OBJECT_PROPERTY.iri.value,
                owl.OWL_BOTTOM_DATA_PROPERTY.iri.value,
            }:
                bottom_properties = True
    kinds = {value.kind for value in registry.predicates}
    return Expressivity(
        # The role graph deliberately materializes an inverse partner for every role.
        # Expressivity records source usage, not that internal closure.
        inverse_roles=any(isinstance(value, owl.ObjectInverseOf) for value in nodes),
        nominals=any(isinstance(value, owl.ObjectOneOf) for value in nodes),
        datatypes=any(
            isinstance(
                value,
                (
                    owl.DataProperty,
                    owl.Literal,
                    *owl.DATA_RANGE_TYPES,
                    owl.DataSomeValuesFrom,
                    owl.DataAllValuesFrom,
                    owl.DataMinCardinality,
                    owl.DataMaxCardinality,
                ),
            )
            for value in nodes
        ),
        unknown_datatypes=bool(datatype_model.unknown_datatype_ids),
        complex_roles=bool(roles.complex_inclusions),
        number_restrictions=bool(
            {PredicateKind.AT_LEAST_OBJECT, PredicateKind.AT_LEAST_DATA}.intersection(kinds)
        )
        or any(
            isinstance(
                value,
                (
                    owl.ObjectMinCardinality,
                    owl.ObjectMaxCardinality,
                    owl.DataMinCardinality,
                    owl.DataMaxCardinality,
                ),
            )
            for value in nodes
        ),
        keys=keys,
        non_horn=any(len(value.head) > 1 for value in clauses),
        bottom_properties=bottom_properties,
        abox=abox,
    )


def compiled_schema_manifest() -> dict[str, object]:
    """Return the language-neutral schema input consumed by WPR0's binary codec."""

    return {
        "enums": {
            "delta_compatibility": [value.value for value in DeltaCompatibility],
            "predicate_kind": [value.value for value in PredicateKind],
            "symbol_kind": [value.value for value in SymbolKind],
            "term_sort": [value.value for value in TermSort],
        },
        "invariants": [
            "all IDs are dense unsigned 32-bit integers within their domain",
            "records reject unknown fields and schema versions",
            "clauses and facts are unique and canonically ordered",
            "variables are alpha-renamed densely and head variables are range restricted",
            "data constants retain source-literal and data-identity IDs separately",
            "query-local IDs append to immutable permanent domains",
        ],
        "records": {
            "Atom": ["predicate_id", "arguments", "schema_version"],
            "ClauseProgram": [
                "symbols",
                "predicates",
                "clauses",
                "positive_facts",
                "negative_facts",
                "ground_disjunctions",
                "role_model",
                "datatype_model",
                "expressivity",
                "provenance",
                "schema_version",
            ],
            "CompiledDelta": [
                "base_program_sha256",
                "result_program_sha256",
                "compatibility",
                "addition_sha256",
                "removal_sha256",
                "fact_additions",
                "fact_removals",
                "reasons",
                "schema_version",
            ],
            "CompiledQuery": [
                "permanent_program_sha256",
                "query_hash",
                "first_local_predicate_id",
                "first_local_symbols",
                "requires_rebuild",
                "program",
                "reason",
                "interpretation",
                "schema_version",
            ],
            "DLClause": [
                "clause_id",
                "body",
                "head",
                "provenance_ids",
                "join_order",
                "schema_version",
            ],
            "DataConstant": [
                "source_literal_id",
                "data_identity_id",
                "schema_version",
            ],
            "DeltaFactIR": [
                "predicate_id",
                "arguments",
                "negative",
                "schema_version",
            ],
            "DatatypeModelIR": [
                "literal_identities",
                "datatype_definitions",
                "unknown_datatype_ids",
                "semantic_payload_json",
                "schema_version",
            ],
            "Expressivity": [
                "inverse_roles",
                "nominals",
                "datatypes",
                "unknown_datatypes",
                "complex_roles",
                "number_restrictions",
                "keys",
                "non_horn",
                "bottom_properties",
                "abox",
                "schema_version",
            ],
            "GroundAtom": [
                "predicate_id",
                "arguments",
                "provenance_ids",
                "schema_version",
            ],
            "GroundDisjunctionIR": [
                "disjunction_id",
                "disjuncts",
                "provenance_ids",
                "schema_version",
            ],
            "IndividualTerm": ["individual_id", "schema_version"],
            "LiteralIdentityIR": [
                "source_literal_id",
                "data_identity_id",
                "comparison_key",
                "semantic_payload_json",
                "schema_version",
            ],
            "Predicate": [
                "predicate_id",
                "kind",
                "argument_sorts",
                "symbol_id",
                "role_id",
                "cardinality",
                "filler_predicate_id",
                "annotation",
                "internal_key",
                "schema_version",
            ],
            "PredicateRegistry": ["predicates", "schema_version"],
            "ProvenanceEntry": [
                "provenance_id",
                "source_sha256",
                "generated",
                "schema_version",
            ],
            "ProvenanceTable": ["entries", "schema_version"],
            "RoleAutomatonIR": [
                "component_id",
                "state_count",
                "initial_state",
                "final_states",
                "transitions",
                "schema_version",
            ],
            "RoleModelIR": [
                "object_role_count",
                "data_property_count",
                "inverse_role_ids",
                "simple_inclusions",
                "data_inclusions",
                "complex_inclusions",
                "non_simple_components",
                "automata",
                "top_object_role_id",
                "bottom_object_role_id",
                "top_data_property_id",
                "bottom_data_property_id",
                "schema_version",
            ],
            "RoleTransitionIR": [
                "source_state",
                "target_state",
                "role_id",
                "schema_version",
            ],
            "SymbolDomain": ["kind", "values", "schema_version"],
            "SymbolTable": ["domains", "predicates", "schema_version"],
            "SymbolValue": [
                "identifier",
                "key_hex",
                "display",
                "generated",
                "query_local",
                "schema_version",
            ],
            "Variable": ["index", "sort", "schema_version"],
        },
        "schema_version": COMPILED_IR_SCHEMA_VERSION,
        "wire": {
            "canonical_debug": "UTF-8 RFC 8259 JSON with lexicographically sorted keys",
            "endianness": "little",
            "id_width": "u32",
            "unknown_fields": "reject",
        },
    }
