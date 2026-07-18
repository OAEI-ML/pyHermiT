"""Build the independently checked native-input-v1 golden document.

Run from the repository root with ``PYTHONPATH=src:../pyOWLCore/src``.  The tool writes
only canonical JSON to stdout so fixture updates remain an explicit reviewed edit.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass

import pyowl_core.model as owl

from pyhermit.backends.native_input import (
    encode_config,
    encode_delta,
    encode_ontology,
    encode_query,
)
from pyhermit.backends.protocol import CompiledOntology
from pyhermit.clauses import (
    ClauseProgram,
    CompiledDelta,
    CompiledQuery,
    DatatypeModelIR,
    DeltaCompatibility,
    DeltaFactIR,
    Expressivity,
    GroundAtom,
    GroundDisjunctionIR,
    IndividualTerm,
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
    TermSort,
    compile_normalized,
)
from pyhermit.config import ReasonerConfig
from pyhermit.normalize import normalize_axioms


@dataclass(frozen=True, slots=True)
class _Fingerprint:
    algorithm: str
    schema: int
    digest: bytes

    @property
    def hex(self) -> str:
        return self.digest.hex()


def _build_program() -> ClauseProgram:
    predicate = Predicate(0, PredicateKind.CONCEPT, (TermSort.OBJECT,), symbol_id=0)
    predicates = PredicateRegistry((predicate,))
    values = {
        SymbolKind.CLASS_EXPRESSION: (SymbolValue(0, "01", "class:https://example.test/C"),),
        SymbolKind.INDIVIDUAL: (
            SymbolValue(0, "02", "individual:https://example.test/a"),
            SymbolValue(1, "03", "individual:https://example.test/b"),
        ),
    }
    domains = tuple(
        SymbolDomain(kind, values.get(kind, ()))
        for kind in sorted(SymbolKind, key=lambda value: value.value)
    )
    symbols = SymbolTable(domains, predicates)
    provenance = ProvenanceTable((ProvenanceEntry(0, (hashlib.sha256(b"source").hexdigest(),)),))
    facts = tuple(
        sorted(
            (
                GroundAtom(0, (IndividualTerm(0),), (0,)),
                GroundAtom(0, (IndividualTerm(1),), (0,)),
            ),
            key=lambda value: value.canonical_bytes(),
        )
    )
    transitions = tuple(
        sorted(
            (RoleTransitionIR(0, 1, None), RoleTransitionIR(0, 1, 1)),
            key=lambda value: value.canonical_bytes(),
        )
    )
    program = ClauseProgram(
        symbols=symbols,
        predicates=predicates,
        clauses=(),
        positive_facts=facts,
        negative_facts=(),
        ground_disjunctions=(GroundDisjunctionIR(0, facts, (0,)),),
        role_model=RoleModelIR(
            object_role_count=2,
            data_property_count=1,
            inverse_role_ids=(0, 1),
            simple_inclusions=((1, 0),),
            data_inclusions=(),
            complex_inclusions=(((1, 1), 1),),
            non_simple_components=(1,),
            automata=(RoleAutomatonIR(1, 2, 0, (1,), transitions),),
            top_object_role_id=0,
            bottom_object_role_id=1,
            top_data_property_id=0,
            bottom_data_property_id=0,
        ),
        datatype_model=DatatypeModelIR(),
        expressivity=Expressivity(complex_roles=True, non_horn=True, abox=True),
        provenance=provenance,
    )
    return program


def build_fixture_document() -> bytes:
    program = _build_program()
    fingerprint = _Fingerprint("sha256", 1, b"f" * 32)
    ontology = CompiledOntology(
        schema_version=1,
        ontology_fingerprint=hashlib.sha256(b"ontology").hexdigest(),
        source_structural_fingerprint=fingerprint,
        source_logical_fingerprint=fingerprint,
        source_signature_fingerprint=fingerprint,
        core_package_version="0.1.0",
        core_api_version=(0, 1),
        core_model_schema_version=1,
        core_wire_format_version=(1, 1),
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
        named_individuals=(0, 1),
        provenance=program.provenance,
    )
    return encode_ontology(ontology)


def build_fixture_documents() -> dict[str, bytes]:
    program = _build_program()
    cutoffs = tuple(
        (kind.value, len(program.symbols.domain(kind).values))
        for kind in sorted(SymbolKind, key=lambda value: value.value)
    )
    query = CompiledQuery(
        permanent_program_sha256=hashlib.sha256(program.canonical_bytes()).hexdigest(),
        query_hash=hashlib.sha256(b"query").hexdigest(),
        first_local_predicate_id=len(program.predicates.predicates),
        first_local_symbols=cutoffs,
        requires_rebuild=False,
        program=program,
        reason="golden overlay",
        interpretation=("satisfiable",),
    )
    rebuild_query = CompiledQuery(
        permanent_program_sha256=hashlib.sha256(program.canonical_bytes()).hexdigest(),
        query_hash=hashlib.sha256(b"rebuild query").hexdigest(),
        first_local_predicate_id=len(program.predicates.predicates),
        first_local_symbols=cutoffs,
        requires_rebuild=True,
        program=None,
        reason="strategy-changing query",
    )
    delta = CompiledDelta(
        base_program_sha256=hashlib.sha256(program.canonical_bytes()).hexdigest(),
        result_program_sha256=hashlib.sha256(b"result program").hexdigest(),
        compatibility=DeltaCompatibility.ASSERTION_ONLY,
        addition_sha256=(hashlib.sha256(b"addition").hexdigest(),),
        removal_sha256=(),
        fact_additions=(DeltaFactIR(0, (IndividualTerm(0),), False),),
        reasons=("assertion-only",),
    )
    data_property = owl.DataProperty(owl.IRI("urn:golden:data"))
    individual = owl.NamedIndividual(owl.IRI("urn:golden:individual"))
    datatype = owl.Datatype(owl.IRI("http://www.w3.org/2001/XMLSchema#int"))
    datatype_program = compile_normalized(
        normalize_axioms(
            (
                owl.DataPropertyAssertion(data_property, individual, owl.Literal("01", datatype)),
                owl.DataPropertyAssertion(data_property, individual, owl.Literal("1", datatype)),
            ),
            logical_fingerprint="64" * 32,
        )
    )
    fingerprint = _Fingerprint("sha256", 1, b"d" * 32)
    datatype_ontology = CompiledOntology(
        schema_version=1,
        ontology_fingerprint=hashlib.sha256(b"datatype ontology").hexdigest(),
        source_structural_fingerprint=fingerprint,
        source_logical_fingerprint=fingerprint,
        source_signature_fingerprint=fingerprint,
        core_package_version="0.1.0",
        core_api_version=(0, 1),
        core_model_schema_version=1,
        core_wire_format_version=(1, 1),
        core_adapter_protocol_version=1,
        symbols=datatype_program.symbols,
        clauses=datatype_program.clauses,
        positive_facts=datatype_program.positive_facts,
        negative_facts=datatype_program.negative_facts,
        ground_disjunctions=datatype_program.ground_disjunctions,
        role_model=datatype_program.role_model,
        datatype_model=datatype_program.datatype_model,
        expressivity=datatype_program.expressivity,
        declared_entities=(),
        named_individuals=(0,),
        provenance=datatype_program.provenance,
    )
    return {
        "config": encode_config(ReasonerConfig(timeout=2.5, workers=3, max_memory_bytes=4096)),
        "delta": encode_delta(delta),
        "ontology": build_fixture_document(),
        "ontology_datatype": encode_ontology(datatype_ontology),
        "query": encode_query(query),
        "query_rebuild": encode_query(rebuild_query),
    }


def canonical_fixture_json() -> str:
    documents = build_fixture_documents()
    return json.dumps(
        {
            "documents": {
                name: {
                    "hex": document.hex(),
                    "sha256": hashlib.sha256(document).hexdigest(),
                }
                for name, document in sorted(documents.items())
            },
            "expected": {
                "automata": 1,
                "ground_disjunctions": 1,
                "named_individuals": 2,
                "object_roles": 2,
                "positive_facts": 2,
                "predicates": 1,
                "symbols": 3,
                "transitions": 2,
            },
            "generator": "tools.wire.build_native_input_fixture",
            "schema_version": 1,
        },
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    )


if __name__ == "__main__":
    print(canonical_fixture_json())
