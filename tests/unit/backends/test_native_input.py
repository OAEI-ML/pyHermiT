"""Focused Python-side tests for native input schema v1."""

from __future__ import annotations

import hashlib
import struct
from dataclasses import dataclass
from pathlib import Path

import pytest

from pyhermit.backends.native_input import (
    HEADER_SIZE,
    NativeInputError,
    SectionKind,
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
    DataConstant,
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
)
from pyhermit.config import ReasonerConfig
from tools.wire.build_native_input_fixture import canonical_fixture_json


@dataclass(frozen=True, slots=True)
class _Fingerprint:
    algorithm: str
    schema: int
    digest: bytes

    @property
    def hex(self) -> str:
        return self.digest.hex()


def _program(*, size: int = 1, query_local: bool = False, rich: bool = False) -> ClauseProgram:
    predicate = Predicate(0, PredicateKind.CONCEPT, (TermSort.OBJECT,), symbol_id=0)
    predicates = PredicateRegistry((predicate,))
    values_by_kind = {
        SymbolKind.CLASS_EXPRESSION: (
            SymbolValue(0, "01", "class:https://example.test/C", query_local=query_local),
        ),
        SymbolKind.INDIVIDUAL: tuple(
            SymbolValue(
                index,
                (index + 2).to_bytes(4, "big").hex(),
                f"individual:https://example.test/i{index}",
                query_local=query_local,
            )
            for index in range(size)
        ),
    }
    domains = tuple(
        SymbolDomain(kind, values_by_kind.get(kind, ()))
        for kind in sorted(SymbolKind, key=lambda value: value.value)
    )
    symbols = SymbolTable(domains, predicates)
    provenance = ProvenanceTable((ProvenanceEntry(0, (hashlib.sha256(b"source").hexdigest(),)),))
    facts = tuple(
        sorted(
            (GroundAtom(0, (IndividualTerm(index),), (0,)) for index in range(size)),
            key=lambda value: value.canonical_bytes(),
        )
    )
    disjunctions = ()
    if rich:
        if size < 2:
            raise ValueError("rich fixture needs two individuals")
        disjuncts = tuple(
            sorted(
                (
                    GroundAtom(0, (IndividualTerm(0),), (0,)),
                    GroundAtom(0, (IndividualTerm(1),), (0,)),
                ),
                key=lambda value: value.canonical_bytes(),
            )
        )
        disjunctions = (GroundDisjunctionIR(0, disjuncts, (0,)),)
    transitions = ()
    automata = ()
    complex_inclusions = ()
    non_simple = ()
    simple_inclusions = ()
    object_role_count = 1
    inverse_roles = (0,)
    bottom_object_role_id = 0
    if rich:
        object_role_count = 2
        inverse_roles = (0, 1)
        bottom_object_role_id = 1
        simple_inclusions = ((1, 0),)
        complex_inclusions = (((1, 1), 1),)
        non_simple = (1,)
        transitions = tuple(
            sorted(
                (
                    RoleTransitionIR(1, 2, 0),
                    RoleTransitionIR(0, 1, 1),
                    RoleTransitionIR(0, 2, None),
                ),
                key=lambda value: value.canonical_bytes(),
            )
        )
        automata = (RoleAutomatonIR(1, 3, 0, (2,), transitions),)
    return ClauseProgram(
        symbols=symbols,
        predicates=predicates,
        clauses=(),
        positive_facts=facts,
        negative_facts=(),
        ground_disjunctions=disjunctions,
        role_model=RoleModelIR(
            object_role_count=object_role_count,
            data_property_count=1,
            inverse_role_ids=inverse_roles,
            simple_inclusions=simple_inclusions,
            data_inclusions=(),
            complex_inclusions=complex_inclusions,
            non_simple_components=non_simple,
            automata=automata,
            top_object_role_id=0,
            bottom_object_role_id=bottom_object_role_id,
            top_data_property_id=0,
            bottom_data_property_id=0,
        ),
        datatype_model=DatatypeModelIR(),
        expressivity=Expressivity(
            complex_roles=rich,
            non_horn=rich,
            abox=bool(facts),
        ),
        provenance=provenance,
    )


def _ontology(*, size: int = 1, rich: bool = False) -> CompiledOntology:
    program = _program(size=size, rich=rich)
    fingerprint = _Fingerprint("sha256", 1, b"f" * 32)
    return CompiledOntology(
        schema_version=1,
        ontology_fingerprint=hashlib.sha256(b"ontology").hexdigest(),
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
        named_individuals=tuple(range(size)),
        provenance=program.provenance,
    )


def test_ontology_bytes_are_deterministic_hashed_and_large_bulk() -> None:
    small = encode_ontology(_ontology())
    assert small == encode_ontology(_ontology())
    assert small[:8] == b"PYHMINP\0"
    assert int.from_bytes(small[16:24], "little") == len(small)
    assert small[40:72] == hashlib.sha256(small[HEADER_SIZE:]).digest()

    large = encode_ontology(_ontology(size=20_000))
    assert len(large) > len(small)
    # One bulk document, not one callback/FFI object per fact.
    assert int.from_bytes(large[32:36], "little") < 32


def test_config_query_and_delta_are_concrete_deterministic_documents() -> None:
    config = ReasonerConfig(timeout=2.5, workers=3, max_memory_bytes=4096)
    assert encode_config(config) == encode_config(config)

    overlay = _program(query_local=True)
    query = CompiledQuery(
        permanent_program_sha256=hashlib.sha256(_program().canonical_bytes()).hexdigest(),
        query_hash=hashlib.sha256(b"query").hexdigest(),
        first_local_predicate_id=0,
        first_local_symbols=tuple(
            (kind.value, 0) for kind in sorted(SymbolKind, key=lambda value: value.value)
        ),
        requires_rebuild=False,
        program=overlay,
        reason="test overlay",
        interpretation=("satisfiable",),
    )
    assert encode_query(query) == encode_query(query)

    fact = DeltaFactIR(0, (IndividualTerm(0),), False)
    delta = CompiledDelta(
        base_program_sha256=hashlib.sha256(b"base").hexdigest(),
        result_program_sha256=hashlib.sha256(b"result").hexdigest(),
        compatibility=DeltaCompatibility.ASSERTION_ONLY,
        addition_sha256=(hashlib.sha256(b"addition").hexdigest(),),
        removal_sha256=(),
        fact_additions=(fact,),
        reasons=("assertion-only",),
    )
    assert encode_delta(delta) == encode_delta(delta)


def test_role_transitions_use_numeric_native_wire_order_not_ir_json_order() -> None:
    encoded = encode_ontology(_ontology(size=2, rich=True))
    section_count = struct.unpack_from("<I", encoded, 32)[0]
    transition_payload = b""
    for index in range(section_count):
        directory_offset = HEADER_SIZE + index * 32
        kind = struct.unpack_from("<H", encoded, directory_offset)[0]
        if kind != SectionKind.TRANSITIONS:
            continue
        payload_offset, payload_length = struct.unpack_from("<QQ", encoded, directory_offset + 8)
        transition_payload = encoded[payload_offset : payload_offset + payload_length]
        break

    assert transition_payload
    rows = tuple(
        struct.unpack_from("<III", transition_payload, offset)
        for offset in range(0, len(transition_payload), 12)
    )
    assert rows == (
        (0, 1, 1),
        (0, 2, (1 << 32) - 1),
        (1, 2, 0),
    )


def test_encoder_rejects_protocol_standin_and_noncanonical_semantic_json() -> None:
    with pytest.raises(TypeError, match="concrete"):
        encode_ontology(object())  # type: ignore[arg-type]

    malformed = object.__new__(DatatypeModelIR)
    object.__setattr__(malformed, "literal_identities", ())
    object.__setattr__(malformed, "datatype_definitions", ())
    object.__setattr__(malformed, "unknown_datatype_ids", ())
    object.__setattr__(malformed, "semantic_payload_json", '{"schema_version": 1}')
    object.__setattr__(malformed, "schema_version", 1)
    ontology = _ontology()
    object.__setattr__(ontology, "datatype_model", malformed)
    with pytest.raises((NativeInputError, ValueError)):
        encode_ontology(ontology)


def test_delta_keeps_source_literal_and_data_identity_ids_distinct() -> None:
    # Constructor-level coverage for the only term with two independent ID domains.
    term = DataConstant(source_literal_id=3, data_identity_id=7)
    assert term.source_literal_id != term.data_identity_id


def test_python_golden_is_byte_identical_to_the_checked_fixture() -> None:
    fixture = (Path(__file__).parents[2] / "data" / "native-input-v1.json").read_text(
        encoding="utf-8"
    )
    assert fixture.strip() == canonical_fixture_json()
