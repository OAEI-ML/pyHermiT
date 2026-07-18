from __future__ import annotations

import dataclasses
import hashlib
import itertools
import json
from pathlib import Path

import pyowl_core
import pyowl_core.model as owl
import pytest

import pyhermit.clauses.compiler as clause_compiler
from pyhermit.backends.protocol import (
    CompiledDelta as BackendCompiledDelta,
)
from pyhermit.backends.protocol import (
    CompiledQuery as BackendCompiledQuery,
)
from pyhermit.clauses import (
    CLAUSIFICATION_HANDLER_TABLE,
    ClauseProgram,
    CompilationLimits,
    CompiledDelta,
    CompiledQuery,
    DeltaCompatibility,
    PredicateKind,
    SymbolKind,
    TermSort,
    Variable,
    compile_delta_plan,
    compile_normalized,
    compile_query_program,
    compiled_schema_manifest,
)
from pyhermit.config import ReasonerConfig
from pyhermit.core import CapturedOntology
from pyhermit.datatypes import (
    XSD_INTEGER,
    DatatypeSemanticEvaluator,
    OpaqueLiteralSemanticPayload,
    decode_datatype_semantic_model,
    decode_literal_semantic_payload,
)
from pyhermit.exceptions import (
    ReasonerInterruptedError,
    ResourceLimitError,
    UnsupportedDatatypeError,
)
from pyhermit.normalize import (
    NormalizedFamily,
    NormalizedOntology,
    NormalizedRecord,
    normalize_axioms,
    normalize_query,
)

FINGERPRINT = "32" * 32
INTEGER = owl.Datatype(owl.IRI(XSD_INTEGER))


def _logical_axioms() -> tuple[owl.AxiomNode, ...]:
    first = owl.Class(owl.IRI("urn:test:clauses:First"))
    second = owl.Class(owl.IRI("urn:test:clauses:Second"))
    third = owl.Class(owl.IRI("urn:test:clauses:Third"))
    role = owl.ObjectProperty(owl.IRI("urn:test:clauses:role"))
    other_role = owl.ObjectProperty(owl.IRI("urn:test:clauses:other-role"))
    data = owl.DataProperty(owl.IRI("urn:test:clauses:data"))
    other_data = owl.DataProperty(owl.IRI("urn:test:clauses:other-data"))
    datatype = owl.Datatype(owl.IRI("urn:test:clauses:datatype"))
    first_individual = owl.NamedIndividual(owl.IRI("urn:test:clauses:first"))
    second_individual = owl.NamedIndividual(owl.IRI("urn:test:clauses:second"))
    literal = owl.Literal("1", INTEGER)
    classes = owl.CanonicalSet((first, second, third))
    roles = owl.CanonicalSet((role, other_role))
    data_roles = owl.CanonicalSet((data, other_data))
    individuals = owl.CanonicalSet((first_individual, second_individual))
    return (
        owl.SubClassOf(first, owl.ObjectSomeValuesFrom(role, second)),
        owl.EquivalentClasses(classes),
        owl.DisjointClasses(classes),
        owl.DisjointUnion(first, owl.CanonicalSet((second, third))),
        owl.SubObjectPropertyOf(role, other_role),
        owl.EquivalentObjectProperties(roles),
        owl.DisjointObjectProperties(roles),
        owl.InverseObjectProperties(role, other_role),
        owl.ObjectPropertyDomain(role, first),
        owl.ObjectPropertyRange(role, second),
        owl.FunctionalObjectProperty(role),
        owl.InverseFunctionalObjectProperty(role),
        owl.ReflexiveObjectProperty(role),
        owl.IrreflexiveObjectProperty(role),
        owl.SymmetricObjectProperty(role),
        owl.AsymmetricObjectProperty(role),
        owl.TransitiveObjectProperty(role),
        owl.SubDataPropertyOf(data, other_data),
        owl.EquivalentDataProperties(data_roles),
        owl.DisjointDataProperties(data_roles),
        owl.DataPropertyDomain(data, first),
        owl.DataPropertyRange(data, INTEGER),
        owl.FunctionalDataProperty(data),
        owl.DatatypeDefinition(datatype, INTEGER),
        owl.HasKey(first, owl.CanonicalSet((role,)), owl.CanonicalSet((data,))),
        owl.SameIndividual(individuals),
        owl.DifferentIndividuals(individuals),
        owl.ClassAssertion(owl.ObjectSomeValuesFrom(role, second), first_individual),
        owl.ObjectPropertyAssertion(role, first_individual, second_individual),
        owl.NegativeObjectPropertyAssertion(role, first_individual, second_individual),
        owl.DataPropertyAssertion(data, first_individual, literal),
        owl.NegativeDataPropertyAssertion(data, first_individual, literal),
    )


def test_handler_table_is_closed_and_every_normalized_family_compiles() -> None:
    expected = {
        owl.SubClassOf,
        owl.DisjointClasses,
        owl.SubObjectPropertyOf,
        owl.EquivalentObjectProperties,
        owl.DisjointObjectProperties,
        owl.InverseObjectProperties,
        owl.ObjectPropertyDomain,
        owl.ObjectPropertyRange,
        owl.FunctionalObjectProperty,
        owl.InverseFunctionalObjectProperty,
        owl.ReflexiveObjectProperty,
        owl.IrreflexiveObjectProperty,
        owl.SymmetricObjectProperty,
        owl.AsymmetricObjectProperty,
        owl.TransitiveObjectProperty,
        owl.SubDataPropertyOf,
        owl.EquivalentDataProperties,
        owl.DisjointDataProperties,
        owl.DataPropertyDomain,
        owl.DataPropertyRange,
        owl.FunctionalDataProperty,
        owl.DatatypeDefinition,
        owl.HasKey,
        owl.SameIndividual,
        owl.DifferentIndividuals,
        owl.ClassAssertion,
        owl.ObjectPropertyAssertion,
        owl.NegativeObjectPropertyAssertion,
        owl.DataPropertyAssertion,
        owl.NegativeDataPropertyAssertion,
    }
    assert expected < set(CLAUSIFICATION_HANDLER_TABLE)
    normalized = normalize_axioms(_logical_axioms(), logical_fingerprint=FINGERPRINT)
    assert {type(value.statement) for value in normalized.records} <= set(
        CLAUSIFICATION_HANDLER_TABLE
    )
    program = compile_normalized(normalized)
    assert program.clauses
    assert program.positive_facts
    assert program.negative_facts
    assert program.expressivity.keys
    assert program.expressivity.abox


def test_permutation_is_byte_identical_and_canonical_json_round_trips() -> None:
    axioms = _logical_axioms()
    forward = compile_normalized(normalize_axioms(axioms, logical_fingerprint=FINGERPRINT))
    reverse = compile_normalized(
        normalize_axioms(tuple(reversed(axioms)), logical_fingerprint=FINGERPRINT)
    )
    assert forward.canonical_bytes() == reverse.canonical_bytes()
    assert ClauseProgram.from_canonical_json(forward.canonical_json()) == forward
    assert compiled_schema_manifest()["wire"]["id_width"] == "u32"  # type: ignore[index]


def test_declaration_only_entities_populate_typed_domains_without_fake_datatype_constraints() -> (
    None
):
    declared = (
        owl.Class(owl.IRI("urn:test:clauses:declared-class")),
        owl.ObjectProperty(owl.IRI("urn:test:clauses:declared-object-property")),
        owl.DataProperty(owl.IRI("urn:test:clauses:declared-data-property")),
        owl.NamedIndividual(owl.IRI("urn:test:clauses:declared-individual")),
        owl.Datatype(owl.IRI("urn:test:clauses:declared-datatype")),
    )
    program = compile_normalized(
        normalize_axioms(
            tuple(owl.Declaration(value) for value in declared),
            logical_fingerprint=FINGERPRINT,
        )
    )
    expected = {
        SymbolKind.CLASS_EXPRESSION: declared[0].canonical_bytes(),
        SymbolKind.OBJECT_ROLE: declared[1].canonical_bytes(),
        SymbolKind.DATA_PROPERTY: declared[2].canonical_bytes(),
        SymbolKind.INDIVIDUAL: declared[3].canonical_bytes(),
        SymbolKind.DATA_RANGE: declared[4].canonical_bytes(),
    }
    for kind, encoded in expected.items():
        assert encoded in {
            bytes.fromhex(value.key_hex) for value in program.symbols.domain(kind).values
        }
    assert not program.datatype_model.unknown_datatype_ids
    assert not program.expressivity.unknown_datatypes
    semantic_model = decode_datatype_semantic_model(
        program.datatype_model.semantic_payload_json.encode("utf-8")
    )
    declared_datatype_id = next(
        value.identifier
        for value in program.symbols.domain(SymbolKind.DATA_RANGE).values
        if bytes.fromhex(value.key_hex) == declared[4].canonical_bytes()
    )
    assert declared_datatype_id in semantic_model.opaque_data_range_ids


def test_language_neutral_schema_artifact_matches_the_runtime_manifest() -> None:
    schema = Path(__file__).parents[3] / "tools/clausification/compiled-ir-schema-v1.json"
    assert json.loads(schema.read_text()) == compiled_schema_manifest()


def test_compile_captured_preserves_the_exact_view_boundary_and_dense_rule_order(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    normalized = normalize_axioms(_logical_axioms()[:4], logical_fingerprint=FINGERPRINT)
    program = compile_normalized(normalized)
    view_marker = object()
    fingerprint = pyowl_core.Fingerprint("sha256", 1, b"v" * 32)
    captured = CapturedOntology(
        view=view_marker,  # type: ignore[arg-type]
        structural_fingerprint=fingerprint,
        logical_fingerprint=fingerprint,
        signature_fingerprint=fingerprint,
        core_package_version="0.1.0",
        core_api_version=(0, 1),
        core_model_schema_version=1,
        core_wire_format_version=(1, 0),
        core_adapter_protocol_version=1,
    )
    observed: list[object] = []

    def normalize_exact_view(view: object, **_options: object) -> NormalizedOntology:
        observed.append(view)
        return normalized

    monkeypatch.setattr(clause_compiler, "normalize_view", normalize_exact_view)
    monkeypatch.setattr(clause_compiler, "compile_normalized", lambda *_args, **_kwargs: program)
    compiled = clause_compiler.compile_captured(captured, ReasonerConfig())
    assert observed == [view_marker]
    assert compiled.clauses is program.clauses
    assert compiled.ground_disjunctions is program.ground_disjunctions


def test_compile_captured_bundle_normalizes_and_compiles_exactly_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    normalized = normalize_axioms(_logical_axioms()[:4], logical_fingerprint=FINGERPRINT)
    program = compile_normalized(normalized)
    view_marker = object()
    fingerprint = pyowl_core.Fingerprint("sha256", 1, b"b" * 32)
    captured = CapturedOntology(
        view=view_marker,  # type: ignore[arg-type]
        structural_fingerprint=fingerprint,
        logical_fingerprint=fingerprint,
        signature_fingerprint=fingerprint,
        core_package_version="0.1.0",
        core_api_version=(0, 1),
        core_model_schema_version=1,
        core_wire_format_version=(1, 0),
        core_adapter_protocol_version=1,
    )
    normalized_calls: list[object] = []
    compiled_calls: list[NormalizedOntology] = []

    def normalize_once(view: object, **_options: object) -> NormalizedOntology:
        normalized_calls.append(view)
        return normalized

    def compile_once(value: NormalizedOntology, **_options: object) -> ClauseProgram:
        compiled_calls.append(value)
        return program

    monkeypatch.setattr(clause_compiler, "normalize_view", normalize_once)
    monkeypatch.setattr(clause_compiler, "compile_normalized", compile_once)

    retained_normalized, retained_program, compiled = clause_compiler.compile_captured_bundle(
        captured, ReasonerConfig()
    )

    assert normalized_calls == [view_marker]
    assert compiled_calls == [normalized]
    assert retained_normalized is normalized
    assert retained_program is program
    assert compiled.symbols is program.symbols
    assert tuple(value.clause_id for value in compiled.clauses) == tuple(
        range(len(compiled.clauses))
    )


def test_role_automata_universals_and_qualified_cardinalities_are_explicit() -> None:
    source = owl.Class(owl.IRI("urn:test:clauses:source"))
    filler = owl.Class(owl.IRI("urn:test:clauses:filler"))
    first = owl.ObjectProperty(owl.IRI("urn:test:clauses:chain-first"))
    second = owl.ObjectProperty(owl.IRI("urn:test:clauses:chain-second"))
    target = owl.ObjectProperty(owl.IRI("urn:test:clauses:chain-target"))
    data = owl.DataProperty(owl.IRI("urn:test:clauses:cardinality-data"))
    axioms = (
        owl.SubObjectPropertyOf(owl.ObjectPropertyChain((first, second)), target),
        owl.SubClassOf(source, owl.ObjectAllValuesFrom(target, filler)),
        owl.SubClassOf(source, owl.ObjectMinCardinality(2, first, filler)),
        owl.SubClassOf(source, owl.ObjectMaxCardinality(1, first, filler)),
        owl.SubClassOf(source, owl.DataMinCardinality(2, data, INTEGER)),
        owl.SubClassOf(source, owl.DataMaxCardinality(1, data, INTEGER)),
    )
    program = compile_normalized(normalize_axioms(axioms, logical_fingerprint=FINGERPRINT))
    kinds = {value.kind for value in program.predicates.predicates}
    assert PredicateKind.AUTOMATON_STATE in kinds
    assert PredicateKind.AT_LEAST_OBJECT in kinds
    assert PredicateKind.AT_LEAST_DATA in kinds
    assert PredicateKind.ANNOTATED_EQUALITY in kinds
    assert PredicateKind.EQUALITY in kinds
    assert program.role_model.automata
    assert program.expressivity.complex_roles
    assert program.expressivity.number_restrictions


def test_keys_have_named_and_ordering_guards_and_negative_assertions_stay_negative() -> None:
    program = compile_normalized(
        normalize_axioms(_logical_axioms(), logical_fingerprint=FINGERPRINT)
    )
    kinds = {value.kind for value in program.predicates.predicates}
    assert PredicateKind.NAMED_INDIVIDUAL in kinds
    assert PredicateKind.ORDERING_GUARD in kinds
    assert {
        program.predicates.predicate(value.predicate_id).kind for value in program.negative_facts
    } == {
        PredicateKind.NEGATED_OBJECT_ROLE,
        PredicateKind.NEGATED_DATA_ROLE,
    }
    key_clause = next(
        clause
        for clause in program.clauses
        if PredicateKind.ORDERING_GUARD
        in {program.predicates.predicate(atom.predicate_id).kind for atom in clause.body}
    )
    body_kinds = {program.predicates.predicate(atom.predicate_id).kind for atom in key_clause.body}
    assert PredicateKind.NAMED_INDIVIDUAL in body_kinds
    assert (
        sum(
            kind is PredicateKind.NAMED_INDIVIDUAL
            for kind in (
                program.predicates.predicate(atom.predicate_id).kind for atom in key_clause.body
            )
        )
        == 3
    )
    assert {program.predicates.predicate(atom.predicate_id).kind for atom in key_clause.head} == {
        PredicateKind.EQUALITY,
        PredicateKind.INEQUALITY,
    }


def test_nary_disjoint_classes_compile_linearly() -> None:
    classes = tuple(
        owl.Class(owl.IRI(f"urn:test:clauses:disjoint:{index}")) for index in range(1_000)
    )
    program = compile_normalized(
        normalize_axioms(
            (owl.DisjointClasses(owl.CanonicalSet(classes)),),
            logical_fingerprint=FINGERPRINT,
        )
    )
    guards = [
        value
        for value in program.predicates.predicates
        if value.kind is PredicateKind.DISJOINT_GUARD
    ]
    assert len(guards) == len(classes)
    assert len(program.clauses) < 3 * len(classes) + 20


def test_literal_source_identity_data_identity_and_comparison_are_separate() -> None:
    property = owl.DataProperty(owl.IRI("urn:test:clauses:numeric"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:clauses:numeric-i"))
    datatype = owl.Datatype(owl.IRI("http://www.w3.org/2001/XMLSchema#int"))
    first = owl.Literal("01", datatype)
    second = owl.Literal("1", datatype)
    program = compile_normalized(
        normalize_axioms(
            (
                owl.DataPropertyAssertion(property, individual, first),
                owl.DataPropertyAssertion(property, individual, second),
            ),
            logical_fingerprint=FINGERPRINT,
        )
    )
    assert len(program.symbols.domain(SymbolKind.SOURCE_LITERAL).values) == 2
    assert len(program.symbols.domain(SymbolKind.DATA_VALUE).values) == 1
    identities = program.datatype_model.literal_identities
    assert identities[0].source_literal_id != identities[1].source_literal_id
    assert identities[0].data_identity_id == identities[1].data_identity_id
    assert identities[0].comparison_key == identities[1].comparison_key
    first_payload = decode_literal_semantic_payload(
        identities[0].semantic_payload_json.encode("utf-8")
    )
    second_payload = decode_literal_semantic_payload(
        identities[1].semantic_payload_json.encode("utf-8")
    )
    assert first_payload.canonical_bytes() != second_payload.canonical_bytes()
    semantic_model = decode_datatype_semantic_model(
        program.datatype_model.semantic_payload_json.encode("utf-8")
    )
    datatype_id = next(
        value.identifier
        for value in program.symbols.domain(SymbolKind.DATA_RANGE).values
        if bytes.fromhex(value.key_hex) == datatype.canonical_bytes()
    )
    evaluator = DatatypeSemanticEvaluator(semantic_model)
    assert evaluator.contains(datatype_id, first_payload)
    assert evaluator.contains(datatype_id, second_payload)


def test_unknown_literal_semantics_are_source_preserving_and_fail_only_when_evaluated() -> None:
    unknown = owl.Datatype(owl.IRI("urn:test:clauses:unknown-literal-datatype"))
    property = owl.DataProperty(owl.IRI("urn:test:clauses:unknown-literal-property"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:clauses:unknown-literal-i"))
    literal = owl.Literal("opaque", unknown)
    program = compile_normalized(
        normalize_axioms(
            (owl.DataPropertyAssertion(property, individual, literal),),
            logical_fingerprint=FINGERPRINT,
        )
    )
    payload = decode_literal_semantic_payload(
        program.datatype_model.literal_identities[0].semantic_payload_json.encode("utf-8")
    )
    assert isinstance(payload, OpaqueLiteralSemanticPayload)
    assert payload.source_literal() == literal
    semantic_model = decode_datatype_semantic_model(
        program.datatype_model.semantic_payload_json.encode("utf-8")
    )
    unknown_id = next(
        value.identifier
        for value in program.symbols.domain(SymbolKind.DATA_RANGE).values
        if bytes.fromhex(value.key_hex) == unknown.canonical_bytes()
    )
    assert unknown_id in program.datatype_model.unknown_datatype_ids
    assert program.expressivity.unknown_datatypes
    with pytest.raises(UnsupportedDatatypeError):
        DatatypeSemanticEvaluator(semantic_model).contains(unknown_id, payload)


def test_query_compilation_preserves_permanent_bytes_and_uses_local_ranges() -> None:
    first = owl.Class(owl.IRI("urn:test:clauses:query-first"))
    second = owl.Class(owl.IRI("urn:test:clauses:query-second"))
    third = owl.Class(owl.IRI("urn:test:clauses:query-third"))
    normalized = normalize_axioms(
        (owl.SubClassOf(first, second),),
        logical_fingerprint=FINGERPRINT,
    )
    permanent = compile_normalized(normalized)
    before = permanent.canonical_bytes()
    query = normalize_query(normalized, (owl.SubClassOf(second, third),))
    compiled = compile_query_program(permanent, normalized, query)
    assert not compiled.requires_rebuild
    assert compiled.program is not None
    assert permanent.canonical_bytes() == before
    assert len(compiled.program.predicates.predicates) > compiled.first_local_predicate_id
    boundaries = dict(compiled.first_local_symbols)
    for domain in compiled.program.symbols.domains:
        cutoff = boundaries[domain.kind.value]
        assert all(not value.query_local for value in domain.values[:cutoff])
        assert all(value.query_local for value in domain.values[cutoff:])
    assert isinstance(compiled, BackendCompiledQuery)
    assert CompiledQuery.from_canonical_json(compiled.canonical_json()) == compiled

    with pytest.raises(ValueError, match="exactly every symbol domain"):
        dataclasses.replace(compiled, first_local_symbols=compiled.first_local_symbols[1:])
    with pytest.raises(ValueError, match="exceeds the overlay predicate"):
        dataclasses.replace(
            compiled,
            first_local_predicate_id=len(compiled.program.predicates.predicates) + 1,
        )
    first_kind, _first_cutoff = compiled.first_local_symbols[0]
    invalid_boundaries = dict(compiled.first_local_symbols)
    invalid_boundaries[first_kind] = (
        len(compiled.program.symbols.domain(SymbolKind(first_kind)).values) + 1
    )
    with pytest.raises(ValueError, match="exceeds its overlay domain"):
        dataclasses.replace(compiled, first_local_symbols=tuple(sorted(invalid_boundaries.items())))

    fresh_role = owl.ObjectProperty(owl.IRI("urn:test:clauses:fresh-query-role"))
    rebuild = compile_query_program(
        permanent,
        normalized,
        normalize_query(
            normalized,
            (owl.SubClassOf(first, owl.ObjectSomeValuesFrom(fresh_role, second)),),
        ),
    )
    assert rebuild.requires_rebuild
    assert rebuild.program is None


def test_query_strategy_expansion_requests_rebuild_without_mutating_permanent_ir() -> None:
    concept = owl.Class(owl.IRI("urn:test:clauses:query-negative"))
    other = owl.Class(owl.IRI("urn:test:clauses:query-negative-other"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:clauses:query-negative-i"))
    normalized = normalize_axioms(
        (
            owl.SubClassOf(concept, other),
            owl.ClassAssertion(owl.OWL_THING, individual),
        ),
        logical_fingerprint=FINGERPRINT,
    )
    permanent = compile_normalized(normalized)
    before = permanent.canonical_bytes()
    query = normalize_query(
        normalized,
        (owl.ClassAssertion(owl.ObjectComplementOf(concept), individual),),
    )
    assert not query.requires_rebuild
    compiled = compile_query_program(permanent, normalized, query)
    assert compiled.requires_rebuild
    assert compiled.program is None
    assert compiled.reason is not None and "non_horn" in compiled.reason
    assert permanent.canonical_bytes() == before


def test_query_semantic_payload_reuses_permanent_custom_datatype_definitions() -> None:
    custom = owl.Datatype(owl.IRI("urn:test:clauses:query-custom-datatype"))
    property = owl.DataProperty(owl.IRI("urn:test:clauses:query-custom-property"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:clauses:query-custom-i"))
    literal = owl.Literal("value", owl.XSD_STRING)
    permanent_normalized = normalize_axioms(
        (
            owl.DatatypeDefinition(custom, owl.XSD_STRING),
            owl.DataPropertyRange(property, custom),
            owl.ClassAssertion(owl.OWL_THING, individual),
        ),
        logical_fingerprint=FINGERPRINT,
    )
    permanent = compile_normalized(permanent_normalized)
    compiled = compile_query_program(
        permanent,
        permanent_normalized,
        normalize_query(
            permanent_normalized,
            (owl.DataPropertyAssertion(property, individual, literal),),
        ),
    )
    assert not compiled.requires_rebuild
    assert compiled.program is not None
    semantic_model = decode_datatype_semantic_model(
        compiled.program.datatype_model.semantic_payload_json.encode("utf-8")
    )
    custom_id = next(
        value.identifier
        for value in compiled.program.symbols.domain(SymbolKind.DATA_RANGE).values
        if bytes.fromhex(value.key_hex) == custom.canonical_bytes()
    )
    source_id = next(
        value.identifier
        for value in compiled.program.symbols.domain(SymbolKind.SOURCE_LITERAL).values
        if bytes.fromhex(value.key_hex) == literal.canonical_bytes()
    )
    payload = decode_literal_semantic_payload(
        compiled.program.datatype_model.literal_identities[source_id].semantic_payload_json.encode(
            "utf-8"
        )
    )
    assert DatatypeSemanticEvaluator(semantic_model).contains(custom_id, payload)


def test_delta_classification_is_conservative_and_serializable() -> None:
    concept = owl.Class(owl.IRI("urn:test:clauses:delta-class"))
    other = owl.Class(owl.IRI("urn:test:clauses:delta-other"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:clauses:delta-i"))
    base_axioms = (
        owl.SubClassOf(concept, other),
        owl.ClassAssertion(owl.OWL_THING, individual),
    )
    program = compile_normalized(normalize_axioms(base_axioms, logical_fingerprint=FINGERPRINT))
    result = compile_normalized(
        normalize_axioms(
            (*base_axioms, owl.ClassAssertion(concept, individual)),
            logical_fingerprint=FINGERPRINT,
        )
    )
    assertion = compile_delta_plan(
        program,
        result,
        additions=(owl.ClassAssertion(concept, individual),),
    )
    assert assertion.compatibility is DeltaCompatibility.ASSERTION_ONLY
    assert isinstance(assertion, BackendCompiledDelta)
    assert assertion.fact_additions
    assert not assertion.fact_removals
    assert CompiledDelta.from_canonical_json(assertion.canonical_json()) == assertion
    empty = compile_normalized(normalize_axioms((), logical_fingerprint=FINGERPRINT))
    fresh = compile_delta_plan(
        empty,
        empty,
        additions=(owl.ClassAssertion(concept, individual),),
    )
    assert fresh.compatibility is DeltaCompatibility.REBUILD_REQUIRED
    rebuild = compile_delta_plan(
        program,
        program,
        additions=(owl.SubClassOf(concept, other), owl.Declaration(concept)),
    )
    assert rebuild.compatibility is DeltaCompatibility.REBUILD_REQUIRED


def test_limits_and_cancellation_use_public_taxonomy() -> None:
    first = owl.Class(owl.IRI("urn:test:clauses:limit-a"))
    second = owl.Class(owl.IRI("urn:test:clauses:limit-b"))
    normalized = normalize_axioms(
        (owl.SubClassOf(first, second),),
        logical_fingerprint=FINGERPRINT,
    )
    with pytest.raises(ResourceLimitError) as caught:
        compile_normalized(normalized, limits=CompilationLimits(max_predicates=1))
    assert caught.value.limit == "max_predicates"
    with pytest.raises(ReasonerInterruptedError, match="cancelled"):
        compile_normalized(normalized, cancelled=lambda: True)


def test_compilation_digest_does_not_depend_on_python_hash_order() -> None:
    axioms = _logical_axioms()
    digests = {
        hashlib.sha256(
            compile_normalized(
                normalize_axioms(permutation, logical_fingerprint=FINGERPRINT)
            ).canonical_bytes()
        ).hexdigest()
        for permutation in itertools.islice(itertools.permutations(axioms[:4]), 12)
    }
    assert len(digests) == 1


def test_nominal_inverse_role_and_at_most_keep_ni_metadata() -> None:
    concept = owl.Class(owl.IRI("urn:test:clauses:nominal-concept"))
    role = owl.ObjectProperty(owl.IRI("urn:test:clauses:nominal-role"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:clauses:nominal-individual"))
    nominal = owl.ObjectOneOf(owl.CanonicalSet((individual,)))
    program = compile_normalized(
        normalize_axioms(
            (
                owl.SubClassOf(
                    nominal,
                    owl.ObjectMaxCardinality(1, owl.ObjectInverseOf(role), concept),
                ),
            ),
            logical_fingerprint=FINGERPRINT,
        )
    )
    kinds = {value.kind for value in program.predicates.predicates}
    assert PredicateKind.NOMINAL in kinds
    assert PredicateKind.ANNOTATED_EQUALITY in kinds
    annotated = next(
        value
        for value in program.predicates.predicates
        if value.kind is PredicateKind.ANNOTATED_EQUALITY
    )
    assert annotated.cardinality == 1
    assert annotated.role_id is not None
    inverse_display = (
        program.symbols.domain(SymbolKind.OBJECT_ROLE).value(annotated.role_id).display
    )
    assert inverse_display == f"inverse_object_property:{role.iri.value}"
    assert program.expressivity.nominals
    assert program.expressivity.inverse_roles


def test_internal_inverse_role_closure_does_not_expand_source_expressivity() -> None:
    concept = owl.Class(owl.IRI("urn:test:clauses:forward-only-concept"))
    role = owl.ObjectProperty(owl.IRI("urn:test:clauses:forward-only-role"))
    program = compile_normalized(
        normalize_axioms(
            (owl.SubClassOf(concept, owl.ObjectSomeValuesFrom(role, concept)),),
            logical_fingerprint=FINGERPRINT,
        )
    )
    assert not program.expressivity.inverse_roles


def test_top_bottom_properties_and_complex_abox_are_not_erased() -> None:
    first = owl.Class(owl.IRI("urn:test:clauses:builtins-a"))
    second = owl.Class(owl.IRI("urn:test:clauses:builtins-b"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:clauses:builtins-i"))
    other = owl.NamedIndividual(owl.IRI("urn:test:clauses:builtins-j"))
    literal = owl.Literal("value", owl.XSD_STRING)
    program = compile_normalized(
        normalize_axioms(
            (
                owl.SubClassOf(
                    first,
                    owl.ObjectSomeValuesFrom(owl.OWL_TOP_OBJECT_PROPERTY, second),
                ),
                owl.ObjectPropertyAssertion(
                    owl.OWL_BOTTOM_OBJECT_PROPERTY,
                    individual,
                    other,
                ),
                owl.DataPropertyAssertion(
                    owl.OWL_BOTTOM_DATA_PROPERTY,
                    individual,
                    literal,
                ),
                owl.ClassAssertion(
                    owl.ObjectUnionOf(owl.CanonicalSet((first, second))),
                    individual,
                ),
            ),
            logical_fingerprint=FINGERPRINT,
        )
    )
    top_id = program.role_model.top_object_role_id
    assert any(
        value.kind is PredicateKind.AT_LEAST_OBJECT and value.role_id == top_id
        for value in program.predicates.predicates
    )
    positive_role_ids = {
        program.predicates.predicate(fact.predicate_id).role_id
        for fact in program.positive_facts
        if program.predicates.predicate(fact.predicate_id).kind
        in {PredicateKind.OBJECT_ROLE, PredicateKind.DATA_ROLE}
    }
    assert program.role_model.bottom_object_role_id in positive_role_ids
    assert program.role_model.bottom_data_property_id in positive_role_ids
    assert any(len(value.head) == 2 for value in program.clauses)
    assert program.expressivity.bottom_properties
    assert program.expressivity.abox


def test_custom_data_ranges_definitions_facets_and_enumerations_retain_ids() -> None:
    custom = owl.Datatype(owl.IRI("urn:test:clauses:custom-datatype"))
    property = owl.DataProperty(owl.IRI("urn:test:clauses:custom-property"))
    facet = owl.FacetRestriction(
        owl.IRI("http://www.w3.org/2001/XMLSchema#minLength"),
        owl.Literal("2", INTEGER),
    )
    restricted = owl.DatatypeRestriction(owl.XSD_STRING, owl.CanonicalSet((facet,)))
    enumeration = owl.DataOneOf(owl.CanonicalSet((owl.Literal("aa", owl.XSD_STRING),)))
    definition = owl.DataUnionOf(owl.CanonicalSet((restricted, enumeration)))
    program = compile_normalized(
        normalize_axioms(
            (
                owl.DatatypeDefinition(custom, definition),
                owl.DataPropertyRange(property, owl.DataComplementOf(enumeration)),
            ),
            logical_fingerprint=FINGERPRINT,
        )
    )
    assert program.datatype_model.datatype_definitions
    assert {
        PredicateKind.DATA_RANGE,
        PredicateKind.NEGATED_DATA_RANGE,
    } <= {value.kind for value in program.predicates.predicates}
    assert program.expressivity.datatypes


def test_unsupported_datatype_range_without_literals_sets_safe_strategy_flag() -> None:
    property = owl.DataProperty(owl.IRI("urn:test:clauses:unknown-property"))
    unsupported = owl.Datatype(owl.IRI("urn:test:clauses:unknown-datatype"))
    program = compile_normalized(
        normalize_axioms(
            (owl.DataPropertyRange(property, unsupported),),
            logical_fingerprint=FINGERPRINT,
        )
    )
    assert program.datatype_model.unknown_datatype_ids
    assert program.expressivity.unknown_datatypes


def test_punning_preserves_separate_symbol_and_predicate_sorts() -> None:
    iri = owl.IRI("urn:test:clauses:punned")
    concept = owl.Class(iri)
    object_role = owl.ObjectProperty(iri)
    data_role = owl.DataProperty(iri)
    individual = owl.NamedIndividual(iri)
    program = compile_normalized(
        normalize_axioms(
            (
                owl.ClassAssertion(concept, individual),
                owl.ObjectPropertyAssertion(object_role, individual, individual),
                owl.DataPropertyAssertion(
                    data_role,
                    individual,
                    owl.Literal("punned", owl.XSD_STRING),
                ),
            ),
            logical_fingerprint=FINGERPRINT,
        )
    )
    displays = {
        value.display
        for value in program.symbols.domain(SymbolKind.ENTITY).values
        if value.display.endswith(f":{iri.value}")
    }
    assert displays == {
        f"class:{iri.value}",
        f"data_property:{iri.value}",
        f"named_individual:{iri.value}",
        f"object_property:{iri.value}",
    }
    assert {
        PredicateKind.CONCEPT,
        PredicateKind.OBJECT_ROLE,
        PredicateKind.DATA_ROLE,
    } <= {value.kind for value in program.predicates.predicates}


def test_negative_superproperty_assertion_clashes_with_derived_positive_edge() -> None:
    sub = owl.ObjectProperty(owl.IRI("urn:test:clauses:negative-sub"))
    sup = owl.ObjectProperty(owl.IRI("urn:test:clauses:negative-super"))
    first = owl.NamedIndividual(owl.IRI("urn:test:clauses:negative-i"))
    second = owl.NamedIndividual(owl.IRI("urn:test:clauses:negative-j"))
    program = compile_normalized(
        normalize_axioms(
            (
                owl.SubObjectPropertyOf(sub, sup),
                owl.ObjectPropertyAssertion(sub, first, second),
                owl.NegativeObjectPropertyAssertion(sup, first, second),
            ),
            logical_fingerprint=FINGERPRINT,
        )
    )
    assert any(
        not clause.head
        and {program.predicates.predicate(atom.predicate_id).kind for atom in clause.body}
        == {PredicateKind.OBJECT_ROLE, PredicateKind.NEGATED_OBJECT_ROLE}
        for clause in program.clauses
    )


def test_nested_property_range_allocates_a_distinct_universal_successor() -> None:
    filler = owl.Class(owl.IRI("urn:test:clauses:fresh-filler"))
    outer = owl.ObjectProperty(owl.IRI("urn:test:clauses:fresh-outer"))
    inner = owl.ObjectProperty(owl.IRI("urn:test:clauses:fresh-inner"))
    statement = owl.ObjectPropertyRange(
        outer,
        owl.ObjectAllValuesFrom(inner, filler),
    )
    provenance = hashlib.sha256(statement.canonical_bytes()).hexdigest()
    normalized = NormalizedOntology(
        logical_fingerprint=FINGERPRINT,
        records=(
            NormalizedRecord(
                NormalizedFamily.OBJECT_PROPERTY,
                statement,
                (provenance,),
            ),
        ),
        definitions=(),
        declared_entities=(),
        source_axiom_count=1,
        ignored_nonlogical_axiom_count=0,
        expression_steps=1,
    )
    program = compile_normalized(normalized)
    clause = next(
        value
        for value in program.clauses
        if sum(
            program.predicates.predicate(atom.predicate_id).kind is PredicateKind.OBJECT_ROLE
            for atom in value.body
        )
        == 2
        and any(
            program.predicates.predicate(atom.predicate_id).kind is PredicateKind.CONCEPT
            for atom in value.head
        )
    )
    variables = {
        (argument.index, argument.sort)
        for atom in clause.body + clause.head
        for argument in atom.arguments
        if isinstance(argument, Variable)
    }
    assert variables == {
        (0, TermSort.OBJECT),
        (1, TermSort.OBJECT),
        (2, TermSort.OBJECT),
    }
