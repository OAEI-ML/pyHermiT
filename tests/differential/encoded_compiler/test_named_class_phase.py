"""Exact scalar/encoded differential for named classes and the first ABox phase."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import json
from typing import cast

import pyowl_core
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1

import pyhermit._native as native
from pyhermit import ReasonerConfig
from pyhermit.clauses.compiler import compile_captured_bundle
from pyhermit.clauses.model import (
    DLClause,
    GroundAtom,
    IndividualTerm,
    PredicateKind,
    SymbolKind,
    SymbolValue,
    TermSort,
    Variable,
)
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import BackendMismatchError
from pyhermit.inputs import capture_ontology

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:named#>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Ontology(<urn:test:named> " + " ".join(body) + ")"
    ).encode()


def _native_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    encoded = native._encoded_named_class_manifest_v1(
        root_kinds=buffers["root_kinds"],
        root_ids=buffers["root_ids"],
        node_tags=buffers["node_tags"],
        node_field_offsets=buffers["node_field_offsets"],
        field_kinds=buffers["field_kinds"],
        field_values=buffers["field_values"],
        field_lengths=buffers["field_lengths"],
        item_kinds=buffers["item_kinds"],
        item_values=buffers["item_values"],
        item_lengths=buffers["item_lengths"],
        scalar_bytes=buffers["scalar_bytes"],
    )
    return cast(dict[str, object], json.loads(encoded))


def _symbol_payload(value: SymbolValue) -> dict[str, object]:
    return {
        "identifier": value.identifier,
        "key_hex": value.key_hex,
        "display": value.display,
        "generated": value.generated,
        "query_local": value.query_local,
    }


def _atom_payload(predicate_id: int) -> dict[str, object]:
    return {
        "predicate_id": predicate_id,
        "arguments": [{"index": 0, "sort": "object"}],
    }


def _ground_atom_payload(
    value: GroundAtom,
    predicate_remap: dict[int, int],
) -> dict[str, object]:
    arguments = []
    for argument in value.arguments:
        assert isinstance(argument, IndividualTerm)
        arguments.append({"individual_id": argument.individual_id})
    return {
        "predicate_id": predicate_remap[value.predicate_id],
        "arguments": arguments,
        "provenance_ids": list(value.provenance_ids),
    }


def _scalar_atom_key(predicate_id: int) -> dict[str, object]:
    return {
        "type": "Atom",
        "predicate_id": predicate_id,
        "arguments": [
            {
                "type": "Variable",
                "index": 0,
                "sort": "object",
                "schema_version": 1,
            }
        ],
        "schema_version": 1,
    }


def _rule_key(body: tuple[int, ...], head: tuple[int, ...]) -> bytes:
    payload = {
        "body": [_scalar_atom_key(value) for value in body],
        "head": [_scalar_atom_key(value) for value in head],
    }
    return json.dumps(payload, separators=(",", ":"), sort_keys=True).encode()


def _expected_manifest(
    snapshot: pyowl_core.OntologyView,
    *,
    compiled_roots: int,
) -> dict[str, object]:
    _normalized, program, ontology = compile_captured_bundle(
        capture_ontology(snapshot).captured,
        ReasonerConfig(),
    )
    class_domain = program.symbols.domain(SymbolKind.CLASS_EXPRESSION)
    individual_domain = program.symbols.domain(SymbolKind.INDIVIDUAL)
    entity_domain = program.symbols.domain(SymbolKind.ENTITY)
    entity_id_by_key = {value.key_hex: value.identifier for value in entity_domain.values}
    declared_class_ids = {
        value.entity_id for value in ontology.declared_entities if value.kind == "class"
    }
    declared_individual_ids = {
        value.entity_id for value in ontology.declared_entities if value.kind == "named_individual"
    }

    fragment_kinds = {
        PredicateKind.CONCEPT,
        PredicateKind.DISJOINT_GUARD,
        PredicateKind.EQUALITY,
        PredicateKind.INEQUALITY,
        PredicateKind.NAMED_INDIVIDUAL,
    }
    fragment_predicates = [
        value for value in program.predicates.predicates if value.kind in fragment_kinds
    ]
    predicate_remap = {
        value.predicate_id: identifier for identifier, value in enumerate(fragment_predicates)
    }
    predicates = [
        {
            "predicate_id": identifier,
            "kind": value.kind.value,
            "argument_sorts": [sort.value for sort in value.argument_sorts],
            "symbol_id": value.symbol_id,
            "role_id": value.role_id,
            "cardinality": value.cardinality,
            "filler_predicate_id": value.filler_predicate_id,
            "annotation": list(value.annotation),
            "internal_key": value.internal_key,
        }
        for identifier, value in enumerate(fragment_predicates)
    ]

    expected_variable = Variable(0, TermSort.OBJECT)
    projected: list[tuple[bytes, DLClause, tuple[int, ...], tuple[int, ...]]] = []
    for clause in program.clauses:
        if not clause.body or any(
            atom.arguments != (expected_variable,) for atom in clause.body + clause.head
        ):
            continue
        body = tuple(
            predicate_remap[atom.predicate_id]
            for atom in clause.body
            if atom.predicate_id in predicate_remap
        )
        head = tuple(
            predicate_remap[atom.predicate_id]
            for atom in clause.head
            if atom.predicate_id in predicate_remap
        )
        if len(body) != len(clause.body) or len(head) != len(clause.head):
            continue
        projected.append((_rule_key(body, head), clause, body, head))
    projected.sort(key=lambda value: value[0])
    clauses = [
        {
            "clause_id": identifier,
            "body": [_atom_payload(value) for value in body],
            "head": [_atom_payload(value) for value in head],
            "provenance_ids": list(clause.provenance_ids),
            "join_order": list(clause.join_order),
        }
        for identifier, (_key, clause, body, head) in enumerate(projected)
    ]
    positive_facts = [
        _ground_atom_payload(value, predicate_remap)
        for value in program.positive_facts
        if value.predicate_id in predicate_remap
    ]

    return {
        "schema_version": 1,
        "family": "named_class_axioms",
        "compiled_roots": compiled_roots,
        "deferred_roots": 0,
        "class_expression_symbols": [_symbol_payload(value) for value in class_domain.values],
        "class_signature": [
            {
                "class_expression_id": value.identifier,
                "entity_id": entity_id_by_key[value.key_hex],
                "declared": entity_id_by_key[value.key_hex] in declared_class_ids,
            }
            for value in class_domain.values
        ],
        "individual_symbols": [_symbol_payload(value) for value in individual_domain.values],
        "individual_signature": [
            {
                "individual_id": value.identifier,
                "entity_id": entity_id_by_key[value.key_hex],
                "declared": entity_id_by_key[value.key_hex] in declared_individual_ids,
            }
            for value in individual_domain.values
        ],
        "named_individuals": list(ontology.named_individuals),
        "predicates": predicates,
        "clauses": clauses,
        "positive_facts": positive_facts,
        "provenance": [
            {
                "provenance_id": value.provenance_id,
                "source_sha256": list(value.source_sha256),
                "generated": value.generated,
            }
            for value in program.provenance.entries
        ],
    }


def test_named_class_signature_predicates_clauses_and_provenance_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "SubClassOf(:A :B)",
            "EquivalentClasses(:B :C)",
            # This merges with one normalized edge from EquivalentClasses and
            # exercises scalar-compatible multi-source provenance ownership.
            "SubClassOf(:B :C)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot, compiled_roots=3)
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_double_digit_fragment_ids_preserve_scalar_predicate_and_clause_order() -> None:
    declarations = [f"Declaration(Class(:C{index}))" for index in range(12)]
    inclusions = [f"SubClassOf(:C{index} :C{index + 1})" for index in range(11)]
    snapshot = pyowl_core.load_snapshot(
        functional(*declarations, *inclusions),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(
        snapshot,
        compiled_roots=len(inclusions),
    )


def test_named_disjoint_classes_match_linear_guards_and_normalization_shortcuts() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(Class(:C))",
            "Declaration(NamedIndividual(:i))",
            "ClassAssertion(:A :i)",
            "DisjointClasses(:A :B)",
            # owl:Nothing is removed, so this merges provenance into the same
            # normalized disjoint record as the preceding source axiom.
            "DisjointClasses(:A :B owl:Nothing)",
            # owl:Thing forces every other live member to bottom.
            "DisjointClasses(:C owl:Thing)",
            # A set containing only one live member normalizes away entirely.
            "DisjointClasses(:C owl:Nothing)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot, compiled_roots=5)


def test_named_class_assertions_and_individual_signature_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:declared))",
            "ClassAssertion(:A :declared)",
            # This source provenance merges with the builtin owl:Thing fact.
            "ClassAssertion(owl:Thing :declared)",
            # Undeclared named individuals remain in the exact individual
            # domain/signature and receive the same builtin facts as scalar.
            "ClassAssertion(owl:Nothing :implicit)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot, compiled_roots=3)


def test_named_same_individual_facts_and_overlapping_provenance_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(NamedIndividual(:a))",
            "Declaration(NamedIndividual(:b))",
            "Declaration(NamedIndividual(:c))",
            "SameIndividual(:a :b :c)",
            # The (a, b) equality is shared by two source axioms, but each
            # source retains its own provenance entry on the merged fact.
            "SameIndividual(:a :b)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot, compiled_roots=2)


def test_named_different_individual_facts_and_pairwise_provenance_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(NamedIndividual(:a))",
            "Declaration(NamedIndividual(:b))",
            "Declaration(NamedIndividual(:c))",
            "DifferentIndividuals(:a :b :c)",
            # The (a, b) inequality is shared by two source axioms, while the
            # three-member root expands to every canonical unordered pair.
            "DifferentIndividuals(:a :b)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot, compiled_roots=2)


def test_double_digit_individual_and_fact_ids_preserve_scalar_order() -> None:
    declarations = [f"Declaration(NamedIndividual(:i{index}))" for index in range(12)]
    assertions = [f"ClassAssertion(owl:Thing :i{index})" for index in range(12)]
    snapshot = pyowl_core.load_snapshot(
        functional(
            *declarations,
            *assertions,
            "SameIndividual(:i8 :i9)",
            "DifferentIndividuals(:i7 :i8 :i9)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(
        snapshot,
        compiled_roots=len(assertions) + 2,
    )


def test_complex_or_annotated_named_abox_root_is_deferred_to_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(NamedIndividual(:j))",
            "ClassAssertion(ObjectSomeValuesFrom(:p :A) :i)",
            'ClassAssertion(Annotation(:note "source") :A :i)',
            'SameIndividual(Annotation(:note "source") :i :j)',
            'DifferentIndividuals(Annotation(:note "source") :i :j)',
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)
    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 4
    assert manifest["named_individuals"] == [0, 1]
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


@pytest.mark.parametrize(
    ("constructor", "predicate_kind"),
    [
        ("SameIndividual", PredicateKind.EQUALITY),
        ("DifferentIndividuals", PredicateKind.INEQUALITY),
    ],
)
def test_anonymous_identity_axiom_defers_the_whole_root_without_partial_fact(
    constructor: str,
    predicate_kind: PredicateKind,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(NamedIndividual(:i))",
            f"{constructor}(:i _:anonymous)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)
    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert manifest["named_individuals"] == [0]
    predicates = cast(list[dict[str, object]], manifest["predicates"])
    assert all(value["kind"] != predicate_kind.value for value in predicates)
    positive_facts = cast(list[dict[str, object]], manifest["positive_facts"])
    assert len(positive_facts) == 2
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_complex_named_class_root_is_deferred_without_breaking_scalar_fallback() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "SubClassOf(ObjectSomeValuesFrom(:p :A) :B)",
        ),
        options=OPTIONS,
    )

    manifest = _native_manifest(snapshot)
    assert manifest["compiled_roots"] == 0
    assert manifest["deferred_roots"] == 1
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_hostile_class_kind_rolls_back_and_valid_retry_is_byte_exact() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "SubClassOf(:A :B)",
        ),
        options=OPTIONS,
    )
    encoded = produce_encoded_structural_view_v1(snapshot)
    buffers = dict(encoded.buffers)
    baseline = native._encoded_named_class_manifest_v1(**buffers)
    scalar_bytes = bytes(buffers["scalar_bytes"])
    assert b"class" in scalar_bytes
    hostile = dict(buffers)
    hostile["scalar_bytes"] = memoryview(scalar_bytes.replace(b"class", b"xxxxx", 1))

    with pytest.raises(BackendMismatchError) as caught:
        native._validate_encoded_columns_v1(**hostile)
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"

    # No partially compiled domain, predicate, clause, or provenance table is
    # retained across the failed transaction.
    assert native._encoded_named_class_manifest_v1(**buffers) == baseline


def test_hostile_individual_kind_rolls_back_and_valid_retry_is_byte_exact() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:i))",
            "ClassAssertion(:A :i)",
        ),
        options=OPTIONS,
    )
    encoded = produce_encoded_structural_view_v1(snapshot)
    buffers = dict(encoded.buffers)
    baseline = native._encoded_named_class_manifest_v1(**buffers)
    scalar_bytes = bytes(buffers["scalar_bytes"])
    assert b"named_individual" in scalar_bytes
    hostile = dict(buffers)
    hostile["scalar_bytes"] = memoryview(
        scalar_bytes.replace(b"named_individual", b"xxxxxxxxxxxxxxxx", 1)
    )

    with pytest.raises(BackendMismatchError) as caught:
        native._validate_encoded_columns_v1(**hostile)
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"

    assert native._encoded_named_class_manifest_v1(**buffers) == baseline
