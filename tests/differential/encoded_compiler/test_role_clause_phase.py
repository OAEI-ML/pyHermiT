"""Exact scalar/encoded differential for the positive role-clause graph."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import json
import random
import struct
from typing import Any, cast

import pyowl_core
import pyowl_core.model as owl
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1

import pyhermit._native as native
from pyhermit import Reasoner, ReasonerConfig
from pyhermit.clauses.compiler import compile_captured_bundle
from pyhermit.clauses.model import PredicateKind, Variable
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import BackendMismatchError
from pyhermit.inputs import capture_ontology

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)
ROLE_KINDS = frozenset({PredicateKind.OBJECT_ROLE, PredicateKind.DATA_ROLE})


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:role-clause#>) "
        "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>) "
        "Ontology(<urn:test:role-clause> " + " ".join(body) + ")"
    ).encode()


def _slice_record(
    snapshot: pyowl_core.OntologyView,
    *,
    posting_mode: int = 0,
    postings: memoryview | None = None,
    member_tokens: tuple[bytes, ...] = (),
    anonymous_scope_maps: tuple[memoryview, ...] = (),
) -> tuple[object, ...]:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    return (
        posting_mode,
        memoryview(b"") if postings is None else postings,
        member_tokens,
        anonymous_scope_maps,
        buffers["root_kinds"],
        buffers["root_ids"],
        buffers["node_tags"],
        buffers["node_field_offsets"],
        buffers["field_kinds"],
        buffers["field_values"],
        buffers["field_lengths"],
        buffers["item_kinds"],
        buffers["item_values"],
        buffers["item_lengths"],
        buffers["scalar_bytes"],
    )


def _native_manifest_bytes(snapshot: pyowl_core.OntologyView) -> bytes:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    return native._encoded_role_clause_manifest_v1(**buffers)


def _native_slices_manifest_bytes(*records: tuple[object, ...]) -> bytes:
    return native._encoded_role_clause_slices_manifest_v1(slices=records)


def _scope_map(replacements: dict[bytes, bytes]) -> memoryview:
    return memoryview(b"".join(source + target for source, target in sorted(replacements.items())))


def _composite_records(
    composite: pyowl_core.OntologyView,
    sources: tuple[pyowl_core.OntologyView, ...],
) -> tuple[tuple[object, ...], ...]:
    tokens = cast(tuple[bytes, ...], cast(Any, composite)._source_tokens())
    mappings = cast(
        tuple[dict[bytes, bytes], ...],
        cast(Any, composite)._scope_replacements(),
    )
    rows = sorted(zip(tokens, sources, mappings, strict=True), key=lambda row: row[0])
    return tuple(
        _slice_record(
            source,
            member_tokens=(token,),
            anonymous_scope_maps=(() if not mapping else (_scope_map(mapping),)),
        )
        for token, source, mapping in rows
    )


def _term_payload(term: object) -> dict[str, object]:
    assert isinstance(term, Variable)
    return {"index": term.index, "sort": term.sort.value}


def _expected_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    _normalized, program, _ontology = compile_captured_bundle(
        capture_ontology(snapshot).captured,
        ReasonerConfig(),
    )
    clauses = [
        clause
        for clause in program.clauses
        if clause.body
        and all(
            program.predicates.predicate(atom.predicate_id).kind in ROLE_KINDS
            and all(isinstance(term, Variable) for term in atom.arguments)
            for atom in clause.body + clause.head
        )
    ]
    referenced_predicates = {
        atom.predicate_id for clause in clauses for atom in clause.body + clause.head
    }
    predicates = [
        predicate
        for predicate in program.predicates.predicates
        if predicate.predicate_id in referenced_predicates
    ]
    predicate_remap = {
        predicate.predicate_id: identifier for identifier, predicate in enumerate(predicates)
    }
    # Supported role-graph and characteristic inputs retain only the always-last
    # owl:Nothing predicate after this fragment, so scalar alpha-ordering is
    # already the exact fragment-local ordering.
    assert all(source == target for source, target in predicate_remap.items())
    referenced_provenance = sorted(
        {identifier for clause in clauses for identifier in clause.provenance_ids}
    )
    provenance_remap = {source: target for target, source in enumerate(referenced_provenance)}
    return {
        "schema_version": 1,
        "family": "role_graph_clauses",
        "predicates": [
            {
                "predicate_id": predicate_remap[predicate.predicate_id],
                "kind": predicate.kind.value,
                "argument_sorts": [sort.value for sort in predicate.argument_sorts],
                "symbol_id": predicate.symbol_id,
                "role_id": predicate.role_id,
                "cardinality": predicate.cardinality,
                "filler_predicate_id": predicate.filler_predicate_id,
                "annotation": list(predicate.annotation),
                "internal_key": predicate.internal_key,
            }
            for predicate in predicates
        ],
        "clauses": [
            {
                "clause_id": identifier,
                "body": [
                    {
                        "predicate_id": predicate_remap[atom.predicate_id],
                        "arguments": [_term_payload(term) for term in atom.arguments],
                    }
                    for atom in clause.body
                ],
                "head": [
                    {
                        "predicate_id": predicate_remap[atom.predicate_id],
                        "arguments": [_term_payload(term) for term in atom.arguments],
                    }
                    for atom in clause.head
                ],
                "provenance_ids": [provenance_remap[value] for value in clause.provenance_ids],
                "join_order": list(clause.join_order),
            }
            for identifier, clause in enumerate(clauses)
        ],
        "provenance": [
            {
                "provenance_id": identifier,
                "source_sha256": list(program.provenance.entries[source].source_sha256),
                "generated": program.provenance.entries[source].generated,
            }
            for identifier, source in enumerate(referenced_provenance)
        ],
    }


def _assert_exact(snapshot: pyowl_core.OntologyView) -> None:
    actual = cast(dict[str, object], json.loads(_native_manifest_bytes(snapshot)))
    assert actual == _expected_manifest(snapshot)


def test_mixed_role_graph_predicates_clauses_and_provenance_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abcdef"),
            *(f"Declaration(DataProperty(:{name}))" for name in "pqr"),
            "Declaration(AnnotationProperty(:note))",
            "SubObjectPropertyOf(:a :b)",
            "EquivalentObjectProperties(:b :c)",
            "InverseObjectProperties(:a :f)",
            "SymmetricObjectProperty(:e)",
            "SubObjectPropertyOf(ObjectPropertyChain(:b :c) :d)",
            "TransitiveObjectProperty(:d)",
            "SubDataPropertyOf(:p :q)",
            "EquivalentDataProperties(:q :r)",
            'DisjointObjectProperties(Annotation(:note "disjoint") :a ObjectInverseOf(:b) :f)',
            'IrreflexiveObjectProperty(Annotation(:note "irreflexive") :c)',
            'AsymmetricObjectProperty(Annotation(:note "asymmetric") :e)',
            'DisjointDataProperties(Annotation(:note "data") :p :r)',
        ),
        options=OPTIONS,
    )

    _assert_exact(snapshot)
    payload = cast(dict[str, object], json.loads(_native_manifest_bytes(snapshot)))
    clauses = cast(list[dict[str, object]], payload["clauses"])
    assert any(len(cast(list[object], clause["body"])) > 1 for clause in clauses)
    assert any(not clause["head"] for clause in clauses)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_empty_graph_retains_inverse_and_bottom_builtin_clauses_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(functional(), options=OPTIONS)

    _assert_exact(snapshot)
    payload = cast(dict[str, object], json.loads(_native_manifest_bytes(snapshot)))
    assert len(cast(list[object], payload["predicates"])) == 3
    assert len(cast(list[object], payload["clauses"])) == 5
    assert payload["provenance"] == [
        {
            "provenance_id": 0,
            "source_sha256": ["03bd514dea4e9b0367cc99a9aa5eca9fd90142bcf60f5a7e42d3ebea01659763"],
            "generated": True,
        }
    ]


def test_composite_clausifies_the_merged_role_graph_once() -> None:
    declarations = (
        *(f"Declaration(ObjectProperty(:{name}))" for name in "abcd"),
        "Declaration(DataProperty(:p))",
        "Declaration(DataProperty(:q))",
    )
    left = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubObjectPropertyOf(:a :b)",
            "SubDataPropertyOf(:p :q)",
            "DisjointObjectProperties(:a :c)",
            "DisjointDataProperties(:p :q)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubObjectPropertyOf(ObjectPropertyChain(:b :c) :d)",
            "TransitiveObjectProperty(:d)",
            "SubDataPropertyOf(:q :p)",
            "IrreflexiveObjectProperty(:c)",
            "AsymmetricObjectProperty(:a)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = cast(
        dict[str, object],
        json.loads(
            _native_slices_manifest_bytes(
                _slice_record(left, member_tokens=(b"1" * 32,)),
                _slice_record(right, member_tokens=(b"2" * 32,)),
            )
        ),
    )

    assert actual == _expected_manifest(composite)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_anonymous_annotation_scope_maps_clause_provenance_exactly() -> None:
    source = functional(
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
        "Declaration(AnnotationProperty(:note))",
        "DisjointObjectProperties(Annotation(:note _:same) :p :q)",
        "IrreflexiveObjectProperty(Annotation(:note _:same) :p)",
    )
    left = pyowl_core.load_snapshot(source, options=OPTIONS)
    right = pyowl_core.load_snapshot(source, options=OPTIONS)
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    records = _composite_records(composite, (left, right))
    assert any(cast(tuple[object, ...], record[3]) for record in records)

    actual = cast(
        dict[str, object],
        json.loads(_native_slices_manifest_bytes(*records)),
    )

    assert actual == _expected_manifest(composite)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize("posting_mode", [1, 2])
def test_source_local_include_and_exclude_clausify_selected_roots(posting_mode: int) -> None:
    declarations = (
        *(f"Declaration(ObjectProperty(:{name}))" for name in "abcd"),
        "Declaration(DataProperty(:p))",
        "Declaration(DataProperty(:q))",
    )
    source = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubObjectPropertyOf(:a :b)",
            "SubObjectPropertyOf(ObjectPropertyChain(:b :c) :d)",
            "TransitiveObjectProperty(:d)",
            "SubDataPropertyOf(:p :q)",
            "IrreflexiveObjectProperty(:a)",
        ),
        options=OPTIONS,
    )
    expected = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubObjectPropertyOf(:a :b)",
            "TransitiveObjectProperty(:d)",
            "SubDataPropertyOf(:p :q)",
            "IrreflexiveObjectProperty(:a)",
        ),
        options=OPTIONS,
    )
    axioms = tuple(source.iter_axioms())
    selected = tuple(
        index
        for index, axiom in enumerate(axioms, start=1)
        if not (
            isinstance(axiom, owl.SubObjectPropertyOf)
            and isinstance(axiom.sub_property, owl.ObjectPropertyChain)
        )
    )
    posting_ids = (
        selected
        if posting_mode == 1
        else tuple(index for index in range(1, len(axioms) + 1) if index not in selected)
    )
    postings = memoryview(b"".join(struct.pack("<I", value) for value in posting_ids))

    actual = cast(
        dict[str, object],
        json.loads(
            _native_slices_manifest_bytes(
                _slice_record(source, posting_mode=posting_mode, postings=postings)
            )
        ),
    )

    assert actual == _expected_manifest(expected)


def test_unowned_class_and_property_semantics_remain_deferred() -> None:
    declarations = (
        "Declaration(Class(:A))",
        "Declaration(NamedIndividual(:i))",
        "Declaration(ObjectProperty(:a))",
        "Declaration(ObjectProperty(:b))",
        "Declaration(DataProperty(:p))",
        "Declaration(DataProperty(:q))",
        "SubObjectPropertyOf(:a :b)",
        "SubDataPropertyOf(:p :q)",
    )
    baseline = pyowl_core.load_snapshot(functional(*declarations), options=OPTIONS)
    enriched = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "ObjectPropertyDomain(:a :A)",
            "ObjectPropertyRange(:b :A)",
            "DataPropertyDomain(:p :A)",
            "DataPropertyRange(:q xsd:string)",
            "ObjectPropertyAssertion(:a :i :i)",
            'DataPropertyAssertion(:p :i "value")',
        ),
        options=OPTIONS,
    )

    assert _native_manifest_bytes(enriched) == _native_manifest_bytes(baseline)
    _assert_exact(baseline)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_hostile_input_rolls_back_before_a_valid_byte_exact_retry() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:a))",
            "Declaration(ObjectProperty(:b))",
            "SubObjectPropertyOf(:a :b)",
        ),
        options=OPTIONS,
    )
    buffers = dict(produce_encoded_structural_view_v1(snapshot).buffers)
    baseline = native._encoded_role_clause_manifest_v1(**buffers)
    hostile = dict(buffers)
    hostile["scalar_bytes"] = memoryview(
        bytes(buffers["scalar_bytes"]).replace(b"object_property", b"xxxxxxxxxxxxxxx", 1)
    )

    with pytest.raises(BackendMismatchError) as caught:
        native._encoded_role_clause_manifest_v1(**hostile)

    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"
    assert native._encoded_role_clause_manifest_v1(**buffers) == baseline
    assert cast(dict[str, object], json.loads(baseline)) == _expected_manifest(snapshot)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_generated_regular_role_clauses_match_scalar_exactly() -> None:
    generator = random.Random(31_337)
    for _case in range(16):
        body = [f"Declaration(ObjectProperty(:o{index}))" for index in range(12)]
        body.extend(f"Declaration(DataProperty(:d{index}))" for index in range(12))
        for lower in range(11):
            if generator.randrange(2):
                body.append(f"SubObjectPropertyOf(:o{lower} :o{lower + 1})")
        for target in range(2, 12):
            if generator.randrange(3) == 0:
                members = generator.sample(range(target), 2)
                body.append(
                    "SubObjectPropertyOf(ObjectPropertyChain("
                    f":o{members[0]} :o{members[1]}) :o{target})"
                )
            if generator.randrange(5) == 0:
                body.append(f"TransitiveObjectProperty(:o{target})")
        for _axiom in range(generator.randrange(1, 12)):
            left, right = generator.sample(range(12), 2)
            if generator.randrange(3):
                body.append(f"SubDataPropertyOf(:d{left} :d{right})")
            else:
                body.append(f"EquivalentDataProperties(:d{left} :d{right})")
        snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)

        _assert_exact(snapshot)

    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_generated_role_characteristic_clauses_match_scalar_exactly() -> None:
    generator = random.Random(72_7992)
    object_expressions = tuple(
        [f":o{index}" for index in range(12)]
        + [f"ObjectInverseOf(:o{index})" for index in range(6)]
    )
    for _case in range(14):
        body = [f"Declaration(ObjectProperty(:o{index}))" for index in range(12)]
        body.extend(f"Declaration(DataProperty(:d{index}))" for index in range(12))
        for _axiom in range(generator.randrange(1, 10)):
            kind = generator.randrange(4)
            if kind == 0:
                members = generator.sample(object_expressions, generator.randrange(2, 5))
                body.append(f"DisjointObjectProperties({' '.join(members)})")
            elif kind == 1:
                body.append(f"IrreflexiveObjectProperty({generator.choice(object_expressions)})")
            elif kind == 2:
                body.append(f"AsymmetricObjectProperty({generator.choice(object_expressions)})")
            else:
                members = generator.sample(range(12), generator.randrange(2, 5))
                body.append(
                    "DisjointDataProperties("
                    + " ".join(f":d{identifier}" for identifier in members)
                    + ")"
                )
        snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)

        _assert_exact(snapshot)

    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_public_compiler_digest_and_role_results_remain_backend_exact() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:a))",
            "Declaration(ObjectProperty(:b))",
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "SubObjectPropertyOf(:a :b)",
            "SubDataPropertyOf(:p :q)",
        ),
        options=OPTIONS,
    )
    object_property = owl.ObjectProperty(owl.IRI("urn:test:role-clause#a"))
    data_property = owl.DataProperty(owl.IRI("urn:test:role-clause#p"))
    reasoners = tuple(
        Reasoner(snapshot, config=ReasonerConfig(backend=backend))
        for backend in ("python", "native", "verify")
    )
    try:
        diagnostics = tuple(reasoner.diagnostics() for reasoner in reasoners)
        results = tuple(
            (
                reasoner.is_consistent(),
                reasoner.super_object_properties(object_property),
                reasoner.super_data_properties(data_property),
            )
            for reasoner in reasoners
        )
    finally:
        for reasoner in reasoners:
            reasoner.dispose()

    assert len({value["compiler_digest"] for value in diagnostics}) == 1
    assert len(set(results)) == 1
    assert {value["ingestion_path"] for value in diagnostics} == {
        "encoded-native",
        "scalar-python",
    }
    assert ENCODED_NATIVE_FEATURE in native.FEATURES
