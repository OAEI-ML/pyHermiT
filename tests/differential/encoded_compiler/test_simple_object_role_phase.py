"""Exact scalar/encoded differential for simple object-role inclusions."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import hashlib
import json
import random
import struct
from typing import cast

import pyowl_core
import pyowl_core.model as owl
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1

import pyhermit._native as native
from pyhermit import ReasonerConfig
from pyhermit.clauses.compiler import compile_captured_bundle
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.inputs import capture_ontology
from pyhermit.normalize.model import NormalizedOntology
from pyhermit.roles import RoleAxiomGraph, build_role_axiom_graph

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:simple-roles#>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>) "
        "Ontology(<urn:test:simple-roles> " + " ".join(body) + ")"
    ).encode()


def _slice_record(
    snapshot: pyowl_core.OntologyView,
    *,
    posting_mode: int = 0,
    postings: memoryview | None = None,
    member_tokens: tuple[bytes, ...] = (),
) -> tuple[object, ...]:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    return (
        posting_mode,
        memoryview(b"") if postings is None else postings,
        member_tokens,
        (),
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


def _role_graph(normalized: NormalizedOntology) -> RoleAxiomGraph:
    axioms = [
        record.statement
        for record in normalized.records
        if isinstance(record.statement, owl.AxiomNode)
    ]
    axioms.extend(owl.Declaration(entity) for entity in normalized.declared_entities)
    return build_role_axiom_graph(axioms)


def _is_compiled_statement(statement: object) -> bool:
    if isinstance(statement, owl.SubObjectPropertyOf):
        return not isinstance(statement.sub_property, owl.ObjectPropertyChain)
    return isinstance(
        statement,
        (
            owl.EquivalentObjectProperties,
            owl.InverseObjectProperties,
            owl.SymmetricObjectProperty,
        ),
    )


def _expected_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    normalized, _program, _ontology = compile_captured_bundle(
        capture_ontology(snapshot).captured,
        ReasonerConfig(),
    )
    roles = _role_graph(normalized)
    compiled = {
        hashlib.sha256(record.statement.canonical_bytes()).digest()
        for record in normalized.records
        if _is_compiled_statement(record.statement)
    }
    return {
        "schema_version": 1,
        "family": "simple_object_role_inclusions",
        "compiled_roots": len(compiled),
        "simple_inclusions": [
            {
                "sub_role_id": inclusion.sub_role_id,
                "super_role_id": inclusion.super_role_id,
                "provenance_sha256": inclusion.provenance_sha256,
                "builtin": inclusion.builtin,
            }
            for inclusion in roles.simple_inclusions
        ],
    }


def _native_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    return cast(
        dict[str, object],
        json.loads(native._encoded_simple_object_role_manifest_v1(**buffers)),
    )


def _native_slices_manifest(*records: tuple[object, ...]) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(native._encoded_simple_object_role_slices_manifest_v1(slices=records)),
    )


def test_simple_role_expansion_and_normalized_provenance_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(ObjectProperty(:r))",
            "Declaration(AnnotationProperty(:note))",
            'SubObjectPropertyOf(Annotation(:note "source") :p :q)',
            # This merges with the annotated root into one normalized record.
            "SubObjectPropertyOf(:p :q)",
            "EquivalentObjectProperties(:q ObjectInverseOf(:r) :p)",
            "InverseObjectProperties(:p :r)",
            "SymmetricObjectProperty(:q)",
            # Structural members remain distinct while the builtin role identity
            # collapses to one self-inverse role.
            "EquivalentObjectProperties("
            "ObjectInverseOf(owl:topObjectProperty) owl:topObjectProperty)",
            # Chains belong to the following role-preprocessing tranche.
            "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot)
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_annotated_only_role_axiom_uses_annotation_stripped_statement_digest() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            'SubObjectPropertyOf(Annotation(:note "only-source") :p :q)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)
    expected = _expected_manifest(snapshot)

    assert actual == expected
    source_axiom = next(
        axiom for axiom in snapshot.iter_axioms() if isinstance(axiom, owl.SubObjectPropertyOf)
    )
    original_digest = hashlib.sha256(source_axiom.canonical_bytes()).hexdigest()
    inclusions = cast(list[dict[str, object]], actual["simple_inclusions"])
    assert inclusions
    assert all(value["provenance_sha256"] != original_digest for value in inclusions)


def test_composite_simple_graph_remaps_ids_and_deduplicates_normalized_edges() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:shared))",
            "SubObjectPropertyOf(:p :shared)",
            "SymmetricObjectProperty(:shared)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:q))",
            "Declaration(ObjectProperty(:shared))",
            "SubObjectPropertyOf(:q :shared)",
            "SymmetricObjectProperty(:shared)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(
        _slice_record(left, member_tokens=(b"1" * 32,)),
        _slice_record(right, member_tokens=(b"2" * 32,)),
    )

    assert actual == _expected_manifest(composite)
    assert actual["compiled_roots"] == 3
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


@pytest.mark.parametrize("posting_mode", [1, 2])
def test_source_local_include_and_exclude_compile_only_the_selected_simple_axiom(
    posting_mode: int,
) -> None:
    source = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(ObjectProperty(:r))",
            "SubObjectPropertyOf(:p :q)",
            "SubObjectPropertyOf(:p :r)",
        ),
        options=OPTIONS,
    )
    expected = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubObjectPropertyOf(:p :q)",
        ),
        options=OPTIONS,
    )
    axioms = tuple(source.iter_axioms())
    selected = next(
        index
        for index, axiom in enumerate(axioms, start=1)
        if isinstance(axiom, owl.SubObjectPropertyOf)
        and isinstance(axiom.super_property, owl.ObjectProperty)
        and axiom.super_property.iri.value.endswith("#q")
    )
    postings_ids = (
        (selected,)
        if posting_mode == 1
        else tuple(index for index in range(1, len(axioms) + 1) if index != selected)
    )
    postings = memoryview(b"".join(struct.pack("<I", value) for value in postings_ids))

    actual = _native_slices_manifest(
        _slice_record(source, posting_mode=posting_mode, postings=postings)
    )

    assert actual == _expected_manifest(expected)


def test_chain_and_other_role_axioms_remain_explicitly_outside_the_simple_graph() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubObjectPropertyOf(ObjectPropertyChain(:p :p) :q)",
            "TransitiveObjectProperty(:q)",
            "AsymmetricObjectProperty(:p)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual["compiled_roots"] == 0
    assert actual["simple_inclusions"] == []
    assert actual == _expected_manifest(snapshot)
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_generated_role_expression_permutations_match_scalar_exactly() -> None:
    generator = random.Random(18_070)
    expressions = (
        ":p",
        ":q",
        ":r",
        "ObjectInverseOf(:p)",
        "ObjectInverseOf(:q)",
        "ObjectInverseOf(:r)",
        "owl:topObjectProperty",
        "ObjectInverseOf(owl:bottomObjectProperty)",
    )
    for _case in range(24):
        body = [
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(ObjectProperty(:r))",
        ]
        for _axiom in range(generator.randrange(1, 8)):
            kind = generator.randrange(4)
            first, second, third = generator.sample(expressions, 3)
            if kind == 0:
                body.append(f"SubObjectPropertyOf({first} {second})")
            elif kind == 1:
                body.append(f"EquivalentObjectProperties({first} {second} {third})")
            elif kind == 2:
                body.append(f"InverseObjectProperties({first} {second})")
            else:
                body.append(f"SymmetricObjectProperty({first})")
        snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)

        assert _native_manifest(snapshot) == _expected_manifest(snapshot)
