"""Exact scalar/encoded differential for data-property inclusions."""

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
from pyhermit.exceptions import BackendMismatchError
from pyhermit.inputs import capture_ontology
from pyhermit.normalize.model import NormalizedOntology
from pyhermit.roles import RoleAxiomGraph, build_role_axiom_graph

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:data-inclusions#>) "
        "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>) "
        "Ontology(<urn:test:data-inclusions> " + " ".join(body) + ")"
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
    return isinstance(
        statement,
        (owl.SubDataPropertyOf, owl.EquivalentDataProperties),
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
        "family": "data_property_inclusions",
        "compiled_roots": len(compiled),
        "data_inclusions": [
            {
                "sub_property_id": inclusion.sub_property_id,
                "super_property_id": inclusion.super_property_id,
                "provenance_sha256": inclusion.provenance_sha256,
                "builtin": inclusion.builtin,
            }
            for inclusion in roles.data_inclusions
        ],
    }


def _native_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    return cast(
        dict[str, object],
        json.loads(native._encoded_data_property_inclusions_manifest_v1(**buffers)),
    )


def _native_slices_manifest(*records: tuple[object, ...]) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(native._encoded_data_property_inclusions_slices_manifest_v1(slices=records)),
    )


def test_data_inclusions_and_normalized_provenance_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(DataProperty(:r))",
            "Declaration(AnnotationProperty(:note))",
            'SubDataPropertyOf(Annotation(:note "source") :p :q)',
            "SubDataPropertyOf(:p :q)",
            "EquivalentDataProperties(:q :r :p)",
            "DisjointDataProperties(:p :r)",
            "DataPropertyRange(:q xsd:string)",
            "FunctionalDataProperty(:r)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot)
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_annotated_only_inclusion_uses_annotation_stripped_digest() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(AnnotationProperty(:note))",
            'SubDataPropertyOf(Annotation(:note "only-source") :p :q)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)
    assert actual == _expected_manifest(snapshot)
    source_axiom = next(
        axiom for axiom in snapshot.iter_axioms() if isinstance(axiom, owl.SubDataPropertyOf)
    )
    original_digest = hashlib.sha256(source_axiom.canonical_bytes()).hexdigest()
    inclusions = cast(list[dict[str, object]], actual["data_inclusions"])
    assert inclusions
    assert all(value["provenance_sha256"] != original_digest for value in inclusions)


def test_composite_remaps_ids_and_deduplicates_normalized_edges() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:shared))",
            "SubDataPropertyOf(:p :shared)",
            "EquivalentDataProperties(:p :shared)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:q))",
            "Declaration(DataProperty(:shared))",
            "SubDataPropertyOf(:q :shared)",
            "EquivalentDataProperties(:p :shared)",
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
def test_include_and_exclude_compile_only_selected_data_inclusion(posting_mode: int) -> None:
    source = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(DataProperty(:r))",
            "SubDataPropertyOf(:p :q)",
            "SubDataPropertyOf(:p :r)",
        ),
        options=OPTIONS,
    )
    expected = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "SubDataPropertyOf(:p :q)",
        ),
        options=OPTIONS,
    )
    axioms = tuple(source.iter_axioms())
    selected = next(
        index
        for index, axiom in enumerate(axioms, start=1)
        if isinstance(axiom, owl.SubDataPropertyOf)
        and axiom.super_property.iri.value.endswith("#q")
    )
    posting_ids = (
        (selected,)
        if posting_mode == 1
        else tuple(index for index in range(1, len(axioms) + 1) if index != selected)
    )
    postings = memoryview(b"".join(struct.pack("<I", value) for value in posting_ids))

    actual = _native_slices_manifest(
        _slice_record(source, posting_mode=posting_mode, postings=postings)
    )

    assert actual == _expected_manifest(expected)


def test_other_data_axioms_remain_outside_the_inclusion_phase() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "DisjointDataProperties(:p :q)",
            "DataPropertyDomain(:p :A)",
            "DataPropertyRange(:p xsd:string)",
            "FunctionalDataProperty(:q)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual["compiled_roots"] == 0
    assert actual["data_inclusions"] == []
    assert actual == _expected_manifest(snapshot)
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_hostile_property_kind_rolls_back_to_byte_exact_retry() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "SubDataPropertyOf(:p :q)",
        ),
        options=OPTIONS,
    )
    buffers = dict(produce_encoded_structural_view_v1(snapshot).buffers)
    baseline = native._encoded_data_property_inclusions_manifest_v1(**buffers)
    scalar_bytes = bytes(buffers["scalar_bytes"])
    hostile = dict(buffers)
    hostile["scalar_bytes"] = memoryview(
        scalar_bytes.replace(b"data_property", b"xxxxxxxxxxxxx", 1)
    )

    with pytest.raises(BackendMismatchError) as caught:
        native._encoded_data_property_inclusions_manifest_v1(**hostile)
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"
    assert native._encoded_data_property_inclusions_manifest_v1(**buffers) == baseline


def test_generated_data_inclusion_permutations_match_scalar_exactly() -> None:
    generator = random.Random(18_140)
    properties = (":p", ":q", ":r", ":s")
    for _case in range(24):
        body = [f"Declaration(DataProperty(:{name}))" for name in "pqrs"]
        for _axiom in range(generator.randrange(1, 9)):
            first, second, third = generator.sample(properties, 3)
            if generator.randrange(2) == 0:
                body.append(f"SubDataPropertyOf({first} {second})")
            else:
                body.append(f"EquivalentDataProperties({first} {second} {third})")
        snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)

        assert _native_manifest(snapshot) == _expected_manifest(snapshot)
