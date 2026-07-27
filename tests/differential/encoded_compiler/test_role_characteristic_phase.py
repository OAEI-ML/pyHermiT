"""Exact scalar/encoded differential for pure role-characteristic clashes."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import hashlib
import itertools
import json
import random
import struct
from typing import Any, cast

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
_KINDS = {
    "disjoint_object": 0,
    "irreflexive_object": 1,
    "asymmetric_object": 2,
    "disjoint_data": 3,
}
_CHARACTERISTIC_TYPES = (
    owl.DisjointObjectProperties,
    owl.IrreflexiveObjectProperty,
    owl.AsymmetricObjectProperty,
    owl.DisjointDataProperties,
)


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:role-characteristic#>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Ontology(<urn:test:role-characteristic> " + " ".join(body) + ")"
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


def _role_graph(normalized: NormalizedOntology) -> RoleAxiomGraph:
    axioms = [
        record.statement
        for record in normalized.records
        if isinstance(record.statement, owl.AxiomNode)
    ]
    axioms.extend(owl.Declaration(entity) for entity in normalized.declared_entities)
    return build_role_axiom_graph(axioms)


def _expected_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    normalized, _program, _ontology = compile_captured_bundle(
        capture_ontology(snapshot).captured,
        ReasonerConfig(),
    )
    roles = _role_graph(normalized)
    compiled: set[str] = set()
    clashes: set[tuple[str, int, int | None, str]] = set()
    for source in snapshot.iter_axioms():
        if not isinstance(source, _CHARACTERISTIC_TYPES):
            continue
        provenance = hashlib.sha256(source.canonical_bytes()).hexdigest()
        compiled.add(provenance)
        if isinstance(source, owl.DisjointObjectProperties):
            for first, second in itertools.combinations(tuple(source.properties), 2):
                clashes.add(
                    (
                        "disjoint_object",
                        roles.object_role_id(first),
                        roles.object_role_id(second),
                        provenance,
                    )
                )
        elif isinstance(source, owl.IrreflexiveObjectProperty):
            clashes.add(
                (
                    "irreflexive_object",
                    roles.object_role_id(source.property),
                    None,
                    provenance,
                )
            )
        elif isinstance(source, owl.AsymmetricObjectProperty):
            clashes.add(
                (
                    "asymmetric_object",
                    roles.object_role_id(source.property),
                    None,
                    provenance,
                )
            )
        else:
            assert isinstance(source, owl.DisjointDataProperties)
            for first, second in itertools.combinations(tuple(source.properties), 2):
                clashes.add(
                    (
                        "disjoint_data",
                        roles.data_property_id(first),
                        roles.data_property_id(second),
                        provenance,
                    )
                )
    ordered = sorted(
        clashes,
        key=lambda value: (_KINDS[value[0]], value[1], value[2], value[3]),
    )
    return {
        "schema_version": 1,
        "family": "role_characteristic_clashes",
        "compiled_roots": len(compiled),
        "deferred_roots": 0,
        "clashes": [
            {
                "kind": kind,
                "first_role_id": first,
                "second_role_id": second,
                "provenance_sha256": provenance,
            }
            for kind, first, second, provenance in ordered
        ],
    }


def _native_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    return cast(
        dict[str, object],
        json.loads(native._encoded_role_characteristic_manifest_v1(**buffers)),
    )


def _native_slices_manifest(*records: tuple[object, ...]) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(native._encoded_role_characteristic_slices_manifest_v1(slices=records)),
    )


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


def test_role_characteristic_clashes_and_provenance_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "pqrs"),
            *(f"Declaration(DataProperty(:{name}))" for name in "abc"),
            "DisjointObjectProperties(:p ObjectInverseOf(:q) :r)",
            "IrreflexiveObjectProperty(ObjectInverseOf(:s))",
            "AsymmetricObjectProperty(:q)",
            "DisjointDataProperties(:a :b :c)",
        ),
        options=OPTIONS,
    )

    assert _native_manifest(snapshot) == _expected_manifest(snapshot)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_annotated_characteristics_preserve_exact_nested_provenance() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(DataProperty(:a))",
            "Declaration(DataProperty(:b))",
            "Declaration(AnnotationProperty(:note))",
            "Declaration(AnnotationProperty(:meta))",
            'DisjointObjectProperties(Annotation(Annotation(:meta "nested") :note "source") :p :q)',
            "IrreflexiveObjectProperty(Annotation(:note <urn:annotation:value>) :p)",
            'AsymmetricObjectProperty(Annotation(:note "bonjour"@fr) :q)',
            "DisjointDataProperties(Annotation(:note _:source) :a :b)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert actual["compiled_roots"] == 4
    assert actual["deferred_roots"] == 0
    assert len(cast(list[object], actual["clashes"])) == 4
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_scope_maps_annotated_anonymous_provenance_exactly() -> None:
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

    actual = _native_slices_manifest(*records)

    assert actual == _expected_manifest(composite)
    assert actual["compiled_roots"] == 4
    assert actual["deferred_roots"] == 0
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_characteristics_remap_ids_and_preserve_clause_provenance() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:left))",
            "Declaration(ObjectProperty(:shared))",
            "Declaration(DataProperty(:a))",
            "Declaration(DataProperty(:sharedData))",
            "DisjointObjectProperties(:left :shared)",
            "DisjointDataProperties(:a :sharedData)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:right))",
            "Declaration(ObjectProperty(:shared))",
            "Declaration(DataProperty(:b))",
            "Declaration(DataProperty(:sharedData))",
            "IrreflexiveObjectProperty(:shared)",
            "AsymmetricObjectProperty(:right)",
            "DisjointDataProperties(:b :sharedData)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(
        _slice_record(left, member_tokens=(b"1" * 32,)),
        _slice_record(right, member_tokens=(b"2" * 32,)),
    )

    assert actual == _expected_manifest(composite)
    assert actual["compiled_roots"] == 5
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize("posting_mode", [1, 2])
def test_include_and_exclude_compile_only_selected_characteristic(posting_mode: int) -> None:
    source = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "IrreflexiveObjectProperty(:p)",
            "AsymmetricObjectProperty(:q)",
        ),
        options=OPTIONS,
    )
    expected = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "IrreflexiveObjectProperty(:p)",
        ),
        options=OPTIONS,
    )
    axioms = tuple(source.iter_axioms())
    selected = tuple(
        index
        for index, axiom in enumerate(axioms, start=1)
        if not isinstance(axiom, owl.AsymmetricObjectProperty)
    )
    posting_ids = (
        selected
        if posting_mode == 1
        else tuple(index for index in range(1, len(axioms) + 1) if index not in selected)
    )
    postings = memoryview(b"".join(struct.pack("<I", value) for value in posting_ids))

    actual = _native_slices_manifest(
        _slice_record(source, posting_mode=posting_mode, postings=postings)
    )

    assert actual == _expected_manifest(expected)


def test_hostile_property_kind_rolls_back_to_a_byte_exact_retry() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "DisjointObjectProperties(:p :q)",
        ),
        options=OPTIONS,
    )
    buffers = dict(produce_encoded_structural_view_v1(snapshot).buffers)
    baseline = native._encoded_role_characteristic_manifest_v1(**buffers)
    hostile = dict(buffers)
    hostile["scalar_bytes"] = memoryview(
        bytes(buffers["scalar_bytes"]).replace(b"object_property", b"xxxxxxxxxxxxxxx", 1)
    )

    with pytest.raises(BackendMismatchError) as caught:
        native._encoded_role_characteristic_manifest_v1(**hostile)

    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"
    assert native._encoded_role_characteristic_manifest_v1(**buffers) == baseline


def test_generated_role_characteristics_match_scalar_exactly() -> None:
    generator = random.Random(92_7981)
    object_expressions = tuple(
        [f":o{index}" for index in range(12)]
        + [f"ObjectInverseOf(:o{index})" for index in range(6)]
    )
    for _case in range(18):
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

        assert _native_manifest(snapshot) == _expected_manifest(snapshot)

    assert ENCODED_NATIVE_FEATURE in native.FEATURES
