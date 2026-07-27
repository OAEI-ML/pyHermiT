"""Exact scalar/encoded differential for complex object-role inclusions."""

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
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import BackendMismatchError
from pyhermit.normalize import normalize_view
from pyhermit.normalize.model import NormalizedOntology
from pyhermit.roles import RoleAxiomGraph, build_role_axiom_graph

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)

_BUILTIN_TOP_TRANSITIVITY = hashlib.sha256(
    b"pyhermit:role-model:builtin-top-transitivity:v1"
).hexdigest()


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:complex-roles#>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Ontology(<urn:test:complex-roles> " + " ".join(body) + ")"
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
    return (
        isinstance(statement, owl.SubObjectPropertyOf)
        and isinstance(statement.sub_property, owl.ObjectPropertyChain)
    ) or isinstance(statement, owl.TransitiveObjectProperty)


def _expected_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    normalized = normalize_view(snapshot)
    roles = _role_graph(normalized)
    compiled = {
        hashlib.sha256(record.statement.canonical_bytes()).digest()
        for record in normalized.records
        if _is_compiled_statement(record.statement)
    }
    return {
        "schema_version": 1,
        "family": "complex_object_role_inclusions",
        "compiled_roots": len(compiled),
        "complex_inclusions": [
            {
                "chain_role_ids": list(inclusion.chain_role_ids),
                "super_role_id": inclusion.super_role_id,
                "provenance_sha256": inclusion.provenance_sha256,
                "inverse_generated": inclusion.inverse_generated,
            }
            for inclusion in roles.complex_inclusions
        ],
    }


def _native_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    return cast(
        dict[str, object],
        json.loads(native._encoded_complex_object_role_manifest_v1(**buffers)),
    )


def _native_slices_manifest(*records: tuple[object, ...]) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(native._encoded_complex_object_role_slices_manifest_v1(slices=records)),
    )


def test_chains_transitivity_inverses_and_annotation_stripped_provenance_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(ObjectProperty(:r))",
            "Declaration(AnnotationProperty(:note))",
            "SubObjectPropertyOf(ObjectPropertyChain(:p ObjectInverseOf(:q) :r) :q)",
            'SubObjectPropertyOf(Annotation(:note "source") '
            "ObjectPropertyChain(ObjectInverseOf(owl:bottomObjectProperty) :p) :r)",
            "TransitiveObjectProperty(:q)",
            "TransitiveObjectProperty(owl:bottomObjectProperty)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    source_axiom = next(
        axiom
        for axiom in snapshot.iter_axioms()
        if isinstance(axiom, owl.SubObjectPropertyOf) and axiom.annotations
    )
    original_digest = hashlib.sha256(source_axiom.canonical_bytes()).hexdigest()
    inclusions = cast(list[dict[str, object]], actual["complex_inclusions"])
    assert all(value["provenance_sha256"] != original_digest for value in inclusions)
    assert any(cast(bool, value["inverse_generated"]) for value in inclusions)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_empty_model_contains_only_builtin_top_transitivity() -> None:
    snapshot = pyowl_core.load_snapshot(functional(), options=OPTIONS)

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert actual["compiled_roots"] == 0
    inclusions = cast(list[dict[str, object]], actual["complex_inclusions"])
    assert len(inclusions) == 1
    assert inclusions[0]["provenance_sha256"] == _BUILTIN_TOP_TRANSITIVITY
    assert inclusions[0]["inverse_generated"] is False
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_explicit_top_transitivity_is_overwritten_by_builtin_provenance() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "TransitiveObjectProperty(owl:topObjectProperty)",
            "TransitiveObjectProperty(ObjectInverseOf(owl:topObjectProperty))",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert actual["compiled_roots"] == 2
    inclusions = cast(list[dict[str, object]], actual["complex_inclusions"])
    assert len(inclusions) == 1
    assert inclusions[0]["provenance_sha256"] == _BUILTIN_TOP_TRANSITIVITY


def test_semantic_duplicate_uses_last_canonical_normalized_statement() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubObjectPropertyOf("
            "ObjectPropertyChain(ObjectInverseOf(owl:topObjectProperty) :p) :q)",
            "SubObjectPropertyOf(ObjectPropertyChain(owl:topObjectProperty :p) :q)",
        ),
        options=OPTIONS,
    )
    normalized = normalize_view(snapshot)
    candidates = sorted(
        record.statement.canonical_bytes()
        for record in normalized.records
        if isinstance(record.statement, owl.SubObjectPropertyOf)
    )
    expected_winner = hashlib.sha256(candidates[-1]).hexdigest()
    expected_loser = hashlib.sha256(candidates[0]).hexdigest()

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    provenances = {
        cast(str, value["provenance_sha256"])
        for value in cast(list[dict[str, object]], actual["complex_inclusions"])
    }
    assert expected_winner in provenances
    assert expected_loser not in provenances


def test_composite_remaps_ids_and_resolves_cross_slice_semantic_duplicates() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubObjectPropertyOf("
            "ObjectPropertyChain(ObjectInverseOf(owl:topObjectProperty) :p) :q)",
            "TransitiveObjectProperty(:p)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(ObjectProperty(:r))",
            "SubObjectPropertyOf(ObjectPropertyChain(owl:topObjectProperty :p) :q)",
            "SubObjectPropertyOf(ObjectPropertyChain(:q :p) :r)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(
        _slice_record(left, member_tokens=(b"1" * 32,)),
        _slice_record(right, member_tokens=(b"2" * 32,)),
    )

    assert actual == _expected_manifest(composite)
    assert actual["compiled_roots"] == 4
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize("posting_mode", [1, 2])
def test_source_local_include_and_exclude_compile_exact_complex_graph(posting_mode: int) -> None:
    source = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(ObjectProperty(:r))",
            "SubObjectPropertyOf(ObjectPropertyChain(:p :p) :q)",
            "TransitiveObjectProperty(:q)",
            "SubObjectPropertyOf(ObjectPropertyChain(:q :q) :r)",
        ),
        options=OPTIONS,
    )
    expected = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "SubObjectPropertyOf(ObjectPropertyChain(:p :p) :q)",
            "TransitiveObjectProperty(:q)",
        ),
        options=OPTIONS,
    )
    axioms = tuple(source.iter_axioms())
    selected = tuple(
        index
        for index, axiom in enumerate(axioms, start=1)
        if not (
            isinstance(axiom, owl.Declaration)
            and isinstance(axiom.entity, owl.ObjectProperty)
            and axiom.entity.iri.value.endswith("#r")
        )
        and not (
            isinstance(axiom, owl.SubObjectPropertyOf)
            and isinstance(axiom.super_property, owl.ObjectProperty)
            and axiom.super_property.iri.value.endswith("#r")
        )
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


def test_hostile_role_kind_rolls_back_and_valid_retry_is_byte_exact() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "TransitiveObjectProperty(:p)",
        ),
        options=OPTIONS,
    )
    encoded = produce_encoded_structural_view_v1(snapshot)
    buffers = dict(encoded.buffers)
    baseline = native._encoded_complex_object_role_manifest_v1(**buffers)
    scalar_bytes = bytes(buffers["scalar_bytes"])
    hostile = dict(buffers)
    hostile["scalar_bytes"] = memoryview(
        scalar_bytes.replace(b"object_property", b"xxxxxxxxxxxxxxx", 1)
    )

    with pytest.raises(BackendMismatchError) as caught:
        native._validate_encoded_columns_v1(**hostile)
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"
    assert native._encoded_complex_object_role_manifest_v1(**buffers) == baseline


def test_generated_chain_and_transitivity_permutations_match_scalar_exactly() -> None:
    generator = random.Random(18_090)
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
        body = [f"Declaration(ObjectProperty(:{name}))" for name in "pqr"]
        for _axiom in range(generator.randrange(1, 8)):
            if generator.randrange(3) == 0:
                body.append(f"TransitiveObjectProperty({generator.choice(expressions)})")
            else:
                length = generator.randrange(2, 5)
                chain = " ".join(generator.choice(expressions) for _ in range(length))
                body.append(
                    "SubObjectPropertyOf("
                    f"ObjectPropertyChain({chain}) {generator.choice(expressions)})"
                )
        snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)

        assert _native_manifest(snapshot) == _expected_manifest(snapshot)
