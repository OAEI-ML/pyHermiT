"""Exact scalar/encoded differential for role regularity and simplicity."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

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


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:role-semantics#>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Ontology(<urn:test:role-semantics> " + " ".join(body) + ")"
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


def _dependencies(roles: RoleAxiomGraph) -> list[list[int]]:
    edges = {
        (
            roles.object_component_by_role[inclusion.sub_role_id],
            roles.object_component_by_role[inclusion.super_role_id],
        )
        for inclusion in roles.simple_inclusions
        if roles.object_component_by_role[inclusion.sub_role_id]
        != roles.object_component_by_role[inclusion.super_role_id]
    }
    for inclusion in roles.complex_inclusions:
        if inclusion.super_role_id == roles.top_object_role_id:
            continue
        target = roles.object_component_by_role[inclusion.super_role_id]
        edges.update(
            (component, target)
            for role_id in inclusion.chain_role_ids
            if (component := roles.object_component_by_role[role_id]) != target
        )
    return [
        sorted(dependency for dependency, consumer in edges if consumer == component)
        for component in range(len(roles.object_components))
    ]


def _expected_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    roles = _role_graph(normalize_view(snapshot))
    return {
        "schema_version": 1,
        "family": "object_role_semantics",
        "regularity_violations": [
            {
                "code": violation.code,
                "message": violation.message,
                "super_role_id": violation.super_role_id,
                "chain_role_ids": list(violation.chain_role_ids),
                "provenance_sha256": violation.provenance_sha256,
                "position": violation.position,
                "component_cycle": list(violation.component_cycle),
            }
            for violation in roles.regularity_violations
        ],
        "dependencies": _dependencies(roles),
        "non_simple_components": sorted(roles.non_simple_components),
    }


def _native_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    return cast(
        dict[str, object],
        json.loads(native._encoded_object_role_semantics_manifest_v1(**buffers)),
    )


def _native_slices_manifest(*records: tuple[object, ...]) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(native._encoded_object_role_semantics_slices_manifest_v1(slices=records)),
    )


def test_structured_recursive_inverse_and_dependency_cycle_diagnostics_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abcdg"),
            "SubObjectPropertyOf(ObjectPropertyChain(:b :g) :a)",
            "SubObjectPropertyOf(ObjectPropertyChain(:a :g) :b)",
            "SubObjectPropertyOf(ObjectPropertyChain(:c :a :d) :a)",
            "SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:a) :g) :a)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    codes = {
        cast(str, violation["code"])
        for violation in cast(list[dict[str, object]], actual["regularity_violations"])
    }
    assert codes == {
        "RIA_DEPENDENCY_CYCLE",
        "RIA_INVERSE_RECURSION",
        "RIA_NON_REGULAR_RECURSION",
    }
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_legal_boundary_recursion_top_exception_and_non_simple_closure_match_scalar() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abcd"),
            "SubObjectPropertyOf(ObjectPropertyChain(:a :b) :a)",
            "SubObjectPropertyOf(ObjectPropertyChain(:c :d) :d)",
            "TransitiveObjectProperty(:b)",
            "SubObjectPropertyOf(:b :c)",
            "SubObjectPropertyOf(ObjectPropertyChain(:d :c :a) owl:topObjectProperty)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert actual["regularity_violations"] == []
    assert cast(list[int], actual["non_simple_components"])
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_composite_recomputes_cross_slice_cycle_and_non_simple_propagation() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abg"),
            "SubObjectPropertyOf(ObjectPropertyChain(:b :g) :a)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abgs"),
            "SubObjectPropertyOf(ObjectPropertyChain(:a :g) :b)",
            "SubObjectPropertyOf(:a :s)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(
        _slice_record(left, member_tokens=(b"1" * 32,)),
        _slice_record(right, member_tokens=(b"2" * 32,)),
    )

    assert actual == _expected_manifest(composite)
    assert any(
        violation["code"] == "RIA_DEPENDENCY_CYCLE"
        for violation in cast(list[dict[str, object]], actual["regularity_violations"])
    )
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


@pytest.mark.parametrize("posting_mode", [1, 2])
def test_source_local_include_and_exclude_compile_exact_semantics(posting_mode: int) -> None:
    source = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abg"),
            "SubObjectPropertyOf(ObjectPropertyChain(:b :g) :a)",
            "SubObjectPropertyOf(ObjectPropertyChain(:a :g) :b)",
            "TransitiveObjectProperty(:g)",
        ),
        options=OPTIONS,
    )
    expected = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abg"),
            "SubObjectPropertyOf(ObjectPropertyChain(:b :g) :a)",
            "TransitiveObjectProperty(:g)",
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
            and isinstance(axiom.super_property, owl.ObjectProperty)
            and axiom.super_property.iri.value.endswith("#b")
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
            "Declaration(ObjectProperty(:a))",
            "TransitiveObjectProperty(:a)",
        ),
        options=OPTIONS,
    )
    encoded = produce_encoded_structural_view_v1(snapshot)
    buffers = dict(encoded.buffers)
    baseline = native._encoded_object_role_semantics_manifest_v1(**buffers)
    scalar_bytes = bytes(buffers["scalar_bytes"])
    hostile = dict(buffers)
    hostile["scalar_bytes"] = memoryview(
        scalar_bytes.replace(b"object_property", b"xxxxxxxxxxxxxxx", 1)
    )

    with pytest.raises(BackendMismatchError) as caught:
        native._validate_encoded_columns_v1(**hostile)
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"
    assert native._encoded_object_role_semantics_manifest_v1(**buffers) == baseline


def test_generated_role_semantics_match_scalar_exactly() -> None:
    generator = random.Random(18_120)
    expressions = (
        ":a",
        ":b",
        ":c",
        ":d",
        "ObjectInverseOf(:a)",
        "ObjectInverseOf(:b)",
        "owl:topObjectProperty",
        "ObjectInverseOf(owl:bottomObjectProperty)",
    )
    for _case in range(24):
        body = [f"Declaration(ObjectProperty(:{name}))" for name in "abcd"]
        for _axiom in range(generator.randrange(1, 9)):
            if generator.randrange(4) == 0:
                body.append(
                    f"SubObjectPropertyOf({generator.choice(expressions)} "
                    f"{generator.choice(expressions)})"
                )
            else:
                length = generator.randrange(2, 5)
                chain = " ".join(generator.choice(expressions) for _ in range(length))
                body.append(
                    "SubObjectPropertyOf("
                    f"ObjectPropertyChain({chain}) {generator.choice(expressions)})"
                )
        snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)

        assert _native_manifest(snapshot) == _expected_manifest(snapshot)
