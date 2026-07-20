"""Exact scalar/encoded differential for the object-role signature phase."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import json
import struct
from typing import cast

import pyowl_core
import pyowl_core.model as owl
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1

import pyhermit._native as native
from pyhermit import ReasonerConfig
from pyhermit.clauses.compiler import compile_captured_bundle
from pyhermit.clauses.model import SymbolKind, SymbolValue
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.inputs import capture_ontology

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:roles#>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Ontology(<urn:test:roles> " + " ".join(body) + ")"
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


def _symbol_payload(value: SymbolValue) -> dict[str, object]:
    return {
        "identifier": value.identifier,
        "key_hex": value.key_hex,
        "display": value.display,
        "generated": value.generated,
        "query_local": value.query_local,
    }


def _expected_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    _normalized, program, _ontology = compile_captured_bundle(
        capture_ontology(snapshot).captured,
        ReasonerConfig(),
    )
    domain = program.symbols.domain(SymbolKind.OBJECT_ROLE)
    return {
        "schema_version": 1,
        "family": "object_role_signature",
        "object_role_symbols": [_symbol_payload(value) for value in domain.values],
        "inverse_role_ids": list(program.role_model.inverse_role_ids),
        "top_object_role_id": program.role_model.top_object_role_id,
        "bottom_object_role_id": program.role_model.bottom_object_role_id,
    }


def _native_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    return cast(
        dict[str, object],
        json.loads(native._encoded_object_role_manifest_v1(**buffers)),
    )


def _native_slices_manifest(*records: tuple[object, ...]) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(native._encoded_object_role_slices_manifest_v1(slices=records)),
    )


def test_object_role_symbols_inverse_ids_and_builtins_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(ObjectProperty(:r))",
            "Declaration(ObjectProperty(:s))",
            "Declaration(ObjectProperty(:functional))",
            "Declaration(ObjectProperty(:inverseFunctional))",
            "Declaration(ObjectProperty(:reflexive))",
            "Declaration(ObjectProperty(:asymmetric))",
            "SubObjectPropertyOf(:p :q)",
            "EquivalentObjectProperties(:q :r)",
            "InverseObjectProperties(:r :s)",
            "DisjointObjectProperties(:functional :reflexive)",
            "ObjectPropertyDomain(:p :A)",
            "ObjectPropertyRange(:p :B)",
            "FunctionalObjectProperty(:functional)",
            "InverseFunctionalObjectProperty(:inverseFunctional)",
            "ReflexiveObjectProperty(:reflexive)",
            "IrreflexiveObjectProperty(:functional)",
            "SymmetricObjectProperty(:inverseFunctional)",
            "AsymmetricObjectProperty(:asymmetric)",
            "TransitiveObjectProperty(:s)",
            "SubClassOf(ObjectSomeValuesFrom(ObjectInverseOf(:p) :A) :B)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    roles = cast(list[dict[str, object]], actual["object_role_symbols"])
    by_display = {cast(str, value["display"]): cast(int, value["identifier"]) for value in roles}
    inverse_ids = cast(list[int], actual["inverse_role_ids"])
    for iri in ("p", "q", "r", "s"):
        forward = by_display[f"object_property:urn:test:roles#{iri}"]
        inverse = by_display[f"inverse_object_property:urn:test:roles#{iri}"]
        assert inverse_ids[forward] == inverse
        assert inverse_ids[inverse] == forward
    assert inverse_ids[cast(int, actual["top_object_role_id"])] == actual["top_object_role_id"]
    assert (
        inverse_ids[cast(int, actual["bottom_object_role_id"])] == actual["bottom_object_role_id"]
    )
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_empty_ontology_still_matches_scalar_builtin_role_domain() -> None:
    snapshot = pyowl_core.load_snapshot(functional(), options=OPTIONS)

    assert _native_manifest(snapshot) == _expected_manifest(snapshot)
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_composite_role_domain_merges_source_local_ids_by_canonical_key() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:shared))",
            "ObjectPropertyDomain(:p :A)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:B))",
            "Declaration(ObjectProperty(:q))",
            "Declaration(ObjectProperty(:shared))",
            "ObjectPropertyRange(:q :B)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest(
        _slice_record(left, member_tokens=(b"1" * 32,)),
        _slice_record(right, member_tokens=(b"2" * 32,)),
    )

    assert actual == _expected_manifest(composite)
    displays = [
        value["display"] for value in cast(list[dict[str, object]], actual["object_role_symbols"])
    ]
    assert displays.count("object_property:urn:test:roles#shared") == 1
    assert displays.count("inverse_object_property:urn:test:roles#shared") == 1
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


@pytest.mark.parametrize("posting_mode", [1, 2])
def test_source_local_include_and_exclude_rebuild_the_exact_role_domain(
    posting_mode: int,
) -> None:
    source = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
        ),
        options=OPTIONS,
    )
    expected = pyowl_core.load_snapshot(
        functional("Declaration(ObjectProperty(:p))"),
        options=OPTIONS,
    )
    axioms = tuple(source.iter_axioms())
    p_root = next(
        index
        for index, axiom in enumerate(axioms, start=1)
        if isinstance(axiom, owl.Declaration)
        and isinstance(axiom.entity, owl.ObjectProperty)
        and axiom.entity.iri.value.endswith("#p")
    )
    q_root = next(
        index
        for index, axiom in enumerate(axioms, start=1)
        if isinstance(axiom, owl.Declaration)
        and isinstance(axiom.entity, owl.ObjectProperty)
        and axiom.entity.iri.value.endswith("#q")
    )
    selected_root = p_root if posting_mode == 1 else q_root
    postings = memoryview(struct.pack("<I", selected_root))

    actual = _native_slices_manifest(
        _slice_record(source, posting_mode=posting_mode, postings=postings)
    )

    assert actual == _expected_manifest(expected)
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES
