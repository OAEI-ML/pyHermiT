"""Byte-exact scalar/encoded differential for the complete role-model IR."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import json
import random
import struct
from typing import cast

import pyowl_core
import pyowl_core.model as owl
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v2

import pyhermit._native as native
from pyhermit import ReasonerConfig
from pyhermit.clauses.compiler import compile_captured_bundle
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import BackendMismatchError
from pyhermit.inputs import capture_ontology

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:role-model#>) "
        "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>) "
        "Ontology(<urn:test:role-model> " + " ".join(body) + ")"
    ).encode()


def _slice_record(
    snapshot: pyowl_core.OntologyView,
    *,
    posting_mode: int = 0,
    postings: memoryview | None = None,
    member_tokens: tuple[bytes, ...] = (),
) -> tuple[object, ...]:
    buffers = produce_encoded_structural_view_v2(snapshot).buffers
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


def _expected_manifest_bytes(snapshot: pyowl_core.OntologyView) -> bytes:
    _normalized, program, _ontology = compile_captured_bundle(
        capture_ontology(snapshot).captured,
        ReasonerConfig(),
    )
    return program.role_model.canonical_bytes()


def _native_manifest_bytes(snapshot: pyowl_core.OntologyView) -> bytes:
    buffers = produce_encoded_structural_view_v2(snapshot).buffers
    return native._encoded_role_model_manifest_v1(**buffers)


def _native_slices_manifest_bytes(*records: tuple[object, ...]) -> bytes:
    return native._encoded_role_model_slices_manifest_v1(slices=records)


def test_complete_object_and_data_role_model_is_scalar_canonical_bytes() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abcdef"),
            *(f"Declaration(DataProperty(:{name}))" for name in "pqr"),
            "SubObjectPropertyOf(:a :b)",
            "EquivalentObjectProperties(:b :c)",
            "InverseObjectProperties(:a :f)",
            "SymmetricObjectProperty(:e)",
            "SubObjectPropertyOf(ObjectPropertyChain(:b :c) :d)",
            "SubObjectPropertyOf(ObjectPropertyChain(:e :d) :d)",
            "SubObjectPropertyOf(ObjectPropertyChain(:d :f) :d)",
            "TransitiveObjectProperty(:d)",
            "SubDataPropertyOf(:p :q)",
            "EquivalentDataProperties(:q :r)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest_bytes(snapshot)

    assert actual == _expected_manifest_bytes(snapshot)
    payload = cast(dict[str, object], json.loads(actual))
    assert payload["type"] == "RoleModelIR"
    assert payload["complex_inclusions"]
    assert payload["data_inclusions"]
    assert payload["automata"]
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_empty_role_model_retains_builtins_in_exact_scalar_order() -> None:
    snapshot = pyowl_core.load_snapshot(functional(), options=OPTIONS)

    actual = _native_manifest_bytes(snapshot)

    assert actual == _expected_manifest_bytes(snapshot)
    payload = cast(dict[str, object], json.loads(actual))
    assert payload["object_role_count"] == 2
    assert payload["data_property_count"] == 2
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_freezes_cross_slice_inclusions_and_automata_after_union() -> None:
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
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubObjectPropertyOf(ObjectPropertyChain(:b :c) :d)",
            "TransitiveObjectProperty(:d)",
            "SubDataPropertyOf(:q :p)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))

    actual = _native_slices_manifest_bytes(
        _slice_record(left, member_tokens=(b"1" * 32,)),
        _slice_record(right, member_tokens=(b"2" * 32,)),
    )

    assert actual == _expected_manifest_bytes(composite)
    payload = cast(dict[str, object], json.loads(actual))
    assert payload["complex_inclusions"]
    assert payload["automata"]
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize("posting_mode", [1, 2])
def test_source_local_include_and_exclude_freeze_exact_model(posting_mode: int) -> None:
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
        ),
        options=OPTIONS,
    )
    expected = pyowl_core.load_snapshot(
        functional(
            *declarations,
            "SubObjectPropertyOf(:a :b)",
            "TransitiveObjectProperty(:d)",
            "SubDataPropertyOf(:p :q)",
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

    actual = _native_slices_manifest_bytes(
        _slice_record(source, posting_mode=posting_mode, postings=postings)
    )

    assert actual == _expected_manifest_bytes(expected)


def test_unrelated_axioms_do_not_change_the_frozen_role_model() -> None:
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
            "ClassAssertion(:A :i)",
            'DataPropertyAssertion(:p :i "value")',
        ),
        options=OPTIONS,
    )

    assert _native_manifest_bytes(enriched) == _native_manifest_bytes(baseline)
    assert _native_manifest_bytes(enriched) == _expected_manifest_bytes(enriched)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_hostile_symbol_kind_rolls_back_and_valid_retry_is_byte_exact() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:a))",
            "Declaration(ObjectProperty(:b))",
            "SubObjectPropertyOf(:a :b)",
        ),
        options=OPTIONS,
    )
    buffers = dict(produce_encoded_structural_view_v2(snapshot).buffers)
    baseline = native._encoded_role_model_manifest_v1(**buffers)
    hostile = dict(buffers)
    hostile["scalar_bytes"] = memoryview(
        bytes(buffers["scalar_bytes"]).replace(b"object_property", b"xxxxxxxxxxxxxxx", 1)
    )

    with pytest.raises(BackendMismatchError) as caught:
        native._encoded_role_model_manifest_v1(**hostile)
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"
    assert native._encoded_role_model_manifest_v1(**buffers) == baseline
    assert baseline == _expected_manifest_bytes(snapshot)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_generated_regular_role_models_match_scalar_canonical_bytes() -> None:
    generator = random.Random(22_817)
    for _case in range(16):
        body = [f"Declaration(ObjectProperty(:o{index}))" for index in range(5)]
        body.extend(f"Declaration(DataProperty(:d{index}))" for index in range(4))
        for lower in range(4):
            if generator.randrange(2):
                body.append(f"SubObjectPropertyOf(:o{lower} :o{lower + 1})")
        for target in range(1, 5):
            if generator.randrange(2):
                chain = " ".join(
                    f":o{generator.randrange(target)}" for _ in range(generator.choice((2, 3)))
                )
                body.append(f"SubObjectPropertyOf(ObjectPropertyChain({chain}) :o{target})")
            if generator.randrange(4) == 0:
                body.append(f"TransitiveObjectProperty(:o{target})")
        for _axiom in range(generator.randrange(1, 8)):
            left, right = generator.sample(range(4), 2)
            if generator.randrange(3):
                body.append(f"SubDataPropertyOf(:d{left} :d{right})")
            else:
                body.append(f"EquivalentDataProperties(:d{left} :d{right})")
        snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)

        assert _native_manifest_bytes(snapshot) == _expected_manifest_bytes(snapshot)

    assert ENCODED_NATIVE_FEATURE in native.FEATURES
