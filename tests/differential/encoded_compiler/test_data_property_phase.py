"""Exact scalar/encoded differential for the data-property signature phase."""

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
from pyhermit.clauses.model import SymbolKind, SymbolValue
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import BackendMismatchError
from pyhermit.inputs import capture_ontology

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)


def functional(*body: str) -> bytes:
    return (
        "Prefix(:=<urn:test:data-roles#>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>) "
        "Ontology(<urn:test:data-roles> " + " ".join(body) + ")"
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
    domain = program.symbols.domain(SymbolKind.DATA_PROPERTY)
    return {
        "schema_version": 1,
        "family": "data_property_signature",
        "data_property_symbols": [_symbol_payload(value) for value in domain.values],
        "top_data_property_id": program.role_model.top_data_property_id,
        "bottom_data_property_id": program.role_model.bottom_data_property_id,
    }


def _native_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    buffers = produce_encoded_structural_view_v2(snapshot).buffers
    return cast(
        dict[str, object],
        json.loads(native._encoded_data_property_manifest_v1(**buffers)),
    )


def _native_slices_manifest(*records: tuple[object, ...]) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(native._encoded_data_property_slices_manifest_v1(slices=records)),
    )


def test_data_property_symbols_and_builtins_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(NamedIndividual(:i))",
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(DataProperty(:r))",
            "Declaration(DataProperty(:s))",
            "Declaration(DataProperty(:functional))",
            "SubDataPropertyOf(:p :q)",
            "EquivalentDataProperties(:q :r)",
            "DisjointDataProperties(:r :s)",
            "DataPropertyDomain(:p :A)",
            "DataPropertyRange(:q xsd:string)",
            "FunctionalDataProperty(:functional)",
            'DataPropertyAssertion(:p :i "7"^^xsd:integer)',
            'NegativeDataPropertyAssertion(:s :i "blocked")',
            "SubClassOf(:A DataSomeValuesFrom(:r xsd:string))",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    symbols = cast(list[dict[str, object]], actual["data_property_symbols"])
    displays = {cast(str, value["display"]) for value in symbols}
    assert "data_property:urn:test:data-roles#p" in displays
    assert "data_property:http://www.w3.org/2002/07/owl#topDataProperty" in displays
    assert "data_property:http://www.w3.org/2002/07/owl#bottomDataProperty" in displays
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_empty_ontology_still_matches_scalar_builtin_data_property_domain() -> None:
    snapshot = pyowl_core.load_snapshot(functional(), options=OPTIONS)

    assert _native_manifest(snapshot) == _expected_manifest(snapshot)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_composite_data_property_domain_remaps_and_deduplicates_keys() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:shared))",
            "SubDataPropertyOf(:p :shared)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:q))",
            "Declaration(DataProperty(:shared))",
            "SubDataPropertyOf(:shared :q)",
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
        value["display"] for value in cast(list[dict[str, object]], actual["data_property_symbols"])
    ]
    assert displays.count("data_property:urn:test:data-roles#shared") == 1
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


@pytest.mark.parametrize("posting_mode", [1, 2])
def test_source_local_include_and_exclude_rebuild_exact_data_property_domain(
    posting_mode: int,
) -> None:
    source = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
        ),
        options=OPTIONS,
    )
    expected = pyowl_core.load_snapshot(
        functional("Declaration(DataProperty(:p))"),
        options=OPTIONS,
    )
    axioms = tuple(source.iter_axioms())
    p_root = next(
        index
        for index, axiom in enumerate(axioms, start=1)
        if isinstance(axiom, owl.Declaration)
        and isinstance(axiom.entity, owl.DataProperty)
        and axiom.entity.iri.value.endswith("#p")
    )
    q_root = next(
        index
        for index, axiom in enumerate(axioms, start=1)
        if isinstance(axiom, owl.Declaration)
        and isinstance(axiom.entity, owl.DataProperty)
        and axiom.entity.iri.value.endswith("#q")
    )
    selected_root = p_root if posting_mode == 1 else q_root
    postings = memoryview(struct.pack("<I", selected_root))

    actual = _native_slices_manifest(
        _slice_record(source, posting_mode=posting_mode, postings=postings)
    )

    assert actual == _expected_manifest(expected)
    assert ENCODED_NATIVE_FEATURE in native.FEATURES


def test_hostile_data_property_kind_rolls_back_to_byte_exact_retry() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "DataPropertyRange(:p xsd:string)",
        ),
        options=OPTIONS,
    )
    encoded = produce_encoded_structural_view_v2(snapshot)
    buffers = dict(encoded.buffers)
    baseline = native._encoded_data_property_manifest_v1(**buffers)
    scalar_bytes = bytes(buffers["scalar_bytes"])
    assert b"data_property" in scalar_bytes
    hostile = dict(buffers)
    hostile["scalar_bytes"] = memoryview(
        scalar_bytes.replace(b"data_property", b"xxxxxxxxxxxxx", 1)
    )

    with pytest.raises(BackendMismatchError) as caught:
        native._encoded_data_property_manifest_v1(**hostile)
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"
    assert native._encoded_data_property_manifest_v1(**buffers) == baseline


def test_generated_data_property_uses_match_scalar_exactly() -> None:
    generator = random.Random(18_130)
    properties = (":p", ":q", ":r", ":s")
    for _case in range(24):
        body = [
            "Declaration(Class(:A))",
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "Declaration(DataProperty(:r))",
            "Declaration(DataProperty(:s))",
        ]
        for _axiom in range(generator.randrange(1, 9)):
            kind = generator.randrange(6)
            first, second, third = generator.sample(properties, 3)
            if kind == 0:
                body.append(f"SubDataPropertyOf({first} {second})")
            elif kind == 1:
                body.append(f"EquivalentDataProperties({first} {second} {third})")
            elif kind == 2:
                body.append(f"DisjointDataProperties({first} {second} {third})")
            elif kind == 3:
                body.append(f"FunctionalDataProperty({first})")
            elif kind == 4:
                body.append(f"DataPropertyDomain({first} :A)")
            else:
                body.append(f"DataPropertyRange({first} xsd:string)")
        snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)

        assert _native_manifest(snapshot) == _expected_manifest(snapshot)
