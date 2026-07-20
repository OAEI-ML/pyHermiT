"""Exact scalar/encoded differential for object-role NFAs and acceptance."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import json
import random
import struct
from itertools import product
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
        "Prefix(:=<urn:test:role-automata#>) "
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>) "
        "Ontology(<urn:test:role-automata> " + " ".join(body) + ")"
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


def _expected_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    graph = _role_graph(normalize_view(snapshot))
    return {
        "schema_version": 1,
        "family": "object_role_automata",
        "automata": [
            {
                "target_component_id": component,
                "state_count": automaton.state_count,
                "initial_state": automaton.initial_state,
                "final_states": list(automaton.final_states),
                "transitions": [
                    [transition.source_state, transition.role_id, transition.target_state]
                    for transition in automaton.transitions
                ],
            }
            for component, automaton in sorted(graph.automata.items())
        ],
    }


def _native_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    return cast(
        dict[str, object],
        json.loads(native._encoded_object_role_automata_manifest_v1(**buffers)),
    )


def _native_slices_manifest(*records: tuple[object, ...]) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(native._encoded_object_role_automata_slices_manifest_v1(slices=records)),
    )


def _assert_direct_acceptance(
    snapshot: pyowl_core.OntologyView,
    graph: RoleAxiomGraph,
    target_id: int,
    word_ids: tuple[int, ...],
) -> None:
    buffers = produce_encoded_structural_view_v1(snapshot).buffers
    expected = graph.accepts(
        graph.object_roles[target_id],
        tuple(graph.object_roles[role_id] for role_id in word_ids),
    )
    assert (
        native._encoded_object_role_accepts_v1(
            target_role_id=target_id,
            word_role_ids=word_ids,
            **buffers,
        )
        is expected
    )


def test_chain_subrole_recursion_and_builtin_languages_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abcdef"),
            "SubObjectPropertyOf(:a :b)",
            "SubObjectPropertyOf(ObjectPropertyChain(:b :c) :d)",
            "SubObjectPropertyOf(ObjectPropertyChain(:e :d) :d)",
            "SubObjectPropertyOf(ObjectPropertyChain(:d :f) :d)",
            "TransitiveObjectProperty(:d)",
        ),
        options=OPTIONS,
    )
    graph = _role_graph(normalize_view(snapshot))

    assert _native_manifest(snapshot) == _expected_manifest(snapshot)
    role_ids = {
        role.iri.value.rsplit("#", 1)[-1]: index
        for index, role in enumerate(graph.object_roles)
        if isinstance(role, owl.ObjectProperty)
    }
    target = role_ids["d"]
    for word in (
        (),
        (target,),
        (target, target, target),
        (role_ids["a"], role_ids["c"]),
        (role_ids["e"], target, role_ids["f"]),
        (role_ids["a"],),
        (graph.bottom_object_role_id,),
        (role_ids["a"], graph.bottom_object_role_id, role_ids["f"]),
    ):
        _assert_direct_acceptance(snapshot, graph, target, word)
    for word in ((), (role_ids["a"],), (role_ids["a"], role_ids["c"])):
        _assert_direct_acceptance(snapshot, graph, graph.top_object_role_id, word)
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_irregular_graph_emits_no_automata_and_uses_scalar_single_role_fallback() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abg"),
            "SubObjectPropertyOf(:g :a)",
            "SubObjectPropertyOf(ObjectPropertyChain(:b :g) :a)",
            "SubObjectPropertyOf(ObjectPropertyChain(:a :g) :b)",
        ),
        options=OPTIONS,
    )
    graph = _role_graph(normalize_view(snapshot))
    assert graph.regularity_violations

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert actual["automata"] == []
    for target_id in range(len(graph.object_roles)):
        for word_ids in (
            (),
            (target_id,),
            (graph.bottom_object_role_id, target_id),
            (target_id, target_id),
        ):
            _assert_direct_acceptance(snapshot, graph, target_id, word_ids)


def test_composite_rebuilds_cross_slice_automata_and_acceptance() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abc"),
            "SubObjectPropertyOf(:a :b)",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abcd"),
            "SubObjectPropertyOf(ObjectPropertyChain(:b :c) :d)",
            "TransitiveObjectProperty(:d)",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    graph = _role_graph(normalize_view(composite))
    records = (
        _slice_record(left, member_tokens=(b"1" * 32,)),
        _slice_record(right, member_tokens=(b"2" * 32,)),
    )

    assert _native_slices_manifest(*records) == _expected_manifest(composite)
    for target_id in range(len(graph.object_roles)):
        word_ids = (target_id, target_id)
        expected = graph.accepts(
            graph.object_roles[target_id],
            tuple(graph.object_roles[role_id] for role_id in word_ids),
        )
        assert (
            native._encoded_object_role_slices_accepts_v1(
                slices=records,
                target_role_id=target_id,
                word_role_ids=word_ids,
            )
            is expected
        )


@pytest.mark.parametrize("posting_mode", [1, 2])
def test_source_local_include_and_exclude_compile_exact_automata(posting_mode: int) -> None:
    source = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abcd"),
            "SubObjectPropertyOf(:a :b)",
            "SubObjectPropertyOf(ObjectPropertyChain(:b :c) :d)",
            "TransitiveObjectProperty(:d)",
        ),
        options=OPTIONS,
    )
    expected = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abcd"),
            "SubObjectPropertyOf(:a :b)",
            "TransitiveObjectProperty(:d)",
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

    actual = _native_slices_manifest(
        _slice_record(source, posting_mode=posting_mode, postings=postings)
    )

    assert actual == _expected_manifest(expected)


def test_hostile_input_and_argument_types_roll_back_to_byte_exact_retry() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:a))",
            "TransitiveObjectProperty(:a)",
        ),
        options=OPTIONS,
    )
    buffers = dict(produce_encoded_structural_view_v1(snapshot).buffers)
    baseline = native._encoded_object_role_automata_manifest_v1(**buffers)
    scalar_bytes = bytes(buffers["scalar_bytes"])
    hostile = dict(buffers)
    hostile["scalar_bytes"] = memoryview(
        scalar_bytes.replace(b"object_property", b"xxxxxxxxxxxxxxx", 1)
    )

    with pytest.raises(BackendMismatchError) as caught:
        native._encoded_object_role_automata_manifest_v1(**hostile)
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"
    with pytest.raises(BackendMismatchError) as caught:
        native._encoded_object_role_accepts_v1(
            target_role_id=True,
            word_role_ids=(),
            **buffers,
        )
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"
    with pytest.raises(BackendMismatchError) as caught:
        native._encoded_object_role_accepts_v1(
            target_role_id=0,
            word_role_ids=[0],
            **buffers,
        )
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"
    with pytest.raises(BackendMismatchError) as caught:
        native._encoded_object_role_accepts_v1(
            target_role_id=2**32 - 1,
            word_role_ids=(),
            **buffers,
        )
    assert caught.value.code == "NATIVE_ENCODED_VIEW_INVALID"
    assert native._encoded_object_role_automata_manifest_v1(**buffers) == baseline


def test_generated_regular_automata_and_bounded_languages_match_scalar_exactly() -> None:
    generator = random.Random(19_731)
    for _case in range(12):
        body = [f"Declaration(ObjectProperty(:p{index}))" for index in range(5)]
        for lower in range(4):
            if generator.randrange(2):
                body.append(f"SubObjectPropertyOf(:p{lower} :p{lower + 1})")
        for target in range(1, 5):
            if generator.randrange(2):
                chain = " ".join(
                    f":p{generator.randrange(target)}" for _ in range(generator.choice((2, 3)))
                )
                body.append(f"SubObjectPropertyOf(ObjectPropertyChain({chain}) :p{target})")
            if generator.randrange(4) == 0:
                body.append(f"TransitiveObjectProperty(:p{target})")
        snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)
        graph = _role_graph(normalize_view(snapshot))
        assert graph.regular
        assert _native_manifest(snapshot) == _expected_manifest(snapshot)

        ordinary_ids = tuple(
            index
            for index, role in enumerate(graph.object_roles)
            if isinstance(role, owl.ObjectProperty)
            and role.iri.value.startswith("urn:test:role-automata#")
        )
        sampled_words = [(), *(tuple([role_id]) for role_id in ordinary_ids)]
        sampled_words.extend(
            tuple(generator.choice(ordinary_ids) for _ in range(length))
            for length in (2, 3)
            for _sample in range(3)
        )
        targets = ordinary_ids[:3]
        for target_id, word_ids in product(targets, sampled_words):
            _assert_direct_acceptance(snapshot, graph, target_id, word_ids)
