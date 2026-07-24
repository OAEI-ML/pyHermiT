"""Exact scalar/encoded differential for the first private profile phase."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import hashlib
import json
import struct
from typing import Any, cast

import pyowl_core
import pyowl_core.model as owl
import pytest
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1

import pyhermit._native as native
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import BackendMismatchError, ReasonerInterruptedError
from pyhermit.profile import validate_owl2_dl_view

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)
RULE_ID = "OWL2_DATA_RANGE_ARITY"


def functional(*body: str, ontology_iri: str = "urn:test:profile") -> bytes:
    return (
        "Prefix(:=<urn:test:profile#>) "
        "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>) "
        f"Ontology(<{ontology_iri}> " + " ".join(body) + ")"
    ).encode()


def _buffers(snapshot: pyowl_core.OntologyView) -> dict[str, memoryview]:
    return dict(produce_encoded_structural_view_v1(snapshot).buffers)


def _slice_record(
    snapshot: pyowl_core.OntologyView,
    *,
    posting_mode: int = 0,
    postings: memoryview | None = None,
    member_tokens: tuple[bytes, ...] = (),
    anonymous_scope_maps: tuple[memoryview, ...] = (),
) -> tuple[object, ...]:
    buffers = _buffers(snapshot)
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


def _native_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(native._encoded_profile_manifest_v1(**_buffers(snapshot))),
    )


def _native_slices_manifest(*records: tuple[object, ...]) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(native._encoded_profile_slices_manifest_v1(slices=records)),
    )


def _expected_manifest(snapshot: pyowl_core.OntologyView) -> dict[str, object]:
    report = validate_owl2_dl_view(snapshot)
    projected = sorted(
        {
            (
                issue.rule_id,
                issue.severity.value,
                issue.message,
                cast(str, issue.constructor),
                cast(str, issue.provenance_sha256),
            )
            for issue in report.issues
            if issue.rule_id == RULE_ID
        }
    )
    return {
        "schema_version": 1,
        "family": "owl2_dl_profile",
        "conforms": not projected,
        "axioms_checked": report.axioms_checked,
        "ordered_rule_ids": [issue[0] for issue in projected],
        "issues": [
            {
                "rule_id": rule_id,
                "severity": severity,
                "message": message,
                "constructor": constructor,
                "provenance_sha256": provenance_sha256,
            }
            for rule_id, severity, message, constructor, provenance_sha256 in projected
        ],
    }


def _invalid_body() -> tuple[str, ...]:
    return (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(DataProperty(:p))",
        "Declaration(DataProperty(:q))",
        "Declaration(AnnotationProperty(:note))",
        'SubClassOf(Annotation(:note "source") '
        ":A DataSomeValuesFrom(:p :q xsd:string))",
        "SubClassOf(:B DataAllValuesFrom(:q :p xsd:string))",
    )


def _bad_root_posting(snapshot: pyowl_core.OntologyView) -> memoryview:
    for index, axiom in enumerate(snapshot.iter_axioms(), 1):
        if any(
            isinstance(node, owl.DataSomeValuesFrom) and len(node.properties) != 1
            for node in owl.walk(axiom)
        ):
            return memoryview(struct.pack("<I", index))
    raise AssertionError("profile fixture has no invalid data existential")


def test_valid_unary_data_restrictions_match_scalar_projection() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(Class(:B))",
            "Declaration(DataProperty(:p))",
            "SubClassOf(:A DataSomeValuesFrom(:p xsd:string))",
            "SubClassOf(:B DataAllValuesFrom(:p xsd:string))",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert actual["conforms"] is True
    assert actual["issues"] == []
    assert ENCODED_NATIVE_FEATURE not in native.FEATURES


def test_multi_property_diagnostics_order_and_provenance_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(*_invalid_body()),
        options=OPTIONS,
    )
    scalar = validate_owl2_dl_view(snapshot)

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    issues = cast(list[dict[str, object]], actual["issues"])
    assert [issue["constructor"] for issue in issues] == [
        "DataAllValuesFrom",
        "DataSomeValuesFrom",
    ]
    assert all(len(cast(str, issue["provenance_sha256"])) == 64 for issue in issues)
    assert all(issue.document_keys for issue in scalar.issues if issue.rule_id == RULE_ID)
    assert all("document_keys" not in issue for issue in issues)


def test_duplicate_bad_nodes_in_one_axiom_collapse_by_scalar_issue_identity() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "SubClassOf(ObjectIntersectionOf("
            "DataSomeValuesFrom(:p :q xsd:string) "
            "DataSomeValuesFrom(:q :p xsd:string)"
            ") :A)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert actual["ordered_rule_ids"] == [RULE_ID]
    assert len(cast(list[object], actual["issues"])) == 1


def test_include_and_equivalent_exclude_selection_are_byte_identical() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(*_invalid_body()[:-1]),
        options=OPTIONS,
    )
    bad = _bad_root_posting(snapshot)
    root_count = len(tuple(snapshot.iter_axioms()))
    bad_id = struct.unpack("<I", bad)[0]
    complement = memoryview(
        b"".join(
            struct.pack("<I", index)
            for index in range(1, root_count + 1)
            if index != bad_id
        )
    )

    included = native._encoded_profile_slices_manifest_v1(
        slices=(_slice_record(snapshot, posting_mode=1, postings=bad),)
    )
    excluded = native._encoded_profile_slices_manifest_v1(
        slices=(_slice_record(snapshot, posting_mode=2, postings=complement),)
    )

    assert included == excluded
    manifest = cast(dict[str, object], json.loads(included))
    assert manifest["axioms_checked"] == 1
    assert manifest["ordered_rule_ids"] == [RULE_ID]


def test_composite_merge_deduplicates_axioms_and_is_slice_order_independent() -> None:
    left = pyowl_core.load_snapshot(
        functional(*_invalid_body()[:-1], ontology_iri="urn:test:profile:left"),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(*_invalid_body()[:-1], ontology_iri="urn:test:profile:right"),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    tokens = cast(tuple[bytes, ...], cast(Any, composite)._source_tokens())
    sources_by_token = sorted(zip(tokens, (left, right), strict=True), key=lambda row: row[0])
    records = tuple(
        _slice_record(source, member_tokens=(token,))
        for token, source in sources_by_token
    )

    forward = native._encoded_profile_slices_manifest_v1(slices=records)
    reverse = native._encoded_profile_slices_manifest_v1(slices=tuple(reversed(records)))

    assert forward == reverse
    assert json.loads(forward) == _expected_manifest(composite)


def test_anonymous_scope_map_rebases_issue_provenance_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "Declaration(DataProperty(:q))",
            "SubClassOf(ObjectOneOf(_:a) "
            "DataSomeValuesFrom(:p :q xsd:string))",
        ),
        options=OPTIONS,
    )
    source_anon = next(
        node
        for axiom in snapshot.iter_axioms()
        for node in owl.walk(axiom)
        if isinstance(node, owl.AnonymousIndividual)
    )
    target_scope = hashlib.sha256(b"profile-target-scope").digest()
    target_anon = owl.AnonymousIndividual(target_scope, source_anon.local_key)
    expected_axiom = owl.SubClassOf(
        owl.ObjectOneOf(owl.CanonicalSet((target_anon,))),
        owl.DataSomeValuesFrom(
            (
                owl.DataProperty(owl.IRI("urn:test:profile#p")),
                owl.DataProperty(owl.IRI("urn:test:profile#q")),
            ),
            owl.XSD_STRING,
        ),
    )
    scope_map = memoryview(source_anon.document_scope + target_scope)

    baseline = _native_manifest(snapshot)
    mapped = _native_slices_manifest(
        _slice_record(snapshot, anonymous_scope_maps=(scope_map,))
    )

    baseline_issue = cast(list[dict[str, object]], baseline["issues"])[0]
    mapped_issue = cast(list[dict[str, object]], mapped["issues"])[0]
    assert mapped_issue["provenance_sha256"] == hashlib.sha256(
        expected_axiom.canonical_bytes()
    ).hexdigest()
    assert mapped_issue["provenance_sha256"] != baseline_issue["provenance_sha256"]


def test_hostile_columns_fail_transactionally_and_valid_retry_is_unchanged() -> None:
    snapshot = pyowl_core.load_snapshot(functional(*_invalid_body()), options=OPTIONS)
    buffers = _buffers(snapshot)
    baseline = native._encoded_profile_manifest_v1(**buffers)
    hostile = dict(buffers)
    hostile["node_field_offsets"] = memoryview(bytes(buffers["node_field_offsets"])[:-1])

    with pytest.raises(BackendMismatchError, match="node_field_offsets"):
        native._encoded_profile_manifest_v1(**hostile)

    assert native._encoded_profile_manifest_v1(**buffers) == baseline


def test_profile_cancellation_preserves_reason_and_retry() -> None:
    snapshot = pyowl_core.load_snapshot(functional(*_invalid_body()), options=OPTIONS)
    records = (_slice_record(snapshot),)
    baseline = native._encoded_profile_slices_manifest_v1(slices=records)
    cancellation = native.CancellationHandle()
    assert cancellation.interrupt("cancel encoded profile scan")

    with pytest.raises(
        ReasonerInterruptedError,
        match="cancel encoded profile scan",
    ) as interrupted:
        native._encoded_profile_slices_manifest_v1(
            slices=records,
            cancellation=cancellation,
        )
    assert interrupted.value.code == "REASONER_INTERRUPTED"

    cancellation.reset()
    assert (
        native._encoded_profile_slices_manifest_v1(
            slices=records,
            cancellation=cancellation,
        )
        == baseline
    )
