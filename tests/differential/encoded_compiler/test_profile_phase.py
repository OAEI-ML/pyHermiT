"""Exact scalar/encoded differential for the first private profile phase."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import hashlib
import json
import struct
from types import SimpleNamespace
from typing import Any, cast

import pyowl_core
import pyowl_core.model as owl
import pytest
from pyowl_core import (
    DetectionBasis,
    DigestKind,
    DocumentFormat,
    DocumentProvenance,
    OntologyDocument,
    OntologyID,
)
from pyowl_core.backends.native_views import produce_encoded_structural_view_v1
from pyowl_core.extensions import swrl
from pyowl_core.index import OntologyIdentityIndex

import pyhermit._native as native
from pyhermit.backends.native import NativeBackendFactory
from pyhermit.config import UnsupportedDatatypePolicy
from pyhermit.encoded_input import ENCODED_NATIVE_FEATURE
from pyhermit.exceptions import (
    BackendMismatchError,
    OntologyProfileError,
    ReasonerInterruptedError,
)
from pyhermit.inputs import capture_ontology
from pyhermit.profile import validate_owl2_dl_view

OPTIONS = pyowl_core.LoadOptions(
    imports=pyowl_core.ImportPolicy.IGNORE,
    backend=pyowl_core.BackendPreference.PYTHON,
)
DATA_RANGE_ARITY_RULE = "OWL2_DATA_RANGE_ARITY"
EXTENSION_COMPONENT_RULE = "OWL2DL_EXTENSION_COMPONENT"
TOP_DATA_PROPERTY_RULE = "OWL2DL_TOP_DATA_PROPERTY_POSITION"
ANONYMOUS_AXIOM_POSITION_RULE = "OWL2DL_ANONYMOUS_AXIOM_POSITION"
ANONYMOUS_CLASS_EXPRESSION_RULE = "OWL2DL_ANONYMOUS_CLASS_EXPRESSION"
ANONYMOUS_GRAPH_CYCLE_RULE = "OWL2DL_ANONYMOUS_GRAPH_CYCLE"
ANONYMOUS_PARALLEL_EDGE_RULE = "OWL2DL_ANONYMOUS_PARALLEL_EDGE"
ANONYMOUS_TREE_ROOT_RULE = "OWL2DL_ANONYMOUS_TREE_ROOT"
PROPERTY_PUNNING_RULE = "OWL2DL_PROPERTY_PUNNING"
CLASS_DATATYPE_PUNNING_RULE = "OWL2DL_CLASS_DATATYPE_PUNNING"
RESERVED_VOCABULARY_RULE = "OWL2DL_RESERVED_VOCABULARY"
BUILTIN_ENTITY_KIND_RULE = "OWL2DL_BUILTIN_ENTITY_KIND"
MISSING_DECLARATION_RULE = "OWL2DL_MISSING_DECLARATION"
RESERVED_ONTOLOGY_IRI_RULE = "OWL2DL_RESERVED_ONTOLOGY_IRI"
RESERVED_VERSION_IRI_RULE = "OWL2DL_RESERVED_VERSION_IRI"
NON_SIMPLE_PROPERTY_RULE = "OWL2DL_NON_SIMPLE_PROPERTY"
BUILTIN_DATATYPE_REDEFINITION_RULE = "BUILTIN_DATATYPE_REDEFINITION"
CUSTOM_DATATYPE_LITERAL_RULE = "CUSTOM_DATATYPE_LITERAL"
DUPLICATE_DATATYPE_DEFINITION_RULE = "DUPLICATE_DATATYPE_DEFINITION"
ILLEGAL_DATATYPE_FACET_RULE = "ILLEGAL_DATATYPE_FACET"
INVALID_FACET_VALUE_RULE = "INVALID_FACET_VALUE"
INVALID_LITERAL_RULE = "INVALID_LITERAL"
RECURSIVE_DATATYPE_DEFINITION_RULE = "RECURSIVE_DATATYPE_DEFINITION"
UNSUPPORTED_DATATYPE_RULE = "UNSUPPORTED_DATATYPE"
UNSUPPORTED_DATATYPE_OPAQUE_RULE = "UNSUPPORTED_DATATYPE_OPAQUE"
RIA_DEPENDENCY_CYCLE_RULE = "RIA_DEPENDENCY_CYCLE"
RIA_INVERSE_RECURSION_RULE = "RIA_INVERSE_RECURSION"
RIA_NON_REGULAR_RECURSION_RULE = "RIA_NON_REGULAR_RECURSION"
ENTITY_RULES = frozenset(
    (
        BUILTIN_ENTITY_KIND_RULE,
        CLASS_DATATYPE_PUNNING_RULE,
        MISSING_DECLARATION_RULE,
        PROPERTY_PUNNING_RULE,
        RESERVED_VOCABULARY_RULE,
    )
)
OntologyIdentityContext = tuple[
    int,
    tuple[tuple[str, str | None, str | None], ...],
]
ProfileOriginContext = tuple[
    int,
    tuple[tuple[bytes, tuple[str, ...]], ...],
]
PROJECTED_RULES = frozenset(
    (
        ANONYMOUS_AXIOM_POSITION_RULE,
        ANONYMOUS_CLASS_EXPRESSION_RULE,
        ANONYMOUS_GRAPH_CYCLE_RULE,
        ANONYMOUS_PARALLEL_EDGE_RULE,
        ANONYMOUS_TREE_ROOT_RULE,
        BUILTIN_ENTITY_KIND_RULE,
        BUILTIN_DATATYPE_REDEFINITION_RULE,
        CLASS_DATATYPE_PUNNING_RULE,
        CUSTOM_DATATYPE_LITERAL_RULE,
        DATA_RANGE_ARITY_RULE,
        DUPLICATE_DATATYPE_DEFINITION_RULE,
        EXTENSION_COMPONENT_RULE,
        ILLEGAL_DATATYPE_FACET_RULE,
        INVALID_FACET_VALUE_RULE,
        INVALID_LITERAL_RULE,
        MISSING_DECLARATION_RULE,
        NON_SIMPLE_PROPERTY_RULE,
        PROPERTY_PUNNING_RULE,
        RESERVED_ONTOLOGY_IRI_RULE,
        RESERVED_VOCABULARY_RULE,
        RESERVED_VERSION_IRI_RULE,
        RECURSIVE_DATATYPE_DEFINITION_RULE,
        RIA_DEPENDENCY_CYCLE_RULE,
        RIA_INVERSE_RECURSION_RULE,
        RIA_NON_REGULAR_RECURSION_RULE,
        TOP_DATA_PROPERTY_RULE,
        UNSUPPORTED_DATATYPE_OPAQUE_RULE,
        UNSUPPORTED_DATATYPE_RULE,
    )
)


def functional(*body: str, ontology_iri: str = "urn:test:profile") -> bytes:
    return (
        "Prefix(:=<urn:test:profile#>) "
        "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>) "
        f"Ontology(<{ontology_iri}> " + " ".join(body) + ")"
    ).encode()


def _buffers(snapshot: pyowl_core.OntologyView) -> dict[str, memoryview]:
    return dict(produce_encoded_structural_view_v1(snapshot).buffers)


def _ontology_identity_context(
    snapshot: pyowl_core.OntologyView,
) -> OntologyIdentityContext:
    identity = snapshot.view(OntologyIdentityIndex)
    documents = tuple(
        sorted(
            (
                document.document_key,
                (
                    None
                    if document.ontology_id.ontology_iri is None
                    else document.ontology_id.ontology_iri.value
                ),
                (
                    None
                    if document.ontology_id.version_iri is None
                    else document.ontology_id.version_iri.value
                ),
            )
            for document in identity.documents
        )
    )
    return (1, documents)


def _profile_origin_context(
    snapshot: pyowl_core.OntologyView,
) -> ProfileOriginContext:
    documents_by_provenance: dict[bytes, set[str]] = {}
    for value in (*snapshot.iter_axioms(), *snapshot.iter_extensions()):
        document_keys = {origin.document_key for origin in snapshot.origin_index.origins_for(value)}
        if not document_keys:
            continue
        provenance = hashlib.sha256(value.canonical_bytes()).digest()
        documents_by_provenance.setdefault(provenance, set()).update(document_keys)
    return (
        1,
        tuple(
            (provenance, tuple(sorted(document_keys)))
            for provenance, document_keys in sorted(documents_by_provenance.items())
        ),
    )


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


def _native_manifest(
    snapshot: pyowl_core.OntologyView,
    *,
    unsupported_datatypes: UnsupportedDatatypePolicy = UnsupportedDatatypePolicy.ERROR,
) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(
            native._encoded_profile_manifest_v1(
                **_buffers(snapshot),
                unsupported_datatypes=unsupported_datatypes.value,
                ontology_identity_context=_ontology_identity_context(snapshot),
            )
        ),
    )


def _native_slices_manifest(
    *records: tuple[object, ...],
    unsupported_datatypes: UnsupportedDatatypePolicy = UnsupportedDatatypePolicy.ERROR,
    ontology_identity_context: OntologyIdentityContext | None = None,
) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(
            native._encoded_profile_slices_manifest_v1(
                slices=records,
                unsupported_datatypes=unsupported_datatypes.value,
                ontology_identity_context=ontology_identity_context,
            )
        ),
    )


def _native_origin_manifest(
    snapshot: pyowl_core.OntologyView,
    *,
    unsupported_datatypes: UnsupportedDatatypePolicy = UnsupportedDatatypePolicy.ERROR,
) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(
            native._encoded_profile_manifest_v1(
                **_buffers(snapshot),
                unsupported_datatypes=unsupported_datatypes.value,
                ontology_identity_context=_ontology_identity_context(snapshot),
                origin_context=_profile_origin_context(snapshot),
            )
        ),
    )


def _native_origin_slices_manifest(
    *records: tuple[object, ...],
    unsupported_datatypes: UnsupportedDatatypePolicy = UnsupportedDatatypePolicy.ERROR,
    ontology_identity_context: OntologyIdentityContext,
    origin_context: ProfileOriginContext,
) -> dict[str, object]:
    return cast(
        dict[str, object],
        json.loads(
            native._encoded_profile_slices_manifest_v1(
                slices=records,
                unsupported_datatypes=unsupported_datatypes.value,
                ontology_identity_context=ontology_identity_context,
                origin_context=origin_context,
            )
        ),
    )


def _expected_manifest(
    snapshot: pyowl_core.OntologyView,
    *,
    unsupported_datatypes: UnsupportedDatatypePolicy = UnsupportedDatatypePolicy.ERROR,
) -> dict[str, object]:
    report = validate_owl2_dl_view(
        snapshot,
        unsupported_datatypes=unsupported_datatypes,
    )
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
            if issue.rule_id in PROJECTED_RULES
        }
    )
    return {
        "schema_version": 1,
        "family": "owl2_dl_profile",
        "conforms": all(issue[1] != "error" for issue in projected),
        "axioms_checked": report.axioms_checked,
        "extensions_checked": report.extensions_checked,
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


def _expected_origin_manifest(
    snapshot: pyowl_core.OntologyView,
    *,
    unsupported_datatypes: UnsupportedDatatypePolicy = UnsupportedDatatypePolicy.ERROR,
) -> dict[str, object]:
    report = validate_owl2_dl_view(
        snapshot,
        unsupported_datatypes=unsupported_datatypes,
    )
    projected = tuple(issue for issue in report.issues if issue.rule_id in PROJECTED_RULES)
    return {
        "schema_version": 1,
        "family": "owl2_dl_profile",
        "conforms": not any(issue.severity.value == "error" for issue in projected),
        "axioms_checked": report.axioms_checked,
        "extensions_checked": report.extensions_checked,
        "ordered_rule_ids": [issue.rule_id for issue in projected],
        "issues": [
            {
                "rule_id": issue.rule_id,
                "severity": issue.severity.value,
                "message": issue.message,
                "constructor": issue.constructor,
                "document_keys": list(issue.document_keys),
                "provenance_sha256": issue.provenance_sha256,
            }
            for issue in projected
        ],
    }


def _invalid_body() -> tuple[str, ...]:
    return (
        "Declaration(Class(:A))",
        "Declaration(Class(:B))",
        "Declaration(DataProperty(:p))",
        "Declaration(DataProperty(:q))",
        "Declaration(AnnotationProperty(:note))",
        'SubClassOf(Annotation(:note "source") :A DataSomeValuesFrom(:p :q xsd:string))',
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


def _top_data_root_posting(snapshot: pyowl_core.OntologyView) -> memoryview:
    for index, axiom in enumerate(snapshot.iter_axioms(), 1):
        if (
            isinstance(axiom, owl.FunctionalDataProperty)
            and axiom.property.iri == owl.OWL_TOP_DATA_PROPERTY.iri
        ):
            return memoryview(struct.pack("<I", index))
    raise AssertionError("profile fixture has no invalid top-data-property root")


def _anonymous_root_posting(snapshot: pyowl_core.OntologyView) -> memoryview:
    for index, axiom in enumerate(snapshot.iter_axioms(), 1):
        if isinstance(axiom, owl.SameIndividual):
            return memoryview(struct.pack("<I", index))
    raise AssertionError("profile fixture has no forbidden anonymous-individual root")


def _anonymous_graph_snapshot() -> pyowl_core.OntologyView:
    return pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(ObjectProperty(:q))",
            "ObjectPropertyAssertion(:p _:a _:b)",
            "ObjectPropertyAssertion(:p _:b _:c)",
            "ObjectPropertyAssertion(:p _:c _:a)",
            "ObjectPropertyAssertion(:p _:d _:e)",
            "ObjectPropertyAssertion(:q _:e _:d)",
            "ObjectPropertyAssertion(:p _:f :first)",
            "ObjectPropertyAssertion(:p :second _:f)",
        ),
        options=OPTIONS,
    )


def _entity_profile_snapshot() -> pyowl_core.OntologyView:
    return pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:shared))",
            "Declaration(DataProperty(:shared))",
            "Declaration(Class(:dual))",
            "Declaration(Datatype(:dual))",
            "Declaration(Class(<http://www.w3.org/1999/02/22-rdf-syntax-ns#custom>))",
            "Declaration(Class(owl:real))",
            "SubClassOf(:Missing owl:Thing)",
            'Annotation(:annotationMissing "value")',
        ),
        options=OPTIONS,
    )


def _extension_snapshot(label: str) -> pyowl_core.OntologyView:
    class_a = owl.Class(owl.IRI("urn:test:profile#A"))
    variable = swrl.Variable(owl.IRI("urn:test:profile#x"))
    rule = swrl.SWRLRule(
        owl.CanonicalSet((swrl.ClassAtom(class_a, variable),)),
        owl.CanonicalSet((swrl.ClassAtom(class_a, variable),)),
    )
    provenance = DocumentProvenance(
        hashlib.sha256(f"profile-extension:{label}".encode()).digest(),
        DigestKind.EXACT_BYTES,
        0,
        0,
        None,
        None,
        DocumentFormat.FUNCTIONAL,
        DetectionBasis.EXPLICIT,
    )
    document = OntologyDocument(
        OntologyID(owl.IRI(f"urn:test:profile:extension:{label}")),
        None,
        (),
        owl.CanonicalSet(),
        owl.CanonicalSet((owl.Declaration(class_a),)),
        owl.CanonicalSet((rule,)),
        provenance,
    )
    return pyowl_core.load_snapshot(document, options=OPTIONS)


def _extension_root_posting(snapshot: pyowl_core.OntologyView) -> memoryview:
    root_kinds = bytes(_buffers(snapshot)["root_kinds"])
    return memoryview(struct.pack("<I", root_kinds.index(3) + 1))


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
    assert all(
        issue.document_keys for issue in scalar.issues if issue.rule_id == DATA_RANGE_ARITY_RULE
    )
    assert all("document_keys" not in issue for issue in issues)


def test_origin_context_restores_full_scalar_root_diagnostics() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(*_invalid_body()),
        options=OPTIONS,
    )

    actual = _native_origin_manifest(snapshot)

    assert actual == _expected_origin_manifest(snapshot)
    issues = cast(list[dict[str, object]], actual["issues"])
    assert issues
    assert all(issue["document_keys"] for issue in issues)
    assert all(len(cast(str, issue["provenance_sha256"])) == 64 for issue in issues)


def test_public_capture_checks_origin_bearing_native_profile_before_rejection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(*_invalid_body()),
        options=OPTIONS,
    )
    factory = NativeBackendFactory(native)
    buffers = _buffers(snapshot)
    lease = SimpleNamespace()
    lease.buffers = buffers
    lease.root_slices = lambda: (
        SimpleNamespace(
            lease=lease,
            posting_mode=0,
            root_ids=memoryview(b""),
            member_tokens=(),
            anonymous_scope_maps=(),
        ),
    )
    monkeypatch.setattr(
        "pyhermit.backends.native.negotiate_encoded_input",
        lambda _view, _schemas: SimpleNamespace(lease=lease),
    )

    with pytest.raises(OntologyProfileError) as caught:
        capture_ontology(
            snapshot,
            _profile_validator=factory._validate_encoded_profile_handoff,
        )

    assert caught.value.context == {
        "issue_count": 2,
        "rule_ids": DATA_RANGE_ARITY_RULE,
    }


def test_top_data_property_positions_match_scalar_exactly() -> None:
    allowed = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "SubDataPropertyOf(:p owl:topDataProperty)",
        ),
        options=OPTIONS,
    )
    invalid = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "FunctionalDataProperty(owl:topDataProperty)",
            "SubDataPropertyOf(owl:topDataProperty owl:topDataProperty)",
            "SubClassOf(:A DataSomeValuesFrom(owl:topDataProperty xsd:string))",
        ),
        options=OPTIONS,
    )

    allowed_manifest = _native_manifest(allowed)
    scalar = validate_owl2_dl_view(invalid)
    actual = _native_manifest(invalid)

    assert allowed_manifest == _expected_manifest(allowed)
    assert allowed_manifest["conforms"] is True
    assert actual == _expected_manifest(invalid)
    issues = cast(list[dict[str, object]], actual["issues"])
    top_issues = [issue for issue in issues if issue["rule_id"] == TOP_DATA_PROPERTY_RULE]
    assert {issue["constructor"] for issue in top_issues} == {
        "FunctionalDataProperty",
        "SubClassOf",
        "SubDataPropertyOf",
    }
    assert len(top_issues) == 3
    assert all(len(cast(str, issue["provenance_sha256"])) == 64 for issue in top_issues)
    assert all(
        issue.document_keys for issue in scalar.issues if issue.rule_id == TOP_DATA_PROPERTY_RULE
    )
    assert all("document_keys" not in issue for issue in top_issues)


def test_local_anonymous_individual_positions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:p))",
            "Declaration(DataProperty(:value))",
            "SameIndividual(_:a :named)",
            "DifferentIndividuals(_:a :named)",
            "NegativeObjectPropertyAssertion(:p _:a :named)",
            'NegativeDataPropertyAssertion(:value _:a "x")',
            "ClassAssertion(ObjectOneOf(_:a) :named)",
            "ClassAssertion(ObjectHasValue(:p _:a) :named)",
        ),
        options=OPTIONS,
    )
    scalar = validate_owl2_dl_view(snapshot)

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    issues = cast(list[dict[str, object]], actual["issues"])
    axiom_issues = [issue for issue in issues if issue["rule_id"] == ANONYMOUS_AXIOM_POSITION_RULE]
    expression_issues = [
        issue for issue in issues if issue["rule_id"] == ANONYMOUS_CLASS_EXPRESSION_RULE
    ]
    assert {issue["constructor"] for issue in axiom_issues} == {
        "DifferentIndividuals",
        "NegativeDataPropertyAssertion",
        "NegativeObjectPropertyAssertion",
        "SameIndividual",
    }
    assert {issue["constructor"] for issue in expression_issues} == {
        "ObjectHasValue",
        "ObjectOneOf",
    }
    assert len(axiom_issues) == 4
    assert len(expression_issues) == 2
    assert all(
        issue.document_keys
        for issue in scalar.issues
        if issue.rule_id in {ANONYMOUS_AXIOM_POSITION_RULE, ANONYMOUS_CLASS_EXPRESSION_RULE}
    )
    assert all("document_keys" not in issue for issue in (*axiom_issues, *expression_issues))


def test_anonymous_forest_diagnostics_match_scalar_exactly() -> None:
    snapshot = _anonymous_graph_snapshot()
    scalar = validate_owl2_dl_view(snapshot)

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    issues = cast(list[dict[str, object]], actual["issues"])
    graph_issues = [
        issue
        for issue in issues
        if issue["rule_id"]
        in {
            ANONYMOUS_GRAPH_CYCLE_RULE,
            ANONYMOUS_PARALLEL_EDGE_RULE,
            ANONYMOUS_TREE_ROOT_RULE,
        }
    ]
    assert {issue["rule_id"] for issue in graph_issues} == {
        ANONYMOUS_GRAPH_CYCLE_RULE,
        ANONYMOUS_PARALLEL_EDGE_RULE,
        ANONYMOUS_TREE_ROOT_RULE,
    }
    assert all(issue["constructor"] == "ObjectPropertyAssertion" for issue in graph_issues)
    assert all(len(cast(str, issue["provenance_sha256"])) == 64 for issue in graph_issues)
    assert all(
        issue.document_keys
        for issue in scalar.issues
        if issue.rule_id
        in {
            ANONYMOUS_GRAPH_CYCLE_RULE,
            ANONYMOUS_PARALLEL_EDGE_RULE,
            ANONYMOUS_TREE_ROOT_RULE,
        }
    )
    assert all("document_keys" not in issue for issue in graph_issues)


def test_global_entity_diagnostics_match_scalar_exactly_with_null_origin_fields() -> None:
    snapshot = _entity_profile_snapshot()

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    issues = cast(list[dict[str, object]], actual["issues"])
    entity_issues = [issue for issue in issues if issue["rule_id"] in ENTITY_RULES]
    assert {issue["rule_id"] for issue in entity_issues} == {
        PROPERTY_PUNNING_RULE,
        CLASS_DATATYPE_PUNNING_RULE,
        RESERVED_VOCABULARY_RULE,
        BUILTIN_ENTITY_KIND_RULE,
        MISSING_DECLARATION_RULE,
    }
    assert all(issue["constructor"] is None for issue in entity_issues)
    assert all(issue["provenance_sha256"] is None for issue in entity_issues)
    assert all("document_keys" not in issue for issue in entity_issues)
    assert sum(issue["rule_id"] == MISSING_DECLARATION_RULE for issue in entity_issues) == 2


def test_legal_builtin_entity_kinds_match_scalar_without_global_issues() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(owl:Thing))",
            "Declaration(ObjectProperty(owl:bottomObjectProperty))",
            "Declaration(DataProperty(owl:bottomDataProperty))",
            "Declaration(AnnotationProperty(<http://www.w3.org/2000/01/rdf-schema#label>))",
            "Declaration(Datatype(xsd:string))",
            "Declaration(Datatype(owl:rational))",
            "Declaration(Datatype(<http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral>))",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert not any(
        issue["rule_id"] in ENTITY_RULES
        for issue in cast(list[dict[str, object]], actual["issues"])
    )


@pytest.mark.parametrize(
    ("source", "expected_rule", "expected_message"),
    (
        (
            (
                "Ontology(<http://www.w3.org/1999/02/22-rdf-syntax-ns#ontology> "
                "Declaration(Class(<urn:test#A>)))"
            ),
            RESERVED_ONTOLOGY_IRI_RULE,
            (
                "ontology IRI must not use reserved OWL/RDF vocabulary: "
                "http://www.w3.org/1999/02/22-rdf-syntax-ns#ontology"
            ),
        ),
        (
            ("Ontology(<http://www.w3.org/2002/07/owl#ontology> Declaration(Class(<urn:test#A>)))"),
            RESERVED_ONTOLOGY_IRI_RULE,
            (
                "ontology IRI must not use reserved OWL/RDF vocabulary: "
                "http://www.w3.org/2002/07/owl#ontology"
            ),
        ),
        (
            (
                "Ontology(<urn:test:ontology> "
                "<http://www.w3.org/2001/XMLSchema#version> "
                "Declaration(Class(<urn:test#A>)))"
            ),
            RESERVED_VERSION_IRI_RULE,
            (
                "version IRI must not use reserved OWL/RDF vocabulary: "
                "http://www.w3.org/2001/XMLSchema#version"
            ),
        ),
        (
            (
                "Ontology(<urn:test:ontology> "
                "<http://www.w3.org/2000/01/rdf-schema#version> "
                "Declaration(Class(<urn:test#A>)))"
            ),
            RESERVED_VERSION_IRI_RULE,
            (
                "version IRI must not use reserved OWL/RDF vocabulary: "
                "http://www.w3.org/2000/01/rdf-schema#version"
            ),
        ),
    ),
)
def test_reserved_ontology_identifiers_match_scalar_projection(
    source: str,
    expected_rule: str,
    expected_message: str,
) -> None:
    snapshot = pyowl_core.load_snapshot(source.encode(), options=OPTIONS)

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    issue = next(
        issue
        for issue in cast(list[dict[str, object]], actual["issues"])
        if issue["rule_id"] == expected_rule
    )
    assert issue == {
        "rule_id": expected_rule,
        "severity": "error",
        "message": expected_message,
        "constructor": "OntologyID",
        "provenance_sha256": None,
    }
    assert "document_keys" not in issue


def test_reserved_ontology_identifiers_compose_canonically_across_documents() -> None:
    left = pyowl_core.load_snapshot(
        (b"Ontology(<http://www.w3.org/2002/07/owl#left> Declaration(Class(<urn:left#A>)))"),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        (
            b"Ontology(<urn:right> <http://www.w3.org/2000/01/rdf-schema#right> "
            b"Declaration(Class(<urn:right#A>)))"
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    tokens = cast(tuple[bytes, ...], cast(Any, composite)._source_tokens())
    sources_by_token = sorted(zip(tokens, (left, right), strict=True), key=lambda row: row[0])
    records = tuple(
        _slice_record(source, member_tokens=(token,)) for token, source in sources_by_token
    )
    context = _ontology_identity_context(composite)

    forward = _native_slices_manifest(
        *records,
        ontology_identity_context=context,
    )
    reverse = _native_slices_manifest(
        *reversed(records),
        ontology_identity_context=context,
    )

    assert forward == reverse == _expected_manifest(composite)
    assert {
        RESERVED_ONTOLOGY_IRI_RULE,
        RESERVED_VERSION_IRI_RULE,
    } <= set(cast(list[str], forward["ordered_rule_ids"]))


def test_origin_context_preserves_document_specific_ontology_identity_issues() -> None:
    left = pyowl_core.load_snapshot(
        (b"Ontology(<http://www.w3.org/2002/07/owl#left> Declaration(Class(<urn:left#A>)))"),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        (
            b"Ontology(<urn:right> <http://www.w3.org/2000/01/rdf-schema#right> "
            b"Declaration(Class(<urn:right#A>)))"
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    tokens = cast(tuple[bytes, ...], cast(Any, composite)._source_tokens())
    sources_by_token = sorted(zip(tokens, (left, right), strict=True), key=lambda row: row[0])
    records = tuple(
        _slice_record(source, member_tokens=(token,)) for token, source in sources_by_token
    )

    forward = _native_origin_slices_manifest(
        *records,
        ontology_identity_context=_ontology_identity_context(composite),
        origin_context=_profile_origin_context(composite),
    )
    reverse = _native_origin_slices_manifest(
        *reversed(records),
        ontology_identity_context=_ontology_identity_context(composite),
        origin_context=_profile_origin_context(composite),
    )

    assert forward == reverse == _expected_origin_manifest(composite)
    issues = cast(list[dict[str, object]], forward["issues"])
    assert all(len(cast(list[str], issue["document_keys"])) == 1 for issue in issues)


def test_origin_context_does_not_change_legacy_identity_deduplication() -> None:
    ontology_iri = "http://www.w3.org/2002/07/owl#ontology"
    left = pyowl_core.load_snapshot(
        functional("Declaration(Class(:A))", ontology_iri=ontology_iri),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional("Declaration(Class(:B))", ontology_iri=ontology_iri),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    tokens = cast(tuple[bytes, ...], cast(Any, composite)._source_tokens())
    sources_by_token = sorted(zip(tokens, (left, right), strict=True), key=lambda row: row[0])
    records = tuple(
        _slice_record(source, member_tokens=(token,)) for token, source in sources_by_token
    )
    identity_context = _ontology_identity_context(composite)

    legacy = _native_slices_manifest(
        *records,
        ontology_identity_context=identity_context,
    )
    with_origins = _native_origin_slices_manifest(
        *records,
        ontology_identity_context=identity_context,
        origin_context=_profile_origin_context(composite),
    )

    legacy_issues = [
        issue
        for issue in cast(list[dict[str, object]], legacy["issues"])
        if issue["rule_id"] == RESERVED_ONTOLOGY_IRI_RULE
    ]
    origin_issues = [
        issue
        for issue in cast(list[dict[str, object]], with_origins["issues"])
        if issue["rule_id"] == RESERVED_ONTOLOGY_IRI_RULE
    ]
    assert len(legacy_issues) == 1
    assert "document_keys" not in legacy_issues[0]
    assert with_origins == _expected_origin_manifest(composite)
    assert len(origin_issues) == 2
    assert len({tuple(cast(list[str], issue["document_keys"])) for issue in origin_issues}) == 2


def test_origin_context_unions_documents_for_deduplicated_composite_axioms() -> None:
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
        _slice_record(source, member_tokens=(token,)) for token, source in sources_by_token
    )
    identity_context = _ontology_identity_context(composite)
    origin_context = _profile_origin_context(composite)

    forward = _native_origin_slices_manifest(
        *records,
        ontology_identity_context=identity_context,
        origin_context=origin_context,
    )
    reverse = _native_origin_slices_manifest(
        *reversed(records),
        ontology_identity_context=identity_context,
        origin_context=origin_context,
    )

    assert forward == reverse == _expected_origin_manifest(composite)
    issues = cast(list[dict[str, object]], forward["issues"])
    provenance_issues = [issue for issue in issues if issue["provenance_sha256"] is not None]
    assert provenance_issues
    assert all(len(cast(list[str], issue["document_keys"])) == 2 for issue in provenance_issues)


@pytest.mark.parametrize(
    ("body", "expected_rule"),
    (
        (
            ("Declaration(Datatype(:unknown))",),
            UNSUPPORTED_DATATYPE_RULE,
        ),
        (
            ("DatatypeDefinition(xsd:string xsd:integer)",),
            BUILTIN_DATATYPE_REDEFINITION_RULE,
        ),
        (
            (
                "Declaration(Datatype(:custom))",
                "DatatypeDefinition(:custom xsd:string)",
                "DatatypeDefinition(:custom xsd:integer)",
            ),
            DUPLICATE_DATATYPE_DEFINITION_RULE,
        ),
        (
            (
                "Declaration(Datatype(:first))",
                "Declaration(Datatype(:second))",
                "DatatypeDefinition(:first DataComplementOf(:second))",
                "DatatypeDefinition(:second DataUnionOf(:first xsd:string))",
            ),
            RECURSIVE_DATATYPE_DEFINITION_RULE,
        ),
    ),
)
def test_global_datatype_definition_errors_match_scalar_exactly(
    body: tuple[str, ...],
    expected_rule: str,
) -> None:
    snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    datatype_rules = {
        BUILTIN_DATATYPE_REDEFINITION_RULE,
        DUPLICATE_DATATYPE_DEFINITION_RULE,
        RECURSIVE_DATATYPE_DEFINITION_RULE,
        UNSUPPORTED_DATATYPE_RULE,
    }
    assert [
        rule for rule in cast(list[str], actual["ordered_rule_ids"]) if rule in datatype_rules
    ] == [expected_rule]


def test_opaque_datatype_policy_matches_scalar_warning_and_conformance() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:opaque))",
            "Declaration(DataProperty(:value))",
            "DataPropertyRange(:value DataUnionOf(:opaque xsd:string))",
            'DataPropertyAssertion(:value :individual "value"^^:opaque)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(
        snapshot,
        unsupported_datatypes=UnsupportedDatatypePolicy.IGNORE_WITH_WARNING,
    )

    assert actual == _expected_manifest(
        snapshot,
        unsupported_datatypes=UnsupportedDatatypePolicy.IGNORE_WITH_WARNING,
    )
    assert actual["conforms"] is True
    assert actual["ordered_rule_ids"] == [UNSUPPORTED_DATATYPE_OPAQUE_RULE]
    assert actual["issues"] == [
        {
            "rule_id": UNSUPPORTED_DATATYPE_OPAQUE_RULE,
            "severity": "warning",
            "message": ("unsupported datatype is treated as opaque: urn:test:profile#opaque"),
            "constructor": "Datatype",
            "provenance_sha256": None,
        }
    ]
    assert UNSUPPORTED_DATATYPE_RULE in _native_manifest(snapshot)["ordered_rule_ids"]


@pytest.mark.parametrize(
    "body",
    (
        (
            "Declaration(Datatype(:opaque))",
            "Declaration(DataProperty(:value))",
            (
                "DataPropertyRange(:value DatatypeRestriction(:opaque "
                'xsd:minLength "2"^^xsd:integer))'
            ),
        ),
        (
            "Declaration(Datatype(:custom))",
            "Declaration(Datatype(:opaque))",
            "DatatypeDefinition(:custom :opaque)",
        ),
        (
            "Declaration(Datatype(:opaque))",
            "Declaration(DataProperty(:value))",
            'DataPropertyRange(:value DataOneOf("value"^^:opaque))',
        ),
    ),
)
def test_opaque_policy_keeps_unsupported_range_boundaries(
    body: tuple[str, ...],
) -> None:
    snapshot = pyowl_core.load_snapshot(functional(*body), options=OPTIONS)

    actual = _native_manifest(
        snapshot,
        unsupported_datatypes=UnsupportedDatatypePolicy.IGNORE_WITH_WARNING,
    )

    assert actual == _expected_manifest(
        snapshot,
        unsupported_datatypes=UnsupportedDatatypePolicy.IGNORE_WITH_WARNING,
    )
    issues = cast(list[dict[str, object]], actual["issues"])
    assert {issue["rule_id"] for issue in issues} == {
        UNSUPPORTED_DATATYPE_OPAQUE_RULE,
        UNSUPPORTED_DATATYPE_RULE,
    }
    assert [
        issue["constructor"] for issue in issues if issue["rule_id"] == UNSUPPORTED_DATATYPE_RULE
    ] == ["DataRange"]


def test_opaque_datatype_warnings_recompute_across_slices() -> None:
    left = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:opaque))",
            "Declaration(DataProperty(:value))",
            ontology_iri="urn:test:profile:opaque:left",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            'DataPropertyAssertion(:value :individual "value"^^:opaque)',
            ontology_iri="urn:test:profile:opaque:right",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    tokens = cast(tuple[bytes, ...], cast(Any, composite)._source_tokens())
    sources_by_token = sorted(zip(tokens, (left, right), strict=True), key=lambda row: row[0])
    records = tuple(
        _slice_record(source, member_tokens=(token,)) for token, source in sources_by_token
    )

    forward = _native_slices_manifest(
        *records,
        unsupported_datatypes=UnsupportedDatatypePolicy.IGNORE_WITH_WARNING,
    )
    reverse = _native_slices_manifest(
        *reversed(records),
        unsupported_datatypes=UnsupportedDatatypePolicy.IGNORE_WITH_WARNING,
    )

    assert forward == reverse
    assert forward == _expected_manifest(
        composite,
        unsupported_datatypes=UnsupportedDatatypePolicy.IGNORE_WITH_WARNING,
    )
    assert forward["conforms"] is True
    assert forward["ordered_rule_ids"] == [UNSUPPORTED_DATATYPE_OPAQUE_RULE]


def test_custom_datatype_literal_message_matches_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:custom))",
            "Declaration(DataProperty(:value))",
            "DatatypeDefinition(:custom xsd:string)",
            'DataPropertyAssertion(:value :individual "value"^^:custom)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    issue = next(
        item
        for item in cast(list[dict[str, object]], actual["issues"])
        if item["rule_id"] == CUSTOM_DATATYPE_LITERAL_RULE
    )
    assert issue["constructor"] == "Literal"
    assert issue["message"] == (
        "a datatype defined in the ontology has no lexical space and cannot be "
        "used on a literal: urn:test:profile#custom"
    )
    assert issue["provenance_sha256"] is None


def test_datatype_definition_error_precedence_matches_scalar_statement_order() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:custom))",
            "DatatypeDefinition(:custom xsd:string)",
            "DatatypeDefinition(:custom xsd:integer)",
            "DatatypeDefinition(xsd:boolean xsd:string)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)


def test_invalid_literal_messages_and_constructors_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:value))",
            'DataPropertyAssertion(:value :integer "nope"^^xsd:integer)',
            'DataPropertyAssertion(:value :xml "<broken>"^^rdf:XMLLiteral)',
            (
                'DataPropertyAssertion(:value :declaration "<!DOCTYPE x [<!ENTITY y '
                "'z'>]><x>&y;</x>\"^^rdf:XMLLiteral)"
            ),
            'DataPropertyAssertion(:value :universal "value"^^rdfs:Literal)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    messages = {
        cast(str, issue["message"])
        for issue in cast(list[dict[str, object]], actual["issues"])
        if issue["rule_id"] == INVALID_LITERAL_RULE
    }
    assert messages == {
        "literal lexical form is outside the datatype lexical space",
        "rdf:XMLLiteral is not a well-formed XML fragment",
        "rdf:XMLLiteral forbids DTD and entity declarations",
    }
    assert {
        issue["constructor"]
        for issue in cast(list[dict[str, object]], actual["issues"])
        if issue["rule_id"] == INVALID_LITERAL_RULE
    } == {"Literal"}


def test_invalid_data_enumeration_literal_has_data_range_and_literal_issues() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:value))",
            'DataPropertyRange(:value DataOneOf("nope"^^xsd:integer))',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert {
        issue["constructor"]
        for issue in cast(list[dict[str, object]], actual["issues"])
        if issue["rule_id"] == INVALID_LITERAL_RULE
    } == {"DataRange", "Literal"}


@pytest.mark.parametrize(
    ("data_range", "expected_rule", "expected_message"),
    (
        (
            'DatatypeRestriction(xsd:boolean xsd:minInclusive "false"^^xsd:boolean)',
            ILLEGAL_DATATYPE_FACET_RULE,
            "facet is not legal for the restricted OWL 2 datatype",
        ),
        (
            'DatatypeRestriction(xsd:string xsd:length "-1"^^xsd:integer)',
            INVALID_FACET_VALUE_RULE,
            "facet literal has the wrong datatype or value domain",
        ),
        (
            'DatatypeRestriction(xsd:integer xsd:minInclusive "1"^^xsd:string)',
            INVALID_FACET_VALUE_RULE,
            "facet literal has the wrong datatype or value domain",
        ),
        (
            'DatatypeRestriction(rdf:PlainLiteral rdf:langRange "-bad"^^xsd:string)',
            INVALID_FACET_VALUE_RULE,
            "rdf:langRange requires an RFC 4647 basic language range",
        ),
    ),
)
def test_datatype_facet_rules_match_scalar_exactly(
    data_range: str,
    expected_rule: str,
    expected_message: str,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:value))",
            f"DataPropertyRange(:value {data_range})",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    issue = next(
        issue
        for issue in cast(list[dict[str, object]], actual["issues"])
        if issue["rule_id"] == expected_rule
    )
    assert issue["message"] == expected_message
    assert issue["constructor"] == "DataRange"
    assert issue["provenance_sha256"] is None


def test_facet_literal_compilation_precedes_facet_legality() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:value))",
            (
                "DataPropertyRange(:value DatatypeRestriction(xsd:boolean "
                'xsd:minInclusive "nope"^^xsd:boolean))'
            ),
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert INVALID_LITERAL_RULE in cast(list[str], actual["ordered_rule_ids"])
    assert ILLEGAL_DATATYPE_FACET_RULE not in cast(list[str], actual["ordered_rule_ids"])


@pytest.mark.parametrize(
    ("pattern", "expected_rule"),
    (
        ("[ab]+", ILLEGAL_DATATYPE_FACET_RULE),
        ("[", None),
    ),
)
def test_pattern_errors_preserve_scalar_semantic_error_precedence(
    pattern: str,
    expected_rule: str | None,
) -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:value))",
            (
                "DataPropertyRange(:value DatatypeRestriction(xsd:string "
                f'xsd:pattern "{pattern}"^^xsd:string '
                'xsd:totalDigits "1"^^xsd:integer))'
            ),
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    if expected_rule is None:
        assert ILLEGAL_DATATYPE_FACET_RULE not in cast(list[str], actual["ordered_rule_ids"])
    else:
        assert expected_rule in cast(list[str], actual["ordered_rule_ids"])


def test_non_simple_object_property_positions_match_scalar_exactly() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:left))",
            "Declaration(ObjectProperty(:right))",
            "Declaration(ObjectProperty(:chain))",
            "Declaration(ObjectProperty(:super))",
            "Declaration(ObjectProperty(:equivalent))",
            "Declaration(ObjectProperty(:inversePartner))",
            "Declaration(ObjectProperty(:simple))",
            "Declaration(ObjectProperty(:transitive))",
            "SubObjectPropertyOf(ObjectPropertyChain(:left :right) :chain)",
            "SubObjectPropertyOf(:chain :super)",
            "EquivalentObjectProperties(:super :equivalent)",
            "InverseObjectProperties(:super :inversePartner)",
            "SymmetricObjectProperty(:super)",
            "TransitiveObjectProperty(:transitive)",
            "FunctionalObjectProperty(:super)",
            "FunctionalObjectProperty(:equivalent)",
            "FunctionalObjectProperty(:inversePartner)",
            "FunctionalObjectProperty(:transitive)",
            "InverseFunctionalObjectProperty(ObjectInverseOf(:super))",
            "IrreflexiveObjectProperty(:chain)",
            "AsymmetricObjectProperty(:super)",
            "DisjointObjectProperties(:chain :simple)",
            "SubClassOf(ObjectHasSelf(:chain) :A)",
            "SubClassOf(ObjectMinCardinality(2 :super :A) :A)",
            "SubClassOf(ObjectMaxCardinality(2 ObjectInverseOf(:super) :A) :A)",
            "SubClassOf(ObjectExactCardinality(2 :simple :A) :A)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    issues = [
        issue
        for issue in cast(list[dict[str, object]], actual["issues"])
        if issue["rule_id"] == NON_SIMPLE_PROPERTY_RULE
    ]
    assert len(issues) == 11
    assert {issue["constructor"] for issue in issues} == {
        "AsymmetricObjectProperty",
        "DisjointObjectProperties",
        "FunctionalObjectProperty",
        "InverseFunctionalObjectProperty",
        "IrreflexiveObjectProperty",
        "SubClassOf",
    }
    assert all(len(cast(str, issue["provenance_sha256"])) == 64 for issue in issues)


def test_simple_object_property_positions_remain_conformant() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Class(:A))",
            "Declaration(ObjectProperty(:simple))",
            "FunctionalObjectProperty(:simple)",
            "InverseFunctionalObjectProperty(ObjectInverseOf(:simple))",
            "IrreflexiveObjectProperty(:simple)",
            "AsymmetricObjectProperty(:simple)",
            "DisjointObjectProperties(:simple ObjectInverseOf(:simple))",
            "SubClassOf(ObjectHasSelf(:simple) :A)",
            "SubClassOf(ObjectMinCardinality(2 :simple :A) :A)",
            "SubClassOf(ObjectMaxCardinality(2 :simple :A) :A)",
            "SubClassOf(ObjectExactCardinality(2 :simple :A) :A)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert NON_SIMPLE_PROPERTY_RULE not in actual["ordered_rule_ids"]


def test_role_regularity_diagnostics_match_scalar_exactly() -> None:
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
    assert set(cast(list[str], actual["ordered_rule_ids"])) == {
        RIA_DEPENDENCY_CYCLE_RULE,
        RIA_INVERSE_RECURSION_RULE,
        RIA_NON_REGULAR_RECURSION_RULE,
    }
    assert all(
        issue["constructor"] == "SubObjectPropertyOf"
        for issue in cast(list[dict[str, object]], actual["issues"])
    )


def test_legal_role_recursion_and_top_exception_remain_conformant() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abcd"),
            "SubObjectPropertyOf(ObjectPropertyChain(:a :b) :a)",
            "SubObjectPropertyOf(ObjectPropertyChain(:c :d) :d)",
            "TransitiveObjectProperty(:b)",
            "SubObjectPropertyOf(ObjectPropertyChain(:d :c :a) owl:topObjectProperty)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert not {
        RIA_DEPENDENCY_CYCLE_RULE,
        RIA_INVERSE_RECURSION_RULE,
        RIA_NON_REGULAR_RECURSION_RULE,
    } & set(cast(list[str], actual["ordered_rule_ids"]))


def test_annotated_duplicate_regularity_source_uses_scalar_last_statement() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(AnnotationProperty(:note))",
            *(f"Declaration(ObjectProperty(:{name}))" for name in "acd"),
            'SubObjectPropertyOf(Annotation(:note "first") ObjectPropertyChain(:c :a :d) :a)',
            'SubObjectPropertyOf(Annotation(:note "second") ObjectPropertyChain(:c :a :d) :a)',
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    issues = [
        issue
        for issue in cast(list[dict[str, object]], actual["issues"])
        if issue["rule_id"] == RIA_NON_REGULAR_RECURSION_RULE
    ]
    assert len(issues) == 1


def test_regularity_cycle_selection_uses_canonical_role_byte_order() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in ("aa", "ab", "g", "y", "z")),
            "SubObjectPropertyOf(ObjectPropertyChain(:ab :g) :aa)",
            "SubObjectPropertyOf(ObjectPropertyChain(:aa :g) :ab)",
            "SubObjectPropertyOf(ObjectPropertyChain(:z :g) :y)",
            "SubObjectPropertyOf(ObjectPropertyChain(:y :g) :z)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    cycles = [
        issue
        for issue in cast(list[dict[str, object]], actual["issues"])
        if issue["rule_id"] == RIA_DEPENDENCY_CYCLE_RULE
    ]
    assert len(cycles) == 1


def test_inverse_recursion_disappears_inside_a_symmetric_role_component() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:a))",
            "Declaration(ObjectProperty(:g))",
            "SymmetricObjectProperty(:a)",
            "SubObjectPropertyOf(ObjectPropertyChain(ObjectInverseOf(:a) :g) :a)",
        ),
        options=OPTIONS,
    )

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert RIA_INVERSE_RECURSION_RULE not in actual["ordered_rule_ids"]


def test_extension_component_diagnostic_and_count_match_scalar_exactly() -> None:
    snapshot = _extension_snapshot("single")
    scalar = validate_owl2_dl_view(snapshot)
    extension = next(snapshot.iter_extensions())

    actual = _native_manifest(snapshot)

    assert actual == _expected_manifest(snapshot)
    assert actual["axioms_checked"] == 1
    assert actual["extensions_checked"] == 1
    assert actual["ordered_rule_ids"] == [EXTENSION_COMPONENT_RULE]
    issue = cast(list[dict[str, object]], actual["issues"])[0]
    assert issue["constructor"] == "SWRLRule"
    assert issue["provenance_sha256"] == hashlib.sha256(extension.canonical_bytes()).hexdigest()
    scalar_issue = next(item for item in scalar.issues if item.rule_id == EXTENSION_COMPONENT_RULE)
    assert scalar_issue.document_keys
    assert "document_keys" not in issue


def test_origin_context_restores_extension_document_keys() -> None:
    snapshot = _extension_snapshot("origin")

    actual = _native_origin_manifest(snapshot)

    assert actual == _expected_origin_manifest(snapshot)
    issue = cast(list[dict[str, object]], actual["issues"])[0]
    assert issue["rule_id"] == EXTENSION_COMPONENT_RULE
    assert issue["document_keys"]


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
    assert actual["ordered_rule_ids"] == [DATA_RANGE_ARITY_RULE]
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
        b"".join(struct.pack("<I", index) for index in range(1, root_count + 1) if index != bad_id)
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
    assert cast(list[str], manifest["ordered_rule_ids"]).count(MISSING_DECLARATION_RULE) == 4
    assert cast(list[str], manifest["ordered_rule_ids"]).count(DATA_RANGE_ARITY_RULE) == 1


def test_top_data_property_selection_and_composite_deduplication_are_canonical() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(DataProperty(:p))",
            "FunctionalDataProperty(owl:topDataProperty)",
            "SubDataPropertyOf(:p owl:topDataProperty)",
        ),
        options=OPTIONS,
    )
    invalid = _top_data_root_posting(snapshot)
    root_count = len(tuple(snapshot.iter_axioms()))
    invalid_id = struct.unpack("<I", invalid)[0]
    complement = memoryview(
        b"".join(
            struct.pack("<I", index) for index in range(1, root_count + 1) if index != invalid_id
        )
    )

    included = native._encoded_profile_slices_manifest_v1(
        slices=(_slice_record(snapshot, posting_mode=1, postings=invalid),)
    )
    excluded = native._encoded_profile_slices_manifest_v1(
        slices=(_slice_record(snapshot, posting_mode=2, postings=complement),)
    )

    assert included == excluded
    selected = cast(dict[str, object], json.loads(included))
    assert selected["axioms_checked"] == 1
    assert selected["ordered_rule_ids"] == [TOP_DATA_PROPERTY_RULE]

    left = pyowl_core.load_snapshot(
        functional(
            "FunctionalDataProperty(owl:topDataProperty)",
            ontology_iri="urn:test:profile:top:left",
        ),
        options=OPTIONS,
    )
    right = pyowl_core.load_snapshot(
        functional(
            "FunctionalDataProperty(owl:topDataProperty)",
            ontology_iri="urn:test:profile:top:right",
        ),
        options=OPTIONS,
    )
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    tokens = cast(tuple[bytes, ...], cast(Any, composite)._source_tokens())
    sources_by_token = sorted(zip(tokens, (left, right), strict=True), key=lambda row: row[0])
    records = tuple(
        _slice_record(source, member_tokens=(token,)) for token, source in sources_by_token
    )
    forward = native._encoded_profile_slices_manifest_v1(slices=records)
    reverse = native._encoded_profile_slices_manifest_v1(slices=tuple(reversed(records)))

    assert forward == reverse
    assert json.loads(forward) == _expected_manifest(composite)
    assert json.loads(forward)["axioms_checked"] == 1


def test_anonymous_position_selection_and_duplicate_slice_merge_are_canonical() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "SameIndividual(_:a :named)",
            "ClassAssertion(ObjectOneOf(_:a) :named)",
        ),
        options=OPTIONS,
    )
    invalid = _anonymous_root_posting(snapshot)
    root_count = len(tuple(snapshot.iter_axioms()))
    invalid_id = struct.unpack("<I", invalid)[0]
    complement = memoryview(
        b"".join(
            struct.pack("<I", index) for index in range(1, root_count + 1) if index != invalid_id
        )
    )

    included = native._encoded_profile_slices_manifest_v1(
        slices=(_slice_record(snapshot, posting_mode=1, postings=invalid),)
    )
    excluded = native._encoded_profile_slices_manifest_v1(
        slices=(_slice_record(snapshot, posting_mode=2, postings=complement),)
    )

    assert included == excluded
    selected = cast(dict[str, object], json.loads(included))
    assert selected["axioms_checked"] == 1
    assert selected["ordered_rule_ids"] == [ANONYMOUS_AXIOM_POSITION_RULE]

    record = _slice_record(snapshot)
    merged = native._encoded_profile_slices_manifest_v1(slices=(record, record))

    assert merged == native._encoded_profile_manifest_v1(**_buffers(snapshot))
    assert json.loads(merged) == _expected_manifest(snapshot)


def test_anonymous_forest_is_recomputed_across_selected_slices() -> None:
    snapshot = _anonymous_graph_snapshot()
    root_count = len(bytes(_buffers(snapshot)["root_kinds"]))
    odd = memoryview(
        b"".join(struct.pack("<I", index) for index in range(1, root_count + 1) if index % 2 == 1)
    )
    even = memoryview(
        b"".join(struct.pack("<I", index) for index in range(1, root_count + 1) if index % 2 == 0)
    )
    records = (
        _slice_record(snapshot, posting_mode=1, postings=odd),
        _slice_record(snapshot, posting_mode=1, postings=even),
    )

    direct = native._encoded_profile_manifest_v1(**_buffers(snapshot))
    forward = native._encoded_profile_slices_manifest_v1(slices=records)
    reverse = native._encoded_profile_slices_manifest_v1(slices=tuple(reversed(records)))

    assert forward == reverse == direct
    assert json.loads(forward) == _expected_manifest(snapshot)


def test_entity_rules_are_recomputed_across_one_root_slices() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:shared))",
            "Declaration(DataProperty(:shared))",
            "Declaration(Class(:declared))",
            "SubClassOf(:declared owl:Thing)",
        ),
        options=OPTIONS,
    )
    root_count = len(bytes(_buffers(snapshot)["root_kinds"]))
    records = tuple(
        _slice_record(
            snapshot,
            posting_mode=1,
            postings=memoryview(struct.pack("<I", index)),
        )
        for index in range(1, root_count + 1)
    )

    direct = native._encoded_profile_manifest_v1(**_buffers(snapshot))
    forward = native._encoded_profile_slices_manifest_v1(slices=records)
    reverse = native._encoded_profile_slices_manifest_v1(slices=tuple(reversed(records)))

    assert forward == reverse == direct
    assert json.loads(forward) == _expected_manifest(snapshot)
    assert json.loads(forward)["ordered_rule_ids"] == [PROPERTY_PUNNING_RULE]


def test_non_simple_role_closure_is_recomputed_across_one_root_slices() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(ObjectProperty(:left))",
            "Declaration(ObjectProperty(:right))",
            "Declaration(ObjectProperty(:chain))",
            "Declaration(ObjectProperty(:super))",
            "SubObjectPropertyOf(ObjectPropertyChain(:left :right) :chain)",
            "SubObjectPropertyOf(:chain :super)",
            "FunctionalObjectProperty(:super)",
        ),
        options=OPTIONS,
    )
    root_count = len(bytes(_buffers(snapshot)["root_kinds"]))
    records = tuple(
        _slice_record(
            snapshot,
            posting_mode=1,
            postings=memoryview(struct.pack("<I", index)),
        )
        for index in range(1, root_count + 1)
    )

    direct = native._encoded_profile_manifest_v1(**_buffers(snapshot))
    forward = native._encoded_profile_slices_manifest_v1(slices=records)
    reverse = native._encoded_profile_slices_manifest_v1(slices=tuple(reversed(records)))

    assert forward == reverse == direct
    assert json.loads(forward) == _expected_manifest(snapshot)
    assert json.loads(forward)["ordered_rule_ids"] == [NON_SIMPLE_PROPERTY_RULE]


def test_role_regularity_is_recomputed_across_one_root_slices() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            *(f"Declaration(ObjectProperty(:{name}))" for name in "abg"),
            "SubObjectPropertyOf(ObjectPropertyChain(:b :g) :a)",
            "SubObjectPropertyOf(ObjectPropertyChain(:a :g) :b)",
        ),
        options=OPTIONS,
    )
    root_count = len(bytes(_buffers(snapshot)["root_kinds"]))
    records = tuple(
        _slice_record(
            snapshot,
            posting_mode=1,
            postings=memoryview(struct.pack("<I", index)),
        )
        for index in range(1, root_count + 1)
    )

    direct = native._encoded_profile_manifest_v1(**_buffers(snapshot))
    forward = native._encoded_profile_slices_manifest_v1(slices=records)
    reverse = native._encoded_profile_slices_manifest_v1(slices=tuple(reversed(records)))

    assert forward == reverse == direct
    assert json.loads(forward) == _expected_manifest(snapshot)
    assert RIA_DEPENDENCY_CYCLE_RULE in json.loads(forward)["ordered_rule_ids"]


def test_datatype_rules_are_recomputed_across_one_root_slices() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:first))",
            "Declaration(Datatype(:second))",
            "Declaration(DataProperty(:value))",
            "DatatypeDefinition(:first :second)",
            "DatatypeDefinition(:second :first)",
            'DataPropertyAssertion(:value :individual "value"^^:first)',
        ),
        options=OPTIONS,
    )
    root_count = len(bytes(_buffers(snapshot)["root_kinds"]))
    records = tuple(
        _slice_record(
            snapshot,
            posting_mode=1,
            postings=memoryview(struct.pack("<I", index)),
        )
        for index in range(1, root_count + 1)
    )

    direct = native._encoded_profile_manifest_v1(**_buffers(snapshot))
    forward = native._encoded_profile_slices_manifest_v1(slices=records)
    reverse = native._encoded_profile_slices_manifest_v1(slices=tuple(reversed(records)))

    assert forward == reverse == direct
    assert json.loads(forward) == _expected_manifest(snapshot)
    assert {
        RECURSIVE_DATATYPE_DEFINITION_RULE,
        CUSTOM_DATATYPE_LITERAL_RULE,
    } <= set(json.loads(forward)["ordered_rule_ids"])


def test_datatype_facet_precedence_is_recomputed_across_one_root_slices() -> None:
    snapshot = pyowl_core.load_snapshot(
        functional(
            "Declaration(Datatype(:custom))",
            "Declaration(DataProperty(:value))",
            (
                "DatatypeDefinition(:custom DatatypeRestriction(xsd:boolean "
                'xsd:minInclusive "false"^^xsd:boolean))'
            ),
            (
                "DataPropertyRange(:value DatatypeRestriction(xsd:string "
                'xsd:length "-1"^^xsd:integer))'
            ),
        ),
        options=OPTIONS,
    )
    root_count = len(bytes(_buffers(snapshot)["root_kinds"]))
    records = tuple(
        _slice_record(
            snapshot,
            posting_mode=1,
            postings=memoryview(struct.pack("<I", index)),
        )
        for index in range(1, root_count + 1)
    )

    direct = native._encoded_profile_manifest_v1(**_buffers(snapshot))
    forward = native._encoded_profile_slices_manifest_v1(slices=records)
    reverse = native._encoded_profile_slices_manifest_v1(slices=tuple(reversed(records)))

    assert forward == reverse == direct
    assert json.loads(forward) == _expected_manifest(snapshot)
    assert ILLEGAL_DATATYPE_FACET_RULE in json.loads(forward)["ordered_rule_ids"]
    assert INVALID_FACET_VALUE_RULE not in json.loads(forward)["ordered_rule_ids"]


def test_extension_selection_and_composite_deduplication_are_canonical() -> None:
    snapshot = _extension_snapshot("selection")
    extension = _extension_root_posting(snapshot)
    root_count = len(bytes(_buffers(snapshot)["root_kinds"]))
    extension_id = struct.unpack("<I", extension)[0]
    complement = memoryview(
        b"".join(
            struct.pack("<I", index) for index in range(1, root_count + 1) if index != extension_id
        )
    )

    included = native._encoded_profile_slices_manifest_v1(
        slices=(_slice_record(snapshot, posting_mode=1, postings=extension),)
    )
    excluded = native._encoded_profile_slices_manifest_v1(
        slices=(_slice_record(snapshot, posting_mode=2, postings=complement),)
    )

    assert included == excluded
    selected = cast(dict[str, object], json.loads(included))
    assert selected["axioms_checked"] == 0
    assert selected["extensions_checked"] == 1
    assert selected["ordered_rule_ids"] == [EXTENSION_COMPONENT_RULE]

    left = _extension_snapshot("left")
    right = _extension_snapshot("right")
    composite = pyowl_core.compose_views(left, right, roles=("left", "right"))
    tokens = cast(tuple[bytes, ...], cast(Any, composite)._source_tokens())
    sources_by_token = sorted(zip(tokens, (left, right), strict=True), key=lambda row: row[0])
    records = tuple(
        _slice_record(source, member_tokens=(token,)) for token, source in sources_by_token
    )
    forward = native._encoded_profile_slices_manifest_v1(slices=records)
    reverse = native._encoded_profile_slices_manifest_v1(slices=tuple(reversed(records)))

    assert forward == reverse
    assert json.loads(forward) == _expected_manifest(composite)
    assert json.loads(forward)["extensions_checked"] == 1


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
        _slice_record(source, member_tokens=(token,)) for token, source in sources_by_token
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
            "SubClassOf(ObjectOneOf(_:a) DataSomeValuesFrom(:p :q xsd:string))",
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
    mapped = _native_slices_manifest(_slice_record(snapshot, anonymous_scope_maps=(scope_map,)))

    baseline_issues = cast(list[dict[str, object]], baseline["issues"])
    mapped_issues = cast(list[dict[str, object]], mapped["issues"])
    expected_provenance = hashlib.sha256(expected_axiom.canonical_bytes()).hexdigest()
    assert {cast(str, issue["provenance_sha256"]) for issue in mapped_issues} == {
        expected_provenance
    }
    assert {cast(str, issue["provenance_sha256"]) for issue in baseline_issues} != {
        expected_provenance
    }


def test_hostile_columns_fail_transactionally_and_valid_retry_is_unchanged() -> None:
    snapshot = pyowl_core.load_snapshot(functional(*_invalid_body()), options=OPTIONS)
    buffers = _buffers(snapshot)
    baseline = native._encoded_profile_manifest_v1(**buffers)
    hostile = dict(buffers)
    hostile["node_field_offsets"] = memoryview(bytes(buffers["node_field_offsets"])[:-1])

    with pytest.raises(BackendMismatchError, match="node_field_offsets"):
        native._encoded_profile_manifest_v1(**hostile)

    assert native._encoded_profile_manifest_v1(**buffers) == baseline


def test_unknown_unsupported_datatype_policy_fails_before_profile_publication() -> None:
    snapshot = pyowl_core.load_snapshot(functional(*_invalid_body()), options=OPTIONS)
    buffers = _buffers(snapshot)
    baseline = native._encoded_profile_manifest_v1(**buffers)

    with pytest.raises(
        BackendMismatchError,
        match="unsupported-datatype policy is not recognized",
    ):
        native._encoded_profile_manifest_v1(
            **buffers,
            unsupported_datatypes="opaque",
        )

    assert native._encoded_profile_manifest_v1(**buffers) == baseline


@pytest.mark.parametrize(
    "context",
    (
        (2, ()),
        (1, ()),
        (1, []),
        (1, (("urn:document:b", "urn:b", None), ("urn:document:a", "urn:a", None))),
        (1, (("urn:document:a", "urn:a", None), ("urn:document:a", "urn:b", None))),
        (1, (("", "urn:a", None),)),
        (1, (("urn:document:a", "", None),)),
        (1, (("urn:document:a", None, "urn:version"),)),
        (1, (("urn:document:a", "relative/ontology", None),)),
        (1, (("urn:document:a", "1bad:ontology", None),)),
        (1, (("urn:document:a", "urn:ontology", "urn:bad|version"),)),
        (1, (("urn:document:a", "urn:bad%2", None),)),
    ),
)
def test_hostile_ontology_identity_context_fails_transactionally(
    context: object,
) -> None:
    snapshot = pyowl_core.load_snapshot(functional(*_invalid_body()), options=OPTIONS)
    buffers = _buffers(snapshot)
    baseline = native._encoded_profile_manifest_v1(**buffers)

    with pytest.raises(BackendMismatchError, match="ontology identity"):
        native._encoded_profile_manifest_v1(
            **buffers,
            ontology_identity_context=context,
        )

    assert native._encoded_profile_manifest_v1(**buffers) == baseline


@pytest.mark.parametrize(
    "context",
    (
        (2, ()),
        (1, []),
        (1, ()),
        (1, ((b"\x00" * 31, ("urn:document:a",)),)),
        (1, ((b"\x00" * 32, ()),)),
        (1, ((b"\x00" * 32, ["urn:document:a"]),)),
        (1, ((b"\x00" * 32, ("",)),)),
        (1, ((b"\x00" * 32, ("urn:document:b", "urn:document:a")),)),
        (1, ((b"\x00" * 32, ("urn:document:a", "urn:document:a")),)),
        (
            1,
            (
                (b"\x01" * 32, ("urn:document:b",)),
                (b"\x00" * 32, ("urn:document:a",)),
            ),
        ),
        (
            1,
            (
                (b"\x00" * 32, ("urn:document:a",)),
                (b"\x00" * 32, ("urn:document:b",)),
            ),
        ),
    ),
)
def test_hostile_profile_origin_context_fails_transactionally(
    context: object,
) -> None:
    snapshot = pyowl_core.load_snapshot(functional(*_invalid_body()), options=OPTIONS)
    buffers = _buffers(snapshot)
    identity_context = _ontology_identity_context(snapshot)
    origin_context = _profile_origin_context(snapshot)
    baseline = native._encoded_profile_manifest_v1(
        **buffers,
        ontology_identity_context=identity_context,
        origin_context=origin_context,
    )

    with pytest.raises(BackendMismatchError, match="profile origin"):
        native._encoded_profile_manifest_v1(
            **buffers,
            ontology_identity_context=identity_context,
            origin_context=context,
        )

    assert (
        native._encoded_profile_manifest_v1(
            **buffers,
            ontology_identity_context=identity_context,
            origin_context=origin_context,
        )
        == baseline
    )


def test_ontology_identity_context_decode_cancellation_is_transactional() -> None:
    snapshot = pyowl_core.load_snapshot(functional(*_invalid_body()), options=OPTIONS)
    records = (_slice_record(snapshot),)
    context = _ontology_identity_context(snapshot)
    baseline = native._encoded_profile_slices_manifest_v1(
        slices=records,
        ontology_identity_context=context,
    )
    expected_phases = (
        "profile-ontology-identity-context-preflight",
        "profile-ontology-identity-context-document",
        "profile-ontology-identity-context-complete",
    )

    for checkpoint, expected_phase in enumerate(expected_phases, start=1):
        with pytest.raises(ReasonerInterruptedError) as interrupted:
            native._debug_encoded_profile_context_cancel_v1(
                slices=records,
                ontology_identity_context=context,
                cancel_at_checkpoint=checkpoint,
            )
        assert interrupted.value.code == "REASONER_INTERRUPTED"
        assert interrupted.value.context == {
            "checkpoint": str(checkpoint),
            "phase": expected_phase,
        }
        assert (
            native._encoded_profile_slices_manifest_v1(
                slices=records,
                ontology_identity_context=context,
            )
            == baseline
        )


def test_profile_origin_context_decode_cancellation_is_transactional() -> None:
    snapshot = pyowl_core.load_snapshot(functional(*_invalid_body()), options=OPTIONS)
    records = (_slice_record(snapshot),)
    identity_context = _ontology_identity_context(snapshot)
    origin_context = _profile_origin_context(snapshot)
    baseline = native._encoded_profile_slices_manifest_v1(
        slices=records,
        ontology_identity_context=identity_context,
        origin_context=origin_context,
    )
    expected_phases = ["profile-origin-context-preflight"]
    for _provenance, document_keys in origin_context[1]:
        expected_phases.append("profile-origin-context-row")
        expected_phases.extend("profile-origin-context-document" for _key in document_keys)
    expected_phases.append("profile-origin-context-complete")
    first_checkpoint = len(identity_context[1]) + 3

    for checkpoint, expected_phase in enumerate(expected_phases, start=first_checkpoint):
        with pytest.raises(ReasonerInterruptedError) as interrupted:
            native._debug_encoded_profile_context_cancel_v1(
                slices=records,
                ontology_identity_context=identity_context,
                origin_context=origin_context,
                cancel_at_checkpoint=checkpoint,
            )
        assert interrupted.value.code == "REASONER_INTERRUPTED"
        assert interrupted.value.context == {
            "checkpoint": str(checkpoint),
            "phase": expected_phase,
        }
        assert (
            native._encoded_profile_slices_manifest_v1(
                slices=records,
                ontology_identity_context=identity_context,
                origin_context=origin_context,
            )
            == baseline
        )


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
