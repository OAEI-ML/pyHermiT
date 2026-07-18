from __future__ import annotations

import hashlib

import pyowl_core.model as owl
import pytest
from pyowl_core import (
    BackendPreference,
    DetectionBasis,
    DigestKind,
    DocumentFormat,
    DocumentProvenance,
    ImportPolicy,
    LoadOptions,
    OntologyDocument,
    OntologyID,
    load_snapshot,
)
from pyowl_core.extensions import swrl

from pyhermit.config import UnsupportedDatatypePolicy
from pyhermit.exceptions import OntologyProfileError
from pyhermit.profile import validate_owl2_dl_view

OPTIONS = LoadOptions(imports=ImportPolicy.IGNORE, backend=BackendPreference.PYTHON)


def view(*body: str):  # type: ignore[no-untyped-def]
    source = (
        "Prefix(:=<urn:test#>) Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>) "
        "Ontology(<urn:test:profile> " + " ".join(body) + ")"
    ).encode()
    return load_snapshot(source, options=OPTIONS)


def codes(*body: str) -> set[str]:
    return {issue.rule_id for issue in validate_owl2_dl_view(view(*body)).issues}


def test_valid_complete_closure_has_stable_provenance_and_role_model() -> None:
    ontology = view(
        "Declaration(Class(:A))",
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
        "Declaration(ObjectProperty(:r))",
        "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)",
        "HasKey(:A (:r) ())",
    )

    report = validate_owl2_dl_view(ontology)

    assert report.conforms
    assert report.complete
    assert report.axioms_checked == 6
    assert report.role_graph.regular
    assert not report.role_graph.is_simple(owl.ObjectProperty(owl.IRI("urn:test#r")))
    assert report.issues == ()


def test_typing_reserved_vocabulary_and_missing_declarations_are_reported() -> None:
    found = codes(
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:p))",
        "SubClassOf(:Missing owl:Thing)",
        "Declaration(Class(owl:real))",
    )

    assert found >= {
        "OWL2DL_PROPERTY_PUNNING",
        "OWL2DL_MISSING_DECLARATION",
        "OWL2DL_BUILTIN_ENTITY_KIND",
    }


@pytest.mark.parametrize(
    ("identity", "expected"),
    (
        (
            "<http://www.w3.org/2002/07/owl#ontology>",
            "OWL2DL_RESERVED_ONTOLOGY_IRI",
        ),
        (
            "<urn:test:ontology> <http://www.w3.org/2000/01/rdf-schema#version>",
            "OWL2DL_RESERVED_VERSION_IRI",
        ),
    ),
)
def test_reserved_ontology_and_version_iris_use_shared_identity_provenance(
    identity: str,
    expected: str,
) -> None:
    ontology = load_snapshot(
        f"Ontology({identity} Declaration(Class(<urn:test#A>)))".encode(),
        options=OPTIONS,
    )

    issue = next(
        item for item in validate_owl2_dl_view(ontology).issues if item.rule_id == expected
    )

    assert issue.constructor == "OntologyID"
    assert issue.document_keys


def test_role_regularity_and_simplicity_share_the_role_preprocessor() -> None:
    found = codes(
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:left))",
        "Declaration(ObjectProperty(:right))",
        "SubObjectPropertyOf(ObjectPropertyChain(:left :p :right) :p)",
        "FunctionalObjectProperty(:p)",
    )

    assert "RIA_NON_REGULAR_RECURSION" in found
    assert "OWL2DL_NON_SIMPLE_PROPERTY" in found


def test_top_data_property_is_allowed_only_in_the_super_property_position() -> None:
    valid = validate_owl2_dl_view(
        view(
            "Declaration(DataProperty(:p))",
            "SubDataPropertyOf(:p owl:topDataProperty)",
        )
    )
    invalid = codes("FunctionalDataProperty(owl:topDataProperty)")

    assert valid.conforms
    assert "OWL2DL_TOP_DATA_PROPERTY_POSITION" in invalid


def test_datatype_definitions_literals_facets_and_opaque_policy_are_validated() -> None:
    valid = validate_owl2_dl_view(
        view(
            "Declaration(Datatype(:small))",
            "Declaration(DataProperty(:value))",
            "DatatypeDefinition(:small DatatypeRestriction(xsd:integer "
            'xsd:minInclusive "0"^^xsd:integer))',
            "DataPropertyRange(:value :small)",
        )
    )
    malformed = codes(
        "Declaration(DataProperty(:value))",
        'DataPropertyAssertion(:value :i "nope"^^xsd:integer)',
    )
    custom_literal = codes(
        "Declaration(Datatype(:custom))",
        "Declaration(DataProperty(:value))",
        "DatatypeDefinition(:custom xsd:string)",
        'DataPropertyAssertion(:value :i "x"^^:custom)',
    )
    unknown_view = view(
        "Declaration(Datatype(:unknown))",
        "Declaration(DataProperty(:value))",
        "DataPropertyRange(:value :unknown)",
    )
    opaque = validate_owl2_dl_view(
        unknown_view,
        unsupported_datatypes=UnsupportedDatatypePolicy.IGNORE_WITH_WARNING,
    )

    assert valid.conforms
    assert "INVALID_LITERAL" in malformed
    assert "CUSTOM_DATATYPE_LITERAL" in custom_literal
    with pytest.raises(OntologyProfileError):
        validate_owl2_dl_view(unknown_view).raise_for_errors()
    assert opaque.conforms
    assert {issue.rule_id for issue in opaque.issues} == {"UNSUPPORTED_DATATYPE_OPAQUE"}


def test_datatype_definition_uniqueness_acyclicity_and_builtin_rules_are_reported() -> None:
    duplicate = codes(
        "Declaration(Datatype(:custom))",
        "DatatypeDefinition(:custom xsd:string)",
        "DatatypeDefinition(:custom xsd:integer)",
    )
    recursive = codes(
        "Declaration(Datatype(:first))",
        "Declaration(Datatype(:second))",
        "DatatypeDefinition(:first :second)",
        "DatatypeDefinition(:second :first)",
    )
    builtin = codes("DatatypeDefinition(xsd:string xsd:integer)")
    illegal_facet = codes(
        "Declaration(DataProperty(:value))",
        "DataPropertyRange(:value DatatypeRestriction(xsd:boolean "
        'xsd:minInclusive "false"^^xsd:boolean))',
    )

    assert "DUPLICATE_DATATYPE_DEFINITION" in duplicate
    assert "RECURSIVE_DATATYPE_DEFINITION" in recursive
    assert "BUILTIN_DATATYPE_REDEFINITION" in builtin
    assert "ILLEGAL_DATATYPE_FACET" in illegal_facet


def test_only_unary_data_ranges_are_supported_by_owl2() -> None:
    assert "OWL2_DATA_RANGE_ARITY" in codes(
        "Declaration(Class(:A))",
        "Declaration(DataProperty(:p))",
        "Declaration(DataProperty(:q))",
        "SubClassOf(:A DataSomeValuesFrom(:p :q xsd:string))",
    )


def test_anonymous_individual_positions_and_forest_conditions_are_enforced() -> None:
    forbidden = codes("SameIndividual(_:a :named)")
    cycle = codes(
        "Declaration(ObjectProperty(:p))",
        "ObjectPropertyAssertion(:p _:a _:b)",
        "ObjectPropertyAssertion(:p _:b _:c)",
        "ObjectPropertyAssertion(:p _:c _:a)",
    )
    parallel = codes(
        "Declaration(ObjectProperty(:p))",
        "Declaration(ObjectProperty(:q))",
        "ObjectPropertyAssertion(:p _:a _:b)",
        "ObjectPropertyAssertion(:q _:b _:a)",
    )
    no_root = codes(
        "Declaration(ObjectProperty(:p))",
        "ObjectPropertyAssertion(:p _:a :first)",
        "ObjectPropertyAssertion(:p :second _:a)",
    )

    assert "OWL2DL_ANONYMOUS_AXIOM_POSITION" in forbidden
    assert "OWL2DL_ANONYMOUS_GRAPH_CYCLE" in cycle
    assert "OWL2DL_ANONYMOUS_PARALLEL_EDGE" in parallel
    assert "OWL2DL_ANONYMOUS_TREE_ROOT" in no_root


@pytest.mark.parametrize(
    "axiom",
    (
        "DifferentIndividuals(_:a :named)",
        "NegativeObjectPropertyAssertion(:p _:a :named)",
        'NegativeDataPropertyAssertion(:value _:a "x")',
        "ClassAssertion(ObjectOneOf(_:a) :named)",
        "ClassAssertion(ObjectHasValue(:p _:a) :named)",
    ),
)
def test_every_forbidden_anonymous_position_is_rejected(axiom: str) -> None:
    declarations = (
        "Declaration(ObjectProperty(:p))",
        "Declaration(DataProperty(:value))",
    )
    found = codes(*declarations, axiom)

    assert found & {
        "OWL2DL_ANONYMOUS_AXIOM_POSITION",
        "OWL2DL_ANONYMOUS_CLASS_EXPRESSION",
    }


def test_extension_components_are_rejected_with_origin_provenance() -> None:
    class_a = owl.Class(owl.IRI("urn:test#A"))
    variable = swrl.Variable(owl.IRI("urn:test#x"))
    rule = swrl.SWRLRule(
        owl.CanonicalSet((swrl.ClassAtom(class_a, variable),)),
        owl.CanonicalSet((swrl.ClassAtom(class_a, variable),)),
    )
    provenance = DocumentProvenance(
        hashlib.sha256(b"profile-extension").digest(),
        DigestKind.EXACT_BYTES,
        0,
        0,
        None,
        None,
        DocumentFormat.FUNCTIONAL,
        DetectionBasis.EXPLICIT,
    )
    document = OntologyDocument(
        OntologyID(owl.IRI("urn:test:extension")),
        None,
        (),
        owl.CanonicalSet(),
        owl.CanonicalSet((owl.Declaration(class_a),)),
        owl.CanonicalSet((rule,)),
        provenance,
    )
    ontology = load_snapshot(document, options=OPTIONS)

    report = validate_owl2_dl_view(ontology)
    issue = next(item for item in report.issues if item.rule_id == "OWL2DL_EXTENSION_COMPONENT")

    assert not report.conforms
    assert report.extensions_checked == 1
    assert issue.document_keys
    assert issue.provenance_sha256 == hashlib.sha256(rule.canonical_bytes()).hexdigest()
