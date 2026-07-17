from __future__ import annotations

import hashlib
import inspect
import os
import subprocess
import sys
from dataclasses import replace

import pyowl_core.model as owl
import pytest

from pyhermit.exceptions import ReasonerInterruptedError, ResourceLimitError
from pyhermit.normalize import (
    AXIOM_HANDLER_TABLE,
    DefinitionRecord,
    NormalizationLimits,
    NormalizedFamily,
    NormalizedRecord,
    Polarity,
    UnknownAxiomError,
    normalize_axioms,
)

FINGERPRINT = "12" * 32

_IDENTITY_FAMILIES: dict[type[owl.AxiomNode], NormalizedFamily] = {
    owl.SubObjectPropertyOf: NormalizedFamily.OBJECT_PROPERTY,
    owl.EquivalentObjectProperties: NormalizedFamily.OBJECT_PROPERTY,
    owl.DisjointObjectProperties: NormalizedFamily.OBJECT_PROPERTY,
    owl.InverseObjectProperties: NormalizedFamily.OBJECT_PROPERTY,
    owl.ObjectPropertyDomain: NormalizedFamily.OBJECT_PROPERTY,
    owl.ObjectPropertyRange: NormalizedFamily.OBJECT_PROPERTY,
    owl.FunctionalObjectProperty: NormalizedFamily.OBJECT_PROPERTY,
    owl.InverseFunctionalObjectProperty: NormalizedFamily.OBJECT_PROPERTY,
    owl.ReflexiveObjectProperty: NormalizedFamily.OBJECT_PROPERTY,
    owl.IrreflexiveObjectProperty: NormalizedFamily.OBJECT_PROPERTY,
    owl.SymmetricObjectProperty: NormalizedFamily.OBJECT_PROPERTY,
    owl.AsymmetricObjectProperty: NormalizedFamily.OBJECT_PROPERTY,
    owl.TransitiveObjectProperty: NormalizedFamily.OBJECT_PROPERTY,
    owl.SubDataPropertyOf: NormalizedFamily.DATA_PROPERTY,
    owl.EquivalentDataProperties: NormalizedFamily.DATA_PROPERTY,
    owl.DisjointDataProperties: NormalizedFamily.DATA_PROPERTY,
    owl.DataPropertyDomain: NormalizedFamily.DATA_PROPERTY,
    owl.DataPropertyRange: NormalizedFamily.DATA_PROPERTY,
    owl.FunctionalDataProperty: NormalizedFamily.DATA_PROPERTY,
    owl.DatatypeDefinition: NormalizedFamily.DATATYPE,
    owl.HasKey: NormalizedFamily.KEY,
    owl.SameIndividual: NormalizedFamily.ASSERTION,
    owl.DifferentIndividuals: NormalizedFamily.ASSERTION,
    owl.ObjectPropertyAssertion: NormalizedFamily.ASSERTION,
    owl.NegativeObjectPropertyAssertion: NormalizedFamily.ASSERTION,
    owl.DataPropertyAssertion: NormalizedFamily.ASSERTION,
    owl.NegativeDataPropertyAssertion: NormalizedFamily.ASSERTION,
}


def _all_axioms() -> tuple[owl.AxiomNode, ...]:
    first = owl.Class(owl.IRI("urn:test:First"))
    second = owl.Class(owl.IRI("urn:test:Second"))
    third = owl.Class(owl.IRI("urn:test:Third"))
    prop = owl.ObjectProperty(owl.IRI("urn:test:prop"))
    other_prop = owl.ObjectProperty(owl.IRI("urn:test:otherProp"))
    data = owl.DataProperty(owl.IRI("urn:test:data"))
    other_data = owl.DataProperty(owl.IRI("urn:test:otherData"))
    datatype = owl.Datatype(owl.IRI("urn:test:datatype"))
    first_individual = owl.NamedIndividual(owl.IRI("urn:test:firstIndividual"))
    second_individual = owl.NamedIndividual(owl.IRI("urn:test:secondIndividual"))
    literal = owl.Literal("value", owl.XSD_STRING)
    annotation = owl.AnnotationProperty(owl.IRI("urn:test:annotation"))
    class_set = owl.CanonicalSet((first, second, third))
    object_set = owl.CanonicalSet((prop, other_prop))
    data_set = owl.CanonicalSet((data, other_data))
    individual_set = owl.CanonicalSet((first_individual, second_individual))
    return (
        owl.Declaration(first),
        owl.SubClassOf(first, owl.ObjectSomeValuesFrom(prop, second)),
        owl.EquivalentClasses(class_set),
        owl.DisjointClasses(class_set),
        owl.DisjointUnion(first, owl.CanonicalSet((second, third))),
        owl.SubObjectPropertyOf(prop, other_prop),
        owl.EquivalentObjectProperties(object_set),
        owl.DisjointObjectProperties(object_set),
        owl.InverseObjectProperties(prop, other_prop),
        owl.ObjectPropertyDomain(prop, first),
        owl.ObjectPropertyRange(prop, second),
        owl.FunctionalObjectProperty(prop),
        owl.InverseFunctionalObjectProperty(prop),
        owl.ReflexiveObjectProperty(prop),
        owl.IrreflexiveObjectProperty(prop),
        owl.SymmetricObjectProperty(prop),
        owl.AsymmetricObjectProperty(prop),
        owl.TransitiveObjectProperty(prop),
        owl.SubDataPropertyOf(data, other_data),
        owl.EquivalentDataProperties(data_set),
        owl.DisjointDataProperties(data_set),
        owl.DataPropertyDomain(data, first),
        owl.DataPropertyRange(data, owl.XSD_STRING),
        owl.FunctionalDataProperty(data),
        owl.DatatypeDefinition(datatype, owl.XSD_STRING),
        owl.HasKey(first, owl.CanonicalSet((prop,)), owl.CanonicalSet((data,))),
        owl.SameIndividual(individual_set),
        owl.DifferentIndividuals(individual_set),
        owl.ClassAssertion(owl.ObjectSomeValuesFrom(prop, second), first_individual),
        owl.ObjectPropertyAssertion(prop, first_individual, second_individual),
        owl.NegativeObjectPropertyAssertion(prop, first_individual, second_individual),
        owl.DataPropertyAssertion(data, first_individual, literal),
        owl.NegativeDataPropertyAssertion(data, first_individual, literal),
        owl.AnnotationAssertion(annotation, first.iri, literal),
        owl.SubAnnotationPropertyOf(annotation, annotation),
        owl.AnnotationPropertyDomain(annotation, owl.IRI("urn:test:domain")),
        owl.AnnotationPropertyRange(annotation, owl.IRI("urn:test:range")),
    )


def test_handler_table_is_exact_and_every_axiom_constructor_executes() -> None:
    values = _all_axioms()
    assert set(AXIOM_HANDLER_TABLE) == set(owl.AXIOM_TYPES)
    assert {type(value) for value in values} == set(owl.AXIOM_TYPES)
    result = normalize_axioms(values, logical_fingerprint=FINGERPRINT)
    assert result.source_axiom_count == len(values)
    assert result.ignored_nonlogical_axiom_count == 5
    assert result.records
    assert result.definitions


@pytest.mark.parametrize(
    ("axiom", "family"),
    tuple(
        (axiom, _IDENTITY_FAMILIES[type(axiom)])
        for axiom in _all_axioms()
        if type(axiom) in _IDENTITY_FAMILIES
    ),
    ids=lambda value: type(value).__name__ if isinstance(value, owl.AxiomNode) else None,
)
def test_semantics_preserving_handlers_retain_exact_atomic_axioms(
    axiom: owl.AxiomNode,
    family: NormalizedFamily,
) -> None:
    result = normalize_axioms((axiom,), logical_fingerprint=FINGERPRINT)
    assert not result.definitions
    assert len(result.records) == 1
    record = result.records[0]
    assert record.family is family
    assert record.statement == axiom
    assert record.provenance_sha256 == (hashlib.sha256(axiom.canonical_bytes()).hexdigest(),)


def test_role_chain_builtins_and_axiom_annotations_preserve_logical_shape() -> None:
    first = owl.ObjectProperty(owl.IRI("urn:test:chain-first"))
    second = owl.ObjectProperty(owl.IRI("urn:test:chain-second"))
    target = owl.ObjectProperty(owl.IRI("urn:test:chain-target"))
    chain = owl.ObjectPropertyChain((first, owl.ObjectInverseOf(second)))
    annotation = owl.Annotation(
        owl.AnnotationProperty(owl.IRI("urn:test:chain-note")),
        owl.Literal("source-only", owl.XSD_STRING),
    )
    annotated = owl.SubObjectPropertyOf(
        chain,
        target,
        owl.CanonicalSet((annotation,)),
    )
    values = (
        annotated,
        owl.SubObjectPropertyOf(owl.OWL_BOTTOM_OBJECT_PROPERTY, first),
        owl.SubObjectPropertyOf(first, owl.OWL_TOP_OBJECT_PROPERTY),
    )
    result = normalize_axioms(values, logical_fingerprint=FINGERPRINT)
    assert {value.statement for value in result.records} == {
        owl.SubObjectPropertyOf(chain, target),
        values[1],
        values[2],
    }
    chain_record = next(
        value
        for value in result.records
        if isinstance(value.statement, owl.SubObjectPropertyOf)
        and isinstance(value.statement.sub_property, owl.ObjectPropertyChain)
    )
    assert chain_record.provenance_sha256 == (
        hashlib.sha256(annotated.canonical_bytes()).hexdigest(),
    )


def test_inverse_object_assertions_are_canonical_forward_facts() -> None:
    prop = owl.ObjectProperty(owl.IRI("urn:test:prop"))
    source = owl.NamedIndividual(owl.IRI("urn:test:source"))
    target = owl.NamedIndividual(owl.IRI("urn:test:target"))
    result = normalize_axioms(
        (owl.ObjectPropertyAssertion(owl.ObjectInverseOf(prop), source, target),),
        logical_fingerprint=FINGERPRINT,
    )
    assertion = result.records[0].statement
    assert assertion == owl.ObjectPropertyAssertion(prop, target, source)


def test_normalized_records_reject_wrong_families_and_annotations() -> None:
    first = owl.Class(owl.IRI("urn:test:record-first"))
    second = owl.Class(owl.IRI("urn:test:record-second"))
    provenance = ("ab" * 32,)
    statement = owl.SubClassOf(first, second)
    with pytest.raises(TypeError, match="invalid for assertion records"):
        NormalizedRecord(NormalizedFamily.ASSERTION, statement, provenance)

    annotation = owl.Annotation(
        owl.AnnotationProperty(owl.IRI("urn:test:record-note")),
        owl.Literal("note", owl.XSD_STRING),
    )
    annotated = owl.SubClassOf(
        first,
        second,
        owl.CanonicalSet((annotation,)),
    )
    with pytest.raises(ValueError, match="must not retain annotations"):
        NormalizedRecord(NormalizedFamily.CLASS, annotated, provenance)
    assert "_canonical_statement" not in inspect.signature(NormalizedRecord).parameters

    with pytest.raises(TypeError, match="core structural value"):
        DefinitionRecord(first, "not-an-expression", Polarity.POSITIVE, provenance)
    assert "_canonical_expression" not in inspect.signature(DefinitionRecord).parameters


def test_definition_symbols_and_generated_records_are_relationally_validated() -> None:
    first = owl.Class(owl.IRI("urn:test:definition-first"))
    second = owl.Class(owl.IRI("urn:test:definition-second"))
    third = owl.Class(owl.IRI("urn:test:definition-third"))
    expression = owl.ObjectUnionOf(owl.CanonicalSet((second, third)))
    provenance = ("ab" * 32,)
    with pytest.raises(ValueError, match="generated definition namespace"):
        DefinitionRecord(first, expression, Polarity.POSITIVE, provenance)

    normalized = normalize_axioms(
        (owl.SubClassOf(first, expression),),
        logical_fingerprint=FINGERPRINT,
    )
    assert normalized.definitions
    with pytest.raises(ValueError, match="wrong namespace"):
        replace(normalized, logical_fingerprint="fe" * 32)
    with pytest.raises(ValueError, match="missing its generated record"):
        replace(
            normalized,
            records=tuple(record for record in normalized.records if not record.generated),
        )
    with pytest.raises(ValueError, match="directional definition owner"):
        replace(normalized, definitions=())


def test_nary_disjointness_remains_linear_and_handles_simplified_duplicates() -> None:
    classes = tuple(owl.Class(owl.IRI(f"urn:test:disjoint-{index}")) for index in range(100))
    result = normalize_axioms(
        (owl.DisjointClasses(owl.CanonicalSet(classes)),),
        logical_fingerprint=FINGERPRINT,
    )
    assert len(result.records) == 1
    assert not result.definitions
    assert result.records[0].statement == owl.DisjointClasses(owl.CanonicalSet(classes))

    first, second = classes[:2]
    equivalent_first = owl.ObjectUnionOf(owl.CanonicalSet((first, owl.OWL_NOTHING)))
    duplicate = normalize_axioms(
        (owl.DisjointClasses(owl.CanonicalSet((first, equivalent_first, second))),),
        logical_fingerprint=FINGERPRINT,
    )
    assert tuple(value.statement for value in duplicate.records) == (
        owl.SubClassOf(first, owl.OWL_NOTHING),
    )

    with_top = normalize_axioms(
        (owl.DisjointClasses(owl.CanonicalSet((owl.OWL_THING, first, second))),),
        logical_fingerprint=FINGERPRINT,
    )
    assert {value.statement for value in with_top.records} == {
        owl.SubClassOf(first, owl.OWL_NOTHING),
        owl.SubClassOf(second, owl.OWL_NOTHING),
    }


def test_unknown_axiom_fails_before_structural_serialization() -> None:
    class FutureAxiom(owl.AxiomNode):
        pass

    with pytest.raises(UnknownAxiomError, match="FutureAxiom"):
        normalize_axioms((FutureAxiom(),), logical_fingerprint=FINGERPRINT)


def test_limits_and_cancellation_fail_closed() -> None:
    first = owl.Class(owl.IRI("urn:test:First"))
    second = owl.Class(owl.IRI("urn:test:Second"))
    axioms = (owl.SubClassOf(first, second), owl.SubClassOf(second, first))
    with pytest.raises(ResourceLimitError, match="source axiom limit"):
        normalize_axioms(
            axioms,
            logical_fingerprint=FINGERPRINT,
            limits=NormalizationLimits(max_source_axioms=1),
        )
    with pytest.raises(ReasonerInterruptedError, match="cancelled"):
        normalize_axioms(
            axioms,
            logical_fingerprint=FINGERPRINT,
            cancelled=lambda: True,
        )


def test_every_normalization_limit_uses_the_public_resource_taxonomy() -> None:
    first = owl.Class(owl.IRI("urn:test:limit-first"))
    second = owl.Class(owl.IRI("urn:test:limit-second"))
    third = owl.Class(owl.IRI("urn:test:limit-third"))
    fourth = owl.Class(owl.IRI("urn:test:limit-fourth"))

    with pytest.raises(ResourceLimitError) as record_error:
        normalize_axioms(
            (owl.SubClassOf(first, second), owl.SubClassOf(second, third)),
            logical_fingerprint=FINGERPRINT,
            limits=NormalizationLimits(max_records=1),
        )
    assert record_error.value.limit == "max_records"
    assert record_error.value.observed == 2
    assert record_error.value.allowed == 1

    with pytest.raises(ResourceLimitError) as definition_error:
        normalize_axioms(
            (
                owl.SubClassOf(
                    owl.ObjectIntersectionOf(owl.CanonicalSet((first, second))),
                    owl.ObjectUnionOf(owl.CanonicalSet((third, fourth))),
                ),
            ),
            logical_fingerprint=FINGERPRINT,
            limits=NormalizationLimits(max_definitions=1),
        )
    assert definition_error.value.limit == "max_definitions"
    assert definition_error.value.observed == 2
    assert definition_error.value.allowed == 1

    role = owl.ObjectProperty(owl.IRI("urn:test:limit-role"))
    nested: owl.ClassExpression = second
    for _ in range(20):
        nested = owl.ObjectSomeValuesFrom(role, nested)
    with pytest.raises(ResourceLimitError) as depth_error:
        normalize_axioms(
            (owl.SubClassOf(first, nested),),
            logical_fingerprint=FINGERPRINT,
            limits=NormalizationLimits(max_expression_depth=5),
        )
    assert depth_error.value.limit == "max_expression_depth"
    assert depth_error.value.observed == 6
    assert depth_error.value.allowed == 5

    with pytest.raises(ValueError, match="core limit 512"):
        NormalizationLimits(max_expression_depth=513)


def test_deep_definition_introduction_is_iterative_and_resource_bounded() -> None:
    first = owl.Class(owl.IRI("urn:test:deep-first"))
    role = owl.ObjectProperty(owl.IRI("urn:test:deep-role"))
    expression: owl.ClassExpression = first
    for _ in range(400):
        expression = owl.ObjectSomeValuesFrom(role, expression)
    result = normalize_axioms(
        (owl.SubClassOf(first, expression),),
        logical_fingerprint=FINGERPRINT,
        limits=NormalizationLimits(max_expression_depth=512),
    )
    assert len(result.definitions) == 400
    assert len(result.records) == 401


def test_normalize_import_has_no_tableau_java_or_native_side_effects() -> None:
    script = """
import sys
import pyhermit.normalize
for name in ('jpype', 'pyhermit._native', 'pyhermit.backends.python.state'):
    assert name not in sys.modules, name
"""
    subprocess.run(
        [sys.executable, "-c", script],
        check=True,
        env=dict(os.environ),
    )
