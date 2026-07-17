from __future__ import annotations

import itertools
import json

import pyowl_core.model as owl
import pytest

from pyhermit.exceptions import ResourceLimitError
from pyhermit.normalize import (
    DataRangeInclusion,
    NormalizationLimits,
    NormalizedOntology,
    NormalizedQuery,
    Polarity,
    normalize_axioms,
    normalize_query,
)

FINGERPRINT = "34" * 32


def cls(name: str) -> owl.Class:
    return owl.Class(owl.IRI(f"urn:test:{name}"))


def test_content_addressed_definitions_are_polarity_aware_and_reused() -> None:
    first, second, target = cls("first"), cls("second"), cls("target")
    expression = owl.ObjectUnionOf(owl.CanonicalSet((first, second)))
    axioms = (
        owl.SubClassOf(expression, target),
        owl.SubClassOf(target, expression),
        owl.ClassAssertion(expression, owl.NamedIndividual(owl.IRI("urn:test:i"))),
    )
    result = normalize_axioms(axioms, logical_fingerprint=FINGERPRINT)
    matching = [value for value in result.definitions if value.expression == expression]
    assert {value.polarity for value in matching} == {
        Polarity.POSITIVE,
        Polarity.NEGATIVE,
    }
    assert len({value.symbol for value in matching}) == 2
    assert all(value.symbol not in result.declared_entities for value in matching)
    assert all(
        value.symbol.iri.value.startswith("urn:pyhermit:generated:v1:") for value in matching
    )


def test_domain_range_key_and_assertion_atomization_use_sound_directions() -> None:
    first, second = cls("direction-first"), cls("direction-second")
    role = owl.ObjectProperty(owl.IRI("urn:test:direction-role"))
    data_property = owl.DataProperty(owl.IRI("urn:test:direction-data"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:direction-individual"))
    union = owl.ObjectUnionOf(owl.CanonicalSet((first, second)))
    intersection = owl.ObjectIntersectionOf(owl.CanonicalSet((first, second)))

    for axiom, expression_field in (
        (owl.ObjectPropertyDomain(role, union), "domain"),
        (owl.ObjectPropertyRange(role, union), "range"),
        (owl.DataPropertyDomain(data_property, union), "domain"),
    ):
        result = normalize_axioms(
            (axiom,),
            logical_fingerprint=FINGERPRINT,
        )
        definition = result.definitions[0]
        assert definition.polarity is Polarity.POSITIVE
        assert owl.SubClassOf(definition.symbol, union) in {
            value.statement for value in result.records
        }
        principal = next(value.statement for value in result.records if not value.generated)
        assert getattr(principal, expression_field) == definition.symbol

    data_first = owl.DataOneOf(owl.CanonicalSet((owl.Literal("first", owl.XSD_STRING),)))
    data_second = owl.DataOneOf(owl.CanonicalSet((owl.Literal("second", owl.XSD_STRING),)))
    data_union = owl.DataUnionOf(owl.CanonicalSet((data_first, data_second)))
    data_range_result = normalize_axioms(
        (owl.DataPropertyRange(data_property, data_union),),
        logical_fingerprint=FINGERPRINT,
    )
    data_definition = data_range_result.definitions[0]
    assert data_definition.polarity is Polarity.POSITIVE
    assert DataRangeInclusion(data_definition.symbol, data_union) in {
        value.statement for value in data_range_result.records
    }
    range_record = next(
        value.statement for value in data_range_result.records if not value.generated
    )
    assert isinstance(range_record, owl.DataPropertyRange)
    assert range_record.range == data_definition.symbol

    key_result = normalize_axioms(
        (
            owl.HasKey(
                intersection,
                owl.CanonicalSet((role,)),
                owl.CanonicalSet((data_property,)),
            ),
        ),
        logical_fingerprint=FINGERPRINT,
    )
    key_definition = key_result.definitions[0]
    assert key_definition.polarity is Polarity.NEGATIVE
    assert owl.SubClassOf(intersection, key_definition.symbol) in {
        value.statement for value in key_result.records
    }
    key_record = next(
        value.statement for value in key_result.records if isinstance(value.statement, owl.HasKey)
    )
    assert isinstance(key_record, owl.HasKey)
    assert key_record.class_expression == key_definition.symbol

    assertion_result = normalize_axioms(
        (owl.ClassAssertion(union, individual),),
        logical_fingerprint=FINGERPRINT,
    )
    assertion_definition = assertion_result.definitions[0]
    assert assertion_definition.polarity is Polarity.POSITIVE
    assert owl.SubClassOf(assertion_definition.symbol, union) in {
        value.statement for value in assertion_result.records
    }
    assertion = next(
        value.statement
        for value in assertion_result.records
        if isinstance(value.statement, owl.ClassAssertion)
    )
    assert isinstance(assertion, owl.ClassAssertion)
    assert assertion.class_expression == assertion_definition.symbol

    custom_datatype = owl.Datatype(owl.IRI("urn:test:direction-datatype"))
    complemented_union = owl.DataComplementOf(data_union)
    datatype_result = normalize_axioms(
        (owl.DatatypeDefinition(custom_datatype, complemented_union),),
        logical_fingerprint=FINGERPRINT,
    )
    datatype_statement = datatype_result.records[0].statement
    assert isinstance(datatype_statement, owl.DatatypeDefinition)
    assert datatype_statement.data_range == owl.DataIntersectionOf(
        owl.CanonicalSet(
            (
                owl.DataComplementOf(data_first),
                owl.DataComplementOf(data_second),
            )
        )
    )


def test_semantic_digest_excludes_provenance_and_diagnostic_metadata() -> None:
    first, second = cls("digest-first"), cls("digest-second")
    annotation_property = owl.AnnotationProperty(owl.IRI("urn:test:note"))
    annotation = owl.Annotation(
        annotation_property,
        owl.Literal("diagnostic only", owl.XSD_STRING),
    )
    plain = normalize_axioms(
        (owl.SubClassOf(first, second),),
        logical_fingerprint=FINGERPRINT,
    )
    annotated = normalize_axioms(
        (
            owl.SubClassOf(
                first,
                second,
                owl.CanonicalSet((annotation,)),
            ),
        ),
        logical_fingerprint=FINGERPRINT,
    )
    assert plain.canonical_snapshot() != annotated.canonical_snapshot()
    assert plain.semantic_snapshot() == annotated.semantic_snapshot()
    assert plain.digest == annotated.digest


def test_generated_definition_collision_with_declared_signature_fails_closed() -> None:
    first, second, target = cls("collision-first"), cls("collision-second"), cls("target")
    source = owl.SubClassOf(
        owl.ObjectIntersectionOf(owl.CanonicalSet((first, second))),
        target,
    )
    initial = normalize_axioms((source,), logical_fingerprint=FINGERPRINT)
    generated = initial.definitions[0].symbol
    with pytest.raises(ValueError, match="collides with the source signature"):
        normalize_axioms(
            (owl.Declaration(generated), source),
            logical_fingerprint=FINGERPRINT,
        )

    used_without_declaration = owl.SubClassOf(generated, target)
    with pytest.raises(ValueError, match="collides with the source signature"):
        normalize_axioms(
            (used_without_declaration, source),
            logical_fingerprint=FINGERPRINT,
        )


def test_axiom_permutations_produce_byte_identical_normalization() -> None:
    first, second, third = cls("first"), cls("second"), cls("third")
    role = owl.ObjectProperty(owl.IRI("urn:test:role"))
    axioms = (
        owl.SubClassOf(first, owl.ObjectSomeValuesFrom(role, second)),
        owl.SubClassOf(owl.ObjectIntersectionOf(owl.CanonicalSet((first, second))), third),
        owl.EquivalentClasses(owl.CanonicalSet((second, third))),
    )
    snapshots = {
        normalize_axioms(order, logical_fingerprint=FINGERPRINT).canonical_snapshot()
        for order in itertools.permutations(axioms)
    }
    assert len(snapshots) == 1


def test_nested_shared_definition_provenance_is_order_independent() -> None:
    first, second, third, left, right = (
        cls("shared-first"),
        cls("shared-second"),
        cls("shared-third"),
        cls("shared-left"),
        cls("shared-right"),
    )
    role = owl.ObjectProperty(owl.IRI("urn:test:shared-role"))
    nested = owl.ObjectIntersectionOf(owl.CanonicalSet((second, third)))
    shared = owl.ObjectUnionOf(owl.CanonicalSet((first, nested)))
    axioms = (
        owl.SubClassOf(left, shared),
        owl.SubClassOf(
            right,
            owl.ObjectSomeValuesFrom(
                role,
                owl.ObjectSomeValuesFrom(role, shared),
            ),
        ),
    )
    results = [
        normalize_axioms(order, logical_fingerprint=FINGERPRINT)
        for order in itertools.permutations(axioms)
    ]
    assert len({value.canonical_snapshot() for value in results}) == 1
    nested_definition = next(
        value for value in results[0].definitions if value.expression == nested
    )
    assert len(nested_definition.provenance_sha256) == 2


def test_query_symbols_are_isolated_and_permanent_state_is_unchanged() -> None:
    first, second, third = cls("first"), cls("second"), cls("third")
    permanent = normalize_axioms(
        (owl.SubClassOf(first, owl.ObjectUnionOf(owl.CanonicalSet((second, third)))),),
        logical_fingerprint=FINGERPRINT,
    )
    before = permanent.canonical_snapshot()
    query_axiom = owl.SubClassOf(
        owl.ObjectIntersectionOf(owl.CanonicalSet((first, second))),
        third,
    )
    first_query = normalize_query(permanent, (query_axiom,))
    second_query = normalize_query(permanent, (query_axiom,))
    assert first_query.canonical_snapshot() == second_query.canonical_snapshot()
    assert permanent.canonical_snapshot() == before
    assert all(value.query_local for value in first_query.definitions)
    permanent_symbols = {value.symbol for value in permanent.definitions}
    assert permanent_symbols.isdisjoint(value.symbol for value in first_query.definitions)
    assert not first_query.requires_rebuild

    role = owl.ObjectProperty(owl.IRI("urn:test:role"))
    role_query = normalize_query(
        permanent,
        (owl.TransitiveObjectProperty(role),),
    )
    assert role_query.requires_rebuild


def test_query_identity_is_set_semantic_and_ignores_duplicate_axioms() -> None:
    first, second, third = cls("query-first"), cls("query-second"), cls("query-third")
    permanent = normalize_axioms(
        (owl.SubClassOf(first, second),),
        logical_fingerprint=FINGERPRINT,
    )
    query_axiom = owl.SubClassOf(
        owl.ObjectIntersectionOf(owl.CanonicalSet((first, second))),
        third,
    )
    once = normalize_query(permanent, (query_axiom,))
    repeated = normalize_query(permanent, (query_axiom, query_axiom))
    assert once.query_hash == repeated.query_hash
    assert once.semantic_snapshot() == repeated.semantic_snapshot()
    assert once.digest == repeated.digest
    assert once.canonical_snapshot() != repeated.canonical_snapshot()

    annotation = owl.Annotation(
        owl.AnnotationProperty(owl.IRI("urn:test:query-note")),
        owl.Literal("diagnostic", owl.XSD_STRING),
    )
    annotated_axiom = owl.SubClassOf(
        query_axiom.sub_class,
        query_axiom.super_class,
        owl.CanonicalSet((annotation,)),
    )
    annotated = normalize_query(permanent, (annotated_axiom,))
    assert once.query_hash == annotated.query_hash
    assert once.semantic_snapshot() == annotated.semantic_snapshot()
    assert once.digest == annotated.digest
    assert once.canonical_snapshot() != annotated.canonical_snapshot()


def test_query_rebuild_classifier_is_conservative_for_strategy_features() -> None:
    first, second, third = cls("feature-first"), cls("feature-second"), cls("feature-third")
    role = owl.ObjectProperty(owl.IRI("urn:test:feature-role"))
    permanent = normalize_axioms(
        (owl.SubClassOf(first, second),),
        logical_fingerprint=FINGERPRINT,
    )
    safe_horn = owl.SubClassOf(
        owl.ObjectIntersectionOf(owl.CanonicalSet((first, second))),
        third,
    )
    disjunctive = owl.SubClassOf(
        first,
        owl.ObjectUnionOf(owl.CanonicalSet((second, third))),
    )
    number_restriction = owl.SubClassOf(
        first,
        owl.ObjectMinCardinality(2, role, second),
    )
    non_horn_assertion = owl.ClassAssertion(
        owl.ObjectUnionOf(owl.CanonicalSet((second, third))),
        owl.NamedIndividual(owl.IRI("urn:test:feature-individual")),
    )
    assert not normalize_query(permanent, (safe_horn,)).requires_rebuild
    for query_axiom in (disjunctive, number_restriction, non_horn_assertion):
        assert normalize_query(permanent, (query_axiom,)).requires_rebuild


def test_normalized_ontology_and_query_canonical_json_round_trip() -> None:
    first, second, third = cls("round-first"), cls("round-second"), cls("round-third")
    permanent = normalize_axioms(
        (
            owl.Declaration(first),
            owl.SubClassOf(
                owl.ObjectIntersectionOf(owl.CanonicalSet((first, second))),
                third,
            ),
        ),
        logical_fingerprint=FINGERPRINT,
    )
    restored = NormalizedOntology.from_canonical_snapshot(permanent.canonical_snapshot())
    assert restored == permanent
    assert restored.canonical_snapshot() == permanent.canonical_snapshot()

    query = normalize_query(
        permanent,
        (
            owl.SubClassOf(
                first,
                owl.ObjectUnionOf(owl.CanonicalSet((second, third))),
            ),
        ),
    )
    restored_query = NormalizedQuery.from_canonical_snapshot(query.canonical_snapshot())
    assert restored_query == query
    assert restored_query.canonical_snapshot() == query.canonical_snapshot()

    payload = json.loads(query.canonical_snapshot())
    payload["records"].reverse()
    with pytest.raises(ValueError, match="query records must be in canonical order"):
        NormalizedQuery.from_canonical_snapshot(json.dumps(payload))


def _evaluate(
    expression: owl.ClassExpression,
    valuation: dict[owl.Class, bool],
) -> bool:
    if isinstance(expression, owl.Class):
        if expression.iri.value == owl.OWL_THING.iri.value:
            return True
        if expression.iri.value == owl.OWL_NOTHING.iri.value:
            return False
        return valuation[expression]
    if isinstance(expression, owl.ObjectComplementOf):
        return not _evaluate(expression.operand, valuation)
    if isinstance(expression, owl.ObjectIntersectionOf):
        return all(_evaluate(item, valuation) for item in expression.operands)
    if isinstance(expression, owl.ObjectUnionOf):
        return any(_evaluate(item, valuation) for item in expression.operands)
    raise AssertionError(f"non-propositional expression in oracle: {expression!r}")


def _subclass_holds(axiom: owl.SubClassOf, valuation: dict[owl.Class, bool]) -> bool:
    return not _evaluate(axiom.sub_class, valuation) or _evaluate(
        axiom.super_class,
        valuation,
    )


def _class_axiom_holds(
    axiom: owl.AxiomNode,
    valuation: dict[owl.Class, bool],
) -> bool:
    if isinstance(axiom, owl.SubClassOf):
        return _subclass_holds(axiom, valuation)
    if isinstance(axiom, owl.EquivalentClasses):
        values = {_evaluate(expression, valuation) for expression in axiom.expressions}
        return len(values) == 1
    if isinstance(axiom, owl.DisjointClasses):
        return sum(_evaluate(expression, valuation) for expression in axiom.expressions) <= 1
    if isinstance(axiom, owl.DisjointUnion):
        members = tuple(_evaluate(expression, valuation) for expression in axiom.expressions)
        return _evaluate(axiom.defined_class, valuation) == any(members) and sum(members) <= 1
    if isinstance(axiom, owl.ClassAssertion):
        return _evaluate(axiom.class_expression, valuation)
    raise AssertionError(f"unsupported class oracle axiom: {axiom!r}")


def _assert_equisatisfiable(
    source: owl.AxiomNode,
    base_classes: tuple[owl.Class, ...],
) -> None:
    normalized = normalize_axioms((source,), logical_fingerprint=FINGERPRINT)
    statements = tuple(
        value.statement
        for value in normalized.records
        if isinstance(
            value.statement,
            (owl.SubClassOf, owl.DisjointClasses, owl.ClassAssertion),
        )
    )
    generated = tuple(
        value.symbol for value in normalized.definitions if isinstance(value.symbol, owl.Class)
    )
    for base_bits in itertools.product((False, True), repeat=len(base_classes)):
        base = dict(zip(base_classes, base_bits, strict=True))
        source_holds = _class_axiom_holds(source, base)
        normalized_has_extension = False
        for generated_bits in itertools.product((False, True), repeat=len(generated)):
            valuation = dict(base)
            valuation.update(dict(zip(generated, generated_bits, strict=True)))
            if all(_class_axiom_holds(statement, valuation) for statement in statements):
                normalized_has_extension = True
                break
        assert source_holds == normalized_has_extension


def test_polarity_translation_is_equisatisfiable_in_exhaustive_finite_oracle() -> None:
    first, second, third = cls("first"), cls("second"), cls("third")
    source = owl.SubClassOf(
        owl.ObjectIntersectionOf(
            owl.CanonicalSet(
                (
                    first,
                    owl.ObjectUnionOf(owl.CanonicalSet((second, third))),
                )
            )
        ),
        owl.ObjectUnionOf(
            owl.CanonicalSet(
                (
                    owl.ObjectIntersectionOf(owl.CanonicalSet((first, second))),
                    third,
                )
            )
        ),
    )
    _assert_equisatisfiable(source, (first, second, third))


def test_generated_propositional_cases_match_exhaustive_assignment_oracle() -> None:
    first, second, third = cls("gen-first"), cls("gen-second"), cls("gen-third")
    union = owl.ObjectUnionOf(owl.CanonicalSet((first, second)))
    intersection = owl.ObjectIntersectionOf(owl.CanonicalSet((second, third)))
    nested_union = owl.ObjectUnionOf(owl.CanonicalSet((first, intersection)))
    nested_intersection = owl.ObjectIntersectionOf(owl.CanonicalSet((union, third)))
    expressions: tuple[owl.ClassExpression, ...] = (
        first,
        owl.ObjectComplementOf(first),
        union,
        intersection,
        nested_union,
        nested_intersection,
        owl.ObjectComplementOf(nested_union),
        owl.ObjectComplementOf(nested_intersection),
    )
    for index in range(len(expressions)):
        source = owl.SubClassOf(
            expressions[index],
            expressions[(index * 3 + 1) % len(expressions)],
        )
        _assert_equisatisfiable(source, (first, second, third))


def test_all_transformed_class_axiom_families_match_finite_oracle() -> None:
    first, second, third, defined = (
        cls("family-first"),
        cls("family-second"),
        cls("family-third"),
        cls("family-defined"),
    )
    union = owl.ObjectUnionOf(owl.CanonicalSet((first, second)))
    intersection = owl.ObjectIntersectionOf(owl.CanonicalSet((second, third)))
    complement = owl.ObjectComplementOf(first)
    individual = owl.NamedIndividual(owl.IRI("urn:test:family-individual"))
    sources: tuple[owl.AxiomNode, ...] = (
        owl.EquivalentClasses(owl.CanonicalSet((union, intersection, complement))),
        owl.DisjointClasses(owl.CanonicalSet((union, intersection, complement))),
        owl.DisjointUnion(defined, owl.CanonicalSet((union, intersection))),
        owl.ClassAssertion(union, individual),
    )
    for source in sources:
        _assert_equisatisfiable(source, (first, second, third, defined))


def test_query_collection_enforces_limits_before_consuming_the_iterable() -> None:
    first, second = cls("query-limit-first"), cls("query-limit-second")
    axiom = owl.SubClassOf(first, second)
    permanent = normalize_axioms((axiom,), logical_fingerprint=FINGERPRINT)
    consumed = 0

    def values():
        nonlocal consumed
        for _ in range(100):
            consumed += 1
            yield axiom

    with pytest.raises(ResourceLimitError) as error:
        normalize_query(
            permanent,
            values(),
            limits=NormalizationLimits(max_source_axioms=1),
        )
    assert consumed == 2
    assert error.value.limit == "max_source_axioms"
    assert error.value.observed == 2
    assert error.value.allowed == 1
