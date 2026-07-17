from __future__ import annotations

from dataclasses import replace
from pathlib import Path
from typing import Any

import pyowl_core.model as owl
from pyowl_core import BackendPreference, LoadOptions, logical_fingerprint, parse_document

from pyhermit.normalize import ExpressionNormalizer, NormalizedFamily, normalize_axioms
from tools.reference.canonicalize import canonical_normalization
from tools.reference.goldens import load_jsonl

ROOT = Path(__file__).parents[3]
REFERENCE = ROOT / "tests/data/reference"


def _entity(value: owl.Entity) -> dict[str, str]:
    kinds: tuple[tuple[type[owl.Entity], str], ...] = (
        (owl.Class, "class"),
        (owl.Datatype, "datatype"),
        (owl.ObjectProperty, "object_property"),
        (owl.DataProperty, "data_property"),
        (owl.NamedIndividual, "named_individual"),
    )
    for constructor, kind in kinds:
        if isinstance(value, constructor):
            return {"kind": kind, "iri": value.iri.value}
    raise AssertionError(f"atomic parity fixture contains unsupported entity {value!r}")


def _literal(value: owl.Literal) -> dict[str, str]:
    return {
        "kind": "literal",
        "lexical": value.lexical_form,
        "datatype": value.datatype.iri.value,
        "language": value.language or "",
    }


def _object_property(value: owl.ObjectPropertyExpression) -> dict[str, Any]:
    if isinstance(value, owl.ObjectProperty):
        return _entity(value)
    if isinstance(value, owl.ObjectInverseOf):
        return {
            "kind": "inverse_object_property",
            "property": _entity(value.property),
        }
    raise AssertionError(f"unsupported object property expression {value!r}")


def _data_range(value: owl.DataRange) -> dict[str, Any]:
    if isinstance(value, owl.Datatype):
        return _entity(value)
    if isinstance(value, owl.DataOneOf):
        return {"kind": "data_one_of", "values": [_literal(item) for item in value.values]}
    if isinstance(value, owl.DataUnionOf):
        return {
            "kind": "data_union",
            "operands": [_data_range(item) for item in value.operands],
        }
    if isinstance(value, owl.DataIntersectionOf):
        return {
            "kind": "data_intersection",
            "operands": [_data_range(item) for item in value.operands],
        }
    if isinstance(value, owl.DataComplementOf):
        return {"kind": "data_complement", "operand": _data_range(value.operand)}
    raise AssertionError(f"unsupported broad-fixture data range {value!r}")


def _class_expression(value: owl.ClassExpression) -> dict[str, Any]:
    if isinstance(value, owl.Class):
        return _entity(value)
    if isinstance(value, owl.ObjectIntersectionOf):
        return {
            "kind": "object_intersection",
            "operands": [_class_expression(item) for item in value.operands],
        }
    if isinstance(value, owl.ObjectUnionOf):
        return {
            "kind": "object_union",
            "operands": [_class_expression(item) for item in value.operands],
        }
    if isinstance(value, owl.ObjectComplementOf):
        return {
            "kind": "object_complement",
            "operand": _class_expression(value.operand),
        }
    if isinstance(value, owl.ObjectSomeValuesFrom):
        return {
            "kind": "object_some",
            "property": _object_property(value.property),
            "filler": _class_expression(value.filler),
        }
    if isinstance(value, owl.DataSomeValuesFrom):
        assert len(value.properties) == 1
        return {
            "kind": "data_some",
            "property": _entity(value.properties[0]),
            "filler": _data_range(value.filler),
        }
    raise AssertionError(f"unsupported broad-fixture class expression {value!r}")


def _fact(statement: owl.AxiomNode) -> dict[str, Any]:
    if isinstance(statement, owl.ClassAssertion):
        assert isinstance(statement.individual, owl.NamedIndividual)
        return {
            "kind": "class_assertion",
            "class_expression": _class_expression(statement.class_expression),
            "individual": _entity(statement.individual),
        }
    if isinstance(statement, owl.ObjectPropertyAssertion):
        assert isinstance(statement.property, owl.ObjectProperty)
        assert isinstance(statement.source, owl.NamedIndividual)
        assert isinstance(statement.target, owl.NamedIndividual)
        return {
            "kind": "object_property_assertion",
            "property": _entity(statement.property),
            "subject": _entity(statement.source),
            "object": _entity(statement.target),
        }
    if isinstance(statement, owl.NegativeObjectPropertyAssertion):
        assert isinstance(statement.property, owl.ObjectProperty)
        assert isinstance(statement.source, owl.NamedIndividual)
        assert isinstance(statement.target, owl.NamedIndividual)
        return {
            "kind": "negative_object_property_assertion",
            "property": _entity(statement.property),
            "subject": _entity(statement.source),
            "object": _entity(statement.target),
        }
    if isinstance(statement, owl.DataPropertyAssertion):
        assert isinstance(statement.source, owl.NamedIndividual)
        return {
            "kind": "data_property_assertion",
            "property": _entity(statement.property),
            "subject": _entity(statement.source),
            "value": _literal(statement.value),
        }
    if isinstance(statement, owl.NegativeDataPropertyAssertion):
        assert isinstance(statement.source, owl.NamedIndividual)
        return {
            "kind": "negative_data_property_assertion",
            "property": _entity(statement.property),
            "subject": _entity(statement.source),
            "value": _literal(statement.value),
        }
    if isinstance(statement, owl.SameIndividual):
        return {
            "kind": "same_individual",
            "individuals": [_entity(value) for value in statement.individuals],
        }
    if isinstance(statement, owl.DifferentIndividuals):
        return {
            "kind": "different_individuals",
            "individuals": [_entity(value) for value in statement.individuals],
        }
    raise AssertionError(f"atomic parity fixture contains unsupported fact {statement!r}")


def _empty_families() -> dict[str, list[Any]]:
    return {
        "asymmetric_object_properties": [],
        "complex_object_property_inclusions": [],
        "concept_inclusions": [],
        "data_property_inclusions": [],
        "data_range_inclusions": [],
        "defined_datatypes": [],
        "disjoint_data_properties": [],
        "disjoint_object_properties": [],
        "facts": [],
        "has_keys": [],
        "irreflexive_object_properties": [],
        "reflexive_object_properties": [],
        "simple_object_property_inclusions": [],
    }


def _class_disjuncts(value: owl.ClassExpression) -> list[dict[str, Any]]:
    if isinstance(value, owl.ObjectUnionOf):
        return [_class_expression(item) for item in value.operands]
    return [_class_expression(value)]


def _data_disjuncts(value: owl.DataRange) -> list[dict[str, Any]]:
    if isinstance(value, owl.DataUnionOf):
        return [_data_range(item) for item in value.operands]
    return [_data_range(value)]


def _source_holder_projection(axioms: tuple[owl.AxiomNode, ...]) -> dict[str, Any]:
    families = _empty_families()
    expressions = ExpressionNormalizer()
    for axiom in axioms:
        if isinstance(axiom, owl.Declaration):
            continue
        if isinstance(axiom, owl.SubClassOf):
            negative = expressions.class_nnf(axiom.sub_class, negated=True)
            positive = expressions.class_nnf(axiom.super_class)
            families["concept_inclusions"].append(
                [*_class_disjuncts(negative), *_class_disjuncts(positive)]
            )
        elif isinstance(axiom, owl.DatatypeDefinition):
            datatype = _entity(axiom.datatype)
            positive = expressions.data_nnf(axiom.data_range)
            families["defined_datatypes"].append(datatype)
            families["data_range_inclusions"].append(
                [
                    {
                        "kind": "data_complement",
                        "operand": datatype,
                    },
                    *_data_disjuncts(positive),
                ]
            )
            negative = expressions.data_nnf(axiom.data_range, negated=True)
            reverse_disjuncts = (
                tuple(negative.operands)
                if isinstance(negative, owl.DataIntersectionOf)
                else (negative,)
            )
            for disjunct in reverse_disjuncts:
                families["data_range_inclusions"].append([_data_range(disjunct), datatype])
        elif isinstance(axiom, owl.SubObjectPropertyOf):
            if isinstance(axiom.sub_property, owl.ObjectPropertyChain):
                families["complex_object_property_inclusions"].append(
                    {
                        "chain": [
                            _object_property(value) for value in axiom.sub_property.properties
                        ],
                        "super_property": _object_property(axiom.super_property),
                    }
                )
            else:
                families["simple_object_property_inclusions"].append(
                    [
                        _object_property(axiom.sub_property),
                        _object_property(axiom.super_property),
                    ]
                )
        elif isinstance(axiom, owl.DisjointObjectProperties):
            families["disjoint_object_properties"].append(
                [_object_property(value) for value in axiom.properties]
            )
        elif isinstance(axiom, owl.ReflexiveObjectProperty):
            families["reflexive_object_properties"].append(_object_property(axiom.property))
        elif isinstance(axiom, owl.IrreflexiveObjectProperty):
            families["irreflexive_object_properties"].append(_object_property(axiom.property))
        elif isinstance(axiom, owl.AsymmetricObjectProperty):
            families["asymmetric_object_properties"].append(_object_property(axiom.property))
        elif isinstance(axiom, owl.SubDataPropertyOf):
            families["data_property_inclusions"].append(
                [_entity(axiom.sub_property), _entity(axiom.super_property)]
            )
        elif isinstance(axiom, owl.DisjointDataProperties):
            families["disjoint_data_properties"].append(
                [_entity(value) for value in axiom.properties]
            )
        elif isinstance(axiom, owl.HasKey):
            families["has_keys"].append(
                {
                    "class_expression": _class_expression(
                        expressions.class_nnf(axiom.class_expression)
                    ),
                    "object_properties": [
                        _object_property(value) for value in axiom.object_properties
                    ],
                    "data_properties": [_entity(value) for value in axiom.data_properties],
                }
            )
        elif isinstance(
            axiom,
            (
                owl.ClassAssertion,
                owl.ObjectPropertyAssertion,
                owl.NegativeObjectPropertyAssertion,
                owl.DataPropertyAssertion,
                owl.NegativeDataPropertyAssertion,
                owl.SameIndividual,
                owl.DifferentIndividuals,
            ),
        ):
            families["facts"].append(_fact(axiom))
        else:
            raise AssertionError(f"broad fixture contains unsupported axiom {axiom!r}")
    return canonical_normalization({"kind": "raw_structural_normalization", "families": families})


def _private_key(value: Any, kind: str) -> tuple[str, str] | None:
    if (
        isinstance(value, dict)
        and value.get("kind") == kind
        and isinstance(value.get("private"), str)
    ):
        return kind, value["private"]
    return None


def _definition_operand(value: Any, kind: str) -> tuple[str, str] | None:
    if not isinstance(value, dict) or value.get("kind") != kind:
        return None
    return _private_key(
        value.get("operand"), "class" if kind == "object_complement" else "datatype"
    )


def _infer_java_definitions(
    families: dict[str, Any],
) -> tuple[dict[tuple[str, str], dict[str, Any]], dict[str, Any]]:
    mappings: dict[tuple[str, str], dict[str, Any]] = {}
    class_groups: dict[tuple[str, str], list[list[dict[str, Any]]]] = {}
    retained_concepts: list[list[dict[str, Any]]] = []
    for inclusion in families["concept_inclusions"]:
        owners = [_definition_operand(value, "object_complement") for value in inclusion]
        owner_keys = [value for value in owners if value is not None]
        if len(owner_keys) == 1:
            owner = owner_keys[0]
            remainder = [
                value
                for value in inclusion
                if _definition_operand(value, "object_complement") != owner
            ]
            class_groups.setdefault(owner, []).append(remainder)
        else:
            retained_concepts.append(inclusion)
    for owner, groups in class_groups.items():
        if len(groups) == 1:
            operands = groups[0]
            mappings[owner] = (
                operands[0]
                if len(operands) == 1
                else {"kind": "object_union", "operands": operands}
            )
        else:
            assert all(len(group) == 1 for group in groups)
            mappings[owner] = {
                "kind": "object_intersection",
                "operands": [group[0] for group in groups],
            }

    retained_data: list[list[dict[str, Any]]] = []
    for inclusion in families["data_range_inclusions"]:
        owners = [_definition_operand(value, "data_complement") for value in inclusion]
        owner_keys = [value for value in owners if value is not None]
        if len(owner_keys) == 1:
            owner = owner_keys[0]
            operands = [
                value
                for value in inclusion
                if _definition_operand(value, "data_complement") != owner
            ]
            mappings[owner] = (
                operands[0] if len(operands) == 1 else {"kind": "data_union", "operands": operands}
            )
        else:
            retained_data.append(inclusion)

    retained = dict(families)
    retained["concept_inclusions"] = retained_concepts
    retained["data_range_inclusions"] = retained_data
    return mappings, retained


def _substitute_private(
    value: Any,
    mappings: dict[tuple[str, str], dict[str, Any]],
) -> Any:
    if isinstance(value, dict):
        key = next(
            (
                candidate
                for kind in ("class", "datatype")
                if (candidate := _private_key(value, kind)) is not None
            ),
            None,
        )
        if key is not None:
            return _substitute_private(mappings[key], mappings)
        return {field: _substitute_private(item, mappings) for field, item in value.items()}
    if isinstance(value, list):
        return [_substitute_private(item, mappings) for item in value]
    return value


def _expanded_java_projection(value: dict[str, Any]) -> dict[str, Any]:
    mappings, retained = _infer_java_definitions(value["families"])
    assert set(mappings) == {
        ("class", "class:0"),
        ("class", "class:1"),
        ("datatype", "datatype:0"),
    }
    expanded = _substitute_private(retained, mappings)
    return canonical_normalization({"kind": "raw_structural_normalization", "families": expanded})


def _expand_python_value(
    value: Any,
    mappings: dict[bytes, owl.StructuralNode],
) -> Any:
    if isinstance(value, (owl.Class, owl.Datatype)):
        replacement = mappings.get(value.canonical_bytes())
        if replacement is not None:
            return _expand_python_value(replacement, mappings)
    if isinstance(value, owl.Entity):
        return value
    if isinstance(value, owl.CanonicalSet):
        return owl.CanonicalSet(_expand_python_value(item, mappings) for item in value)
    if isinstance(value, tuple):
        return tuple(_expand_python_value(item, mappings) for item in value)
    if isinstance(value, owl.StructuralNode):
        updates = {
            field: _expand_python_value(getattr(value, field), mappings)
            for field in owl.constructor_spec(value).fields
        }
        return replace(value, **updates)
    return value


def _expanded_python_axioms(
    normalized: Any,
) -> tuple[owl.AxiomNode, ...]:
    mappings = {
        definition.symbol.canonical_bytes(): definition.expression
        for definition in normalized.definitions
    }
    expanded: list[owl.AxiomNode] = []
    for record in normalized.records:
        if record.generated:
            continue
        assert isinstance(record.statement, owl.AxiomNode)
        statement = _expand_python_value(record.statement, mappings)
        assert isinstance(statement, owl.AxiomNode)
        expanded.append(statement)
    return tuple(sorted(expanded, key=lambda value: value.canonical_bytes()))


def _python_atomic_projection() -> dict[str, Any]:
    source = (REFERENCE / "inputs/normalization-atomic.ofn").read_bytes()
    document = parse_document(
        source,
        format="functional",
        options=LoadOptions(backend=BackendPreference.PYTHON),
    )
    fingerprint = logical_fingerprint(
        document.axioms,
        document.extension_components,
    ).hex
    normalized = normalize_axioms(
        document.axioms,
        logical_fingerprint=fingerprint,
    )
    assert not normalized.definitions

    families = _empty_families()
    for record in normalized.records:
        statement = record.statement
        if record.family is NormalizedFamily.CLASS:
            assert isinstance(statement, owl.SubClassOf)
            assert isinstance(statement.sub_class, owl.Class)
            assert isinstance(statement.super_class, owl.Class)
            families["concept_inclusions"].append(
                [
                    _entity(statement.super_class),
                    {
                        "kind": "object_complement",
                        "operand": _entity(statement.sub_class),
                    },
                ]
            )
        elif record.family is NormalizedFamily.OBJECT_PROPERTY:
            assert isinstance(statement, owl.SubObjectPropertyOf)
            assert isinstance(statement.sub_property, owl.ObjectProperty)
            assert isinstance(statement.super_property, owl.ObjectProperty)
            families["simple_object_property_inclusions"].append(
                [_entity(statement.sub_property), _entity(statement.super_property)]
            )
        elif record.family is NormalizedFamily.DATA_PROPERTY:
            assert isinstance(statement, owl.SubDataPropertyOf)
            families["data_property_inclusions"].append(
                [_entity(statement.sub_property), _entity(statement.super_property)]
            )
        elif record.family is NormalizedFamily.KEY:
            assert isinstance(statement, owl.HasKey)
            assert isinstance(statement.class_expression, owl.Class)
            families["has_keys"].append(
                {
                    "class_expression": _entity(statement.class_expression),
                    "object_properties": [_entity(value) for value in statement.object_properties],
                    "data_properties": [_entity(value) for value in statement.data_properties],
                }
            )
        elif record.family is NormalizedFamily.ASSERTION:
            assert isinstance(statement, owl.AxiomNode)
            families["facts"].append(_fact(statement))
        else:
            raise AssertionError(f"unexpected atomic parity record {record!r}")
    return canonical_normalization({"kind": "raw_structural_normalization", "families": families})


def test_atomic_normalization_matches_pinned_java_golden_exactly() -> None:
    records = {
        record["request_id"]: record for record in load_jsonl(REFERENCE / "goldens-v1.jsonl")
    }
    expected = records["atomic-structural-normalization"]["value"]
    assert _python_atomic_projection() == expected


def test_broad_java_and_python_normalization_share_one_semantic_projection() -> None:
    source = (REFERENCE / "inputs/normalization.ofn").read_bytes()
    document = parse_document(
        source,
        format="functional",
        options=LoadOptions(backend=BackendPreference.PYTHON),
    )
    source_axioms = tuple(
        sorted(
            (axiom for axiom in document.axioms if not isinstance(axiom, owl.Declaration)),
            key=lambda value: value.canonical_bytes(),
        )
    )
    source_projection = _source_holder_projection(tuple(document.axioms))
    records = {
        record["request_id"]: record for record in load_jsonl(REFERENCE / "goldens-v1.jsonl")
    }
    java_projection = _expanded_java_projection(records["structural-normalization"]["value"])
    assert java_projection == source_projection

    normalized = normalize_axioms(
        document.axioms,
        logical_fingerprint=logical_fingerprint(
            document.axioms,
            document.extension_components,
        ).hex,
    )
    assert _expanded_python_axioms(normalized) == source_axioms
