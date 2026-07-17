from __future__ import annotations

import itertools
from dataclasses import dataclass

import pyowl_core.model as owl

from pyhermit.normalize import DataRangeInclusion, normalize_axioms

FINGERPRINT = "9a" * 32
OBJECT_DOMAIN = frozenset((0, 1))
DATA_DOMAIN = frozenset((0, 1))


@dataclass(frozen=True)
class Interpretation:
    classes: dict[owl.Class, frozenset[int]]
    roles: dict[owl.ObjectProperty, frozenset[tuple[int, int]]]
    data_roles: dict[owl.DataProperty, frozenset[tuple[int, int]]]
    individuals: dict[owl.Individual, int]
    literals: dict[bytes, int]
    datatypes: dict[owl.Datatype, frozenset[int]]


@dataclass(frozen=True)
class PreparedNormalization:
    class_symbols: tuple[owl.Class, ...]
    data_symbols: tuple[owl.Datatype, ...]
    statements: tuple[owl.AxiomNode | DataRangeInclusion, ...]


def _relation(
    property: owl.ObjectPropertyExpression,
    interpretation: Interpretation,
) -> frozenset[tuple[int, int]]:
    if isinstance(property, owl.ObjectProperty):
        return interpretation.roles.get(property, frozenset())
    return frozenset(
        (target, source)
        for source, target in interpretation.roles.get(property.property, frozenset())
    )


def _data_extension(
    data_range: owl.DataRange,
    interpretation: Interpretation,
) -> frozenset[int]:
    if isinstance(data_range, owl.Datatype):
        if data_range.iri.value == owl.RDFS_LITERAL.iri.value:
            return DATA_DOMAIN
        return interpretation.datatypes.get(data_range, DATA_DOMAIN)
    if isinstance(data_range, owl.DataOneOf):
        return frozenset(
            interpretation.literals[value.canonical_bytes()] for value in data_range.values
        )
    if isinstance(data_range, owl.DataUnionOf):
        return frozenset().union(
            *(_data_extension(value, interpretation) for value in data_range.operands)
        )
    if isinstance(data_range, owl.DataIntersectionOf):
        result = DATA_DOMAIN
        for value in data_range.operands:
            result = result.intersection(_data_extension(value, interpretation))
        return frozenset(result)
    if isinstance(data_range, owl.DataComplementOf):
        return DATA_DOMAIN.difference(_data_extension(data_range.operand, interpretation))
    raise AssertionError(f"unsupported bounded data range {data_range!r}")


def _class_extension(
    expression: owl.ClassExpression,
    interpretation: Interpretation,
) -> frozenset[int]:
    if isinstance(expression, owl.Class):
        if expression.iri.value == owl.OWL_THING.iri.value:
            return OBJECT_DOMAIN
        if expression.iri.value == owl.OWL_NOTHING.iri.value:
            return frozenset()
        return interpretation.classes.get(expression, frozenset())
    if isinstance(expression, owl.ObjectIntersectionOf):
        result = OBJECT_DOMAIN
        for operand in expression.operands:
            result = result.intersection(_class_extension(operand, interpretation))
        return frozenset(result)
    if isinstance(expression, owl.ObjectUnionOf):
        return frozenset().union(
            *(_class_extension(operand, interpretation) for operand in expression.operands)
        )
    if isinstance(expression, owl.ObjectComplementOf):
        return OBJECT_DOMAIN.difference(_class_extension(expression.operand, interpretation))
    if isinstance(expression, owl.ObjectOneOf):
        return frozenset(interpretation.individuals[value] for value in expression.individuals)
    if isinstance(expression, (owl.ObjectSomeValuesFrom, owl.ObjectAllValuesFrom)):
        relation = _relation(expression.property, interpretation)
        filler = _class_extension(expression.filler, interpretation)
        if isinstance(expression, owl.ObjectSomeValuesFrom):
            return frozenset(
                source
                for source in OBJECT_DOMAIN
                if any((source, target) in relation for target in filler)
            )
        return frozenset(
            source
            for source in OBJECT_DOMAIN
            if all(target in filler for left, target in relation if left == source)
        )
    if isinstance(expression, owl.ObjectHasValue):
        target = interpretation.individuals[expression.value]
        relation = _relation(expression.property, interpretation)
        return frozenset(source for source in OBJECT_DOMAIN if (source, target) in relation)
    if isinstance(expression, owl.ObjectHasSelf):
        relation = _relation(expression.property, interpretation)
        return frozenset(value for value in OBJECT_DOMAIN if (value, value) in relation)
    if isinstance(
        expression,
        (
            owl.ObjectMinCardinality,
            owl.ObjectMaxCardinality,
            owl.ObjectExactCardinality,
        ),
    ):
        relation = _relation(expression.property, interpretation)
        filler = _class_extension(expression.filler, interpretation)
        counts = {
            source: sum((source, target) in relation for target in filler)
            for source in OBJECT_DOMAIN
        }
        if isinstance(expression, owl.ObjectMinCardinality):
            return frozenset(
                source for source, count in counts.items() if count >= expression.cardinality
            )
        if isinstance(expression, owl.ObjectMaxCardinality):
            return frozenset(
                source for source, count in counts.items() if count <= expression.cardinality
            )
        return frozenset(
            source for source, count in counts.items() if count == expression.cardinality
        )
    if isinstance(expression, (owl.DataSomeValuesFrom, owl.DataAllValuesFrom)):
        assert len(expression.properties) == 1
        relation = interpretation.data_roles.get(expression.properties[0], frozenset())
        filler = _data_extension(expression.filler, interpretation)
        if isinstance(expression, owl.DataSomeValuesFrom):
            return frozenset(
                source
                for source in OBJECT_DOMAIN
                if any((source, target) in relation for target in filler)
            )
        return frozenset(
            source
            for source in OBJECT_DOMAIN
            if all(target in filler for left, target in relation if left == source)
        )
    if isinstance(expression, owl.DataHasValue):
        target = interpretation.literals[expression.value.canonical_bytes()]
        relation = interpretation.data_roles.get(expression.property, frozenset())
        return frozenset(source for source in OBJECT_DOMAIN if (source, target) in relation)
    if isinstance(
        expression,
        (owl.DataMinCardinality, owl.DataMaxCardinality, owl.DataExactCardinality),
    ):
        relation = interpretation.data_roles.get(expression.property, frozenset())
        filler = _data_extension(expression.filler, interpretation)
        counts = {
            source: sum((source, target) in relation for target in filler)
            for source in OBJECT_DOMAIN
        }
        if isinstance(expression, owl.DataMinCardinality):
            return frozenset(
                source for source, count in counts.items() if count >= expression.cardinality
            )
        if isinstance(expression, owl.DataMaxCardinality):
            return frozenset(
                source for source, count in counts.items() if count <= expression.cardinality
            )
        return frozenset(
            source for source, count in counts.items() if count == expression.cardinality
        )
    raise AssertionError(f"unsupported bounded class expression {expression!r}")


def _statement_holds(
    statement: owl.AxiomNode | DataRangeInclusion,
    interpretation: Interpretation,
) -> bool:
    if isinstance(statement, owl.SubClassOf):
        return _class_extension(statement.sub_class, interpretation) <= _class_extension(
            statement.super_class,
            interpretation,
        )
    if isinstance(statement, owl.DisjointClasses):
        extensions = [_class_extension(value, interpretation) for value in statement.expressions]
        return all(
            not extensions[left].intersection(extensions[right])
            for left in range(len(extensions))
            for right in range(left + 1, len(extensions))
        )
    if isinstance(statement, DataRangeInclusion):
        return _data_extension(statement.sub_range, interpretation) <= _data_extension(
            statement.super_range,
            interpretation,
        )
    if isinstance(statement, owl.ClassAssertion):
        return interpretation.individuals[statement.individual] in _class_extension(
            statement.class_expression, interpretation
        )
    if isinstance(statement, owl.HasKey):
        members = _class_extension(statement.class_expression, interpretation)
        for left in OBJECT_DOMAIN:
            for right in OBJECT_DOMAIN:
                if left >= right or left not in members or right not in members:
                    continue
                object_match = all(
                    any(
                        (left, target) in _relation(property, interpretation)
                        and (right, target) in _relation(property, interpretation)
                        for target in OBJECT_DOMAIN
                    )
                    for property in statement.object_properties
                )
                data_match = all(
                    any(
                        (left, target) in interpretation.data_roles.get(property, frozenset())
                        and (right, target) in interpretation.data_roles.get(property, frozenset())
                        for target in DATA_DOMAIN
                    )
                    for property in statement.data_properties
                )
                if object_match and data_match:
                    return False
        return True
    raise AssertionError(f"unsupported bounded normalized statement {statement!r}")


def _bits(size: int, mask: int) -> frozenset[int]:
    return frozenset(index for index in range(size) if mask & (1 << index))


def _pairs(mask: int) -> frozenset[tuple[int, int]]:
    return frozenset(
        (source, target)
        for source in range(2)
        for target in range(2)
        if mask & (1 << (source * 2 + target))
    )


def _prepare(source: owl.AxiomNode) -> PreparedNormalization:
    normalized = normalize_axioms((source,), logical_fingerprint=FINGERPRINT)
    class_symbols = tuple(
        value.symbol for value in normalized.definitions if isinstance(value.symbol, owl.Class)
    )
    data_symbols = tuple(
        value.symbol for value in normalized.definitions if isinstance(value.symbol, owl.Datatype)
    )
    statements = tuple(value.statement for value in normalized.records)
    return PreparedNormalization(class_symbols, data_symbols, statements)


def _has_generated_extension(
    prepared: PreparedNormalization,
    interpretation: Interpretation,
) -> bool:
    bit_count = 2 * (len(prepared.class_symbols) + len(prepared.data_symbols))
    for assignment in range(1 << bit_count):
        offset = 0
        classes = dict(interpretation.classes)
        for symbol in prepared.class_symbols:
            classes[symbol] = _bits(2, assignment >> offset)
            offset += 2
        datatypes = dict(interpretation.datatypes)
        for symbol in prepared.data_symbols:
            datatypes[symbol] = _bits(2, assignment >> offset)
            offset += 2
        candidate = Interpretation(
            classes,
            interpretation.roles,
            interpretation.data_roles,
            interpretation.individuals,
            interpretation.literals,
            datatypes,
        )
        if all(_statement_holds(statement, candidate) for statement in prepared.statements):
            return True
    return False


def test_object_restrictions_nominals_and_cardinalities_match_finite_models() -> None:
    concept = owl.Class(owl.IRI("urn:test:oracle:C"))
    role = owl.ObjectProperty(owl.IRI("urn:test:oracle:r"))
    first = owl.NamedIndividual(owl.IRI("urn:test:oracle:i"))
    second = owl.NamedIndividual(owl.IRI("urn:test:oracle:j"))
    expressions: tuple[owl.ClassExpression, ...] = (
        owl.ObjectSomeValuesFrom(role, concept),
        owl.ObjectSomeValuesFrom(owl.ObjectInverseOf(role), concept),
        owl.ObjectAllValuesFrom(role, concept),
        owl.ObjectHasValue(role, first),
        owl.ObjectHasSelf(role),
        owl.ObjectOneOf(owl.CanonicalSet((first, second))),
        owl.ObjectMinCardinality(1, role, concept),
        owl.ObjectMaxCardinality(1, role, concept),
        owl.ObjectExactCardinality(1, role, concept),
    )
    for expression_index, expression in enumerate(expressions):
        source = (
            owl.SubClassOf(concept, expression)
            if expression_index % 2
            else owl.SubClassOf(expression, concept)
        )
        prepared = _prepare(source)
        for class_mask, role_mask in itertools.product(range(4), range(16)):
            interpretation = Interpretation(
                {concept: _bits(2, class_mask)},
                {role: _pairs(role_mask)},
                {},
                {first: 0, second: 1},
                {},
                {},
            )
            assert _statement_holds(source, interpretation) == _has_generated_extension(
                prepared,
                interpretation,
            )


def test_data_restrictions_and_cardinalities_match_finite_models() -> None:
    concept = owl.Class(owl.IRI("urn:test:oracle:DataC"))
    property = owl.DataProperty(owl.IRI("urn:test:oracle:data"))
    first = owl.Literal("first", owl.XSD_STRING)
    second = owl.Literal("second", owl.XSD_STRING)
    one_first = owl.DataOneOf(owl.CanonicalSet((first,)))
    either = owl.DataUnionOf(
        owl.CanonicalSet((one_first, owl.DataOneOf(owl.CanonicalSet((second,)))))
    )
    expressions: tuple[owl.ClassExpression, ...] = (
        owl.DataSomeValuesFrom((property,), either),
        owl.DataAllValuesFrom((property,), one_first),
        owl.DataHasValue(property, first),
        owl.DataMinCardinality(1, property, either),
        owl.DataMaxCardinality(1, property, either),
        owl.DataExactCardinality(1, property, either),
    )
    literal_ids = {first.canonical_bytes(): 0, second.canonical_bytes(): 1}
    for expression_index, expression in enumerate(expressions):
        source = (
            owl.SubClassOf(concept, expression)
            if expression_index % 2
            else owl.SubClassOf(expression, concept)
        )
        prepared = _prepare(source)
        for class_mask, relation_mask in itertools.product(range(4), range(16)):
            interpretation = Interpretation(
                {concept: _bits(2, class_mask)},
                {},
                {property: _pairs(relation_mask)},
                {},
                literal_ids,
                {},
            )
            assert _statement_holds(source, interpretation) == _has_generated_extension(
                prepared,
                interpretation,
            )


def test_complex_assertions_and_keys_match_finite_models() -> None:
    first = owl.Class(owl.IRI("urn:test:oracle:KeyA"))
    second = owl.Class(owl.IRI("urn:test:oracle:KeyB"))
    role = owl.ObjectProperty(owl.IRI("urn:test:oracle:key-role"))
    data_property = owl.DataProperty(owl.IRI("urn:test:oracle:key-data"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:oracle:key-i"))
    other = owl.NamedIndividual(owl.IRI("urn:test:oracle:key-j"))
    intersection = owl.ObjectIntersectionOf(owl.CanonicalSet((first, second)))
    assertion = owl.ClassAssertion(
        owl.ObjectUnionOf(owl.CanonicalSet((first, second))),
        individual,
    )
    key = owl.HasKey(
        intersection,
        owl.CanonicalSet((role,)),
        owl.CanonicalSet((data_property,)),
    )
    for source in (assertion, key):
        prepared = _prepare(source)
        for first_mask, second_mask, role_mask, data_mask in itertools.product(
            range(4),
            range(4),
            range(16),
            range(16),
        ):
            interpretation = Interpretation(
                {first: _bits(2, first_mask), second: _bits(2, second_mask)},
                {role: _pairs(role_mask)},
                {data_property: _pairs(data_mask)},
                {individual: 0, other: 1},
                {},
                {},
            )
            assert _statement_holds(source, interpretation) == _has_generated_extension(
                prepared,
                interpretation,
            )
