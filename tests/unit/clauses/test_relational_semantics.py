from __future__ import annotations

import itertools
from dataclasses import dataclass

import pyowl_core.model as owl
import pytest

from pyhermit.clauses import (
    Atom,
    ClauseProgram,
    DataConstant,
    IndividualTerm,
    Predicate,
    PredicateKind,
    SymbolKind,
    TermSort,
    Variable,
    compile_normalized,
)
from pyhermit.normalize import normalize_axioms

FINGERPRINT = "34" * 32
OBJECTS = (0, 1)


@dataclass(frozen=True)
class _Interpretation:
    classes: frozenset[tuple[str, int]]
    role: frozenset[tuple[int, int]]


def _class_holds(
    expression: owl.ClassExpression,
    value: int,
    interpretation: _Interpretation,
    role_iri: str,
) -> bool:
    if isinstance(expression, owl.Class):
        if expression.iri.value == owl.OWL_THING.iri.value:
            return True
        if expression.iri.value == owl.OWL_NOTHING.iri.value:
            return False
        return (expression.iri.value, value) in interpretation.classes
    if isinstance(expression, owl.ObjectComplementOf):
        return not _class_holds(expression.operand, value, interpretation, role_iri)
    if isinstance(expression, owl.ObjectIntersectionOf):
        return all(
            _class_holds(operand, value, interpretation, role_iri)
            for operand in expression.operands
        )
    if isinstance(expression, owl.ObjectUnionOf):
        return any(
            _class_holds(operand, value, interpretation, role_iri)
            for operand in expression.operands
        )
    if isinstance(expression, owl.ObjectSomeValuesFrom):
        return any(
            (value, target) in interpretation.role
            and _class_holds(expression.filler, target, interpretation, role_iri)
            for target in OBJECTS
        )
    if isinstance(expression, owl.ObjectAllValuesFrom):
        return all(
            (value, target) not in interpretation.role
            or _class_holds(expression.filler, target, interpretation, role_iri)
            for target in OBJECTS
        )
    if isinstance(expression, owl.ObjectMinCardinality):
        return (
            sum(
                (value, target) in interpretation.role
                and _class_holds(expression.filler, target, interpretation, role_iri)
                for target in OBJECTS
            )
            >= expression.cardinality
        )
    if isinstance(expression, owl.ObjectMaxCardinality):
        return (
            sum(
                (value, target) in interpretation.role
                and _class_holds(expression.filler, target, interpretation, role_iri)
                for target in OBJECTS
            )
            <= expression.cardinality
        )
    if isinstance(expression, owl.ObjectHasSelf):
        return (value, value) in interpretation.role
    raise AssertionError(f"unsupported finite source expression {expression!r}")


def _source_holds(
    axiom: owl.SubClassOf,
    interpretation: _Interpretation,
    role_iri: str,
) -> bool:
    return all(
        not _class_holds(axiom.sub_class, value, interpretation, role_iri)
        or _class_holds(axiom.super_class, value, interpretation, role_iri)
        for value in OBJECTS
    )


def _term_value(
    term: Variable | IndividualTerm | DataConstant,
    assignment: dict[tuple[int, TermSort], int],
) -> int:
    if isinstance(term, Variable):
        return assignment[(term.index, term.sort)]
    if isinstance(term, IndividualTerm):
        return term.individual_id
    return term.data_identity_id


def _role_holds(
    display: str,
    source: int,
    target: int,
    interpretation: _Interpretation,
    role_iri: str,
) -> bool:
    if display == f"object_property:{owl.OWL_TOP_OBJECT_PROPERTY.iri.value}":
        return True
    if display == f"object_property:{owl.OWL_BOTTOM_OBJECT_PROPERTY.iri.value}":
        return False
    if display == f"object_property:{role_iri}":
        return (source, target) in interpretation.role
    if display == f"inverse_object_property:{role_iri}":
        return (target, source) in interpretation.role
    raise AssertionError(f"unexpected role in bounded program: {display}")


def _atom_holds(
    program: ClauseProgram,
    atom: Atom,
    assignment: dict[tuple[int, TermSort], int],
    interpretation: _Interpretation,
    role_iri: str,
    internal_classes: frozenset[tuple[int, int]],
) -> bool:
    predicate = program.predicates.predicate(atom.predicate_id)
    arguments = tuple(_term_value(value, assignment) for value in atom.arguments)
    if predicate.kind in {PredicateKind.CONCEPT, PredicateKind.NEGATED_CONCEPT}:
        assert predicate.symbol_id is not None
        symbol = program.symbols.domain(SymbolKind.CLASS_EXPRESSION).value(predicate.symbol_id)
        display = symbol.display
        if symbol.generated:
            result = (predicate.symbol_id, arguments[0]) in internal_classes
        elif display == f"class:{owl.OWL_THING.iri.value}":
            result = True
        elif display == f"class:{owl.OWL_NOTHING.iri.value}":
            result = False
        else:
            result = (display.removeprefix("class:"), arguments[0]) in interpretation.classes
        return not result if predicate.kind is PredicateKind.NEGATED_CONCEPT else result
    if predicate.kind in {PredicateKind.OBJECT_ROLE, PredicateKind.NEGATED_OBJECT_ROLE}:
        assert predicate.role_id is not None
        display = program.symbols.domain(SymbolKind.OBJECT_ROLE).value(predicate.role_id).display
        result = _role_holds(display, arguments[0], arguments[1], interpretation, role_iri)
        return not result if predicate.kind is PredicateKind.NEGATED_OBJECT_ROLE else result
    if predicate.kind in {PredicateKind.DATA_ROLE, PredicateKind.NEGATED_DATA_ROLE}:
        assert predicate.role_id is not None
        display = program.symbols.domain(SymbolKind.DATA_PROPERTY).value(predicate.role_id).display
        if display == f"data_property:{owl.OWL_TOP_DATA_PROPERTY.iri.value}":
            result = True
        elif display == f"data_property:{owl.OWL_BOTTOM_DATA_PROPERTY.iri.value}":
            result = False
        else:
            raise AssertionError(f"unexpected data role in bounded program: {display}")
        return not result if predicate.kind is PredicateKind.NEGATED_DATA_ROLE else result
    if predicate.kind is PredicateKind.AT_LEAST_OBJECT:
        assert predicate.role_id is not None
        assert predicate.cardinality is not None
        assert predicate.filler_predicate_id is not None
        role_display = (
            program.symbols.domain(SymbolKind.OBJECT_ROLE).value(predicate.role_id).display
        )
        filler = program.predicates.predicate(predicate.filler_predicate_id)
        return (
            sum(
                _role_holds(
                    role_display,
                    arguments[0],
                    target,
                    interpretation,
                    role_iri,
                )
                and _unary_predicate_holds(
                    program,
                    filler,
                    target,
                    interpretation,
                    internal_classes,
                )
                for target in OBJECTS
            )
            >= predicate.cardinality
        )
    if predicate.kind is PredicateKind.ANNOTATED_EQUALITY:
        return arguments[0] == arguments[1]
    if predicate.kind is PredicateKind.EQUALITY:
        return arguments[0] == arguments[1]
    if predicate.kind is PredicateKind.INEQUALITY:
        return arguments[0] != arguments[1]
    if predicate.kind is PredicateKind.ORDERING_GUARD:
        return arguments[0] <= arguments[1]
    raise AssertionError(f"unexpected predicate in bounded program: {predicate.kind.value}")


def _unary_predicate_holds(
    program: ClauseProgram,
    predicate: Predicate,
    value: int,
    interpretation: _Interpretation,
    internal_classes: frozenset[tuple[int, int]],
) -> bool:
    assert predicate.symbol_id is not None
    symbol = program.symbols.domain(SymbolKind.CLASS_EXPRESSION).value(predicate.symbol_id)
    display = symbol.display
    if symbol.generated:
        result = (predicate.symbol_id, value) in internal_classes
    elif display == f"class:{owl.OWL_THING.iri.value}":
        result = True
    elif display == f"class:{owl.OWL_NOTHING.iri.value}":
        result = False
    else:
        result = (display.removeprefix("class:"), value) in interpretation.classes
    return not result if predicate.kind is PredicateKind.NEGATED_CONCEPT else result


def _program_holds(
    program: ClauseProgram,
    interpretation: _Interpretation,
    role_iri: str,
) -> bool:
    assert not program.positive_facts
    assert not program.negative_facts
    assert not program.ground_disjunctions
    generated_atoms = tuple(
        (value.identifier, domain_value)
        for value in program.symbols.domain(SymbolKind.CLASS_EXPRESSION).values
        if value.generated
        for domain_value in OBJECTS
    )
    return any(
        _clauses_hold(
            program,
            interpretation,
            role_iri,
            frozenset(atom for index, atom in enumerate(generated_atoms) if mask & (1 << index)),
        )
        for mask in range(1 << len(generated_atoms))
    )


def _clauses_hold(
    program: ClauseProgram,
    interpretation: _Interpretation,
    role_iri: str,
    internal_classes: frozenset[tuple[int, int]],
) -> bool:
    for clause in program.clauses:
        variables = tuple(
            sorted(
                {
                    (argument.index, argument.sort)
                    for atom in clause.body + clause.head
                    for argument in atom.arguments
                    if isinstance(argument, Variable)
                },
                key=lambda value: (value[0], value[1].value),
            )
        )
        for values in itertools.product(OBJECTS, repeat=len(variables)):
            assignment = dict(zip(variables, values, strict=True))
            if all(
                _atom_holds(
                    program,
                    atom,
                    assignment,
                    interpretation,
                    role_iri,
                    internal_classes,
                )
                for atom in clause.body
            ) and not any(
                _atom_holds(
                    program,
                    atom,
                    assignment,
                    interpretation,
                    role_iri,
                    internal_classes,
                )
                for atom in clause.head
            ):
                return False
    return True


def _interpretations(class_iris: tuple[str, ...]) -> tuple[_Interpretation, ...]:
    class_atoms = tuple(itertools.product(class_iris, OBJECTS))
    role_atoms = tuple(itertools.product(OBJECTS, repeat=2))
    return tuple(
        _Interpretation(
            frozenset(atom for index, atom in enumerate(class_atoms) if class_mask & (1 << index)),
            frozenset(atom for index, atom in enumerate(role_atoms) if role_mask & (1 << index)),
        )
        for class_mask in range(1 << len(class_atoms))
        for role_mask in range(1 << len(role_atoms))
    )


@pytest.mark.parametrize(
    "build",
    (
        lambda a, b, role: owl.SubClassOf(a, owl.ObjectAllValuesFrom(role, b)),
        lambda a, b, role: owl.SubClassOf(owl.ObjectSomeValuesFrom(role, a), b),
        lambda a, b, role: owl.SubClassOf(a, owl.ObjectMinCardinality(2, role, b)),
        lambda a, b, role: owl.SubClassOf(a, owl.ObjectMaxCardinality(1, role, b)),
        lambda a, _b, role: owl.SubClassOf(a, owl.ObjectHasSelf(role)),
    ),
)
def test_compiled_relational_clauses_match_every_two_object_interpretation(build) -> None:  # type: ignore[no-untyped-def]
    first = owl.Class(owl.IRI("urn:test:bounded-relational:A"))
    second = owl.Class(owl.IRI("urn:test:bounded-relational:B"))
    role = owl.ObjectProperty(owl.IRI("urn:test:bounded-relational:r"))
    axiom = build(first, second, role)
    program = compile_normalized(normalize_axioms((axiom,), logical_fingerprint=FINGERPRINT))
    for interpretation in _interpretations((first.iri.value, second.iri.value)):
        assert _source_holds(axiom, interpretation, role.iri.value) == _program_holds(
            program,
            interpretation,
            role.iri.value,
        )
