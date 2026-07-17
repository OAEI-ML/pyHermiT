from __future__ import annotations

import itertools

import pyowl_core.model as owl

from pyhermit.clauses import (
    ClauseProgram,
    DataConstant,
    IndividualTerm,
    PredicateKind,
    SymbolKind,
    Variable,
    compile_normalized,
)
from pyhermit.normalize import normalize_axioms

FINGERPRINT = "33" * 32


def _class_truth(expression: owl.ClassExpression, assignment: dict[str, bool]) -> bool:
    if isinstance(expression, owl.Class):
        if expression.iri.value == owl.OWL_THING.iri.value:
            return True
        if expression.iri.value == owl.OWL_NOTHING.iri.value:
            return False
        return assignment[expression.iri.value]
    if isinstance(expression, owl.ObjectComplementOf):
        return not _class_truth(expression.operand, assignment)
    if isinstance(expression, owl.ObjectIntersectionOf):
        return all(_class_truth(value, assignment) for value in expression.operands)
    if isinstance(expression, owl.ObjectUnionOf):
        return any(_class_truth(value, assignment) for value in expression.operands)
    raise AssertionError(f"unsupported bounded source expression {expression!r}")


def _source_holds(axioms: tuple[owl.AxiomNode, ...], assignment: dict[str, bool]) -> bool:
    for axiom in axioms:
        if isinstance(axiom, owl.SubClassOf):
            if _class_truth(axiom.sub_class, assignment) and not _class_truth(
                axiom.super_class,
                assignment,
            ):
                return False
        elif isinstance(axiom, owl.DisjointClasses):
            if sum(_class_truth(value, assignment) for value in axiom.expressions) > 1:
                return False
        else:
            raise AssertionError(f"unsupported bounded axiom {axiom!r}")
    return True


def _program_has_extension(program: ClauseProgram, assignment: dict[str, bool]) -> bool:
    class_domain = program.symbols.domain(SymbolKind.CLASS_EXPRESSION)
    known: dict[int, bool] = {}
    unknown: list[int] = []
    for predicate in program.predicates.predicates:
        if predicate.kind is PredicateKind.CONCEPT:
            assert predicate.symbol_id is not None
            display = class_domain.value(predicate.symbol_id).display
            if display == f"class:{owl.OWL_THING.iri.value}":
                known[predicate.predicate_id] = True
            elif display == f"class:{owl.OWL_NOTHING.iri.value}":
                known[predicate.predicate_id] = False
            elif display.startswith("class:urn:test:bounded:"):
                known[predicate.predicate_id] = assignment[display.split("class:", 1)[1]]
            else:
                unknown.append(predicate.predicate_id)
        elif predicate.kind in {
            PredicateKind.NEGATED_CONCEPT,
            PredicateKind.DISJOINT_GUARD,
        }:
            unknown.append(predicate.predicate_id)

    for mask in range(1 << len(unknown)):
        truth = dict(known)
        truth.update(
            (predicate_id, bool(mask & (1 << index))) for index, predicate_id in enumerate(unknown)
        )
        if all(_clause_holds(program, clause, truth) for clause in program.clauses):
            return True
    return False


def _clause_holds(program: ClauseProgram, clause, truth: dict[int, bool]) -> bool:  # type: ignore[no-untyped-def]
    body = all(_atom_truth(program, atom, truth) for atom in clause.body)
    head = any(_atom_truth(program, atom, truth) for atom in clause.head)
    return not body or head


def _atom_truth(program: ClauseProgram, atom, truth: dict[int, bool]) -> bool:  # type: ignore[no-untyped-def]
    predicate = program.predicates.predicate(atom.predicate_id)
    if predicate.kind in {
        PredicateKind.CONCEPT,
        PredicateKind.NEGATED_CONCEPT,
        PredicateKind.DISJOINT_GUARD,
    }:
        return truth[atom.predicate_id]
    if predicate.kind in {
        PredicateKind.OBJECT_ROLE,
        PredicateKind.NEGATED_OBJECT_ROLE,
        PredicateKind.DATA_ROLE,
        PredicateKind.NEGATED_DATA_ROLE,
        PredicateKind.DATA_RANGE,
        PredicateKind.NEGATED_DATA_RANGE,
        PredicateKind.AT_LEAST_OBJECT,
        PredicateKind.AT_LEAST_DATA,
        PredicateKind.AUTOMATON_STATE,
        PredicateKind.NAMED_INDIVIDUAL,
    }:
        return False
    if predicate.kind is PredicateKind.EQUALITY:
        return _same_term(atom.arguments[0], atom.arguments[1])
    if predicate.kind is PredicateKind.INEQUALITY:
        return not _same_term(atom.arguments[0], atom.arguments[1])
    if predicate.kind is PredicateKind.ORDERING_GUARD:
        return False
    raise AssertionError(f"unsupported bounded predicate {predicate.kind}")


def _same_term(
    first: Variable | IndividualTerm | DataConstant,
    second: Variable | IndividualTerm | DataConstant,
) -> bool:
    if isinstance(first, Variable) and isinstance(second, Variable):
        return first.sort is second.sort
    return first == second


def test_propositional_clausification_matches_all_single_object_models() -> None:
    first = owl.Class(owl.IRI("urn:test:bounded:A"))
    second = owl.Class(owl.IRI("urn:test:bounded:B"))
    third = owl.Class(owl.IRI("urn:test:bounded:C"))
    cases = (
        (
            owl.SubClassOf(
                owl.ObjectIntersectionOf(owl.CanonicalSet((first, second))),
                third,
            ),
        ),
        (
            owl.SubClassOf(
                first,
                owl.ObjectUnionOf(owl.CanonicalSet((second, third))),
            ),
        ),
        (
            owl.SubClassOf(
                owl.ObjectComplementOf(first),
                owl.ObjectUnionOf(owl.CanonicalSet((second, third))),
            ),
        ),
        (owl.DisjointClasses(owl.CanonicalSet((first, second, third))),),
    )
    for axioms in cases:
        program = compile_normalized(normalize_axioms(axioms, logical_fingerprint=FINGERPRINT))
        for values in itertools.product((False, True), repeat=3):
            assignment = dict(
                zip(
                    (first.iri.value, second.iri.value, third.iri.value),
                    values,
                    strict=True,
                )
            )
            assert _source_holds(axioms, assignment) == _program_has_extension(
                program,
                assignment,
            )
