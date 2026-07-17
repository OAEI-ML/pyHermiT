from __future__ import annotations

import dataclasses

import pyowl_core.model as owl
import pytest

from pyhermit.clauses import (
    Atom,
    ClauseProgram,
    DatatypeModelIR,
    DLClause,
    Predicate,
    PredicateKind,
    PredicateRegistry,
    RoleAutomatonIR,
    SymbolTable,
    SymbolValue,
    TermSort,
    Variable,
    compile_normalized,
)
from pyhermit.exceptions import ResourceLimitError
from pyhermit.normalize import normalize_axioms

FINGERPRINT = "31" * 32


def _program() -> ClauseProgram:
    first = owl.Class(owl.IRI("urn:test:ir:A"))
    second = owl.Class(owl.IRI("urn:test:ir:B"))
    return compile_normalized(
        normalize_axioms(
            (owl.SubClassOf(first, second),),
            logical_fingerprint=FINGERPRINT,
        )
    )


def test_canonical_program_round_trip_is_exact_and_rejects_noncanonical_json() -> None:
    program = _program()
    encoded = program.canonical_json()
    assert ClauseProgram.from_canonical_json(encoded) == program
    assert ClauseProgram.from_canonical_json(encoded).canonical_bytes() == program.canonical_bytes()
    with pytest.raises(ValueError, match="not canonical"):
        ClauseProgram.from_canonical_json(encoded.replace(":", ": ", 1))


def test_predicates_reject_wrong_arity_sorts_and_mixed_equality() -> None:
    with pytest.raises(ValueError, match="two object arguments"):
        Predicate(
            0,
            PredicateKind.OBJECT_ROLE,
            (TermSort.OBJECT, TermSort.DATA),
            role_id=0,
        )
    with pytest.raises(ValueError, match="cannot mix"):
        Predicate(
            0,
            PredicateKind.EQUALITY,
            (TermSort.OBJECT, TermSort.DATA),
        )
    with pytest.raises(ValueError, match="positive cardinality"):
        Predicate(
            0,
            PredicateKind.AT_LEAST_OBJECT,
            (TermSort.OBJECT,),
            role_id=0,
            cardinality=0,
            filler_predicate_id=0,
        )
    with pytest.raises(ValueError, match="identify its canonical term sort"):
        Predicate(
            0,
            PredicateKind.ORDERING_GUARD,
            (TermSort.OBJECT, TermSort.OBJECT),
            internal_key="canonical-data-order",
        )


def test_registry_rejects_recursive_or_wrong_cardinality_fillers() -> None:
    first = Predicate(
        0,
        PredicateKind.AT_LEAST_OBJECT,
        (TermSort.OBJECT,),
        role_id=0,
        cardinality=1,
        filler_predicate_id=1,
    )
    second = Predicate(
        1,
        PredicateKind.AT_LEAST_OBJECT,
        (TermSort.OBJECT,),
        role_id=0,
        cardinality=1,
        filler_predicate_id=0,
    )
    with pytest.raises(ValueError, match="object concept literal"):
        PredicateRegistry((first, second))


def test_wire_records_reject_noncanonical_hex_negative_nested_ids_and_duplicate_automata() -> None:
    with pytest.raises(ValueError, match="canonical lowercase"):
        SymbolValue(0, "AA", "value")

    program = _program()
    with pytest.raises((ValueError, ResourceLimitError), match=r"unsigned|complex role"):
        dataclasses.replace(
            program.role_model,
            complex_inclusions=(((-1, 0), 0),),
        )
    automaton = RoleAutomatonIR(0, 1, 0, (0,), ())
    with pytest.raises(ValueError, match="uniquely sorted"):
        dataclasses.replace(program.role_model, automata=(automaton, automaton))
    with pytest.raises((ValueError, ResourceLimitError), match="unsigned"):
        DatatypeModelIR(datatype_definitions=((-1, 0),))


def test_clause_variables_have_one_sort_and_canonical_first_occurrence() -> None:
    concept = owl.Class(owl.IRI("urn:test:ir:variables"))
    role = owl.ObjectProperty(owl.IRI("urn:test:ir:variables-role"))
    data = owl.DataProperty(owl.IRI("urn:test:ir:variables-data"))
    integer = owl.Datatype(owl.IRI("http://www.w3.org/2001/XMLSchema#integer"))
    program = compile_normalized(
        normalize_axioms(
            (
                owl.ObjectPropertyDomain(role, concept),
                owl.DataPropertyRange(data, integer),
            ),
            logical_fingerprint=FINGERPRINT,
        )
    )
    object_role = next(
        value
        for value in program.predicates.predicates
        if value.kind is PredicateKind.OBJECT_ROLE
        and value.role_id != program.role_model.bottom_object_role_id
    )
    data_range = next(
        value for value in program.predicates.predicates if value.kind is PredicateKind.DATA_RANGE
    )
    noncanonical = DLClause(
        0,
        (
            Atom(
                object_role.predicate_id,
                (Variable(1, TermSort.OBJECT), Variable(0, TermSort.OBJECT)),
            ),
        ),
        (),
        (0,),
        (0,),
    )
    with pytest.raises(ValueError, match="first-occurrence"):
        dataclasses.replace(program, clauses=(noncanonical,))

    mixed_atoms = tuple(
        sorted(
            (
                Atom(
                    object_role.predicate_id,
                    (Variable(0, TermSort.OBJECT), Variable(1, TermSort.OBJECT)),
                ),
                Atom(data_range.predicate_id, (Variable(0, TermSort.DATA),)),
            ),
            key=lambda value: value.canonical_bytes(),
        )
    )
    mixed = DLClause(0, mixed_atoms, (), (0,), tuple(range(len(mixed_atoms))))
    with pytest.raises(ValueError, match="both object and data"):
        dataclasses.replace(program, clauses=(mixed,))


def test_ordering_guard_atoms_require_strict_canonical_direction() -> None:
    concept = owl.Class(owl.IRI("urn:test:ir:key-class"))
    role = owl.ObjectProperty(owl.IRI("urn:test:ir:key-role"))
    program = compile_normalized(
        normalize_axioms(
            (owl.HasKey(concept, owl.CanonicalSet((role,)), owl.CanonicalSet()),),
            logical_fingerprint=FINGERPRINT,
        )
    )
    ordering = next(
        value
        for value in program.predicates.predicates
        if value.kind is PredicateKind.ORDERING_GUARD
    )
    malformed = DLClause(
        0,
        (
            Atom(
                ordering.predicate_id,
                (Variable(1, TermSort.OBJECT), Variable(0, TermSort.OBJECT)),
            ),
        ),
        (),
        (0,),
        (0,),
    )
    with pytest.raises(ValueError, match="strict canonical order"):
        dataclasses.replace(program, clauses=(malformed,))


def test_automaton_predicates_reference_existing_component_states() -> None:
    source = owl.Class(owl.IRI("urn:test:ir:automaton-source"))
    target = owl.Class(owl.IRI("urn:test:ir:automaton-target"))
    first = owl.ObjectProperty(owl.IRI("urn:test:ir:automaton-first"))
    second = owl.ObjectProperty(owl.IRI("urn:test:ir:automaton-second"))
    super_role = owl.ObjectProperty(owl.IRI("urn:test:ir:automaton-super"))
    program = compile_normalized(
        normalize_axioms(
            (
                owl.SubObjectPropertyOf(owl.ObjectPropertyChain((first, second)), super_role),
                owl.SubClassOf(source, owl.ObjectAllValuesFrom(super_role, target)),
            ),
            logical_fingerprint=FINGERPRINT,
        )
    )
    predicate = next(
        value
        for value in program.predicates.predicates
        if value.kind is PredicateKind.AUTOMATON_STATE
    )
    component, _state = predicate.annotation
    automaton = next(
        value for value in program.role_model.automata if value.component_id == component
    )
    malformed = dataclasses.replace(predicate, annotation=(component, automaton.state_count))
    predicates = list(program.predicates.predicates)
    predicates[predicate.predicate_id] = malformed
    registry = PredicateRegistry(tuple(predicates))
    symbols = SymbolTable(program.symbols.domains, registry)
    with pytest.raises(ValueError, match="absent role automaton state"):
        dataclasses.replace(program, symbols=symbols, predicates=registry)


def test_program_rejects_dangling_predicate_and_provenance_ids() -> None:
    program = _program()
    variable = Variable(0, TermSort.OBJECT)
    dangling_predicate = DLClause(
        0,
        (Atom(len(program.predicates.predicates), (variable,)),),
        (),
        (0,),
        (0,),
    )
    with pytest.raises(ValueError, match="predicate ID is dangling"):
        dataclasses.replace(program, clauses=(dangling_predicate,))

    predicate_id = next(
        value.predicate_id
        for value in program.predicates.predicates
        if value.kind is PredicateKind.CONCEPT
    )
    dangling_provenance = DLClause(
        0,
        (Atom(predicate_id, (variable,)),),
        (),
        (len(program.provenance.entries),),
        (0,),
    )
    with pytest.raises(ValueError, match="dangling provenance"):
        dataclasses.replace(program, clauses=(dangling_provenance,))


def test_program_rejects_facts_in_the_wrong_polarity_partition() -> None:
    concept = owl.Class(owl.IRI("urn:test:ir:fact-polarity"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:ir:fact-polarity-i"))
    program = compile_normalized(
        normalize_axioms(
            (owl.ClassAssertion(concept, individual),),
            logical_fingerprint=FINGERPRINT,
        )
    )
    assert program.positive_facts
    with pytest.raises(ValueError, match="wrong polarity partition"):
        dataclasses.replace(
            program,
            positive_facts=(),
            negative_facts=program.positive_facts,
        )


def test_program_rejects_unsafe_head_variables_and_wrong_expressivity() -> None:
    program = _program()
    predicates = [
        value.predicate_id
        for value in program.predicates.predicates
        if value.kind is PredicateKind.CONCEPT
    ]
    body = Atom(predicates[0], (Variable(0, TermSort.OBJECT),))
    head = Atom(predicates[1], (Variable(1, TermSort.OBJECT),))
    unsafe = DLClause(0, (body,), (head,), (0,), (0,))
    with pytest.raises(ValueError, match="range-restricted"):
        dataclasses.replace(program, clauses=(unsafe,))

    non_horn = DLClause(
        0,
        (body,),
        (
            Atom(predicates[1], (Variable(0, TermSort.OBJECT),)),
            Atom(predicates[2], (Variable(0, TermSort.OBJECT),)),
        ),
        (0,),
        (0,),
    )
    horn_summary = dataclasses.replace(program.expressivity, non_horn=False)
    with pytest.raises(ValueError, match="non-Horn"):
        dataclasses.replace(program, clauses=(non_horn,), expressivity=horn_summary)


def test_strategy_summary_rejects_nominal_datatype_cardinality_and_role_false_negatives() -> None:
    concept = owl.Class(owl.IRI("urn:test:ir:strategy-class"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:ir:strategy-i"))
    first = owl.ObjectProperty(owl.IRI("urn:test:ir:strategy-r"))
    second = owl.ObjectProperty(owl.IRI("urn:test:ir:strategy-s"))
    target = owl.ObjectProperty(owl.IRI("urn:test:ir:strategy-t"))
    data = owl.DataProperty(owl.IRI("urn:test:ir:strategy-data"))
    unknown = owl.Datatype(owl.IRI("urn:test:ir:strategy-unknown"))
    programs = (
        (
            compile_normalized(
                normalize_axioms(
                    (
                        owl.SubClassOf(
                            owl.ObjectOneOf(owl.CanonicalSet((individual,))),
                            concept,
                        ),
                    ),
                    logical_fingerprint=FINGERPRINT,
                )
            ),
            "nominals",
            "nominals",
        ),
        (
            compile_normalized(
                normalize_axioms(
                    (owl.DataPropertyRange(data, unknown),),
                    logical_fingerprint=FINGERPRINT,
                )
            ),
            "unknown_datatypes",
            "unknown datatype",
        ),
        (
            compile_normalized(
                normalize_axioms(
                    (owl.DataPropertyRange(data, unknown),),
                    logical_fingerprint=FINGERPRINT,
                )
            ),
            "datatypes",
            "datatype constraints",
        ),
        (
            compile_normalized(
                normalize_axioms(
                    (
                        owl.SubClassOf(
                            concept,
                            owl.ObjectMaxCardinality(1, first, concept),
                        ),
                    ),
                    logical_fingerprint=FINGERPRINT,
                )
            ),
            "number_restrictions",
            "number restrictions",
        ),
        (
            compile_normalized(
                normalize_axioms(
                    (
                        owl.SubObjectPropertyOf(
                            owl.ObjectPropertyChain((first, second)),
                            target,
                        ),
                    ),
                    logical_fingerprint=FINGERPRINT,
                )
            ),
            "complex_roles",
            "complex role",
        ),
    )
    for program, field, message in programs:
        summary = dataclasses.replace(program.expressivity, **{field: False})
        with pytest.raises(ValueError, match=message):
            dataclasses.replace(program, expressivity=summary)
