from __future__ import annotations

from collections.abc import Iterable, Iterator
from dataclasses import dataclass
from typing import TypeAlias

import pyowl_core.model as owl

from pyhermit.clauses import (
    Atom,
    ClauseProgram,
    DataConstant,
    DeltaCompatibility,
    GroundAtom,
    IndividualTerm,
    Predicate,
    PredicateKind,
    SymbolKind,
    TermSort,
    Variable,
    compile_delta_plan,
    compile_normalized,
    compile_query_program,
)
from pyhermit.normalize import normalize_axioms, normalize_query

FINGERPRINT = "39" * 32
XSD_INTEGER = owl.Datatype(owl.IRI("http://www.w3.org/2001/XMLSchema#integer"))

_Fact: TypeAlias = tuple[int, tuple[int, ...]]
_VariableKey: TypeAlias = tuple[int, TermSort]
_Binding: TypeAlias = dict[_VariableKey, int]


@dataclass(frozen=True)
class _Closure:
    facts: frozenset[_Fact]
    clashed: bool


def _ground_value(value: IndividualTerm | DataConstant) -> int:
    if isinstance(value, IndividualTerm):
        return value.individual_id
    return value.data_identity_id


def _ground_fact(atom: GroundAtom) -> _Fact:
    return atom.predicate_id, tuple(_ground_value(value) for value in atom.arguments)


def _term_value(
    term: Variable | IndividualTerm | DataConstant,
    binding: _Binding,
) -> int | None:
    if isinstance(term, Variable):
        return binding.get((term.index, term.sort))
    return _ground_value(term)


def _unify(atom: Atom, values: tuple[int, ...], binding: _Binding) -> _Binding | None:
    if len(atom.arguments) != len(values):
        return None
    result = dict(binding)
    for term, value in zip(atom.arguments, values, strict=True):
        if isinstance(term, Variable):
            key = (term.index, term.sort)
            retained = result.get(key)
            if retained is not None and retained != value:
                return None
            result[key] = value
        elif _ground_value(term) != value:
            return None
    return result


def _instantiate(atom: Atom, binding: _Binding) -> _Fact:
    values = tuple(_term_value(term, binding) for term in atom.arguments)
    assert all(value is not None for value in values)
    return atom.predicate_id, tuple(value for value in values if value is not None)


def _semantic_binary_holds(
    predicate: Predicate,
    values: tuple[int, int],
    facts: set[_Fact],
) -> bool:
    first, second = values
    direct = (predicate.predicate_id, values) in facts
    reverse = (predicate.predicate_id, (second, first)) in facts
    if predicate.kind is PredicateKind.EQUALITY:
        return first == second or direct or reverse
    if predicate.kind is PredicateKind.INEQUALITY:
        if predicate.argument_sorts == (TermSort.DATA, TermSort.DATA):
            return first != second
        return direct or reverse
    if predicate.kind is PredicateKind.ORDERING_GUARD:
        return first <= second
    raise AssertionError(f"unexpected semantic predicate {predicate.kind.value}")


def _binary_bindings(
    atom: Atom,
    predicate: Predicate,
    binding: _Binding,
    facts: set[_Fact],
) -> Iterator[_Binding]:
    first = _term_value(atom.arguments[0], binding)
    second = _term_value(atom.arguments[1], binding)
    if first is not None and second is not None:
        if _semantic_binary_holds(predicate, (first, second), facts):
            yield binding
        return

    rows = {
        values
        for predicate_id, values in facts
        if predicate_id == predicate.predicate_id and len(values) == 2
    }
    if predicate.kind is PredicateKind.EQUALITY:
        rows.update((second_value, first_value) for first_value, second_value in tuple(rows))
    for values in sorted(rows):
        retained = _unify(atom, values, binding)
        if retained is not None:
            yield retained

    if predicate.kind is PredicateKind.EQUALITY:
        known = first if first is not None else second
        if known is not None:
            retained = _unify(atom, (known, known), binding)
            if retained is not None:
                yield retained


def _body_bindings(
    registry: ClauseProgram,
    atoms: tuple[Atom, ...],
    facts: set[_Fact],
    binding: _Binding | None = None,
) -> Iterator[_Binding]:
    if not atoms:
        yield {} if binding is None else binding
        return
    retained_binding = {} if binding is None else binding
    ordered = tuple(
        sorted(
            atoms,
            key=lambda atom: (
                registry.predicates.predicate(atom.predicate_id).kind
                in {
                    PredicateKind.EQUALITY,
                    PredicateKind.INEQUALITY,
                    PredicateKind.ORDERING_GUARD,
                }
            ),
        )
    )
    atom, remaining = ordered[0], ordered[1:]
    predicate = registry.predicates.predicate(atom.predicate_id)
    if predicate.kind in {
        PredicateKind.EQUALITY,
        PredicateKind.INEQUALITY,
        PredicateKind.ORDERING_GUARD,
    }:
        candidates: Iterable[_Binding] = _binary_bindings(
            atom,
            predicate,
            retained_binding,
            facts,
        )
    else:
        candidates = (
            candidate
            for predicate_id, values in sorted(facts)
            if predicate_id == atom.predicate_id
            for candidate in (_unify(atom, values, retained_binding),)
            if candidate is not None
        )
    for candidate in candidates:
        yield from _body_bindings(registry, remaining, facts, candidate)


def _head_status(
    registry: ClauseProgram,
    fact: _Fact,
    facts: set[_Fact],
) -> tuple[bool, bool]:
    """Return (already true, definitely false) for a grounded head atom."""

    predicate = registry.predicates.predicate(fact[0])
    if predicate.kind in {
        PredicateKind.EQUALITY,
        PredicateKind.INEQUALITY,
        PredicateKind.ORDERING_GUARD,
    }:
        assert len(fact[1]) == 2
        holds = _semantic_binary_holds(predicate, (fact[1][0], fact[1][1]), facts)
        if holds:
            return True, False
        if predicate.kind is PredicateKind.INEQUALITY and predicate.argument_sorts == (
            TermSort.DATA,
            TermSort.DATA,
        ):
            return False, True
    return fact in facts, False


def _close(
    programs: tuple[ClauseProgram, ...],
    *,
    extra_facts: Iterable[_Fact] = (),
) -> _Closure:
    registry = max(programs, key=lambda program: len(program.predicates.predicates))
    for program in programs:
        prefix = registry.predicates.predicates[: len(program.predicates.predicates)]
        assert tuple(value.identity_payload() for value in prefix) == tuple(
            value.identity_payload() for value in program.predicates.predicates
        )
    facts = {
        _ground_fact(fact)
        for program in programs
        for fact in program.positive_facts + program.negative_facts
    }
    facts.update(extra_facts)
    clauses = tuple(clause for program in programs for clause in program.clauses)
    for _round in range(256):
        changed = False
        for clause in clauses:
            for binding in _body_bindings(registry, clause.body, facts):
                if not clause.head:
                    return _Closure(frozenset(facts), True)
                grounded = tuple(_instantiate(atom, binding) for atom in clause.head)
                statuses = tuple(_head_status(registry, fact, facts) for fact in grounded)
                if any(is_true for is_true, _is_false in statuses):
                    continue
                unresolved = tuple(
                    fact
                    for fact, (_is_true, is_false) in zip(grounded, statuses, strict=True)
                    if not is_false
                )
                if len(unresolved) == 1 and unresolved[0] not in facts:
                    facts.add(unresolved[0])
                    changed = True
        if not changed:
            return _Closure(frozenset(facts), False)
    raise AssertionError("bounded clause application did not converge")


def _symbol_id(
    program: ClauseProgram,
    kind: SymbolKind,
    node: owl.StructuralNode,
) -> int:
    encoded = node.canonical_bytes().hex()
    return next(
        value.identifier
        for value in program.symbols.domain(kind).values
        if value.key_hex == encoded
    )


def _individual_id(program: ClauseProgram, individual: owl.Individual) -> int:
    return _symbol_id(program, SymbolKind.INDIVIDUAL, individual)


def _predicate_id(
    program: ClauseProgram,
    kind: PredicateKind,
    *,
    symbol_id: int | None = None,
    role_id: int | None = None,
    sorts: tuple[TermSort, ...] | None = None,
) -> int:
    return next(
        predicate.predicate_id
        for predicate in program.predicates.predicates
        if predicate.kind is kind
        and (symbol_id is None or predicate.symbol_id == symbol_id)
        and (role_id is None or predicate.role_id == role_id)
        and (sorts is None or predicate.argument_sorts == sorts)
    )


def _concept_predicate(program: ClauseProgram, concept: owl.Class) -> int:
    return _predicate_id(
        program,
        PredicateKind.CONCEPT,
        symbol_id=_symbol_id(program, SymbolKind.CLASS_EXPRESSION, concept),
    )


def _role_predicate(
    program: ClauseProgram,
    property: owl.ObjectProperty | owl.DataProperty,
) -> int:
    if isinstance(property, owl.ObjectProperty):
        domain = SymbolKind.OBJECT_ROLE
        kind = PredicateKind.OBJECT_ROLE
    else:
        domain = SymbolKind.DATA_PROPERTY
        kind = PredicateKind.DATA_ROLE
    return _predicate_id(program, kind, role_id=_symbol_id(program, domain, property))


def _data_identity(program: ClauseProgram, literal: owl.Literal) -> int:
    source_id = _symbol_id(program, SymbolKind.SOURCE_LITERAL, literal)
    return next(
        identity.data_identity_id
        for identity in program.datatype_model.literal_identities
        if identity.source_literal_id == source_id
    )


def test_role_nfa_universal_propagates_to_a_property_chain_successor() -> None:
    source = owl.Class(owl.IRI("urn:test:semantic-application:nfa-source"))
    filler = owl.Class(owl.IRI("urn:test:semantic-application:nfa-filler"))
    first_role = owl.ObjectProperty(owl.IRI("urn:test:semantic-application:nfa-first"))
    second_role = owl.ObjectProperty(owl.IRI("urn:test:semantic-application:nfa-second"))
    super_role = owl.ObjectProperty(owl.IRI("urn:test:semantic-application:nfa-super"))
    first = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:nfa-a"))
    middle = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:nfa-b"))
    last = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:nfa-c"))
    axioms = (
        owl.SubObjectPropertyOf(
            owl.ObjectPropertyChain((first_role, second_role)),
            super_role,
        ),
        owl.SubClassOf(source, owl.ObjectAllValuesFrom(super_role, filler)),
        owl.ClassAssertion(source, first),
        owl.ObjectPropertyAssertion(first_role, first, middle),
        owl.ObjectPropertyAssertion(second_role, middle, last),
    )
    program = compile_normalized(normalize_axioms(axioms, logical_fingerprint=FINGERPRINT))

    closure = _close((program,))
    last_id = _individual_id(program, last)
    assert not closure.clashed
    assert (_concept_predicate(program, filler), (last_id,)) in closure.facts
    assert any(
        program.predicates.predicate(predicate_id).kind is PredicateKind.AUTOMATON_STATE
        and arguments == (last_id,)
        for predicate_id, arguments in closure.facts
    )


def test_nominal_rules_propagate_asserted_equality_in_both_directions() -> None:
    marker = owl.Class(owl.IRI("urn:test:semantic-application:nominal-marker"))
    first = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:nominal-a"))
    second = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:nominal-b"))
    nominal = owl.ObjectOneOf(owl.CanonicalSet((first,)))
    axioms = (
        owl.SubClassOf(nominal, marker),
        owl.SameIndividual(owl.CanonicalSet((first, second))),
    )
    program = compile_normalized(normalize_axioms(axioms, logical_fingerprint=FINGERPRINT))

    closure = _close((program,))
    first_id = _individual_id(program, first)
    second_id = _individual_id(program, second)
    nominal_id = _symbol_id(program, SymbolKind.CLASS_EXPRESSION, nominal)
    nominal_predicate = _predicate_id(
        program,
        PredicateKind.NOMINAL,
        symbol_id=nominal_id,
    )
    marker_predicate = _concept_predicate(program, marker)
    assert not closure.clashed
    assert (nominal_predicate, (first_id,)) in closure.facts
    assert (nominal_predicate, (second_id,)) in closure.facts
    assert (marker_predicate, (second_id,)) in closure.facts


def test_has_key_fires_only_for_named_members_with_a_shared_object_value() -> None:
    member = owl.Class(owl.IRI("urn:test:semantic-application:key-member"))
    object_key = owl.ObjectProperty(owl.IRI("urn:test:semantic-application:key-object"))
    data_key = owl.DataProperty(owl.IRI("urn:test:semantic-application:key-data"))
    first = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:key-a"))
    second = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:key-b"))
    shared = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:key-shared"))
    literal = owl.Literal("shared", owl.XSD_STRING)
    key = owl.HasKey(
        member,
        owl.CanonicalSet((object_key,)),
        owl.CanonicalSet((data_key,)),
    )
    axioms = (
        key,
        owl.ClassAssertion(member, first),
        owl.ClassAssertion(member, second),
        owl.ObjectPropertyAssertion(object_key, first, shared),
        owl.ObjectPropertyAssertion(object_key, second, shared),
        owl.DataPropertyAssertion(data_key, first, literal),
        owl.DataPropertyAssertion(data_key, second, literal),
    )
    program = compile_normalized(normalize_axioms(axioms, logical_fingerprint=FINGERPRINT))

    closure = _close((program,))
    first_id = _individual_id(program, first)
    second_id = _individual_id(program, second)
    equality = _predicate_id(
        program,
        PredicateKind.EQUALITY,
        sorts=(TermSort.OBJECT, TermSort.OBJECT),
    )
    assert not closure.clashed
    assert (equality, tuple(sorted((first_id, second_id)))) in closure.facts

    other = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:key-other"))
    no_shared_target = (
        key,
        owl.ClassAssertion(member, first),
        owl.ClassAssertion(member, second),
        owl.ObjectPropertyAssertion(object_key, first, shared),
        owl.ObjectPropertyAssertion(object_key, second, other),
        owl.DataPropertyAssertion(data_key, first, literal),
        owl.DataPropertyAssertion(data_key, second, literal),
    )
    separated = compile_normalized(
        normalize_axioms(no_shared_target, logical_fingerprint=FINGERPRINT)
    )
    separated_closure = _close((separated,))
    separated_pair = tuple(
        sorted((_individual_id(separated, first), _individual_id(separated, second)))
    )
    separated_equality = _predicate_id(
        separated,
        PredicateKind.EQUALITY,
        sorts=(TermSort.OBJECT, TermSort.OBJECT),
    )
    assert (separated_equality, separated_pair) not in separated_closure.facts


def test_has_key_named_guard_excludes_anonymous_members() -> None:
    scope = b"\x42" * 32
    member = owl.Class(owl.IRI("urn:test:semantic-application:key-anonymous-member"))
    object_key = owl.ObjectProperty(owl.IRI("urn:test:semantic-application:key-anonymous-object"))
    first = owl.AnonymousIndividual(scope, b"first")
    second = owl.AnonymousIndividual(scope, b"second")
    shared = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:key-anonymous-shared"))
    axioms = (
        owl.HasKey(member, owl.CanonicalSet((object_key,)), owl.CanonicalSet(())),
        owl.ClassAssertion(member, first),
        owl.ClassAssertion(member, second),
        owl.ObjectPropertyAssertion(object_key, first, shared),
        owl.ObjectPropertyAssertion(object_key, second, shared),
    )
    program = compile_normalized(normalize_axioms(axioms, logical_fingerprint=FINGERPRINT))

    closure = _close((program,))
    pair = tuple(sorted((_individual_id(program, first), _individual_id(program, second))))
    equality = _predicate_id(
        program,
        PredicateKind.EQUALITY,
        sorts=(TermSort.OBJECT, TermSort.OBJECT),
    )
    assert not closure.clashed
    assert (equality, pair) not in closure.facts


def test_custom_data_range_definition_applies_to_property_values() -> None:
    custom = owl.Datatype(owl.IRI("urn:test:semantic-application:custom-range"))
    property = owl.DataProperty(owl.IRI("urn:test:semantic-application:range-property"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:range-i"))
    facet = owl.FacetRestriction(
        owl.IRI("http://www.w3.org/2001/XMLSchema#minLength"),
        owl.Literal("2", XSD_INTEGER),
    )
    restricted = owl.DatatypeRestriction(owl.XSD_STRING, owl.CanonicalSet((facet,)))
    literal = owl.Literal("large", owl.XSD_STRING)
    axioms = (
        owl.DatatypeDefinition(custom, restricted),
        owl.DataPropertyRange(property, custom),
        owl.DataPropertyAssertion(property, individual, literal),
    )
    program = compile_normalized(normalize_axioms(axioms, logical_fingerprint=FINGERPRINT))

    closure = _close((program,))
    value = _data_identity(program, literal)
    custom_predicate = _predicate_id(
        program,
        PredicateKind.DATA_RANGE,
        symbol_id=_symbol_id(program, SymbolKind.DATA_RANGE, custom),
    )
    restricted_predicate = _predicate_id(
        program,
        PredicateKind.DATA_RANGE,
        symbol_id=_symbol_id(program, SymbolKind.DATA_RANGE, restricted),
    )
    assert not closure.clashed
    assert (custom_predicate, (value,)) in closure.facts
    assert (restricted_predicate, (value,)) in closure.facts


def test_negative_object_abox_clashes_after_subproperty_application() -> None:
    sub = owl.ObjectProperty(owl.IRI("urn:test:semantic-application:negative-object-sub"))
    sup = owl.ObjectProperty(owl.IRI("urn:test:semantic-application:negative-object-super"))
    first = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:negative-object-a"))
    second = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:negative-object-b"))
    axioms = (
        owl.SubObjectPropertyOf(sub, sup),
        owl.ObjectPropertyAssertion(sub, first, second),
        owl.NegativeObjectPropertyAssertion(sup, first, second),
    )
    program = compile_normalized(normalize_axioms(axioms, logical_fingerprint=FINGERPRINT))

    closure = _close((program,))
    edge = (_individual_id(program, first), _individual_id(program, second))
    assert (_role_predicate(program, sup), edge) in closure.facts
    assert closure.clashed


def test_negative_data_abox_clashes_after_subproperty_application() -> None:
    sub = owl.DataProperty(owl.IRI("urn:test:semantic-application:negative-data-sub"))
    sup = owl.DataProperty(owl.IRI("urn:test:semantic-application:negative-data-super"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:negative-data-i"))
    literal = owl.Literal("value", owl.XSD_STRING)
    axioms = (
        owl.SubDataPropertyOf(sub, sup),
        owl.DataPropertyAssertion(sub, individual, literal),
        owl.NegativeDataPropertyAssertion(sup, individual, literal),
    )
    program = compile_normalized(normalize_axioms(axioms, logical_fingerprint=FINGERPRINT))

    closure = _close((program,))
    edge = (_individual_id(program, individual), _data_identity(program, literal))
    assert (_role_predicate(program, sup), edge) in closure.facts
    assert closure.clashed


def test_query_overlay_is_isolated_but_applies_over_permanent_rows() -> None:
    first = owl.Class(owl.IRI("urn:test:semantic-application:query-first"))
    second = owl.Class(owl.IRI("urn:test:semantic-application:query-second"))
    local = owl.Class(owl.IRI("urn:test:semantic-application:query-local"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:query-i"))
    permanent_normalized = normalize_axioms(
        (
            owl.SubClassOf(first, second),
            owl.ClassAssertion(first, individual),
        ),
        logical_fingerprint=FINGERPRINT,
    )
    permanent = compile_normalized(permanent_normalized)
    before = permanent.canonical_bytes()
    compiled = compile_query_program(
        permanent,
        permanent_normalized,
        normalize_query(permanent_normalized, (owl.SubClassOf(second, local),)),
    )

    assert not compiled.requires_rebuild
    assert compiled.program is not None
    overlay = compiled.program
    individual_id = _individual_id(overlay, individual)
    local_fact = (_concept_predicate(overlay, local), (individual_id,))
    assert local_fact not in _close((overlay,)).facts
    assert local_fact in _close((permanent, overlay)).facts
    assert permanent.canonical_bytes() == before


def test_assertion_delta_rows_apply_without_mutating_the_base_program() -> None:
    first = owl.Class(owl.IRI("urn:test:semantic-application:delta-first"))
    second = owl.Class(owl.IRI("urn:test:semantic-application:delta-second"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:semantic-application:delta-i"))
    base_axioms = (
        owl.SubClassOf(first, second),
        owl.ClassAssertion(owl.OWL_THING, individual),
    )
    addition = owl.ClassAssertion(first, individual)
    base = compile_normalized(normalize_axioms(base_axioms, logical_fingerprint=FINGERPRINT))
    result = compile_normalized(
        normalize_axioms((*base_axioms, addition), logical_fingerprint=FINGERPRINT)
    )
    before = base.canonical_bytes()
    plan = compile_delta_plan(base, result, additions=(addition,))
    base_facts = {_ground_fact(fact) for fact in base.positive_facts + base.negative_facts}
    result_facts = {_ground_fact(fact) for fact in result.positive_facts + result.negative_facts}
    added_rows = result_facts - base_facts
    entailed = (
        _concept_predicate(base, second),
        (_individual_id(base, individual),),
    )

    assert plan.compatibility is DeltaCompatibility.ASSERTION_ONLY
    assert entailed not in _close((base,)).facts
    assert entailed in _close((base,), extra_facts=added_rows).facts
    assert entailed in _close((result,)).facts
    assert base.canonical_bytes() == before
