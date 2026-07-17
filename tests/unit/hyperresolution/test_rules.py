from __future__ import annotations

import json
import random
from collections.abc import Iterable
from pathlib import Path

import pyowl_core.model as owl
import pytest

from pyhermit.backends.python.rules import (
    BranchTransition,
    GroundRuleAtom,
    HyperresolutionEngine,
    RuleLimits,
)
from pyhermit.backends.python.state import (
    BranchChoiceKind,
    Clash,
    ClashKind,
    DependencySet,
    NodeHandle,
    NodeKind,
    TableauSession,
)
from pyhermit.clauses import ClauseProgram, PredicateKind, SymbolKind, compile_normalized
from pyhermit.events import CancellationSource, CancellationToken
from pyhermit.exceptions import (
    InternalInvariantError,
    ReasonerInterruptedError,
    ResourceLimitError,
)
from pyhermit.normalize import normalize_axioms

FINGERPRINT = "91" * 32


def _runtime(
    axioms: Iterable[owl.AxiomNode],
    *,
    disjunction_learning: bool = True,
    limits: RuleLimits | None = None,
) -> tuple[
    ClauseProgram,
    TableauSession,
    HyperresolutionEngine,
    dict[int, NodeHandle],
    dict[int, NodeHandle],
]:
    program = compile_normalized(normalize_axioms(tuple(axioms), logical_fingerprint=FINGERPRINT))
    session = TableauSession()
    source_nodes: dict[int, NodeHandle] = {}
    for identifier, value in enumerate(program.symbols.domain(SymbolKind.INDIVIDUAL).values):
        named = value.display.startswith("named_individual:")
        source_nodes[identifier] = session.create_node(
            NodeKind.ROOT,
            is_owl_named_individual=named,
            source_individual_id=identifier if named else None,
        )
    data_nodes = {
        identifier: session.create_node(NodeKind.CONCRETE)
        for identifier, _value in enumerate(program.symbols.domain(SymbolKind.DATA_VALUE).values)
    }
    engine = HyperresolutionEngine(
        program,
        session,
        source_nodes=source_nodes,
        data_nodes=data_nodes,
        limits=limits,
        disjunction_learning=disjunction_learning,
    )
    engine.initialize(CancellationSource().token)
    return program, session, engine, source_nodes, data_nodes


class _CancelAfterMutation(CancellationToken):
    __slots__ = ("_baseline", "_session")

    def __init__(self, session: TableauSession, baseline: int) -> None:
        super().__init__()
        self._session = session
        self._baseline = baseline

    def check(self) -> None:
        if self._session.trail.length > self._baseline:
            raise ReasonerInterruptedError("injected join cancellation")
        super().check()


def _symbol_id(program: ClauseProgram, kind: SymbolKind, value: owl.StructuralNode) -> int:
    key = value.canonical_bytes().hex()
    return next(
        identifier
        for identifier, candidate in enumerate(program.symbols.domain(kind).values)
        if candidate.key_hex == key
    )


def _concept_predicate(program: ClauseProgram, value: owl.ClassExpression) -> int:
    return _concept_literal_predicate(program, value, PredicateKind.CONCEPT)


def _concept_literal_predicate(
    program: ClauseProgram,
    value: owl.ClassExpression,
    kind: PredicateKind,
) -> int:
    symbol_id = _symbol_id(program, SymbolKind.CLASS_EXPRESSION, value)
    return next(
        predicate.predicate_id
        for predicate in program.predicates.predicates
        if predicate.kind is kind and predicate.symbol_id == symbol_id
    )


def _individual_node(
    program: ClauseProgram,
    nodes: dict[int, NodeHandle],
    value: owl.Individual,
) -> NodeHandle:
    return nodes[_symbol_id(program, SymbolKind.INDIVIDUAL, value)]


def _has_fact(
    session: TableauSession,
    predicate_id: int,
    arguments: tuple[NodeHandle, ...],
) -> bool:
    return bool(
        tuple(
            session.extensions.retrieve(
                predicate_id,
                bindings={index: value for index, value in enumerate(arguments)},
            )
        )
    )


def test_indexed_hyperresolution_derives_a_deterministic_concept_head() -> None:
    first = owl.Class(owl.IRI("urn:test:hyp:first"))
    second = owl.Class(owl.IRI("urn:test:hyp:second"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:hyp:i"))
    program, session, engine, source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(first, second),
            owl.ClassAssertion(first, individual),
        )
    )
    node = _individual_node(program, source_nodes, individual)
    target = _concept_predicate(program, second)
    assert not _has_fact(session, target, (node,))
    assert engine.saturate_hyperresolution(CancellationSource().token) >= 1
    assert _has_fact(session, target, (node,))
    session.check_invariants()


def test_indexed_and_naive_join_enumeration_agree_on_shared_variables() -> None:
    member = owl.Class(owl.IRI("urn:test:hyp:join-member"))
    key_role = owl.ObjectProperty(owl.IRI("urn:test:hyp:join-role"))
    first = owl.NamedIndividual(owl.IRI("urn:test:hyp:join-first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:hyp:join-second"))
    shared = owl.NamedIndividual(owl.IRI("urn:test:hyp:join-shared"))
    program, session, engine, _source_nodes, _data_nodes = _runtime(
        (
            owl.HasKey(member, owl.CanonicalSet((key_role,)), owl.CanonicalSet(())),
            owl.ClassAssertion(member, first),
            owl.ClassAssertion(member, second),
            owl.ObjectPropertyAssertion(key_role, first, shared),
            owl.ObjectPropertyAssertion(key_role, second, shared),
        )
    )
    target_predicate = next(
        value.predicate_id
        for value in program.predicates.predicates
        if value.kind is PredicateKind.EQUALITY
    )
    clause = next(
        value
        for value in program.clauses
        if any(atom.predicate_id == target_predicate for atom in value.head)
        and len(value.body) >= 2
    )
    token = CancellationSource().token
    naive = {
        (match.bindings, match.dependency.bits)
        for match in engine.naive_matches(clause.clause_id, token)
    }
    indexed = {
        (match.bindings, match.dependency.bits)
        for plan in engine.join_program.plans
        if plan.clause_id == clause.clause_id
        for row in session.extensions.active_rows()
        if row.key.predicate_id == clause.body[plan.delta_body_index].predicate_id
        for match in engine.indexed_matches(plan, row, token)
    }
    assert indexed == naive
    assert len(indexed) == 1


def test_generated_indexed_and_naive_join_sets_are_identical() -> None:
    for seed in range(16):
        randomizer = random.Random(seed)
        member = owl.Class(owl.IRI(f"urn:test:hyp:generated:member:{seed}"))
        first_role = owl.ObjectProperty(owl.IRI(f"urn:test:hyp:generated:r:{seed}"))
        second_role = owl.ObjectProperty(owl.IRI(f"urn:test:hyp:generated:s:{seed}"))
        individuals = tuple(
            owl.NamedIndividual(owl.IRI(f"urn:test:hyp:generated:i:{seed}:{index}"))
            for index in range(4)
        )
        axioms: list[owl.AxiomNode] = [
            owl.FunctionalObjectProperty(first_role),
            owl.DisjointObjectProperties(owl.CanonicalSet((first_role, second_role))),
            owl.HasKey(member, owl.CanonicalSet((first_role,)), owl.CanonicalSet(())),
        ]
        axioms.extend(owl.ClassAssertion(member, value) for value in individuals[:3])
        for source in individuals[:3]:
            for target in randomizer.sample(individuals, k=2):
                axioms.append(owl.ObjectPropertyAssertion(first_role, source, target))
            if randomizer.randrange(2):
                axioms.append(
                    owl.ObjectPropertyAssertion(
                        second_role,
                        source,
                        randomizer.choice(individuals),
                    )
                )
        program, session, engine, _source_nodes, _data_nodes = _runtime(axioms)
        token = CancellationSource().token
        for clause in program.clauses:
            plans = tuple(
                value for value in engine.join_program.plans if value.clause_id == clause.clause_id
            )
            if not plans:
                continue
            naive = {
                (match.bindings, match.dependency.bits)
                for match in engine.naive_matches(clause.clause_id, token)
            }
            indexed = {
                (match.bindings, match.dependency.bits)
                for plan in plans
                for row in session.extensions.active_rows()
                if row.key.predicate_id == clause.body[plan.delta_body_index].predicate_id
                for match in engine.indexed_matches(plan, row, token)
            }
            assert indexed == naive, (seed, clause.clause_id)


def test_indexed_and_naive_join_sets_agree_across_delta_generations() -> None:
    first = owl.Class(owl.IRI("urn:test:hyp:delta:first"))
    second = owl.Class(owl.IRI("urn:test:hyp:delta:second"))
    third = owl.Class(owl.IRI("urn:test:hyp:delta:third"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:hyp:delta:i"))
    program, session, engine, _source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(first, second),
            owl.SubClassOf(second, third),
            owl.ClassAssertion(first, individual),
        )
    )
    token = CancellationSource().token
    assert engine.apply_next_delta(token) > 0
    session.extensions.prepare_next_delta()

    saw_new_match = False
    for clause in program.clauses:
        plans = tuple(
            value for value in engine.join_program.plans if value.clause_id == clause.clause_id
        )
        if not plans:
            continue
        naive = {
            (match.bindings, match.dependency.bits)
            for match in engine.naive_matches(clause.clause_id, token)
        }
        indexed = {
            (match.bindings, match.dependency.bits)
            for plan in plans
            for row in session.extensions.active_rows()
            if row.key.predicate_id == clause.body[plan.delta_body_index].predicate_id
            for match in engine.indexed_matches(plan, row, token)
        }
        assert indexed == naive
        saw_new_match = saw_new_match or bool(indexed)
    assert saw_new_match

    session.extensions.prepare_next_delta()
    assert all(
        not engine.naive_matches(clause.clause_id, token)
        for clause in program.clauses
        if any(plan.clause_id == clause.clause_id for plan in engine.join_program.plans)
    )


def test_inactive_delta_tuple_is_never_joined() -> None:
    source = owl.Class(owl.IRI("urn:test:hyp:inactive-source"))
    target = owl.Class(owl.IRI("urn:test:hyp:inactive-target"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:hyp:inactive-i"))
    program, session, engine, _source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(source, target),
            owl.ClassAssertion(source, individual),
        )
    )
    source_predicate = _concept_predicate(program, source)
    plan = next(
        value
        for value in engine.join_program.plans
        if program.clauses[value.clause_id].body[value.delta_body_index].predicate_id
        == source_predicate
    )
    row = next(
        value
        for value in session.extensions.active_rows()
        if value.key.predicate_id == source_predicate
    )
    session.extensions.deactivate(row.row_id)
    assert not engine.indexed_matches(plan, row, CancellationSource().token)
    assert not engine.naive_matches(plan.clause_id, CancellationSource().token)
    session.check_invariants()


def test_has_key_join_merges_named_members_but_not_anonymous_roots() -> None:
    member = owl.Class(owl.IRI("urn:test:hyp:key-member"))
    key_role = owl.ObjectProperty(owl.IRI("urn:test:hyp:key-role"))
    first = owl.NamedIndividual(owl.IRI("urn:test:hyp:key-first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:hyp:key-second"))
    shared = owl.NamedIndividual(owl.IRI("urn:test:hyp:key-shared"))
    key = owl.HasKey(member, owl.CanonicalSet((key_role,)), owl.CanonicalSet(()))
    program, session, engine, source_nodes, _data_nodes = _runtime(
        (
            key,
            owl.ClassAssertion(member, first),
            owl.ClassAssertion(member, second),
            owl.ObjectPropertyAssertion(key_role, first, shared),
            owl.ObjectPropertyAssertion(key_role, second, shared),
        )
    )
    engine.saturate_hyperresolution(CancellationSource().token)
    first_node = _individual_node(program, source_nodes, first)
    second_node = _individual_node(program, source_nodes, second)
    assert (
        session.nodes.representative(first_node)[0] == session.nodes.representative(second_node)[0]
    )

    scope = b"\x29" * 32
    anonymous_first = owl.AnonymousIndividual(scope, b"first")
    anonymous_second = owl.AnonymousIndividual(scope, b"second")
    anonymous_program, anonymous_session, anonymous_engine, anonymous_nodes, _data = _runtime(
        (
            key,
            owl.ClassAssertion(member, anonymous_first),
            owl.ClassAssertion(member, anonymous_second),
            owl.ObjectPropertyAssertion(key_role, anonymous_first, shared),
            owl.ObjectPropertyAssertion(key_role, anonymous_second, shared),
        )
    )
    anonymous_engine.saturate_hyperresolution(CancellationSource().token)
    left = _individual_node(anonymous_program, anonymous_nodes, anonymous_first)
    right = _individual_node(anonymous_program, anonymous_nodes, anonymous_second)
    assert (
        anonymous_session.nodes.representative(left)[0]
        != anonymous_session.nodes.representative(right)[0]
    )


def test_data_key_inequality_short_circuits_object_equality_choice() -> None:
    member = owl.Class(owl.IRI("urn:test:hyp:data-key-member"))
    key_property = owl.DataProperty(owl.IRI("urn:test:hyp:data-key-property"))
    first = owl.NamedIndividual(owl.IRI("urn:test:hyp:data-key-first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:hyp:data-key-second"))
    key = owl.HasKey(member, owl.CanonicalSet(()), owl.CanonicalSet((key_property,)))
    program, session, engine, source_nodes, _data_nodes = _runtime(
        (
            key,
            owl.ClassAssertion(member, first),
            owl.ClassAssertion(member, second),
            owl.DataPropertyAssertion(key_property, first, owl.Literal("left", owl.XSD_STRING)),
            owl.DataPropertyAssertion(
                key_property,
                second,
                owl.Literal("right", owl.XSD_STRING),
            ),
        )
    )
    engine.saturate_hyperresolution(CancellationSource().token)
    first_node = _individual_node(program, source_nodes, first)
    second_node = _individual_node(program, source_nodes, second)
    assert (
        session.nodes.representative(first_node)[0] != session.nodes.representative(second_node)[0]
    )
    assert not session.disjunctions.records()


def test_functionality_merges_successors_and_inequality_turns_merge_into_clash() -> None:
    role = owl.ObjectProperty(owl.IRI("urn:test:hyp:functional-role"))
    source = owl.NamedIndividual(owl.IRI("urn:test:hyp:functional-source"))
    first = owl.NamedIndividual(owl.IRI("urn:test:hyp:functional-first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:hyp:functional-second"))
    axioms = (
        owl.FunctionalObjectProperty(role),
        owl.ObjectPropertyAssertion(role, source, first),
        owl.ObjectPropertyAssertion(role, source, second),
    )
    program, session, engine, source_nodes, _data_nodes = _runtime(axioms)
    engine.saturate_hyperresolution(CancellationSource().token)
    first_node = _individual_node(program, source_nodes, first)
    second_node = _individual_node(program, source_nodes, second)
    assert (
        session.nodes.representative(first_node)[0] == session.nodes.representative(second_node)[0]
    )

    distinct_axioms = (
        *axioms,
        owl.DifferentIndividuals(owl.CanonicalSet((first, second))),
    )
    _program, distinct_session, distinct_engine, _nodes, _data = _runtime(distinct_axioms)
    distinct_engine.saturate_hyperresolution(CancellationSource().token)
    assert distinct_session.clashes.current is not None
    assert distinct_session.clashes.current.kind is ClashKind.EQUALITY_INEQUALITY
    assert distinct_session.clashes.current.dependency == DependencySet()


def test_qualified_at_most_queues_annotated_equality_without_eager_merge() -> None:
    member = owl.Class(owl.IRI("urn:test:hyp:max-member"))
    filler = owl.Class(owl.IRI("urn:test:hyp:max-filler"))
    role = owl.ObjectProperty(owl.IRI("urn:test:hyp:max-role"))
    root = owl.NamedIndividual(owl.IRI("urn:test:hyp:max-root"))
    first = owl.NamedIndividual(owl.IRI("urn:test:hyp:max-first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:hyp:max-second"))
    program, session, engine, source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(member, owl.ObjectMaxCardinality(1, role, filler)),
            owl.ClassAssertion(member, root),
            owl.ObjectPropertyAssertion(role, root, first),
            owl.ObjectPropertyAssertion(role, root, second),
            owl.ClassAssertion(filler, first),
            owl.ClassAssertion(filler, second),
        )
    )
    engine.saturate_hyperresolution(CancellationSource().token)
    pending = engine.take_pending_annotated_equality()
    assert pending is not None
    assert (
        program.predicates.predicate(pending.atom.predicate_id).kind
        is PredicateKind.ANNOTATED_EQUALITY
    )
    first_node = _individual_node(program, source_nodes, first)
    second_node = _individual_node(program, source_nodes, second)
    assert (
        session.nodes.representative(first_node)[0] != session.nodes.representative(second_node)[0]
    )


def test_at_least_heads_enqueue_one_node_with_all_pending_obligations() -> None:
    source = owl.Class(owl.IRI("urn:test:hyp:source"))
    filler = owl.Class(owl.IRI("urn:test:hyp:filler"))
    role = owl.ObjectProperty(owl.IRI("urn:test:hyp:role"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:hyp:atleast-i"))
    program, session, engine, source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(source, owl.ObjectSomeValuesFrom(role, filler)),
            owl.ClassAssertion(source, individual),
        )
    )
    node = _individual_node(program, source_nodes, individual)
    engine.saturate_hyperresolution(CancellationSource().token)
    pending = session.nodes.get(node).unprocessed_existentials
    assert pending
    assert all(
        program.predicates.predicate(value).kind is PredicateKind.AT_LEAST_OBJECT
        for value in pending
    )
    assert session.existential_candidates.values() == (node,)


def test_positive_and_negative_role_input_derives_dependency_exact_clash() -> None:
    role = owl.ObjectProperty(owl.IRI("urn:test:hyp:clash-role"))
    first = owl.NamedIndividual(owl.IRI("urn:test:hyp:clash-a"))
    second = owl.NamedIndividual(owl.IRI("urn:test:hyp:clash-b"))
    _program, session, _engine, _source_nodes, _data_nodes = _runtime(
        (
            owl.ObjectPropertyAssertion(role, first, second),
            owl.NegativeObjectPropertyAssertion(role, first, second),
        )
    )
    clash = session.clashes.current
    assert clash is not None
    assert clash.dependency == DependencySet()


def test_opposed_data_role_values_materialize_inequality_without_java_clash_manager() -> None:
    role = owl.DataProperty(owl.IRI("urn:test:hyp:data-negation-role"))
    member = owl.Class(owl.IRI("urn:test:hyp:data-negation-member"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:hyp:data-negation-i"))
    left = owl.Literal("left", owl.XSD_STRING)
    right = owl.Literal("right", owl.XSD_STRING)
    program, session, _engine, _source_nodes, data_nodes = _runtime(
        (
            owl.HasKey(member, owl.CanonicalSet(()), owl.CanonicalSet((role,))),
            owl.DataPropertyAssertion(role, individual, left),
            owl.NegativeDataPropertyAssertion(role, individual, right),
        )
    )
    inequality = next(
        value.predicate_id
        for value in program.predicates.predicates
        if value.kind is PredicateKind.INEQUALITY and value.argument_sorts[0].value == "data"
    )
    values = tuple(data_nodes.values())
    assert len(values) == 2
    assert any(
        _has_fact(session, inequality, orientation)
        for orientation in (values, tuple(reversed(values)))
    )
    assert session.clashes.current is None


def test_ground_head_dispatch_rejects_wrong_sorts_and_handles_empty_heads() -> None:
    concept = owl.Class(owl.IRI("urn:test:hyp:sort-concept"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:hyp:sort-i"))
    literal = owl.Literal(
        "1",
        owl.Datatype(owl.IRI("http://www.w3.org/2001/XMLSchema#integer")),
    )
    property = owl.DataProperty(owl.IRI("urn:test:hyp:sort-p"))
    program, session, engine, _source_nodes, data_nodes = _runtime(
        (
            owl.DataPropertyAssertion(property, individual, literal),
            owl.ClassAssertion(concept, individual),
        )
    )
    predicate_id = _concept_predicate(program, concept)
    data = next(iter(data_nodes.values()))
    with pytest.raises(InternalInvariantError, match="wrong node sort"):
        engine.dispatch_ground_atom(
            GroundRuleAtom(predicate_id, (data,)),
            DependencySet(),
        )
    assert engine.apply_ground_head((), DependencySet(), participant_ids=(4,))
    assert session.clashes.current is not None
    assert session.clashes.current.participants == (4,)


def test_public_ground_head_retains_canonicalization_dependency() -> None:
    marker = owl.Class(owl.IRI("urn:test:hyp:path-marker"))
    target = owl.Class(owl.IRI("urn:test:hyp:path-target"))
    first = owl.NamedIndividual(owl.IRI("urn:test:hyp:path-first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:hyp:path-second"))
    witness = owl.NamedIndividual(owl.IRI("urn:test:hyp:path-witness"))
    program, session, engine, source_nodes, _data_nodes = _runtime(
        (
            owl.ClassAssertion(marker, first),
            owl.ClassAssertion(marker, second),
            owl.ClassAssertion(target, witness),
        )
    )
    first_node = _individual_node(program, source_nodes, first)
    second_node = _individual_node(program, source_nodes, second)
    session.push_branch(
        BranchChoiceKind.GROUND_DISJUNCTION,
        (1, 2),
        source_id=7,
        base_dependency=DependencySet(),
    )
    representative = session.merge_nodes(first_node, second_node, DependencySet.of((0,)))
    stale = second_node if representative == first_node else first_node
    target_predicate = _concept_predicate(program, target)
    assert engine.apply_ground_head(
        (GroundRuleAtom(target_predicate, (stale,)),),
        DependencySet(),
    )
    row = next(
        value
        for value in session.extensions.retrieve(
            target_predicate,
            bindings={0: representative},
        )
    )
    assert DependencySet.of((0,)) in row.supports
    session.check_invariants()


def test_ground_disjunction_branches_advance_and_propagate_exhaustion() -> None:
    source = owl.Class(owl.IRI("urn:test:hyp:branch-source"))
    left = owl.Class(owl.IRI("urn:test:hyp:branch-left"))
    right = owl.Class(owl.IRI("urn:test:hyp:branch-right"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:hyp:branch-i"))
    _program, session, engine, _source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(source, owl.ObjectUnionOf(owl.CanonicalSet((left, right)))),
            owl.ClassAssertion(source, individual),
        )
    )
    token = CancellationSource().token
    engine.saturate_hyperresolution(token)
    assert engine.process_next_disjunction(token) is BranchTransition.BRANCHED
    branch = session.branches[0]
    assert branch.next_alternative == 0
    session.install_clash(Clash(ClashKind.EMPTY_HEAD, DependencySet.of((branch.level,)), (11,)))
    assert engine.resolve_clash(token) is BranchTransition.ADVANCED
    assert session.branches[0].next_alternative == 1
    session.install_clash(Clash(ClashKind.EMPTY_HEAD, DependencySet.of((0,)), (12,)))
    assert engine.resolve_clash(token) is BranchTransition.UNSAT
    assert not session.branches
    assert session.clashes.current is not None
    assert session.clashes.current.dependency == DependencySet()


def test_duplicate_satisfied_unit_and_empty_ground_heads_are_canonical() -> None:
    source = owl.Class(owl.IRI("urn:test:hyp:head-source"))
    left = owl.Class(owl.IRI("urn:test:hyp:head-left"))
    right = owl.Class(owl.IRI("urn:test:hyp:head-right"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:hyp:head-i"))
    negative_left_witness = owl.NamedIndividual(owl.IRI("urn:test:hyp:head-neg-left"))
    negative_right_witness = owl.NamedIndividual(owl.IRI("urn:test:hyp:head-neg-right"))
    axioms = (
        owl.SubClassOf(source, owl.ObjectUnionOf(owl.CanonicalSet((left, right)))),
        owl.ClassAssertion(source, individual),
        owl.ClassAssertion(owl.ObjectComplementOf(left), negative_left_witness),
        owl.ClassAssertion(owl.ObjectComplementOf(right), negative_right_witness),
    )
    program, session, engine, source_nodes, _data_nodes = _runtime(axioms)
    node = _individual_node(program, source_nodes, individual)
    left_atom = GroundRuleAtom(_concept_predicate(program, left), (node,))
    right_atom = GroundRuleAtom(_concept_predicate(program, right), (node,))
    assert engine.apply_ground_head((right_atom, left_atom), DependencySet())
    assert not engine.apply_ground_head((left_atom, right_atom), DependencySet())
    assert len(session.disjunctions.records()) == 1
    engine.dispatch_ground_atom(left_atom, DependencySet())
    assert engine.process_next_disjunction(CancellationSource().token) is BranchTransition.SATISFIED

    unit_program, unit_session, unit_engine, unit_nodes, _data = _runtime(axioms)
    unit_node = _individual_node(unit_program, unit_nodes, individual)
    unit_left = GroundRuleAtom(_concept_predicate(unit_program, left), (unit_node,))
    unit_right = GroundRuleAtom(_concept_predicate(unit_program, right), (unit_node,))
    negative_left = GroundRuleAtom(
        _concept_literal_predicate(unit_program, left, PredicateKind.NEGATED_CONCEPT),
        (unit_node,),
    )
    unit_engine.dispatch_ground_atom(negative_left, DependencySet())
    assert unit_engine.apply_ground_head((unit_left, unit_right), DependencySet())
    assert _has_fact(unit_session, unit_right.predicate_id, unit_right.arguments)
    assert not unit_session.disjunctions.records()

    empty_program, empty_session, empty_engine, empty_nodes, _data = _runtime(axioms)
    empty_node = _individual_node(empty_program, empty_nodes, individual)
    empty_left = GroundRuleAtom(_concept_predicate(empty_program, left), (empty_node,))
    empty_right = GroundRuleAtom(_concept_predicate(empty_program, right), (empty_node,))
    for value, kind in (
        (left, PredicateKind.NEGATED_CONCEPT),
        (right, PredicateKind.NEGATED_CONCEPT),
    ):
        empty_engine.dispatch_ground_atom(
            GroundRuleAtom(_concept_literal_predicate(empty_program, value, kind), (empty_node,)),
            DependencySet(),
        )
    assert empty_engine.apply_ground_head((empty_left, empty_right), DependencySet())
    assert empty_session.clashes.current is not None
    assert empty_session.clashes.current.dependency == DependencySet()


def test_dependency_learning_backjumps_over_multiple_irrelevant_newer_branches() -> None:
    first_source = owl.Class(owl.IRI("urn:test:hyp:jump-source-a"))
    second_source = owl.Class(owl.IRI("urn:test:hyp:jump-source-b"))
    third_source = owl.Class(owl.IRI("urn:test:hyp:jump-source-c"))
    choices = tuple(owl.Class(owl.IRI(f"urn:test:hyp:jump-choice:{index}")) for index in range(6))
    individual = owl.NamedIndividual(owl.IRI("urn:test:hyp:jump-i"))
    _program, session, engine, _source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(
                first_source,
                owl.ObjectUnionOf(owl.CanonicalSet(choices[:2])),
            ),
            owl.SubClassOf(
                second_source,
                owl.ObjectUnionOf(owl.CanonicalSet(choices[2:4])),
            ),
            owl.SubClassOf(
                third_source,
                owl.ObjectUnionOf(owl.CanonicalSet(choices[4:])),
            ),
            owl.ClassAssertion(first_source, individual),
            owl.ClassAssertion(second_source, individual),
            owl.ClassAssertion(third_source, individual),
        )
    )
    token = CancellationSource().token
    engine.saturate_hyperresolution(token)
    assert engine.process_next_disjunction(token) is BranchTransition.BRANCHED
    assert engine.process_next_disjunction(token) is BranchTransition.BRANCHED
    assert engine.process_next_disjunction(token) is BranchTransition.BRANCHED
    assert len(session.branches) == 3
    session.install_clash(Clash(ClashKind.EMPTY_HEAD, DependencySet.of((0,)), (21,)))
    assert engine.resolve_clash(token) is BranchTransition.ADVANCED
    assert len(session.branches) == 1
    assert session.branches[0].next_alternative == 1


def test_chronological_oracle_keeps_an_irrelevant_newer_branch() -> None:
    first_source = owl.Class(owl.IRI("urn:test:hyp:chron-source-a"))
    second_source = owl.Class(owl.IRI("urn:test:hyp:chron-source-b"))
    choices = tuple(owl.Class(owl.IRI(f"urn:test:hyp:chron-choice:{index}")) for index in range(4))
    individual = owl.NamedIndividual(owl.IRI("urn:test:hyp:chron-i"))
    _program, session, engine, _source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(first_source, owl.ObjectUnionOf(owl.CanonicalSet(choices[:2]))),
            owl.SubClassOf(second_source, owl.ObjectUnionOf(owl.CanonicalSet(choices[2:]))),
            owl.ClassAssertion(first_source, individual),
            owl.ClassAssertion(second_source, individual),
        ),
        disjunction_learning=False,
    )
    token = CancellationSource().token
    engine.saturate_hyperresolution(token)
    engine.process_next_disjunction(token)
    engine.process_next_disjunction(token)
    session.install_clash(Clash(ClashKind.EMPTY_HEAD, DependencySet.of((0,)), (31,)))
    assert engine.resolve_clash(token) is BranchTransition.ADVANCED
    assert len(session.branches) == 2
    assert session.branches[1].next_alternative == 1


def test_cancellation_inside_delta_processing_restores_operation_root_and_reuses_engine() -> None:
    source = owl.Class(owl.IRI("urn:test:hyp:cancel-source"))
    target = owl.Class(owl.IRI("urn:test:hyp:cancel-target"))
    individuals = tuple(
        owl.NamedIndividual(owl.IRI(f"urn:test:hyp:cancel-i:{index}")) for index in range(6)
    )
    program, session, engine, source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(source, target),
            *(owl.ClassAssertion(source, value) for value in individuals),
        ),
        limits=RuleLimits(cancellation_interval=1),
    )
    baseline = session.canonical_snapshot()
    token = _CancelAfterMutation(session, session.trail.length + 1)
    with pytest.raises(ReasonerInterruptedError, match="injected join cancellation"):
        engine.apply_next_delta(token)
    assert session.canonical_snapshot() == baseline
    assert session.clashes.current is None

    engine.saturate_hyperresolution(CancellationSource().token)
    predicate = _concept_predicate(program, target)
    assert all(
        _has_fact(session, predicate, (_individual_node(program, source_nodes, value),))
        for value in individuals
    )


def test_cancellation_inside_branch_transition_restores_operation_root() -> None:
    source = owl.Class(owl.IRI("urn:test:hyp:branch-cancel-source"))
    left = owl.Class(owl.IRI("urn:test:hyp:branch-cancel-left"))
    right = owl.Class(owl.IRI("urn:test:hyp:branch-cancel-right"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:hyp:branch-cancel-i"))
    _program, session, engine, _source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(source, owl.ObjectUnionOf(owl.CanonicalSet((left, right)))),
            owl.ClassAssertion(source, individual),
        )
    )
    operation_root = session.canonical_snapshot()
    engine.saturate_hyperresolution(CancellationSource().token)
    token = _CancelAfterMutation(session, session.trail.length)
    with pytest.raises(ReasonerInterruptedError, match="injected join cancellation"):
        engine.process_next_disjunction(token)
    assert session.canonical_snapshot() == operation_root
    assert not session.branches

    live_token = CancellationSource().token
    engine.saturate_hyperresolution(live_token)
    assert engine.process_next_disjunction(live_token) is BranchTransition.BRANCHED


def _solve_branch_case(*, learning: bool, both_inconsistent: bool) -> bool:
    source = owl.Class(owl.IRI("urn:test:hyp:answer-source"))
    left = owl.Class(owl.IRI("urn:test:hyp:answer-left"))
    right = owl.Class(owl.IRI("urn:test:hyp:answer-right"))
    witness = owl.Class(owl.IRI("urn:test:hyp:answer-witness"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:hyp:answer-i"))
    axioms: list[owl.AxiomNode] = [
        owl.SubClassOf(source, owl.ObjectUnionOf(owl.CanonicalSet((left, right)))),
        owl.SubClassOf(left, witness),
        owl.SubClassOf(left, owl.ObjectComplementOf(witness)),
        owl.ClassAssertion(source, individual),
    ]
    if both_inconsistent:
        axioms.extend(
            (
                owl.SubClassOf(right, witness),
                owl.SubClassOf(right, owl.ObjectComplementOf(witness)),
            )
        )
    _program, session, engine, _source_nodes, _data_nodes = _runtime(
        axioms,
        disjunction_learning=learning,
    )
    token = CancellationSource().token
    for _step in range(64):
        engine.saturate_hyperresolution(token)
        if session.clashes.current is not None:
            if engine.resolve_clash(token) is BranchTransition.UNSAT:
                return False
            continue
        transition = engine.process_next_disjunction(token)
        if transition is BranchTransition.NO_WORK:
            return True
    raise AssertionError("branch oracle did not terminate")


@pytest.mark.parametrize("both_inconsistent, expected", ((False, True), (True, False)))
def test_dependency_learning_and_chronological_oracle_return_same_answer(
    both_inconsistent: bool,
    expected: bool,
) -> None:
    assert _solve_branch_case(learning=True, both_inconsistent=both_inconsistent) is expected
    assert _solve_branch_case(learning=False, both_inconsistent=both_inconsistent) is expected


def test_match_resource_limit_rolls_back_partially_derived_generation() -> None:
    source = owl.Class(owl.IRI("urn:test:hyp:limit-source"))
    target = owl.Class(owl.IRI("urn:test:hyp:limit-target"))
    individuals = tuple(
        owl.NamedIndividual(owl.IRI(f"urn:test:hyp:limit-i:{index}")) for index in range(3)
    )
    _program, session, engine, _source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(source, target),
            *(owl.ClassAssertion(source, value) for value in individuals),
        ),
        limits=RuleLimits(max_matches_per_generation=1),
    )
    baseline = session.canonical_snapshot()
    with pytest.raises(ResourceLimitError) as caught:
        engine.apply_next_delta(CancellationSource().token)
    assert caught.value.limit == "max_matches_per_generation"
    assert session.canonical_snapshot() == baseline
    session.check_invariants()


def test_language_neutral_wp09_trace_fixture() -> None:
    trace_path = Path(__file__).parents[2] / "data" / "hyperresolution" / "trace-v1.json"
    payload = json.loads(trace_path.read_text(encoding="utf-8"))
    assert payload["magic"] == "PYHERMIT-HYPERRESOLUTION-TRACE"
    assert payload["version"] == 1
    for case in payload["cases"]:
        classes = {
            name: owl.Class(owl.IRI(f"urn:trace:wp09:class:{name}")) for name in case["classes"]
        }
        individuals = {
            name: owl.NamedIndividual(owl.IRI(f"urn:trace:wp09:individual:{name}"))
            for name in case["individuals"]
        }
        axioms: list[owl.AxiomNode] = []
        for specification in case["axioms"]:
            if specification["kind"] == "subclass":
                axioms.append(
                    owl.SubClassOf(
                        classes[specification["sub"]],
                        classes[specification["super"]],
                    )
                )
            elif specification["kind"] == "class_assertion":
                axioms.append(
                    owl.ClassAssertion(
                        classes[specification["class"]],
                        individuals[specification["individual"]],
                    )
                )
            else:
                raise AssertionError(f"unknown trace axiom {specification['kind']}")
        program, session, engine, source_nodes, _data_nodes = _runtime(axioms)
        token = CancellationSource().token
        for operation in case["operations"]:
            kind = operation["kind"]
            if kind == "saturate":
                observed = engine.saturate_hyperresolution(token)
                assert observed >= operation["expected_minimum"]
            elif kind == "apply_delta":
                assert engine.apply_next_delta(token) == operation["expected"]
            elif kind == "apply_head":
                atoms = tuple(
                    GroundRuleAtom(
                        _concept_predicate(program, classes[class_name]),
                        (_individual_node(program, source_nodes, individuals[individual_name]),),
                    )
                    for class_name, individual_name in operation["atoms"]
                )
                assert engine.apply_ground_head(atoms, DependencySet())
            elif kind == "process_disjunction":
                assert engine.process_next_disjunction(token).value == operation["expected"]
            elif kind == "install_clash":
                session.install_clash(
                    Clash(
                        ClashKind.EMPTY_HEAD,
                        DependencySet.of(operation["dependency"]),
                        (operation["participant"],),
                    )
                )
            elif kind == "resolve_clash":
                assert engine.resolve_clash(token).value == operation["expected"]
            else:
                raise AssertionError(f"unknown trace operation {kind}")
            session.check_invariants()
        for class_name, individual_name in case.get("expected_facts", ()):
            assert _has_fact(
                session,
                _concept_predicate(program, classes[class_name]),
                (_individual_node(program, source_nodes, individuals[individual_name]),),
            )
