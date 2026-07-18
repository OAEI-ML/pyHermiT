# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# SPDX-License-Identifier: LGPL-3.0-or-later
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

from __future__ import annotations

from collections.abc import Iterable

import pyowl_core.model as owl
import pytest

from pyhermit.backends.python.existentials import (
    ExistentialExpansionManager,
    ExpansionLimits,
    ExpansionStatus,
    ExpansionStrategy,
)
from pyhermit.backends.python.merging import MergingManager
from pyhermit.backends.python.rules import (
    BranchTransition,
    GroundRuleAtom,
    HyperresolutionEngine,
)
from pyhermit.backends.python.state import (
    BranchChoiceKind,
    ClashKind,
    DependencySet,
    NodeHandle,
    NodeKind,
    NodeLifecycle,
    TableauSession,
)
from pyhermit.backends.python.state.extensions import FactRow
from pyhermit.clauses import (
    ClauseProgram,
    Predicate,
    PredicateKind,
    SymbolKind,
    compile_normalized,
)
from pyhermit.events import CancellationSource, CancellationToken
from pyhermit.exceptions import ReasonerInterruptedError, ResourceLimitError
from pyhermit.normalize import normalize_axioms

FINGERPRINT = "a7" * 32


def _runtime(
    axioms: Iterable[owl.AxiomNode],
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
    )
    engine.initialize(CancellationSource().token)
    engine.saturate_hyperresolution(CancellationSource().token)
    session.begin_operation()
    return program, session, engine, source_nodes, data_nodes


def _symbol_id(program: ClauseProgram, kind: SymbolKind, value: owl.StructuralNode) -> int:
    key = value.canonical_bytes().hex()
    return next(
        identifier
        for identifier, candidate in enumerate(program.symbols.domain(kind).values)
        if candidate.key_hex == key
    )


def _individual_node(
    program: ClauseProgram,
    nodes: dict[int, NodeHandle],
    value: owl.Individual,
) -> NodeHandle:
    return nodes[_symbol_id(program, SymbolKind.INDIVIDUAL, value)]


def _predicate(program: ClauseProgram, kind: PredicateKind, *, role_id: int | None = None) -> int:
    return next(
        value.predicate_id
        for value in program.predicates.predicates
        if value.kind is kind and (role_id is None or value.role_id == role_id)
    )


def _at_least(program: ClauseProgram, kind: PredicateKind) -> Predicate:
    return next(value for value in program.predicates.predicates if value.kind is kind)


def _row(
    session: TableauSession,
    predicate_id: int,
    arguments: tuple[NodeHandle, ...],
) -> FactRow:
    rows = tuple(
        session.extensions.retrieve(
            predicate_id,
            bindings={index: value for index, value in enumerate(arguments)},
        )
    )
    assert len(rows) == 1
    return rows[0]


def _fact_predicate(
    program: ClauseProgram,
    session: TableauSession,
    kind: PredicateKind,
    arguments: tuple[NodeHandle, ...],
) -> int:
    return next(
        row.key.predicate_id
        for row in session.extensions.active_rows()
        if row.key.arguments == arguments
        and program.predicates.predicate(row.key.predicate_id).kind is kind
    )


class _CancelAfterMutation(CancellationToken):
    __slots__ = ("_baseline", "_session")

    def __init__(self, session: TableauSession, baseline: int) -> None:
        super().__init__()
        self._session = session
        self._baseline = baseline

    def check(self) -> None:
        if self._session.trail.length > self._baseline:
            raise ReasonerInterruptedError("injected expansion cancellation")
        super().check()


def test_object_min_cardinality_creates_core_distinct_tree_witnesses() -> None:
    source = owl.Class(owl.IRI("urn:test:expand:source"))
    filler = owl.Class(owl.IRI("urn:test:expand:filler"))
    role = owl.ObjectProperty(owl.IRI("urn:test:expand:role"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:expand:root"))
    program, session, engine, source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(source, owl.ObjectMinCardinality(2, role, filler)),
            owl.ClassAssertion(source, individual),
        )
    )
    root = _individual_node(program, source_nodes, individual)
    obligation = _at_least(program, PredicateKind.AT_LEAST_OBJECT)
    result = ExistentialExpansionManager(session, engine).process_next(CancellationSource().token)
    assert result.status is ExpansionStatus.EXPANDED
    assert result.root == root
    assert result.existential_id == obligation.predicate_id
    assert len(result.witnesses) == 2
    assert all(session.nodes.get(value).parent == root for value in result.witnesses)
    role_predicate = _predicate(
        program,
        PredicateKind.OBJECT_ROLE,
        role_id=obligation.role_id,
    )
    inequality = _predicate(program, PredicateKind.INEQUALITY)
    assert obligation.filler_predicate_id is not None
    for witness in result.witnesses:
        assert _row(session, role_predicate, (root, witness)).core
        assert _row(session, obligation.filler_predicate_id, (witness,)).core
    left, right = sorted(result.witnesses, key=lambda value: session.nodes.get(value).creation_id)
    assert _row(session, inequality, (left, right)).core
    assert obligation.predicate_id not in session.nodes.get(root).unprocessed_existentials
    session.check_invariants()


def test_canonical_distinct_count_requires_inequality_and_avoids_duplicate_expansion() -> None:
    source = owl.Class(owl.IRI("urn:test:count:source"))
    filler = owl.Class(owl.IRI("urn:test:count:filler"))
    role = owl.ObjectProperty(owl.IRI("urn:test:count:role"))
    root_value = owl.NamedIndividual(owl.IRI("urn:test:count:root"))
    first = owl.NamedIndividual(owl.IRI("urn:test:count:first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:count:second"))
    axioms = (
        owl.SubClassOf(source, owl.ObjectMinCardinality(2, role, filler)),
        owl.ClassAssertion(source, root_value),
        owl.ObjectPropertyAssertion(role, root_value, first),
        owl.ObjectPropertyAssertion(role, root_value, second),
        owl.ClassAssertion(filler, first),
        owl.ClassAssertion(filler, second),
    )
    _program, session, engine, _source_nodes, _data_nodes = _runtime(axioms)
    result = ExistentialExpansionManager(session, engine).process_next(CancellationSource().token)
    assert result.status is ExpansionStatus.EXPANDED
    assert len(result.witnesses) == 2
    assert (
        ExistentialExpansionManager(session, engine).process_next(CancellationSource().token).status
        is ExpansionStatus.NO_WORK
    )

    distinct_program, distinct_session, distinct_engine, _nodes, _data = _runtime(
        (*axioms, owl.DifferentIndividuals(owl.CanonicalSet((first, second))))
    )
    satisfied = ExistentialExpansionManager(distinct_session, distinct_engine).process_next(
        CancellationSource().token
    )
    assert satisfied.status is ExpansionStatus.SATISFIED
    assert not satisfied.witnesses
    distinct_session.check_invariants()
    assert distinct_program.predicates.predicates


def test_data_cardinality_uses_fixed_value_difference_without_expansion() -> None:
    source = owl.Class(owl.IRI("urn:test:data-count:source"))
    role = owl.DataProperty(owl.IRI("urn:test:data-count:role"))
    root_value = owl.NamedIndividual(owl.IRI("urn:test:data-count:root"))
    first = owl.Literal("first", owl.XSD_STRING)
    second = owl.Literal("second", owl.XSD_STRING)
    program, session, engine, _source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(source, owl.DataMinCardinality(2, role, owl.XSD_STRING)),
            owl.ClassAssertion(source, root_value),
            owl.DataPropertyAssertion(role, root_value, first),
            owl.DataPropertyAssertion(role, root_value, second),
        )
    )
    result = ExistentialExpansionManager(session, engine).process_next(CancellationSource().token)
    assert result.status is ExpansionStatus.SATISFIED
    assert not result.witnesses
    assert program.expressivity.datatypes


def test_nary_data_existential_creates_one_value_per_property_and_nary_filler() -> None:
    source = owl.Class(owl.IRI("urn:test:nary-data:source"))
    first_role = owl.DataProperty(owl.IRI("urn:test:nary-data:first"))
    second_role = owl.DataProperty(owl.IRI("urn:test:nary-data:second"))
    root_value = owl.NamedIndividual(owl.IRI("urn:test:nary-data:root"))
    program, session, engine, _source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(
                source,
                owl.DataSomeValuesFrom((first_role, second_role), owl.RDFS_LITERAL),
            ),
            owl.ClassAssertion(source, root_value),
        )
    )
    obligation = _at_least(program, PredicateKind.AT_LEAST_DATA)
    result = ExistentialExpansionManager(session, engine).process_next(CancellationSource().token)
    assert result.status is ExpansionStatus.EXPANDED
    assert result.root is not None
    assert len(result.witnesses) == 2
    assert obligation.filler_predicate_id is not None
    assert _row(session, obligation.filler_predicate_id, result.witnesses).core
    for role_id, witness in zip(obligation.annotation, result.witnesses, strict=True):
        role_predicate = _predicate(program, PredicateKind.DATA_ROLE, role_id=role_id)
        assert _row(session, role_predicate, (result.root, witness)).core
    session.check_invariants()


def test_inverse_and_top_object_roles_attach_witnesses_without_top_materialization() -> None:
    source = owl.Class(owl.IRI("urn:test:role-expand:source"))
    filler = owl.Class(owl.IRI("urn:test:role-expand:filler"))
    role = owl.ObjectProperty(owl.IRI("urn:test:role-expand:role"))
    root_value = owl.NamedIndividual(owl.IRI("urn:test:role-expand:root"))
    inverse_program, inverse_session, inverse_engine, _nodes, _data = _runtime(
        (
            owl.SubClassOf(
                source,
                owl.ObjectSomeValuesFrom(owl.ObjectInverseOf(role), filler),
            ),
            owl.ClassAssertion(source, root_value),
        )
    )
    inverse_obligation = _at_least(inverse_program, PredicateKind.AT_LEAST_OBJECT)
    inverse_result = ExistentialExpansionManager(inverse_session, inverse_engine).process_next(
        CancellationSource().token
    )
    assert inverse_result.root is not None
    inverse_role = _predicate(
        inverse_program,
        PredicateKind.OBJECT_ROLE,
        role_id=inverse_obligation.role_id,
    )
    inverse_witness = inverse_result.witnesses[0]
    assert _row(inverse_session, inverse_role, (inverse_result.root, inverse_witness)).core
    inverse_engine.saturate_hyperresolution(CancellationSource().token)
    assert inverse_obligation.role_id is not None
    forward_id = inverse_program.role_model.inverse_role_ids[inverse_obligation.role_id]
    forward_role = _predicate(
        inverse_program,
        PredicateKind.OBJECT_ROLE,
        role_id=forward_id,
    )
    assert _row(inverse_session, forward_role, (inverse_witness, inverse_result.root))

    top_program, top_session, top_engine, _nodes, _data = _runtime(
        (
            owl.SubClassOf(
                source,
                owl.ObjectSomeValuesFrom(owl.OWL_TOP_OBJECT_PROPERTY, filler),
            ),
            owl.ClassAssertion(source, root_value),
        )
    )
    top_obligation = _at_least(top_program, PredicateKind.AT_LEAST_OBJECT)
    top_result = ExistentialExpansionManager(top_session, top_engine).process_next(
        CancellationSource().token
    )
    assert top_result.root is not None
    assert top_obligation.role_id == top_program.role_model.top_object_role_id
    top_role = _predicate(
        top_program,
        PredicateKind.OBJECT_ROLE,
        role_id=top_program.role_model.top_object_role_id,
    )
    assert not tuple(top_session.extensions.retrieve(top_role))
    assert top_obligation.filler_predicate_id is not None
    assert _row(top_session, top_obligation.filler_predicate_id, top_result.witnesses)


def test_blocked_candidate_is_deferred_until_unblocked() -> None:
    source = owl.Class(owl.IRI("urn:test:blocked-expand:source"))
    filler = owl.Class(owl.IRI("urn:test:blocked-expand:filler"))
    role = owl.ObjectProperty(owl.IRI("urn:test:blocked-expand:role"))
    program, session, engine, _nodes, _data = _runtime(
        (owl.SubClassOf(source, owl.ObjectSomeValuesFrom(role, filler)),)
    )
    root = session.create_node(NodeKind.ROOT)
    child = session.create_node(NodeKind.TREE, parent=root)
    engine.register_node(root)
    engine.register_node(child)
    obligation = _at_least(program, PredicateKind.AT_LEAST_OBJECT)
    engine.dispatch_ground_atom(
        GroundRuleAtom(obligation.predicate_id, (child,)),
        DependencySet(),
    )
    session.nodes.set_blocked(child, root, directly=True)
    manager = ExistentialExpansionManager(session, engine)
    assert manager.process_next(CancellationSource().token).status is ExpansionStatus.BLOCKED
    assert session.existential_candidates.values() == (child,)
    session.nodes.set_blocked(child, None, directly=False)
    result = manager.process_next(CancellationSource().token)
    assert result.status is ExpansionStatus.EXPANDED
    assert result.root == child


def test_expansion_limit_and_cancellation_restore_the_operation_root() -> None:
    source = owl.Class(owl.IRI("urn:test:cancel:source"))
    filler = owl.Class(owl.IRI("urn:test:cancel:filler"))
    role = owl.ObjectProperty(owl.IRI("urn:test:cancel:role"))
    individual = owl.NamedIndividual(owl.IRI("urn:test:cancel:root"))
    _program, session, engine, _source_nodes, _data_nodes = _runtime(
        (
            owl.SubClassOf(source, owl.ObjectMinCardinality(2, role, filler)),
            owl.ClassAssertion(source, individual),
        )
    )
    with pytest.raises(ResourceLimitError, match="witness limit"):
        ExistentialExpansionManager(
            session,
            engine,
            limits=ExpansionLimits(max_witnesses_per_obligation=1),
        ).process_next(CancellationSource().token)

    before = session.canonical_snapshot()
    baseline = session.trail.length
    with pytest.raises(ReasonerInterruptedError, match="injected expansion cancellation"):
        ExistentialExpansionManager(session, engine).process_next(
            _CancelAfterMutation(session, baseline)
        )
    assert session.canonical_snapshot() == before
    assert session.clashes.current is None


def test_individual_reuse_shares_public_atomic_fillers_while_creation_order_does_not() -> None:
    source = owl.Class(owl.IRI("urn:test:reuse:source"))
    filler = owl.Class(owl.IRI("urn:test:reuse:filler"))
    role = owl.ObjectProperty(owl.IRI("urn:test:reuse:role"))
    first = owl.NamedIndividual(owl.IRI("urn:test:reuse:0-root"))
    second = owl.NamedIndividual(owl.IRI("urn:test:reuse:1-root"))
    axioms = (
        owl.SubClassOf(source, owl.ObjectSomeValuesFrom(role, filler)),
        owl.ClassAssertion(source, first),
        owl.ClassAssertion(source, second),
    )

    _program, plain_session, plain_engine, _nodes, _data = _runtime(axioms)
    plain = ExistentialExpansionManager(plain_session, plain_engine)
    plain_first = plain.process_next(CancellationSource().token)
    plain_second = plain.process_next(CancellationSource().token)
    assert plain_first.witnesses != plain_second.witnesses
    assert all(
        plain_session.nodes.get(value).kind is NodeKind.TREE
        for value in (*plain_first.witnesses, *plain_second.witnesses)
    )

    _program, reuse_session, reuse_engine, _nodes, _data = _runtime(axioms)
    reuse = ExistentialExpansionManager(
        reuse_session,
        reuse_engine,
        strategy=ExpansionStrategy.INDIVIDUAL_REUSE,
    )
    reused_first = reuse.process_next(CancellationSource().token)
    reused_second = reuse.process_next(CancellationSource().token)
    assert reused_first.witnesses == reused_second.witnesses
    assert reuse_session.nodes.get(reused_first.witnesses[0]).kind is NodeKind.NI
    assert len(reuse_session.branches) == 2
    assert all(reuse.owns_branch(value) for value in reuse_session.branches)
    reuse_session.check_invariants()


def test_individual_reuse_conflict_backtracks_to_a_fresh_tree_witness() -> None:
    first_source = owl.Class(owl.IRI("urn:test:reuse-fallback:first-source"))
    second_source = owl.Class(owl.IRI("urn:test:reuse-fallback:second-source"))
    filler = owl.Class(owl.IRI("urn:test:reuse-fallback:filler"))
    marker = owl.Class(owl.IRI("urn:test:reuse-fallback:marker"))
    first_role = owl.ObjectProperty(owl.IRI("urn:test:reuse-fallback:first-role"))
    second_role = owl.ObjectProperty(owl.IRI("urn:test:reuse-fallback:second-role"))
    first = owl.NamedIndividual(owl.IRI("urn:test:reuse-fallback:0-root"))
    second = owl.NamedIndividual(owl.IRI("urn:test:reuse-fallback:1-root"))
    _program, session, engine, _nodes, _data = _runtime(
        (
            owl.SubClassOf(first_source, owl.ObjectSomeValuesFrom(first_role, filler)),
            owl.SubClassOf(first_source, owl.ObjectAllValuesFrom(first_role, marker)),
            owl.SubClassOf(second_source, owl.ObjectSomeValuesFrom(second_role, filler)),
            owl.SubClassOf(
                second_source,
                owl.ObjectAllValuesFrom(second_role, owl.ObjectComplementOf(marker)),
            ),
            owl.ClassAssertion(first_source, first),
            owl.ClassAssertion(second_source, second),
        )
    )
    manager = ExistentialExpansionManager(
        session,
        engine,
        strategy=ExpansionStrategy.INDIVIDUAL_REUSE,
    )
    first_result = manager.process_next(CancellationSource().token)
    assert session.nodes.get(first_result.witnesses[0]).kind is NodeKind.NI
    engine.saturate_hyperresolution(CancellationSource().token)
    first_clash = session.clashes.current
    assert first_clash is None

    second_result = manager.process_next(CancellationSource().token)
    assert second_result.witnesses == first_result.witnesses
    engine.saturate_hyperresolution(CancellationSource().token)
    reuse_clash = session.clashes.current
    assert reuse_clash is not None
    target = reuse_clash.dependency.maximum
    assert target is not None
    assert manager.owns_branch(session.branches[target])

    assert manager.resolve_clash(CancellationSource().token) is BranchTransition.ADVANCED
    assert session.clashes.current is None
    fresh = max(
        session.nodes.active_handles(),
        key=lambda value: session.nodes.get(value).creation_id,
    )
    assert session.nodes.get(fresh).kind is NodeKind.TREE
    engine.saturate_hyperresolution(CancellationSource().token)
    assert session.clashes.current is None
    session.check_invariants()


def test_merge_copies_incident_rows_prunes_descendants_and_rolls_back_exactly() -> None:
    role = owl.ObjectProperty(owl.IRI("urn:test:merge:role"))
    root_value = owl.NamedIndividual(owl.IRI("urn:test:merge:root"))
    other_value = owl.NamedIndividual(owl.IRI("urn:test:merge:other"))
    program, session, engine, source_nodes, _data_nodes = _runtime(
        (owl.ObjectPropertyAssertion(role, other_value, root_value),)
    )
    root = _individual_node(program, source_nodes, root_value)
    other = _individual_node(program, source_nodes, other_value)
    source = session.create_node(NodeKind.TREE, parent=root)
    child = session.create_node(NodeKind.TREE, parent=source)
    engine.register_node(source)
    engine.register_node(child)
    role_predicate = _fact_predicate(
        program,
        session,
        PredicateKind.OBJECT_ROLE,
        (other, root),
    )
    for arguments in ((source, other), (other, source), (source, source)):
        engine.dispatch_ground_atom(
            GroundRuleAtom(role_predicate, arguments),
            DependencySet(),
            core=True,
        )
    session.nodes.mark_existential(source, 313, pending=True)
    branch = session.push_branch(
        BranchChoiceKind.MERGE,
        (0, 1),
        source_id=17,
        base_dependency=DependencySet(),
    )
    before = session.canonical_snapshot()
    result = MergingManager(session, engine).merge(
        root,
        source,
        DependencySet.of((branch.level,)),
        CancellationSource().token,
    )
    assert result.representative == root
    assert result.merged == source
    assert child in result.pruned
    assert session.nodes.get(source).lifecycle is NodeLifecycle.MERGED
    assert session.nodes.get(child).lifecycle is NodeLifecycle.PRUNED
    copied = _row(session, role_predicate, (root, other))
    assert copied.core
    assert DependencySet.of((branch.level,)) in copied.supports
    assert _row(session, role_predicate, (other, root))
    assert _row(session, role_predicate, (root, root)).core
    assert 313 in session.nodes.get(root).unprocessed_existentials
    session.backtrack_to(branch.level)
    assert session.canonical_snapshot() == before


def test_explicit_inequality_blocks_merge_with_dependency_exact_clash() -> None:
    first = owl.NamedIndividual(owl.IRI("urn:test:merge-neq:first"))
    second = owl.NamedIndividual(owl.IRI("urn:test:merge-neq:second"))
    program, session, engine, source_nodes, _data_nodes = _runtime(
        (owl.DifferentIndividuals(owl.CanonicalSet((first, second))),)
    )
    left = _individual_node(program, source_nodes, first)
    right = _individual_node(program, source_nodes, second)
    branch = session.push_branch(
        BranchChoiceKind.MERGE,
        (0, 1),
        source_id=19,
        base_dependency=DependencySet(),
    )
    result = MergingManager(session, engine).merge(
        left,
        right,
        DependencySet.of((branch.level,)),
        CancellationSource().token,
    )
    assert result.clashed
    assert session.nodes.representative(left)[0] != session.nodes.representative(right)[0]
    assert session.clashes.current is not None
    assert session.clashes.current.kind is ClashKind.EQUALITY_INEQUALITY
    assert session.clashes.current.dependency == DependencySet.of((branch.level,))


def test_merge_redispatch_detects_positive_negative_role_clash() -> None:
    role = owl.ObjectProperty(owl.IRI("urn:test:merge-opposite:role"))
    root_value = owl.NamedIndividual(owl.IRI("urn:test:merge-opposite:root"))
    other_value = owl.NamedIndividual(owl.IRI("urn:test:merge-opposite:other"))
    program, session, engine, source_nodes, _data_nodes = _runtime(
        (owl.NegativeObjectPropertyAssertion(role, root_value, other_value),)
    )
    root = _individual_node(program, source_nodes, root_value)
    other = _individual_node(program, source_nodes, other_value)
    source = session.create_node(NodeKind.TREE, parent=root)
    engine.register_node(source)
    negative = _fact_predicate(
        program,
        session,
        PredicateKind.NEGATED_OBJECT_ROLE,
        (root, other),
    )
    role_id = program.predicates.predicate(negative).role_id
    positive = _predicate(program, PredicateKind.OBJECT_ROLE, role_id=role_id)
    engine.dispatch_ground_atom(
        GroundRuleAtom(positive, (source, other)),
        DependencySet(),
        core=True,
    )
    branch = session.push_branch(
        BranchChoiceKind.MERGE,
        (0, 1),
        source_id=23,
        base_dependency=DependencySet(),
    )
    result = MergingManager(session, engine).merge(
        root,
        source,
        DependencySet.of((branch.level,)),
        CancellationSource().token,
    )
    assert result.clashed
    assert result.merged == source
    clash = session.clashes.current
    assert clash is not None
    assert clash.kind is ClashKind.POSITIVE_NEGATIVE_ATOM
    assert clash.dependency == DependencySet.of((branch.level,))
