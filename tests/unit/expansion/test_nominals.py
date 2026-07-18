# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# SPDX-License-Identifier: LGPL-3.0-or-later
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

from __future__ import annotations

from dataclasses import dataclass

import pyowl_core.model as owl
import pytest

from pyhermit.backends.python.merging import MergingManager
from pyhermit.backends.python.nominals import (
    NominalEvent,
    NominalIntroductionManager,
    NominalLimits,
)
from pyhermit.backends.python.rules import (
    BranchTransition,
    GroundRuleAtom,
    HyperresolutionEngine,
)
from pyhermit.backends.python.state import (
    BranchChoiceKind,
    Clash,
    ClashKind,
    DependencySet,
    NodeHandle,
    NodeKind,
    NodeLifecycle,
    TableauSession,
)
from pyhermit.clauses import ClauseProgram, Predicate, PredicateKind, compile_normalized
from pyhermit.events import CancellationSource, CancellationToken
from pyhermit.exceptions import ReasonerInterruptedError, ResourceLimitError
from pyhermit.normalize import normalize_axioms

FINGERPRINT = "a7" * 32


@dataclass(slots=True)
class _Runtime:
    program: ClauseProgram
    session: TableauSession
    engine: HyperresolutionEngine
    merger: MergingManager
    manager: NominalIntroductionManager
    annotated: tuple[Predicate, ...]

    def node(
        self,
        kind: NodeKind,
        *,
        parent: NodeHandle | None = None,
        named: bool = False,
    ) -> NodeHandle:
        source_id = 10_000 + len(self.session.nodes.existing_nodes()) if named else None
        handle = self.session.create_node(
            kind,
            parent=parent,
            is_owl_named_individual=named,
            source_individual_id=source_id,
        )
        self.engine.register_node(handle)
        return handle

    def annotation(self, cardinality: int, index: int = 0) -> Predicate:
        matches = tuple(value for value in self.annotated if value.cardinality == cardinality)
        return matches[index]

    def queue(
        self,
        predicate: Predicate,
        first: NodeHandle,
        second: NodeHandle,
        root: NodeHandle,
        dependency: DependencySet | None = None,
    ) -> None:
        self.engine.dispatch_ground_atom(
            GroundRuleAtom(predicate.predicate_id, (first, second, root)),
            self.session.dependencies.empty if dependency is None else dependency,
        )


def _runtime(*, limits: NominalLimits | None = None) -> _Runtime:
    filler = owl.Class(owl.IRI("urn:test:ni:filler"))
    first_source = owl.Class(owl.IRI("urn:test:ni:first-source"))
    second_source = owl.Class(owl.IRI("urn:test:ni:second-source"))
    third_source = owl.Class(owl.IRI("urn:test:ni:third-source"))
    first_role = owl.ObjectProperty(owl.IRI("urn:test:ni:first-role"))
    second_role = owl.ObjectProperty(owl.IRI("urn:test:ni:second-role"))
    program = compile_normalized(
        normalize_axioms(
            (
                owl.SubClassOf(
                    first_source,
                    owl.ObjectMaxCardinality(1, first_role, filler),
                ),
                owl.SubClassOf(
                    second_source,
                    owl.ObjectMaxCardinality(2, first_role, filler),
                ),
                owl.SubClassOf(
                    third_source,
                    owl.ObjectMaxCardinality(1, second_role, filler),
                ),
            ),
            logical_fingerprint=FINGERPRINT,
        )
    )
    session = TableauSession()
    engine = HyperresolutionEngine(program, session, source_nodes={}, data_nodes={})
    engine.initialize(CancellationSource().token)
    merger = MergingManager(session, engine)
    manager = NominalIntroductionManager(session, engine, merger, limits=limits)
    annotated = tuple(
        value
        for value in program.predicates.predicates
        if value.kind is PredicateKind.ANNOTATED_EQUALITY
    )
    assert tuple(value.cardinality for value in annotated).count(1) == 2
    assert tuple(value.cardinality for value in annotated).count(2) == 1
    return _Runtime(program, session, engine, merger, manager, annotated)


def _token() -> CancellationToken:
    return CancellationSource().token


def test_can_forget_covers_each_formal_side_condition_and_target_selection() -> None:
    runtime = _runtime()
    root = runtime.node(NodeKind.NI)
    other_root = runtime.node(NodeKind.ROOT)
    first_child = runtime.node(NodeKind.TREE, parent=root)
    second_child = runtime.node(NodeKind.TREE, parent=root)
    remote_root = runtime.node(NodeKind.NI)
    remote = runtime.node(NodeKind.TREE, parent=remote_root)
    another_remote = runtime.node(NodeKind.TREE, parent=remote_root)

    # Either equality argument already being a root makes the annotation forgettable.
    assert runtime.manager.can_forget(other_root, remote, root)
    assert runtime.manager.can_forget(remote, other_root, root)
    # A nonroot annotation owner is in the tree part, where annotation is unnecessary.
    assert runtime.manager.can_forget(remote, another_remote, first_child)
    # Two direct children of the same root are the formal tree-neighbour exception.
    assert runtime.manager.can_forget(first_child, second_child, root)

    assert not runtime.manager.can_forget(first_child, remote, root)
    assert runtime.manager.target_for(first_child, remote, root) == (remote, first_child)
    assert runtime.manager.target_for(remote, first_child, root) == (remote, first_child)

    predicate = runtime.annotation(1)
    runtime.queue(predicate, first_child, remote, root)
    runtime.manager.process_next(_token())
    target_event = next(
        value for value in runtime.manager.trace if value.event is NominalEvent.TARGET_MERGED
    )
    assert target_event.handles[0] == remote


def test_deterministic_ni_creates_reuses_and_keys_the_correct_root() -> None:
    runtime = _runtime()
    predicate = runtime.annotation(1)
    root = runtime.node(NodeKind.NI)
    host = runtime.node(NodeKind.NI)
    parent = runtime.node(NodeKind.TREE, parent=host)
    target = runtime.node(NodeKind.TREE, parent=parent)
    descendant = runtime.node(NodeKind.TREE, parent=target)

    runtime.queue(predicate, target, target, root)
    assert runtime.manager.process_next(_token()) is BranchTransition.DETERMINISTIC
    introduced = runtime.manager.root_for(root, predicate.predicate_id, 1)
    assert introduced is not None
    introduced_node = runtime.session.nodes.require_active(introduced)
    assert introduced_node.kind is NodeKind.NI
    assert introduced_node.nominal_level == 1
    assert introduced_node.cardinality_tag == predicate.predicate_id
    assert runtime.session.nodes.get(target).lifecycle is NodeLifecycle.MERGED
    assert runtime.session.nodes.representative(target)[0] == introduced
    assert runtime.session.nodes.get(descendant).lifecycle is NodeLifecycle.PRUNED
    assert runtime.session.branches == []

    second_host = runtime.node(NodeKind.NI)
    second_target = runtime.node(NodeKind.TREE, parent=second_host)
    runtime.queue(predicate, second_target, second_target, root)
    assert runtime.manager.process_next(_token()) is BranchTransition.DETERMINISTIC
    assert runtime.manager.root_for(root, predicate.predicate_id, 1) == introduced
    assert runtime.session.nodes.representative(second_target)[0] == introduced
    assert len(runtime.manager.root_keys) == 1
    assert [value.event for value in runtime.manager.trace].count(NominalEvent.ROOT_CREATED) == 1
    assert [value.event for value in runtime.manager.trace].count(NominalEvent.ROOT_REUSED) == 1
    runtime.session.check_invariants()


def test_target_order_prunes_the_ancestor_before_considering_the_other_node() -> None:
    runtime = _runtime()
    predicate = runtime.annotation(1)
    root = runtime.node(NodeKind.NI)
    host = runtime.node(NodeKind.NI)
    ancestor = runtime.node(NodeKind.TREE, parent=host)
    descendant = runtime.node(NodeKind.TREE, parent=ancestor)
    leaf = runtime.node(NodeKind.TREE, parent=descendant)

    runtime.queue(predicate, ancestor, descendant, root)
    assert runtime.manager.process_next(_token()) is BranchTransition.DETERMINISTIC
    introduced = runtime.manager.root_for(root, predicate.predicate_id, 1)
    assert introduced is not None
    assert runtime.session.nodes.representative(ancestor)[0] == introduced
    assert runtime.session.nodes.get(descendant).lifecycle is NodeLifecycle.PRUNED
    assert runtime.session.nodes.get(leaf).lifecycle is NodeLifecycle.PRUNED
    assert [value.event for value in runtime.manager.trace].count(NominalEvent.OTHER_MERGED) == 0


def test_cardinality_branch_advances_to_last_choice_without_branch_dependency() -> None:
    runtime = _runtime()
    predicate = runtime.annotation(2)
    root = runtime.node(NodeKind.NI)
    host = runtime.node(NodeKind.NI)
    target = runtime.node(NodeKind.TREE, parent=host)

    runtime.session.push_branch(
        BranchChoiceKind.DATATYPE,
        (10, 11),
        source_id=999,
        base_dependency=DependencySet(),
    )
    runtime.queue(predicate, target, target, root, DependencySet.of((0,)))
    assert runtime.manager.process_next(_token()) is BranchTransition.BRANCHED
    assert len(runtime.session.branches) == 2
    branch = runtime.session.branches[1]
    assert branch.choice_kind is BranchChoiceKind.MERGE
    assert branch.alternatives == (1, 2)
    first_root = runtime.manager.root_for(root, predicate.predicate_id, 1)
    assert first_root is not None
    assert runtime.session.nodes.get(target).merge_dependency == DependencySet.of((0, 1))

    runtime.session.install_clash(Clash(ClashKind.POSITIVE_NEGATIVE_ATOM, DependencySet.of((0, 1))))
    assert runtime.manager.resolve_clash(_token()) is BranchTransition.ADVANCED
    assert runtime.manager.root_for(root, predicate.predicate_id, 1) is None
    second_root = runtime.manager.root_for(root, predicate.predicate_id, 2)
    assert second_root is not None and second_root != first_root
    assert runtime.session.nodes.representative(target)[0] == second_root
    assert runtime.session.nodes.get(target).merge_dependency == DependencySet.of((0,))
    assert runtime.session.branches[1].current == 2
    assert runtime.session.clashes.current is None
    runtime.session.check_invariants()


def test_repeated_cardinality_ni_reuses_first_level_then_creates_second_level() -> None:
    runtime = _runtime()
    predicate = runtime.annotation(2)
    root = runtime.node(NodeKind.NI)
    host = runtime.node(NodeKind.NI)
    first_target = runtime.node(NodeKind.TREE, parent=host)

    runtime.queue(predicate, first_target, first_target, root)
    assert runtime.manager.process_next(_token()) is BranchTransition.BRANCHED
    first_root = runtime.manager.root_for(root, predicate.predicate_id, 1)
    assert first_root is not None

    second_target = runtime.node(NodeKind.TREE, parent=first_root)
    runtime.queue(
        predicate,
        second_target,
        second_target,
        root,
        DependencySet.of((0,)),
    )
    assert runtime.manager.process_next(_token()) is BranchTransition.BRANCHED
    assert len(runtime.session.branches) == 2
    assert runtime.manager.root_for(root, predicate.predicate_id, 1) == first_root
    assert runtime.session.nodes.representative(second_target)[0] == first_root
    assert runtime.session.nodes.get(second_target).merge_dependency == DependencySet.of((0, 1))

    runtime.session.install_clash(Clash(ClashKind.POSITIVE_NEGATIVE_ATOM, DependencySet.of((0, 1))))
    assert runtime.manager.resolve_clash(_token()) is BranchTransition.ADVANCED
    second_root = runtime.manager.root_for(root, predicate.predicate_id, 2)
    assert second_root is not None and second_root != first_root
    assert runtime.manager.root_for(root, predicate.predicate_id, 1) == first_root
    assert runtime.session.nodes.representative(second_target)[0] == second_root
    assert runtime.session.nodes.get(second_target).merge_dependency == DependencySet.of((0,))


def test_forget_and_preprocessed_root_target_use_ordinary_merge_without_ni_branch() -> None:
    runtime = _runtime()
    predicate = runtime.annotation(2)
    annotation_root = runtime.node(NodeKind.NI)
    first = runtime.node(NodeKind.NI)
    second_host = runtime.node(NodeKind.NI)
    second = runtime.node(NodeKind.TREE, parent=second_host)

    runtime.queue(predicate, first, second, annotation_root)
    assert runtime.manager.process_next(_token()) is BranchTransition.DETERMINISTIC
    assert (
        runtime.session.nodes.representative(first)[0]
        == runtime.session.nodes.representative(second)[0]
    )
    assert runtime.manager.root_keys == ()
    assert runtime.session.branches == []
    assert runtime.manager.trace[-1].event is NominalEvent.FORGOT_ANNOTATION

    # The same outcome must hold when a queued tree target becomes a root before NI runs.
    other_runtime = _runtime()
    predicate = other_runtime.annotation(2)
    annotation_root = other_runtime.node(NodeKind.NI)
    host = other_runtime.node(NodeKind.NI)
    first_tree = other_runtime.node(NodeKind.TREE, parent=host)
    second_tree = other_runtime.node(NodeKind.TREE, parent=host)
    promoted = other_runtime.node(NodeKind.ROOT, named=True)
    other_runtime.queue(predicate, first_tree, second_tree, annotation_root)
    other_runtime.merger.merge(second_tree, promoted, DependencySet(), _token())
    assert other_runtime.manager.process_next(_token()) is BranchTransition.DETERMINISTIC
    assert other_runtime.manager.root_keys == ()
    assert other_runtime.session.branches == []


def test_root_key_and_reused_ni_root_survive_pre_and_post_processing_merges() -> None:
    premerged = _runtime()
    premerged_predicate = premerged.annotation(1)
    premerged_survivor = premerged.node(NodeKind.ROOT, named=True)
    premerged_root = premerged.node(NodeKind.NI)
    premerged_host = premerged.node(NodeKind.NI)
    premerged_target = premerged.node(NodeKind.TREE, parent=premerged_host)
    premerged.queue(
        premerged_predicate,
        premerged_target,
        premerged_target,
        premerged_root,
    )
    premerged.merger.merge(premerged_root, premerged_survivor, DependencySet(), _token())
    premerged.manager.process_next(_token())
    assert (
        premerged.manager.root_for(
            premerged_survivor,
            premerged_predicate.predicate_id,
            1,
        )
        is not None
    )
    assert premerged.manager.root_keys[0].root == premerged_survivor

    runtime = _runtime()
    predicate = runtime.annotation(1)
    survivor = runtime.node(NodeKind.ROOT, named=True)
    annotation_root = runtime.node(NodeKind.NI)
    host = runtime.node(NodeKind.NI)
    first_target = runtime.node(NodeKind.TREE, parent=host)

    runtime.queue(predicate, first_target, first_target, annotation_root)
    runtime.manager.process_next(_token())
    introduced = runtime.manager.root_for(annotation_root, predicate.predicate_id, 1)
    assert introduced is not None

    # Canonicalizing the annotation owner after its merge must still hit the old key.
    runtime.merger.merge(annotation_root, survivor, DependencySet(), _token())
    second_host = runtime.node(NodeKind.NI)
    second_target = runtime.node(NodeKind.TREE, parent=second_host)
    runtime.queue(predicate, second_target, second_target, annotation_root)
    runtime.manager.process_next(_token())
    assert runtime.manager.root_for(survivor, predicate.predicate_id, 1) == introduced

    # If the stored NI root is itself merged, reuse follows its canonical representative.
    named_target = runtime.node(NodeKind.ROOT, named=True)
    runtime.merger.merge(introduced, named_target, DependencySet(), _token())
    third_host = runtime.node(NodeKind.NI)
    third_target = runtime.node(NodeKind.TREE, parent=third_host)
    runtime.queue(predicate, third_target, third_target, survivor)
    runtime.manager.process_next(_token())
    expected = runtime.session.nodes.representative(introduced)[0]
    assert runtime.manager.root_for(survivor, predicate.predicate_id, 1) == expected
    assert runtime.session.nodes.representative(third_target)[0] == expected
    assert len(runtime.manager.root_keys) == 1


def test_distinct_annotation_keys_do_not_reuse_roots() -> None:
    runtime = _runtime()
    first_predicate = runtime.annotation(1, 0)
    second_predicate = runtime.annotation(1, 1)
    root = runtime.node(NodeKind.NI)
    hosts = [runtime.node(NodeKind.NI), runtime.node(NodeKind.NI)]
    targets = [runtime.node(NodeKind.TREE, parent=host) for host in hosts]

    runtime.queue(first_predicate, targets[0], targets[0], root)
    runtime.manager.process_next(_token())
    runtime.queue(second_predicate, targets[1], targets[1], root)
    runtime.manager.process_next(_token())
    first_root = runtime.manager.root_for(root, first_predicate.predicate_id, 1)
    second_root = runtime.manager.root_for(root, second_predicate.predicate_id, 1)
    assert first_root is not None and second_root is not None
    assert first_root != second_root
    assert len(runtime.manager.root_keys) == 2


def test_pruned_pending_arguments_are_ignored_without_reusing_or_creating_roots() -> None:
    runtime = _runtime()
    predicate = runtime.annotation(2)
    root = runtime.node(NodeKind.NI)
    host = runtime.node(NodeKind.NI)
    target = runtime.node(NodeKind.TREE, parent=host)
    runtime.queue(predicate, target, target, root)
    runtime.session.prune_subtree(target)

    assert runtime.manager.process_next(_token()) is BranchTransition.SATISFIED
    assert runtime.manager.root_keys == ()
    assert runtime.session.branches == []
    assert runtime.manager.trace[-1].event is NominalEvent.IGNORED_PRUNED


def test_operation_rollback_restores_pending_queue_roots_branches_and_trace_exactly() -> None:
    runtime = _runtime()
    predicate = runtime.annotation(2)
    root = runtime.node(NodeKind.NI)
    host = runtime.node(NodeKind.NI)
    target = runtime.node(NodeKind.TREE, parent=host)
    runtime.queue(predicate, target, target, root)
    runtime.session.begin_operation()
    state_before = runtime.session.canonical_snapshot()
    nominal_before = runtime.manager.logical_snapshot()

    assert runtime.manager.process_next(_token()) is BranchTransition.BRANCHED
    assert runtime.manager.logical_snapshot() != nominal_before
    runtime.session.reset_to_operation_root()

    assert runtime.session.canonical_snapshot() == state_before
    assert runtime.manager.logical_snapshot() == nominal_before
    pending = runtime.engine.take_pending_annotated_equality()
    assert pending is not None and pending.atom.predicate_id == predicate.predicate_id


class _CancelAfterMutation(CancellationToken):
    __slots__ = ("_baseline", "_session")

    def __init__(self, session: TableauSession, baseline: int) -> None:
        super().__init__()
        self._session = session
        self._baseline = baseline

    def check(self) -> None:
        if self._session.trail.length > self._baseline:
            raise ReasonerInterruptedError("injected nominal cancellation")
        super().check()


def test_cancellation_recovers_the_operation_root_and_pending_action() -> None:
    runtime = _runtime()
    predicate = runtime.annotation(1)
    root = runtime.node(NodeKind.NI)
    host = runtime.node(NodeKind.NI)
    target = runtime.node(NodeKind.TREE, parent=host)
    runtime.queue(predicate, target, target, root)
    runtime.session.begin_operation()
    baseline = runtime.session.trail.length
    snapshot = runtime.session.canonical_snapshot()

    with pytest.raises(ReasonerInterruptedError, match="nominal cancellation"):
        runtime.manager.process_next(_CancelAfterMutation(runtime.session, baseline))

    assert runtime.session.canonical_snapshot() == snapshot
    assert runtime.manager.logical_snapshot() == {
        "branch_actions": [],
        "roots": [],
        "trace": [],
    }
    assert runtime.engine.take_pending_annotated_equality() is not None


def test_trace_is_deterministic_and_branch_cardinality_is_resource_bounded() -> None:
    snapshots = []
    for _ in range(2):
        runtime = _runtime()
        predicate = runtime.annotation(1)
        root = runtime.node(NodeKind.NI)
        host = runtime.node(NodeKind.NI)
        target = runtime.node(NodeKind.TREE, parent=host)
        runtime.queue(predicate, target, target, root)
        runtime.manager.process_next(_token())
        snapshots.append(runtime.manager.logical_snapshot())
    assert snapshots[0] == snapshots[1]

    limited = _runtime(limits=NominalLimits(max_branch_choices=1))
    predicate = limited.annotation(2)
    root = limited.node(NodeKind.NI)
    host = limited.node(NodeKind.NI)
    target = limited.node(NodeKind.TREE, parent=host)
    limited.queue(predicate, target, target, root)
    limited.session.begin_operation()
    with pytest.raises(ResourceLimitError, match="branch-choice limit"):
        limited.manager.process_next(_token())
    assert limited.manager.root_keys == ()
    assert limited.session.branches == []
    assert limited.engine.take_pending_annotated_equality() is not None
