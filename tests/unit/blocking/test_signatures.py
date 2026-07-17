from __future__ import annotations

from pyhermit.backends.python.blocking import (
    BlockingLabels,
    BlockingVocabulary,
    PairwiseDirectBlockingChecker,
    SingleDirectBlockingChecker,
    ValidatedPairwiseDirectBlockingChecker,
    ValidatedSingleDirectBlockingChecker,
)
from pyhermit.backends.python.state import DependencySet, NodeKind, TableauSession

VOCABULARY = BlockingVocabulary(frozenset({1, 2, 3}), frozenset({10, 11}))


def test_single_uses_exact_atomic_label_and_ignores_unclassified_predicates() -> None:
    session = TableauSession()
    root = session.create_node(NodeKind.ROOT)
    blocker = session.create_node(NodeKind.TREE, parent=root)
    blocked = session.create_node(NodeKind.TREE, parent=root)
    session.extensions.add(1, (blocker,), DependencySet())
    session.extensions.add(1, (blocked,), DependencySet())
    session.extensions.add(99, (blocked,), DependencySet())
    labels = BlockingLabels.from_session(session, VOCABULARY)
    checker = SingleDirectBlockingChecker(VOCABULARY)
    assert checker.is_blocked_by(session, labels, blocker, blocked)

    session.extensions.add(2, (blocked,), DependencySet())
    labels = BlockingLabels.from_session(session, VOCABULARY)
    assert not checker.is_blocked_by(session, labels, blocker, blocked)


def test_pairwise_rejects_single_label_match_when_parent_or_edges_differ() -> None:
    session = TableauSession()
    root = session.create_node(NodeKind.ROOT)
    first_parent = session.create_node(NodeKind.TREE, parent=root)
    first = session.create_node(NodeKind.TREE, parent=first_parent)
    second_parent = session.create_node(NodeKind.TREE, parent=root)
    second = session.create_node(NodeKind.TREE, parent=second_parent)
    for node in (first_parent, first, second_parent, second):
        session.extensions.add(1, (node,), DependencySet())
    for parent, child in ((first_parent, first), (second_parent, second)):
        session.extensions.add(10, (parent, child), DependencySet())
        session.extensions.add(11, (child, parent), DependencySet())

    labels = BlockingLabels.from_session(session, VOCABULARY)
    single = SingleDirectBlockingChecker(VOCABULARY)
    pairwise = PairwiseDirectBlockingChecker(VOCABULARY)
    assert single.is_blocked_by(session, labels, first, second)
    assert pairwise.is_blocked_by(session, labels, first, second)

    session.extensions.add(2, (second_parent,), DependencySet())
    labels = BlockingLabels.from_session(session, VOCABULARY)
    assert single.is_blocked_by(session, labels, first, second)
    assert not pairwise.is_blocked_by(session, labels, first, second)

    session.extensions.add(2, (first_parent,), DependencySet())
    session.extensions.add(11, (second_parent, second), DependencySet())
    labels = BlockingLabels.from_session(session, VOCABULARY)
    assert not pairwise.is_blocked_by(session, labels, first, second)


def test_validated_projection_uses_core_but_serializes_full_context() -> None:
    session = TableauSession()
    root = session.create_node(NodeKind.ROOT)
    first = session.create_node(NodeKind.TREE, parent=root)
    second = session.create_node(NodeKind.TREE, parent=root)
    for node in (first, second):
        session.extensions.add(1, (node,), DependencySet(), core=True)
    extra = session.extensions.add(2, (second,), DependencySet(), core=False)
    session.extensions.add(10, (root, second), DependencySet())
    labels = BlockingLabels.from_session(session, VOCABULARY)
    checker = ValidatedSingleDirectBlockingChecker(VOCABULARY, has_inverses=False)
    first_signature = checker.signature(session, labels, first)
    second_signature = checker.signature(session, labels, second)
    assert first_signature.blocks(second_signature)
    assert first_signature.full_node_concepts == (1,)
    assert second_signature.full_node_concepts == (1, 2)
    assert second_signature.full_from_parent_roles == (10,)
    assert first_signature.canonical_bytes() != second_signature.canonical_bytes()

    session.extensions.set_core(extra.row_id)
    labels = BlockingLabels.from_session(session, VOCABULARY)
    assert not checker.is_blocked_by(session, labels, first, second)


def test_validated_pairwise_uses_parent_core_projection_and_inverse_eligibility() -> None:
    session = TableauSession()
    root = session.create_node(NodeKind.ROOT)
    first_parent = session.create_node(NodeKind.TREE, parent=root)
    first = session.create_node(NodeKind.TREE, parent=first_parent)
    second_parent = session.create_node(NodeKind.TREE, parent=root)
    second = session.create_node(NodeKind.TREE, parent=second_parent)
    for node in (first_parent, first, second_parent, second):
        session.extensions.add(1, (node,), DependencySet(), core=True)
    checker = ValidatedPairwiseDirectBlockingChecker(VOCABULARY, has_inverses=True)
    labels = BlockingLabels.from_session(session, VOCABULARY)
    assert checker.is_blocked_by(session, labels, first, second)
    assert not checker.can_be_blocked(session, first_parent)

    session.extensions.add(2, (second_parent,), DependencySet(), core=True)
    labels = BlockingLabels.from_session(session, VOCABULARY)
    assert not checker.is_blocked_by(session, labels, first, second)
