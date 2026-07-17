from __future__ import annotations

import hashlib

from pyhermit.backends.python.blocking import (
    BlockingLabels,
    BlockingManager,
    BlockingRequirements,
    BlockingVocabulary,
    PairwiseDirectBlockingChecker,
    select_blocking_plan,
)
from pyhermit.backends.python.state import DependencySet, NodeKind, TableauSession
from pyhermit.config import BlockingMode


def test_wpr2_pairwise_signature_trace_is_frozen() -> None:
    vocabulary = BlockingVocabulary(frozenset({1, 2, 3}), frozenset({10, 11}))
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

    labels = BlockingLabels.from_session(session, vocabulary)
    checker = PairwiseDirectBlockingChecker(vocabulary)
    plan = select_blocking_plan(
        BlockingMode.ANYWHERE,
        BlockingRequirements(has_inverse_roles=True),
    )
    manager = BlockingManager(session, checker, plan)
    manager.compute()
    snapshot = manager.canonical_snapshot().encode("utf-8")

    assert vocabulary.fingerprint == (
        "afef482dafc98b2e6ba3609daffe8b3454aebd38e5e7e920979c8e4515c4f9fe"
    )
    assert labels.state_digest == (
        "7a3e473b7645ea487009830e281bd4841bf7397cf81cf4ca08a155de57bf3871"
    )
    assert checker.signature(session, labels, second).sha256 == (
        "ca28b8412213a75045055e07b19a54add4e1cf86f1b1b4e61001d3696842cfb5"
    )
    assert hashlib.sha256(snapshot).hexdigest() == (
        "0d5d6e6812947622116f8f0ac34fc3ded80192077dd869517819457f83230e90"
    )
    assert hashlib.sha256(manager.trace_snapshot().encode("utf-8")).hexdigest() == (
        "39dfcc2ffa3d8ee2739faaf26b6214e058aa098848f3f044a8989670f8ccebf4"
    )
