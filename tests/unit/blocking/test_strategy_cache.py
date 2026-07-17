from __future__ import annotations

import pytest

from pyhermit.backends.python.blocking import (
    BlockingCacheNamespace,
    BlockingLabels,
    BlockingManager,
    BlockingManagerKind,
    BlockingRequirements,
    BlockingSignatureCache,
    BlockingVocabulary,
    CoreBlockingMode,
    DirectCheckerKind,
    SingleDirectBlockingChecker,
    create_direct_checker,
    select_blocking_plan,
)
from pyhermit.backends.python.state import DependencySet, NodeKind, TableauSession
from pyhermit.config import BlockingMode

VOCABULARY = BlockingVocabulary(frozenset({1, 2}), frozenset({10}))


def test_auto_strategy_selects_pairwise_for_inverses_and_validated_when_requested() -> None:
    simple = select_blocking_plan(BlockingMode.AUTO, BlockingRequirements())
    assert simple.manager_kind is BlockingManagerKind.ANYWHERE
    assert simple.direct_checker_kind is DirectCheckerKind.SINGLE
    assert simple.cache_allowed

    inverse = select_blocking_plan(BlockingMode.AUTO, BlockingRequirements(has_inverse_roles=True))
    assert inverse.direct_checker_kind is DirectCheckerKind.PAIRWISE

    validated = select_blocking_plan(
        BlockingMode.AUTO,
        BlockingRequirements(
            has_inverse_roles=True,
            has_nominals=True,
            requires_validated_core=True,
            complex_core=True,
        ),
    )
    assert validated.manager_kind is BlockingManagerKind.VALIDATED_ANYWHERE
    assert validated.direct_checker_kind is DirectCheckerKind.VALIDATED_SINGLE
    assert validated.core_mode is CoreBlockingMode.COMPLEX
    assert not validated.cache_allowed

    explicit_validated_pairwise = select_blocking_plan(
        BlockingMode.VALIDATED_ANYWHERE,
        BlockingRequirements(
            requires_validated_core=True,
            direct_checker_kind=DirectCheckerKind.PAIRWISE,
        ),
    )
    assert explicit_validated_pairwise.direct_checker_kind is DirectCheckerKind.VALIDATED_PAIRWISE


def _cache() -> BlockingSignatureCache:
    namespace = BlockingCacheNamespace(
        "a" * 64,
        VOCABULARY.fingerprint,
        DirectCheckerKind.SINGLE,
    )
    return BlockingSignatureCache(namespace, max_entries=2, max_bytes=4_096)


def test_cache_promotes_only_completed_sound_models_and_blocks_without_old_nodes() -> None:
    cache = _cache()
    plan = select_blocking_plan(BlockingMode.AUTO, BlockingRequirements())
    first_session = TableauSession()
    first_root = first_session.create_node(NodeKind.ROOT)
    first = first_session.create_node(NodeKind.TREE, parent=first_root)
    first_session.extensions.add(1, (first,), DependencySet())
    first_manager = BlockingManager(
        first_session,
        SingleDirectBlockingChecker(VOCABULARY),
        plan,
        cache=cache,
    )
    first_manager.compute()
    assert (
        first_manager.model_found(
            satisfiable=True,
            completed=True,
            has_nominals=False,
            has_additional_ontology=False,
            query_local_axioms=False,
        )
        == 1
    )

    second_session = TableauSession()
    second_root = second_session.create_node(NodeKind.ROOT)
    second = second_session.create_node(NodeKind.TREE, parent=second_root)
    second_session.extensions.add(1, (second,), DependencySet())
    second_manager = BlockingManager(
        second_session,
        create_direct_checker(plan.direct_checker_kind, VOCABULARY),
        plan,
        cache=cache,
    )
    second_manager.compute()
    assert second_manager.is_directly_blocked(second)
    assert second_manager.blocker(second) is None
    assert second_manager.reference_assignments()[-1].from_cache

    assert (
        second_manager.model_found(
            satisfiable=True,
            completed=True,
            has_nominals=True,
            has_additional_ontology=False,
            query_local_axioms=False,
        )
        == 0
    )


def test_bounded_cache_evicts_without_affecting_exact_signature_comparison() -> None:
    cache = _cache()
    plan = select_blocking_plan(BlockingMode.AUTO, BlockingRequirements())
    session = TableauSession()
    root = session.create_node(NodeKind.ROOT)
    nodes = [session.create_node(NodeKind.TREE, parent=root) for _ in range(3)]
    for predicate, node in enumerate(nodes, start=1):
        # Predicate 3 is deliberately outside the blocking vocabulary and shares the
        # empty relevant label, so only two exact signatures can survive.
        session.extensions.add(predicate, (node,), DependencySet())
    manager = BlockingManager(
        session,
        SingleDirectBlockingChecker(VOCABULARY),
        plan,
        cache=cache,
    )
    manager.compute()
    manager.model_found(
        satisfiable=True,
        completed=True,
        has_nominals=False,
        has_additional_ontology=False,
        query_local_axioms=False,
    )
    assert cache.entry_count <= 2
    assert cache.size_bytes <= cache.max_bytes


def test_cache_namespace_core_mode_cannot_cross_configuration_boundaries() -> None:
    plan = select_blocking_plan(BlockingMode.AUTO, BlockingRequirements())
    cache = BlockingSignatureCache(
        BlockingCacheNamespace(
            "a" * 64,
            VOCABULARY.fingerprint,
            DirectCheckerKind.SINGLE,
            core_mode=CoreBlockingMode.SIMPLE,
        )
    )
    with pytest.raises(ValueError, match="core mode"):
        BlockingManager(
            TableauSession(),
            SingleDirectBlockingChecker(VOCABULARY),
            plan,
            cache=cache,
        )


@pytest.mark.parametrize(
    ("overrides"),
    (
        {"satisfiable": False},
        {"completed": False},
        {"has_nominals": True},
        {"has_additional_ontology": True},
        {"query_local_axioms": True},
        {"aborted": True},
    ),
)
def test_every_unsound_or_incomplete_cache_promotion_path_is_disabled(
    overrides: dict[str, bool],
) -> None:
    cache = _cache()
    session = TableauSession()
    root = session.create_node(NodeKind.ROOT)
    node = session.create_node(NodeKind.TREE, parent=root)
    session.extensions.add(1, (node,), DependencySet())
    labels = BlockingLabels.from_session(session, VOCABULARY)
    signature = SingleDirectBlockingChecker(VOCABULARY).signature(session, labels, node)
    flags = {
        "satisfiable": True,
        "completed": True,
        "has_nominals": False,
        "has_additional_ontology": False,
        "query_local_axioms": False,
        "aborted": False,
    }
    flags.update(overrides)
    assert (
        cache.promote_model(
            (signature,),
            satisfiable=flags["satisfiable"],
            completed=flags["completed"],
            has_nominals=flags["has_nominals"],
            has_additional_ontology=flags["has_additional_ontology"],
            query_local_axioms=flags["query_local_axioms"],
            aborted=flags["aborted"],
        )
        == 0
    )
    assert cache.entry_count == 0
