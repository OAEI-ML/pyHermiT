from __future__ import annotations

from pyhermit.hierarchy import (
    ClassificationMode,
    IncrementalClassifier,
    SlowAllPairsClassifier,
    build_hierarchy,
)


def _key(value: str) -> bytes:
    return value.encode("ascii")


def test_scc_collapse_and_transitive_reduction_are_canonical() -> None:
    elements = ("bottom", "a", "b", "c", "isolated", "top")
    hierarchy = build_hierarchy(
        reversed(elements),
        (
            ("a", "b"),
            ("b", "a"),
            ("a", "c"),
            ("c", "top"),
            ("a", "top"),
        ),
        top="top",
        bottom="bottom",
        key=_key,
    )

    assert hierarchy.node("a") == frozenset(("a", "b"))
    assert hierarchy.top == frozenset(("top",))
    assert hierarchy.bottom == frozenset(("bottom",))
    a = hierarchy.node_id("a")
    c = hierarchy.node_id("c")
    top = hierarchy.node_id("top")
    assert (a, c) in hierarchy.hierarchy.edges
    assert (c, top) in hierarchy.hierarchy.edges
    assert (a, top) not in hierarchy.hierarchy.edges


def test_incremental_modes_match_the_slow_all_pairs_oracle() -> None:
    elements = ("bottom", "a", "a2", "b", "c", "top")
    true_relations = (
        {(value, value) for value in elements}
        | {("bottom", value) for value in elements}
        | {(value, "top") for value in elements}
        | {
            ("a", "a2"),
            ("a2", "a"),
            ("a", "b"),
            ("a2", "b"),
            ("b", "c"),
            ("a", "c"),
            ("a2", "c"),
        }
    )

    def test(pairs):  # type: ignore[no-untyped-def]
        return tuple(pair in true_relations for pair in pairs)

    deterministic = IncrementalClassifier(
        elements,
        test,
        top="top",
        bottom="bottom",
        key=_key,
    ).classify()
    quasi = IncrementalClassifier(
        reversed(elements),
        test,
        top="top",
        bottom="bottom",
        key=_key,
        mode=ClassificationMode.QUASI_ORDER,
    ).classify()
    slow = SlowAllPairsClassifier(
        elements,
        test,
        top="top",
        bottom="bottom",
        key=_key,
    ).classify()

    assert deterministic.hierarchy.hierarchy == quasi.hierarchy.hierarchy
    assert deterministic.hierarchy.hierarchy == slow.hierarchy.hierarchy
    assert deterministic.statistics.semantic_tests < slow.statistics.semantic_tests
    assert quasi.statistics.possible_subsumptions == 0


def test_deep_biomedical_scale_taxonomy_is_iterative_and_exact() -> None:
    size = 10_000
    hierarchy = build_hierarchy(
        range(size),
        ((value, value + 1) for value in range(size - 1)),
        top=size - 1,
        bottom=0,
        key=lambda value: value.to_bytes(8, "big"),
    )

    assert len(hierarchy.hierarchy.nodes) == size
    assert len(hierarchy.hierarchy.edges) == size - 1
    assert hierarchy.node_id(0) == hierarchy.hierarchy.bottom_node
    assert hierarchy.node_id(size - 1) == hierarchy.hierarchy.top_node
