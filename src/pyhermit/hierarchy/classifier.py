"""Exact deterministic, quasi-order, and slow differential classifiers.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass
from enum import Enum
from typing import Generic, TypeVar

from .builder import CanonicalKey, build_hierarchy, hierarchy_from_partition
from .model import HierarchyIndex

T = TypeVar("T")
BatchTester = Callable[[tuple[tuple[T, T], ...]], tuple[bool, ...]]


class ClassificationMode(str, Enum):
    DETERMINISTIC = "deterministic"
    QUASI_ORDER = "quasi_order"
    SLOW_ALL_PAIRS = "slow_all_pairs"


@dataclass(frozen=True, slots=True)
class ClassificationStatistics:
    mode: ClassificationMode
    elements: int
    semantic_tests: int
    batches: int
    cache_hits: int
    known_subsumptions: int
    possible_subsumptions: int

    def __post_init__(self) -> None:
        if not isinstance(self.mode, ClassificationMode):
            raise TypeError("mode must be ClassificationMode")
        for name in (
            "elements",
            "semantic_tests",
            "batches",
            "cache_hits",
            "known_subsumptions",
            "possible_subsumptions",
        ):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")


@dataclass(frozen=True, slots=True)
class ClassificationResult(Generic[T]):
    hierarchy: HierarchyIndex[T]
    statistics: ClassificationStatistics


class SubsumptionOracle(Generic[T]):
    """Memoized K/P relation with sound closure of newly proven subsumptions."""

    __slots__ = (
        "_batches",
        "_cache",
        "_cache_hits",
        "_cancelled",
        "_elements",
        "_known",
        "_known_successors",
        "_mode",
        "_possible",
        "_semantic_tests",
        "_tester",
    )

    def __init__(
        self,
        elements: Sequence[T],
        tester: BatchTester[T],
        known: Iterable[tuple[T, T]],
        *,
        mode: ClassificationMode,
        cancelled: Callable[[], bool] | None = None,
    ) -> None:
        if not callable(tester):
            raise TypeError("tester must be callable")
        if cancelled is not None and not callable(cancelled):
            raise TypeError("cancelled must be callable or None")
        self._elements = tuple(elements)
        self._tester = tester
        self._mode = mode
        self._cancelled = cancelled
        self._known = set(known)
        self._known.update((value, value) for value in self._elements)
        self._known_successors: dict[T, set[T]] = {value: set() for value in self._elements}
        for child, parent in self._known:
            if child not in self._known_successors or parent not in self._known_successors:
                raise ValueError("known relations must reference only classifier elements")
            self._known_successors[child].add(parent)
        self._cache: dict[tuple[T, T], bool] = {relation: True for relation in self._known}
        # Candidate P-edges are introduced lazily by hierarchy-search frontiers.
        # Eagerly allocating |elements|² pairs would preclude large taxonomies.
        self._possible: set[tuple[T, T]] = set()
        self._semantic_tests = 0
        self._batches = 0
        self._cache_hits = 0

    @property
    def known(self) -> frozenset[tuple[T, T]]:
        return frozenset(self._known)

    @property
    def possible_count(self) -> int:
        return len(self._possible)

    @property
    def semantic_tests(self) -> int:
        return self._semantic_tests

    @property
    def batches(self) -> int:
        return self._batches

    @property
    def cache_hits(self) -> int:
        return self._cache_hits

    def evaluate(self, relations: Iterable[tuple[T, T]]) -> tuple[bool, ...]:
        values = tuple(relations)
        self._checkpoint()
        missing: list[tuple[T, T]] = []
        missing_set: set[tuple[T, T]] = set()
        for relation in values:
            if relation in self._cache:
                self._cache_hits += 1
            elif self._is_known(*relation):
                self._cache[relation] = True
                self._cache_hits += 1
            elif relation not in missing_set:
                missing.append(relation)
                missing_set.add(relation)
        if missing:
            if self._mode is ClassificationMode.QUASI_ORDER:
                self._possible.update(missing)
            checked = tuple(self._tester(tuple(missing)))
            if len(checked) != len(missing) or not all(
                isinstance(value, bool) for value in checked
            ):
                raise RuntimeError("subsumption tester returned an invalid result batch")
            self._semantic_tests += len(missing)
            self._batches += 1
            for relation, entailed in zip(missing, checked, strict=True):
                self._cache[relation] = entailed
                self._possible.discard(relation)
                if entailed:
                    self._add_known(*relation)
            self._checkpoint()
        return tuple(self._cache[value] for value in values)

    def _add_known(self, child: T, parent: T) -> None:
        retained = self._cache.get((child, parent))
        if retained is False:
            raise RuntimeError("semantic subsumption results are contradictory")
        self._known.add((child, parent))
        self._known_successors[child].add(parent)
        self._possible.discard((child, parent))
        self._cache[(child, parent)] = True

    def _is_known(self, child: T, parent: T) -> bool:
        frontier = [child]
        visited: set[T] = set()
        while frontier:
            current = frontier.pop()
            if current == parent:
                return True
            if current in visited:
                continue
            visited.add(current)
            frontier.extend(self._known_successors[current] - visited)
        return False

    def _checkpoint(self) -> None:
        if self._cancelled is not None and self._cancelled():
            from pyhermit.exceptions import ReasonerInterruptedError

            raise ReasonerInterruptedError("classification was interrupted")


class IncrementalClassifier(Generic[T]):
    """HermiT-style hierarchy search over an exact semantic quasi-order."""

    __slots__ = ("_bottom", "_elements", "_key", "_known", "_mode", "_oracle", "_top")

    def __init__(
        self,
        elements: Iterable[T],
        tester: BatchTester[T],
        *,
        top: T,
        bottom: T,
        key: CanonicalKey[T],
        known: Iterable[tuple[T, T]] = (),
        mode: ClassificationMode = ClassificationMode.DETERMINISTIC,
        cancelled: Callable[[], bool] | None = None,
    ) -> None:
        values = frozenset(elements)
        if top not in values or bottom not in values:
            raise ValueError("top and bottom must occur in classifier elements")
        if mode not in {ClassificationMode.DETERMINISTIC, ClassificationMode.QUASI_ORDER}:
            raise ValueError("incremental classifier mode must be deterministic or quasi-order")
        self._elements = tuple(sorted(values, key=key))
        self._top = top
        self._bottom = bottom
        self._key = key
        seed = set(known)
        for value in self._elements:
            seed.update(((bottom, value), (value, top), (value, value)))
        self._known = frozenset(seed)
        self._mode = mode
        self._oracle = SubsumptionOracle(
            self._elements,
            tester,
            seed,
            mode=mode,
            cancelled=cancelled,
        )

    def classify(self) -> ClassificationResult[T]:
        mutable = _MutableHierarchy(self._top, self._bottom, self._key, self._oracle)
        known_relations = self._oracle.known
        ordered = tuple(
            sorted(
                (value for value in self._elements if value not in {self._top, self._bottom}),
                key=lambda value: (
                    sum(child == value for child, _parent in known_relations),
                    self._key(value),
                ),
            )
        )
        for value in ordered:
            mutable.insert(value)
        hierarchy = mutable.freeze()
        statistics = ClassificationStatistics(
            mode=self._mode,
            elements=len(self._elements),
            semantic_tests=self._oracle.semantic_tests,
            batches=self._oracle.batches,
            cache_hits=self._oracle.cache_hits,
            known_subsumptions=len(self._oracle.known),
            possible_subsumptions=self._oracle.possible_count,
        )
        return ClassificationResult(hierarchy, statistics)


class SlowAllPairsClassifier(Generic[T]):
    """Small-domain differential oracle that deliberately tests every ordered pair."""

    __slots__ = ("_bottom", "_cancelled", "_elements", "_key", "_tester", "_top")

    def __init__(
        self,
        elements: Iterable[T],
        tester: BatchTester[T],
        *,
        top: T,
        bottom: T,
        key: CanonicalKey[T],
        cancelled: Callable[[], bool] | None = None,
    ) -> None:
        self._elements = tuple(sorted(frozenset(elements), key=key))
        if top not in self._elements or bottom not in self._elements:
            raise ValueError("top and bottom must occur in classifier elements")
        self._tester = tester
        self._top = top
        self._bottom = bottom
        self._key = key
        self._cancelled = cancelled

    def classify(self) -> ClassificationResult[T]:
        if self._cancelled is not None and self._cancelled():
            from pyhermit.exceptions import ReasonerInterruptedError

            raise ReasonerInterruptedError("classification was interrupted")
        relations = tuple((child, parent) for child in self._elements for parent in self._elements)
        outcomes = tuple(self._tester(relations))
        if len(outcomes) != len(relations) or not all(
            isinstance(value, bool) for value in outcomes
        ):
            raise RuntimeError("subsumption tester returned an invalid result batch")
        hierarchy = build_hierarchy(
            self._elements,
            (relation for relation, entailed in zip(relations, outcomes, strict=True) if entailed),
            top=self._top,
            bottom=self._bottom,
            key=self._key,
        )
        return ClassificationResult(
            hierarchy,
            ClassificationStatistics(
                mode=ClassificationMode.SLOW_ALL_PAIRS,
                elements=len(self._elements),
                semantic_tests=len(relations),
                batches=1,
                cache_hits=0,
                known_subsumptions=sum(outcomes),
                possible_subsumptions=0,
            ),
        )


class _MutableHierarchy(Generic[T]):
    __slots__ = (
        "_bottom_node",
        "_edges",
        "_key",
        "_members",
        "_next_node",
        "_oracle",
        "_top_node",
    )

    def __init__(
        self,
        top: T,
        bottom: T,
        key: CanonicalKey[T],
        oracle: SubsumptionOracle[T],
    ) -> None:
        self._top_node = 0
        self._bottom_node = 1
        self._next_node = 2
        self._members: dict[int, set[T]] = {0: {top}, 1: {bottom}}
        self._edges: set[tuple[int, int]] = {(1, 0)}
        self._key = key
        self._oracle = oracle

    def insert(self, element: T) -> None:
        parents = self._boundary(
            self._top_node,
            upward=False,
            relation=lambda representative: (element, representative),
        )
        children = self._boundary(
            self._bottom_node,
            upward=True,
            relation=lambda representative: (representative, element),
        )
        common = parents.intersection(children)
        if common:
            if parents != children or len(common) != 1:
                raise RuntimeError("subsumption relation violated hierarchy-search invariants")
            self._members[next(iter(common))].add(element)
            return
        node = self._next_node
        self._next_node += 1
        self._members[node] = {element}
        for child in children:
            for parent in parents:
                self._edges.discard((child, parent))
        self._edges.update((child, node) for child in children)
        self._edges.update((node, parent) for parent in parents)

    def freeze(self) -> HierarchyIndex[T]:
        return hierarchy_from_partition(
            self._members,
            self._edges,
            top_node=self._top_node,
            bottom_node=self._bottom_node,
            key=self._key,
        )

    def _boundary(
        self,
        start: int,
        *,
        upward: bool,
        relation: Callable[[T], tuple[T, T]],
    ) -> set[int]:
        frontier = {start}
        visited: set[int] = set()
        proven_true = {start}
        boundary: set[int] = set()
        while frontier:
            ordered_frontier = tuple(sorted(frontier))
            candidates_by_node = {
                node: (
                    {parent for child, parent in self._edges if child == node}
                    if upward
                    else {child for child, parent in self._edges if parent == node}
                )
                for node in ordered_frontier
            }
            candidates = tuple(
                sorted(
                    {
                        candidate
                        for node_candidates in candidates_by_node.values()
                        for candidate in node_candidates
                        if candidate not in visited
                    }
                )
            )
            outcomes = self._oracle.evaluate(
                relation(self._representative(candidate)) for candidate in candidates
            )
            true_candidates = {
                candidate
                for candidate, outcome in zip(candidates, outcomes, strict=True)
                if outcome
            }
            proven_true.update(true_candidates)
            for node in ordered_frontier:
                if not candidates_by_node[node].intersection(proven_true):
                    boundary.add(node)
            visited.update(ordered_frontier)
            frontier = true_candidates - visited
        return boundary

    def _representative(self, node: int) -> T:
        return min(self._members[node], key=self._key)


def canonical_structural_key(value: object) -> bytes:
    canonical = getattr(value, "canonical_bytes", None)
    if not callable(canonical):
        raise TypeError("classified values must provide canonical_bytes()")
    encoded = canonical()
    if not isinstance(encoded, bytes):
        raise TypeError("canonical_bytes() must return bytes")
    return encoded


__all__ = [
    "BatchTester",
    "ClassificationMode",
    "ClassificationResult",
    "ClassificationStatistics",
    "IncrementalClassifier",
    "SlowAllPairsClassifier",
    "SubsumptionOracle",
    "canonical_structural_key",
]
