# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Rollback-safe nominal-introduction over pending annotated equalities.

SPDX-License-Identifier: LGPL-3.0-or-later

The implementation follows the NI side conditions in the pinned HermiT
``NominalIntroductionManager`` while using the shared Python branch/trail substrate.
Annotated equalities remain queued actions: this module never installs them as eager
ordinary equality facts.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Protocol, cast

from pyhermit.backends.python.merging import MergeResult
from pyhermit.backends.python.rules.model import (
    BranchTransition,
    PendingAnnotatedEquality,
)
from pyhermit.backends.python.state import (
    BranchChoiceKind,
    Clash,
    ClashKind,
    DependencySet,
    Node,
    NodeHandle,
    NodeKind,
    NodeLifecycle,
    TableauSession,
)
from pyhermit.clauses import ClauseProgram, Predicate, PredicateKind
from pyhermit.events import CancellationToken
from pyhermit.exceptions import InternalInvariantError, ResourceLimitError


class NominalRuleAccess(Protocol):
    """Small engine boundary required by nominal introduction."""

    @property
    def program(self) -> ClauseProgram: ...

    def take_pending_annotated_equality(self) -> PendingAnnotatedEquality | None: ...

    def register_node(
        self,
        handle: NodeHandle,
        dependency: DependencySet | None = None,
    ) -> None: ...


class NominalMergeAccess(Protocol):
    """Small merge boundary required by nominal introduction."""

    def merge(
        self,
        left: NodeHandle,
        right: NodeHandle,
        dependency: DependencySet,
        token: CancellationToken,
    ) -> MergeResult: ...


@dataclass(frozen=True, slots=True)
class NominalLimits:
    max_branch_choices: int = 1_000_000
    max_actions_per_run: int = 1_000_000

    def __post_init__(self) -> None:
        for name in ("max_branch_choices", "max_actions_per_run"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
                raise ValueError(f"{name} must be a positive integer")


@dataclass(frozen=True, slots=True, order=True)
class NominalRootKey:
    """Canonical root/annotation/cardinality-choice identity for one NI root."""

    root: NodeHandle
    predicate_id: int
    role_id: int
    filler_predicate_id: int
    cardinality: int
    level: int

    def __post_init__(self) -> None:
        if not isinstance(self.root, NodeHandle):
            raise TypeError("root must be NodeHandle")
        for name in (
            "predicate_id",
            "role_id",
            "filler_predicate_id",
            "cardinality",
            "level",
        ):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")
        if self.cardinality < 1 or not 1 <= self.level <= self.cardinality:
            raise ValueError("NI level must be within the positive annotation cardinality")


class NominalEvent(str, Enum):
    IGNORED_PRUNED = "ignored_pruned"
    FORGOT_ANNOTATION = "forgot_annotation"
    BRANCH_CREATED = "branch_created"
    BRANCH_ADVANCED = "branch_advanced"
    BRANCH_EXHAUSTED = "branch_exhausted"
    ROOT_CREATED = "root_created"
    ROOT_REUSED = "root_reused"
    TARGET_MERGED = "target_merged"
    OTHER_MERGED = "other_merged"


@dataclass(frozen=True, slots=True)
class NominalTraceEvent:
    sequence: int
    event: NominalEvent
    action_id: int
    predicate_id: int
    dependency: DependencySet
    handles: tuple[NodeHandle, ...] = ()
    choice: int | None = None

    def __post_init__(self) -> None:
        for name in ("sequence", "action_id", "predicate_id"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")
        if not isinstance(self.event, NominalEvent):
            raise TypeError("event must be NominalEvent")
        if not isinstance(self.dependency, DependencySet):
            raise TypeError("dependency must be DependencySet")
        handles = tuple(self.handles)
        if not all(isinstance(value, NodeHandle) for value in handles):
            raise TypeError("trace handles must contain NodeHandle values")
        if self.choice is not None and (
            isinstance(self.choice, bool) or not isinstance(self.choice, int) or self.choice < 1
        ):
            raise ValueError("trace choice must be a positive integer or None")
        object.__setattr__(self, "handles", handles)

    def logical_dict(self) -> dict[str, object]:
        return {
            "action_id": self.action_id,
            "choice": self.choice,
            "dependency": list(self.dependency),
            "event": self.event.value,
            "handles": [[value.slot, value.generation] for value in self.handles],
            "predicate_id": self.predicate_id,
            "sequence": self.sequence,
        }


@dataclass(frozen=True, slots=True)
class _BranchContext:
    action_id: int
    predicate_id: int
    root: NodeHandle
    target: NodeHandle
    other: NodeHandle
    cardinality: int
    provenance_ids: tuple[int, ...]


class NominalIntroductionManager:
    """Create/reuse NI roots and own NI-specific merge-choice branches."""

    __slots__ = (
        "_access",
        "_branch_contexts",
        "_limits",
        "_merger",
        "_roots",
        "_session",
        "_trace",
    )

    def __init__(
        self,
        session: TableauSession,
        access: NominalRuleAccess,
        merger: NominalMergeAccess,
        *,
        limits: NominalLimits | None = None,
    ) -> None:
        if not isinstance(session, TableauSession):
            raise TypeError("session must be TableauSession")
        selected = NominalLimits() if limits is None else limits
        if not isinstance(selected, NominalLimits):
            raise TypeError("limits must be NominalLimits or None")
        if not isinstance(access.program, ClauseProgram):
            raise TypeError("access.program must be ClauseProgram")
        self._session = session
        self._access = access
        self._merger = merger
        self._limits = selected
        self._roots: dict[NominalRootKey, NodeHandle] = {}
        self._branch_contexts: dict[int, _BranchContext] = {}
        self._trace: list[NominalTraceEvent] = []

    @property
    def trace(self) -> tuple[NominalTraceEvent, ...]:
        return tuple(self._trace)

    @property
    def root_keys(self) -> tuple[NominalRootKey, ...]:
        return tuple(sorted(self._roots))

    def logical_snapshot(self) -> dict[str, object]:
        roots = []
        for key in sorted(self._roots):
            handle = self._roots[key]
            representative, _dependency = self._session.nodes.representative(handle)
            roots.append(
                {
                    "annotation": [
                        key.predicate_id,
                        key.role_id,
                        key.filler_predicate_id,
                        key.cardinality,
                    ],
                    "level": key.level,
                    "node": [representative.slot, representative.generation],
                    "root": [key.root.slot, key.root.generation],
                }
            )
        return {
            "branch_actions": sorted(self._branch_contexts),
            "roots": roots,
            "trace": [value.logical_dict() for value in self._trace],
        }

    def can_forget(
        self,
        first: NodeHandle,
        second: NodeHandle,
        root: NodeHandle,
    ) -> bool:
        """Decide the four formal HermiT annotation-forgetting side conditions."""

        canonical = self._canonical_nodes((first, second, root))
        if canonical is None:
            return True
        (first_rep, second_rep, root_rep), _dependency = canonical
        return self._can_forget_canonical(first_rep, second_rep, root_rep)

    def target_for(
        self,
        first: NodeHandle,
        second: NodeHandle,
        root: NodeHandle,
    ) -> tuple[NodeHandle, NodeHandle] | None:
        """Return the formal NI target followed by the other equality argument."""

        canonical = self._canonical_nodes((first, second, root))
        if canonical is None:
            return None
        (first_rep, second_rep, root_rep), _dependency = canonical
        if self._can_forget_canonical(first_rep, second_rep, root_rep):
            return None
        first_node = self._session.nodes.require_active(first_rep)
        if not self._is_direct_parent(root_rep, first_node):
            return first_rep, second_rep
        return second_rep, first_rep

    def root_for(
        self,
        root: NodeHandle,
        predicate_id: int,
        level: int,
    ) -> NodeHandle | None:
        predicate = self._annotation_predicate(predicate_id)
        if isinstance(level, bool) or not isinstance(level, int):
            raise TypeError("level must be int")
        if not 1 <= level <= cast(int, predicate.cardinality):
            raise ValueError("level must be within the annotation cardinality")
        try:
            root_rep, _path = self._session.nodes.representative(root)
            self._session.nodes.require_active(root_rep)
        except (KeyError, ValueError):
            return None
        match = self._find_root_key(root_rep, predicate, level)
        if match is None:
            return None
        handle = self._roots[match]
        try:
            representative, _dependency = self._session.nodes.representative(handle)
            self._session.nodes.require_active(representative)
        except (KeyError, ValueError) as error:
            raise InternalInvariantError("NI root key references an unavailable node") from error
        return representative

    def process_next(self, token: CancellationToken) -> BranchTransition:
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        return self._session.run_with_recovery(token, lambda: self._process_next(token))

    def process_all(self, token: CancellationToken) -> int:
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        processed = 0
        while processed < self._limits.max_actions_per_run:
            transition = self.process_next(token)
            if transition is BranchTransition.NO_WORK:
                return processed
            processed += 1
        raise ResourceLimitError(
            "nominal-introduction action limit exceeded",
            limit="max_actions_per_run",
            observed=processed + 1,
            allowed=self._limits.max_actions_per_run,
        )

    def resolve_clash(self, token: CancellationToken) -> BranchTransition:
        """Advance only an NI-owned merge branch selected by the current clash."""

        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        return self._session.run_with_recovery(token, lambda: self._resolve_clash(token))

    def _process_next(self, token: CancellationToken) -> BranchTransition:
        token.check()
        pending = self._access.take_pending_annotated_equality()
        if pending is None:
            return BranchTransition.NO_WORK
        token.check()
        predicate = self._annotation_predicate(pending.atom.predicate_id)
        support = min(pending.supports, key=_dependency_rank)
        canonical = self._canonical_nodes(pending.atom.arguments, support)
        if canonical is None:
            self._record(
                NominalEvent.IGNORED_PRUNED,
                pending,
                support,
                handles=pending.atom.arguments,
            )
            return BranchTransition.SATISFIED
        (first, second, root), dependency = canonical
        if self._can_forget_canonical(first, second, root):
            self._merger.merge(first, second, dependency, token)
            self._record(
                NominalEvent.FORGOT_ANNOTATION,
                pending,
                dependency,
                handles=(first, second, root),
            )
            return BranchTransition.DETERMINISTIC

        target, other = cast(
            tuple[NodeHandle, NodeHandle],
            self.target_for(first, second, root),
        )
        cardinality = cast(int, predicate.cardinality)
        if cardinality == 1:
            context = _BranchContext(
                pending.action_id,
                predicate.predicate_id,
                root,
                target,
                other,
                cardinality,
                pending.provenance_ids,
            )
            self._apply_choice(context, 1, dependency, token)
            return BranchTransition.DETERMINISTIC
        if cardinality > self._limits.max_branch_choices:
            raise ResourceLimitError(
                "nominal-introduction cardinality exceeds the branch-choice limit",
                limit="max_branch_choices",
                observed=cardinality,
                allowed=self._limits.max_branch_choices,
            )
        context = _BranchContext(
            pending.action_id,
            predicate.predicate_id,
            root,
            target,
            other,
            cardinality,
            pending.provenance_ids,
        )
        self._store_branch_context(context)
        branch = self._session.push_branch(
            BranchChoiceKind.MERGE,
            tuple(range(1, cardinality + 1)),
            source_id=pending.action_id,
            base_dependency=dependency,
        )
        self._record(
            NominalEvent.BRANCH_CREATED,
            pending,
            dependency,
            handles=(root, target, other),
            choice=branch.current,
        )
        self._apply_choice(context, branch.current, dependency.add(branch.level), token)
        return BranchTransition.BRANCHED

    def _resolve_clash(self, token: CancellationToken) -> BranchTransition:
        token.check()
        clash = self._session.clashes.current
        if clash is None:
            return BranchTransition.NO_WORK
        level = clash.dependency.maximum
        if level is None:
            return BranchTransition.UNSAT
        if not 0 <= level < len(self._session.branches):
            raise InternalInvariantError("clash backjump level has no branching point")
        branch = self._session.branches[level]
        context = self._branch_contexts.get(branch.source_id)
        if branch.choice_kind is not BranchChoiceKind.MERGE or context is None:
            return BranchTransition.NO_WORK
        without_level = DependencySet(clash.dependency.bits & ~(1 << level))
        alternative = self._session.advance_branch(level, without_level)
        token.check()
        if alternative is not None:
            current = self._session.branches[level]
            dependency = without_level if alternative == context.cardinality else clash.dependency
            self._record_context(
                NominalEvent.BRANCH_ADVANCED,
                context,
                dependency,
                handles=(context.root, context.target, context.other),
                choice=alternative,
            )
            self._apply_choice(context, current.current, dependency, token)
            return BranchTransition.ADVANCED

        self._remove_branch_context(context.action_id)
        propagated = self._session.dependencies.union(
            branch.base_dependency,
            branch.learned_dependency,
            without_level,
        )
        self._session.install_clash(
            Clash(
                ClashKind.IMPOSSIBLE_CARDINALITY,
                propagated,
                (context.action_id,),
                None if not context.provenance_ids else context.provenance_ids[0],
            )
        )
        self._record_context(
            NominalEvent.BRANCH_EXHAUSTED,
            context,
            propagated,
            handles=(context.root, context.target, context.other),
        )
        return BranchTransition.EXHAUSTED

    def _apply_choice(
        self,
        context: _BranchContext,
        choice: int,
        dependency: DependencySet,
        token: CancellationToken,
    ) -> None:
        token.check()
        predicate = self._annotation_predicate(context.predicate_id)
        canonical = self._canonical_nodes(
            (context.target, context.other, context.root),
            dependency,
            sort_pair=False,
        )
        if canonical is None:
            return
        (target, other, root), support = canonical
        ni_root, support = self._get_or_create_root(
            root,
            predicate,
            choice,
            support,
            context,
        )
        target_result = self._merger.merge(target, ni_root, support, token)
        self._record_context(
            NominalEvent.TARGET_MERGED,
            context,
            support,
            handles=(target, ni_root, target_result.representative),
            choice=choice,
        )
        if target_result.clashed:
            return
        token.check()
        try:
            other_node = self._session.nodes.get(other)
        except KeyError:
            return
        if other_node.lifecycle is NodeLifecycle.PRUNED:
            return
        other_rep, other_path = self._session.nodes.representative(other)
        ni_rep, ni_path = self._session.nodes.representative(ni_root)
        other_support = self._session.dependencies.union(support, other_path, ni_path)
        other_result = self._merger.merge(other_rep, ni_rep, other_support, token)
        self._record_context(
            NominalEvent.OTHER_MERGED,
            context,
            other_support,
            handles=(other_rep, ni_rep, other_result.representative),
            choice=choice,
        )

    def _get_or_create_root(
        self,
        root: NodeHandle,
        predicate: Predicate,
        level: int,
        dependency: DependencySet,
        context: _BranchContext,
    ) -> tuple[NodeHandle, DependencySet]:
        known = self._find_root_key(root, predicate, level)
        if known is not None:
            stored = self._roots[known]
            representative, path = self._session.nodes.representative(stored)
            self._session.nodes.require_active(representative)
            support = self._session.dependencies.union(dependency, path)
            self._record_context(
                NominalEvent.ROOT_REUSED,
                context,
                support,
                handles=(root, representative),
                choice=level,
            )
            return representative, support

        key = _root_key(root, predicate, level)
        created = self._session.create_node(
            NodeKind.NI,
            nominal_level=level,
            cardinality_tag=predicate.predicate_id,
        )
        self._access.register_node(created, dependency)
        self._roots[key] = created

        def undo() -> None:
            if self._roots.get(key) == created:
                self._roots.pop(key)

        self._session.trail.record("nominal.root.key", undo)
        self._record_context(
            NominalEvent.ROOT_CREATED,
            context,
            dependency,
            handles=(root, created),
            choice=level,
        )
        return created, dependency

    def _find_root_key(
        self,
        root: NodeHandle,
        predicate: Predicate,
        level: int,
    ) -> NominalRootKey | None:
        direct = _root_key(root, predicate, level)
        if direct in self._roots:
            return direct
        matches: list[NominalRootKey] = []
        for candidate in self._roots:
            if (
                candidate.predicate_id != predicate.predicate_id
                or candidate.role_id != predicate.role_id
                or candidate.filler_predicate_id != predicate.filler_predicate_id
                or candidate.cardinality != predicate.cardinality
                or candidate.level != level
            ):
                continue
            try:
                representative, _path = self._session.nodes.representative(candidate.root)
            except KeyError:
                continue
            if representative == root:
                matches.append(candidate)
        return None if not matches else min(matches)

    def _canonical_nodes(
        self,
        handles: tuple[NodeHandle, ...],
        dependency: DependencySet | None = None,
        *,
        sort_pair: bool = True,
    ) -> tuple[tuple[NodeHandle, ...], DependencySet] | None:
        if not all(isinstance(value, NodeHandle) for value in handles):
            raise TypeError("nominal arguments must be NodeHandle values")
        support = self._session.dependencies.empty if dependency is None else dependency
        if not isinstance(support, DependencySet):
            raise TypeError("dependency must be DependencySet or None")
        canonical: list[NodeHandle] = []
        paths: list[DependencySet] = [support]
        for handle in handles:
            try:
                node = self._session.nodes.get(handle)
            except KeyError:
                return None
            if node.lifecycle in {NodeLifecycle.PRUNED, NodeLifecycle.RETIRED}:
                return None
            representative, path = self._session.nodes.representative(handle)
            self._session.nodes.require_active(representative)
            canonical.append(representative)
            paths.append(path)
        if len(canonical) == 3 and sort_pair:
            canonical[:2] = sorted(canonical[:2], key=self._node_rank)
        return tuple(canonical), self._session.dependencies.union(*paths)

    def _can_forget_canonical(
        self,
        first: NodeHandle,
        second: NodeHandle,
        root: NodeHandle,
    ) -> bool:
        first_node = self._session.nodes.require_active(first)
        second_node = self._session.nodes.require_active(second)
        root_node = self._session.nodes.require_active(root)
        return (
            _is_root(first_node)
            or _is_root(second_node)
            or not _is_root(root_node)
            or (
                self._is_direct_parent(root, first_node)
                and self._is_direct_parent(root, second_node)
            )
        )

    @staticmethod
    def _is_direct_parent(root: NodeHandle, child: Node) -> bool:
        return child.parent == root

    def _annotation_predicate(self, predicate_id: int) -> Predicate:
        predicate = self._access.program.predicates.predicate(predicate_id)
        if predicate.kind is not PredicateKind.ANNOTATED_EQUALITY:
            raise ValueError("pending nominal action is not an annotated equality")
        if (
            predicate.cardinality is None
            or predicate.role_id is None
            or predicate.filler_predicate_id is None
        ):
            raise InternalInvariantError("annotated equality metadata is incomplete")
        return predicate

    def _store_branch_context(self, context: _BranchContext) -> None:
        if context.action_id in self._branch_contexts:
            raise InternalInvariantError("annotated equality already owns an NI branch")
        self._branch_contexts[context.action_id] = context

        def undo() -> None:
            if self._branch_contexts.get(context.action_id) == context:
                self._branch_contexts.pop(context.action_id)

        self._session.trail.record("nominal.branch.context", undo)

    def _remove_branch_context(self, action_id: int) -> None:
        context = self._branch_contexts.pop(action_id)
        self._session.trail.record(
            "nominal.branch.context.finish",
            lambda: self._branch_contexts.__setitem__(action_id, context),
        )

    def _record(
        self,
        event: NominalEvent,
        pending: PendingAnnotatedEquality,
        dependency: DependencySet,
        *,
        handles: tuple[NodeHandle, ...] = (),
        choice: int | None = None,
    ) -> None:
        self._append_trace(
            event,
            pending.action_id,
            pending.atom.predicate_id,
            dependency,
            handles,
            choice,
        )

    def _record_context(
        self,
        event: NominalEvent,
        context: _BranchContext,
        dependency: DependencySet,
        *,
        handles: tuple[NodeHandle, ...] = (),
        choice: int | None = None,
    ) -> None:
        self._append_trace(
            event,
            context.action_id,
            context.predicate_id,
            dependency,
            handles,
            choice,
        )

    def _append_trace(
        self,
        event: NominalEvent,
        action_id: int,
        predicate_id: int,
        dependency: DependencySet,
        handles: tuple[NodeHandle, ...],
        choice: int | None,
    ) -> None:
        record = NominalTraceEvent(
            len(self._trace),
            event,
            action_id,
            predicate_id,
            dependency,
            handles,
            choice,
        )
        self._trace.append(record)

        def undo() -> None:
            if not self._trace or self._trace[-1] != record:
                raise InternalInvariantError("nominal trace rollback order diverged")
            self._trace.pop()

        self._session.trail.record("nominal.trace", undo)

    def _node_rank(self, handle: NodeHandle) -> tuple[int, int, int]:
        node = self._session.nodes.get(handle)
        return node.creation_id, handle.slot, handle.generation


def _root_key(root: NodeHandle, predicate: Predicate, level: int) -> NominalRootKey:
    return NominalRootKey(
        root,
        predicate.predicate_id,
        cast(int, predicate.role_id),
        cast(int, predicate.filler_predicate_id),
        cast(int, predicate.cardinality),
        level,
    )


def _is_root(node: Node) -> bool:
    return node.parent is None


def _dependency_rank(value: DependencySet) -> tuple[int, int, int]:
    maximum = value.maximum
    return len(value), -1 if maximum is None else maximum, value.bits


__all__ = [
    "NominalEvent",
    "NominalIntroductionManager",
    "NominalLimits",
    "NominalMergeAccess",
    "NominalRootKey",
    "NominalRuleAccess",
    "NominalTraceEvent",
]
