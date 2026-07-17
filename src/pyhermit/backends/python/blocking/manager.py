"""Ancestor/anywhere/validated blocking maintenance over shared tableau state.

SPDX-License-Identifier: LGPL-3.0-or-later

The manager rebuilds one compact relevant-label projection per blocking pass, then
uses stable creation order and an exact signature index.  Explicit notifications retain
the earliest changed cursor; an unannounced state digest change safely falls back to a
full pass, so missed optimization hooks cannot create stale positive blocks.
"""

from __future__ import annotations

import json
from collections.abc import Callable
from dataclasses import dataclass
from enum import Enum
from typing import cast

from pyhermit.backends.python.state import (
    FactRow,
    Node,
    NodeHandle,
    NodeKind,
    NodeLifecycle,
    TableauSession,
)
from pyhermit.events import CancellationSource, CancellationToken
from pyhermit.exceptions import InternalInvariantError, ResourceLimitError

from .cache import BlockingSignatureCache
from .signatures import BlockingLabels, BlockingSignature, DirectBlockingChecker
from .strategy import BlockingManagerKind, BlockingPlan
from .validation import (
    BlockingValidator,
    CancellableBlockingValidator,
    PassAwareBlockingValidator,
    ValidationPassResult,
)


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class BlockingEvent(_StringEnum):
    INVALIDATED = "invalidated"
    DIRECT_BLOCK = "direct_block"
    INDIRECT_BLOCK = "indirect_block"
    CACHE_BLOCK = "cache_block"
    UNBLOCKED = "unblocked"
    RECOMPUTED = "recomputed"
    BLOCK_VALIDATED = "block_validated"
    BLOCK_REJECTED = "block_rejected"


@dataclass(frozen=True, slots=True)
class BlockingTraceEvent:
    sequence: int
    event: BlockingEvent
    node: NodeHandle | None = None
    blocker: NodeHandle | None = None
    state_digest: str | None = None
    details: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        if isinstance(self.sequence, bool) or not isinstance(self.sequence, int):
            raise TypeError("trace sequence must be a nonnegative integer")
        if self.sequence < 0:
            raise ValueError("trace sequence must be a nonnegative integer")
        if not isinstance(self.event, BlockingEvent):
            raise TypeError("event must be BlockingEvent")
        for name in ("node", "blocker"):
            value = getattr(self, name)
            if value is not None and not isinstance(value, NodeHandle):
                raise TypeError(f"{name} must be NodeHandle or None")
        if self.state_digest is not None and (
            not isinstance(self.state_digest, str) or not self.state_digest
        ):
            raise ValueError("state_digest must be a nonempty string or None")
        details = tuple(self.details)
        if any(
            isinstance(value, bool) or not isinstance(value, int) or value < 0 for value in details
        ):
            raise ValueError("trace details must be nonnegative integers")
        object.__setattr__(self, "details", details)

    def as_dict(self) -> dict[str, object]:
        return {
            "blocker": None
            if self.blocker is None
            else [self.blocker.slot, self.blocker.generation],
            "details": list(self.details),
            "event": self.event.value,
            "node": None if self.node is None else [self.node.slot, self.node.generation],
            "sequence": self.sequence,
            "state_digest": self.state_digest,
        }


@dataclass(frozen=True, slots=True, order=True)
class BlockingAssignment:
    node: NodeHandle
    blocker: NodeHandle | None
    directly: bool
    from_cache: bool = False

    def __post_init__(self) -> None:
        if not isinstance(self.node, NodeHandle):
            raise TypeError("node must be NodeHandle")
        if self.blocker is not None and not isinstance(self.blocker, NodeHandle):
            raise TypeError("blocker must be NodeHandle or None")
        if not isinstance(self.directly, bool) or not isinstance(self.from_cache, bool):
            raise TypeError("assignment flags must be bool")
        if self.from_cache and (self.blocker is not None or not self.directly):
            raise ValueError("a cache block is direct and has no live blocker handle")
        if self.blocker is None and self.directly and not self.from_cache:
            raise ValueError("a direct live block requires a blocker")

    @property
    def blocked(self) -> bool:
        return self.blocker is not None or self.from_cache

    def as_dict(self) -> dict[str, object]:
        return {
            "blocker": None
            if self.blocker is None
            else [self.blocker.slot, self.blocker.generation],
            "directly": self.directly,
            "from_cache": self.from_cache,
            "node": [self.node.slot, self.node.generation],
        }


class BlockingManager:
    __slots__ = (
        "_cache_blocks",
        "_dirty_creation_id",
        "_last_labels",
        "_last_recomputed_from",
        "_rejected_blocks",
        "_trace",
        "_validated_digest",
        "cache",
        "checker",
        "max_trace_events",
        "plan",
        "session",
    )

    def __init__(
        self,
        session: TableauSession,
        checker: DirectBlockingChecker,
        plan: BlockingPlan,
        *,
        cache: BlockingSignatureCache | None = None,
        max_trace_events: int = 100_000,
    ) -> None:
        if not isinstance(session, TableauSession):
            raise TypeError("session must be TableauSession")
        if not isinstance(checker, DirectBlockingChecker):
            raise TypeError("checker must implement DirectBlockingChecker")
        if not isinstance(plan, BlockingPlan):
            raise TypeError("plan must be BlockingPlan")
        if checker.kind is not plan.direct_checker_kind:
            raise ValueError("checker kind does not match the blocking plan")
        if (
            isinstance(max_trace_events, bool)
            or not isinstance(max_trace_events, int)
            or max_trace_events < 0
        ):
            raise ValueError("max_trace_events must be a nonnegative integer")
        if cache is not None:
            if not isinstance(cache, BlockingSignatureCache):
                raise TypeError("cache must be BlockingSignatureCache or None")
            if not plan.cache_allowed:
                raise ValueError("this blocking plan forbids signature caching")
            if cache.namespace.checker_kind is not checker.kind:
                raise ValueError("cache namespace checker kind does not match")
            if cache.namespace.core_mode is not plan.core_mode:
                raise ValueError("cache namespace core mode does not match")
            if cache.namespace.vocabulary_fingerprint != checker.vocabulary.fingerprint:
                raise ValueError("cache namespace vocabulary does not match")
        self.session = session
        self.checker = checker
        self.plan = plan
        self.cache = cache
        self.max_trace_events = max_trace_events
        self._cache_blocks: set[NodeHandle] = set()
        self._dirty_creation_id: int | None = 0
        self._last_labels: BlockingLabels | None = None
        self._last_recomputed_from: int | None = None
        self._rejected_blocks: dict[tuple[NodeHandle, NodeHandle], str] = {}
        self._trace: list[BlockingTraceEvent] = []
        self._validated_digest: str | None = None

    @property
    def last_recomputed_from(self) -> int | None:
        return self._last_recomputed_from

    @property
    def trace(self) -> tuple[BlockingTraceEvent, ...]:
        return tuple(self._trace)

    def invalidate(self, node: NodeHandle | None = None) -> None:
        if node is None:
            changed = 0
        else:
            if not isinstance(node, NodeHandle):
                raise TypeError("node must be NodeHandle or None")
            try:
                changed = self.session.nodes.get(node).creation_id
            except KeyError:
                changed = 0
        dirty = (
            changed if self._dirty_creation_id is None else min(changed, self._dirty_creation_id)
        )
        if dirty == self._dirty_creation_id and self._validated_digest is None:
            return
        self._trail_state("invalidate")
        self._dirty_creation_id = dirty
        self._validated_digest = None
        self._record(BlockingEvent.INVALIDATED, node=node, details=(changed,))

    def notify_fact_change(self, row: FactRow | int) -> None:
        value = self.session.extensions.row(row) if isinstance(row, int) else row
        if not isinstance(value, FactRow):
            raise TypeError("row must be FactRow or row ID")
        relevant = (
            value.key.predicate_id in self.checker.vocabulary.atomic_concepts
            or value.key.predicate_id in self.checker.vocabulary.atomic_object_roles
        )
        if not relevant:
            return
        creation_ids: list[tuple[int, NodeHandle]] = []
        for handle in value.key.arguments:
            try:
                creation_ids.append((self.session.nodes.get(handle).creation_id, handle))
            except KeyError:
                self.invalidate()
                return
        if creation_ids:
            self.invalidate(min(creation_ids)[1])

    def notify_node_change(self, node: NodeHandle) -> None:
        self.invalidate(node)

    def compute(self, *, force_full: bool = False) -> int:
        if not isinstance(force_full, bool):
            raise TypeError("force_full must be bool")
        labels = BlockingLabels.from_session(self.session, self.checker.vocabulary)
        previous = self._last_labels
        if force_full or previous is None:
            earliest = 0
        else:
            projected = previous.earliest_difference(labels)
            candidates = tuple(
                value for value in (self._dirty_creation_id, projected) if value is not None
            )
            if not candidates and previous.state_digest == labels.state_digest:
                return 0
            earliest = min(candidates) if candidates else 0

        checkpoint = self.session.trail.checkpoint("blocking-compute-atomic")
        self._trail_state("compute")
        try:
            expected = self.reference_assignments(labels)
            expected_by_node = {assignment.node: assignment for assignment in expected}
            active_handles = {
                node.handle
                for node in self.session.nodes.existing_nodes()
                if node.lifecycle is NodeLifecycle.ACTIVE
            }
            self._cache_blocks.intersection_update(active_handles)
            changed = 0
            old_blocked = {handle: self.is_blocked(handle) for handle in active_handles}
            for assignment in expected:
                node = self.session.nodes.get(assignment.node)
                current = self._current_assignment(node)
                if current != assignment:
                    self._apply_assignment(assignment, state_digest=labels.state_digest)
                    changed += 1
            for handle in tuple(self._cache_blocks):
                if handle not in expected_by_node or not expected_by_node[handle].from_cache:
                    self._cache_blocks.remove(handle)

            for handle, was_blocked in old_blocked.items():
                if was_blocked and not expected_by_node[handle].blocked:
                    self._reschedule_pending(handle)
            self._last_labels = labels
            if previous is None or previous.state_digest != labels.state_digest:
                self._rejected_blocks = {
                    pair: digest
                    for pair, digest in self._rejected_blocks.items()
                    if digest == labels.state_digest
                }
            self._dirty_creation_id = None
            self._last_recomputed_from = earliest
            if previous is None or previous.state_digest != labels.state_digest:
                self._validated_digest = None
            self._record(
                BlockingEvent.RECOMPUTED,
                state_digest=labels.state_digest,
                details=(earliest, len(expected), changed),
            )
            self.check_invariants(labels=labels, expected=expected)
            return changed
        except Exception:
            self.session.trail.rollback(checkpoint)
            raise

    def reference_assignments(
        self,
        labels: BlockingLabels | None = None,
    ) -> tuple[BlockingAssignment, ...]:
        selected_labels = labels or BlockingLabels.from_session(
            self.session, self.checker.vocabulary
        )
        nodes = sorted(
            (
                node
                for node in self.session.nodes.existing_nodes()
                if node.lifecycle is NodeLifecycle.ACTIVE
            ),
            key=lambda node: node.creation_id,
        )
        assignments: dict[NodeHandle, BlockingAssignment] = {}
        index: dict[tuple[object, ...], list[NodeHandle]] = {}
        for node in nodes:
            assignment = self._reference_assignment(node, selected_labels, assignments, index)
            assignments[node.handle] = assignment
            if not assignment.blocked and self.checker.can_be_blocker(self.session, node.handle):
                signature = self.checker.signature(self.session, selected_labels, node.handle)
                index.setdefault(signature.blocking_key, []).append(node.handle)
        return tuple(assignments[node.handle] for node in nodes)

    def _reference_assignment(
        self,
        node: Node,
        labels: BlockingLabels,
        assignments: dict[NodeHandle, BlockingAssignment],
        index: dict[tuple[object, ...], list[NodeHandle]],
    ) -> BlockingAssignment:
        if node.kind is not NodeKind.TREE or node.parent is None:
            return BlockingAssignment(node.handle, None, False)
        parent_assignment = assignments.get(node.parent)
        if parent_assignment is not None and parent_assignment.blocked:
            return BlockingAssignment(node.handle, node.parent, False)
        if not self.checker.can_be_blocked(self.session, node.handle):
            return BlockingAssignment(node.handle, None, False)
        signature = self.checker.signature(self.session, labels, node.handle)
        if self.cache is not None and self.plan.cache_allowed and self.cache.contains(signature):
            return BlockingAssignment(node.handle, None, True, True)
        blocker = self._reference_blocker(node, signature, labels, assignments, index)
        return BlockingAssignment(node.handle, blocker, blocker is not None)

    def _reference_blocker(
        self,
        node: Node,
        signature: BlockingSignature,
        labels: BlockingLabels,
        assignments: dict[NodeHandle, BlockingAssignment],
        index: dict[tuple[object, ...], list[NodeHandle]],
    ) -> NodeHandle | None:
        if self.plan.manager_kind is BlockingManagerKind.ANCESTOR:
            parent = node.parent
            while parent is not None:
                parent_node = self.session.nodes.get(parent)
                assignment = assignments.get(parent)
                if (
                    assignment is not None
                    and not assignment.blocked
                    and self.checker.can_be_blocker(self.session, parent)
                    and self.checker.signature(self.session, labels, parent).blocks(signature)
                    and self._rejected_blocks.get((node.handle, parent)) != labels.state_digest
                ):
                    return parent
                parent = parent_node.parent
            return None
        for candidate_handle in index.get(signature.blocking_key, ()):
            assignment = assignments[candidate_handle]
            if (
                not assignment.blocked
                and self._rejected_blocks.get((node.handle, candidate_handle))
                != labels.state_digest
            ):
                return candidate_handle
        return None

    def is_blocked(self, node: NodeHandle) -> bool:
        value = self.session.nodes.get(node)
        return value.lifecycle is NodeLifecycle.ACTIVE and (
            value.blocker is not None or node in self._cache_blocks
        )

    def is_directly_blocked(self, node: NodeHandle) -> bool:
        value = self.session.nodes.get(node)
        return value.lifecycle is NodeLifecycle.ACTIVE and (
            value.directly_blocked or node in self._cache_blocks
        )

    def blocker(self, node: NodeHandle) -> NodeHandle | None:
        return self.session.nodes.get(node).blocker

    def validation_pass(
        self,
        validator: BlockingValidator,
        *,
        token: CancellationToken | None = None,
    ) -> ValidationPassResult:
        if self.plan.manager_kind is not BlockingManagerKind.VALIDATED_ANYWHERE:
            raise ValueError("validation is available only for validated-anywhere blocking")
        if not isinstance(validator, BlockingValidator):
            raise TypeError("validator must implement BlockingValidator")
        if token is not None and not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken or None")
        effective_token = CancellationSource().token if token is None else token
        return self.session.run_with_recovery(
            effective_token,
            lambda: self._validation_pass(validator, effective_token),
        )

    def _validation_pass(
        self,
        validator: BlockingValidator,
        token: CancellationToken,
    ) -> ValidationPassResult:
        self.compute()
        labels = self._last_labels
        if labels is None:
            raise InternalInvariantError("blocking labels are unavailable after compute")
        assignments = self.reference_assignments(labels)
        direct_assignments = tuple(
            assignment
            for assignment in assignments
            if assignment.directly and not assignment.from_cache and assignment.blocker is not None
        )
        checkpoint = self.session.trail.checkpoint("blocking-validation-atomic")
        self._trail_state("validation")
        pass_aware = (
            cast(PassAwareBlockingValidator, validator)
            if isinstance(validator, PassAwareBlockingValidator)
            else None
        )
        pass_started = False
        try:
            if pass_aware is not None and direct_assignments:
                pass_aware.begin_validation_pass(self.session, labels.state_digest, token)
                pass_started = True
            try:
                checked = 0
                for assignment in direct_assignments:
                    if assignment.blocker is None:
                        raise InternalInvariantError("direct block has no live blocker")
                    token.check()
                    signature = self.checker.signature(self.session, labels, assignment.node)
                    if isinstance(validator, CancellableBlockingValidator):
                        decision = validator.validate_block_cancellable(
                            self.session,
                            assignment.node,
                            assignment.blocker,
                            signature,
                            token,
                        )
                    else:
                        decision = validator.validate_block(
                            self.session,
                            assignment.node,
                            assignment.blocker,
                            signature,
                        )
                    checked += 1
                    token.check()
                    if decision.valid:
                        self._record(
                            BlockingEvent.BLOCK_VALIDATED,
                            node=assignment.node,
                            blocker=assignment.blocker,
                            state_digest=labels.state_digest,
                        )
                        continue
                    for row_id in decision.promote_row_ids:
                        if not self.session.extensions.row(row_id).active:
                            raise ValueError("validator requested promotion of an inactive row")
                    for node in decision.reschedule_nodes:
                        self.session.nodes.require_active(node)
                    self._rejected_blocks[(assignment.node, assignment.blocker)] = (
                        labels.state_digest
                    )
                    self._apply_assignment(
                        BlockingAssignment(assignment.node, None, False),
                        state_digest=labels.state_digest,
                    )
                    promoted = sum(
                        int(self.session.extensions.set_core(row_id))
                        for row_id in decision.promote_row_ids
                    )
                    reschedule = set(decision.reschedule_nodes)
                    reschedule.add(assignment.node)
                    for node in sorted(
                        reschedule,
                        key=lambda value: self.session.nodes.require_active(value).creation_id,
                    ):
                        self._reschedule_pending(node, force=True)
                    self._record(
                        BlockingEvent.BLOCK_REJECTED,
                        node=assignment.node,
                        blocker=assignment.blocker,
                        state_digest=labels.state_digest,
                        details=decision.violation_ids,
                    )
                    self.invalidate(assignment.node)
                    token.check()
                    return ValidationPassResult(
                        False,
                        checked,
                        1,
                        promoted,
                        len(reschedule),
                        decision.violation_ids,
                        labels.state_digest,
                    )
                self._validated_digest = labels.state_digest
                token.check()
                return ValidationPassResult(
                    True,
                    checked,
                    0,
                    0,
                    0,
                    (),
                    labels.state_digest,
                )
            finally:
                if pass_started and pass_aware is not None:
                    pass_aware.end_validation_pass()
        except Exception:
            self.session.trail.rollback(checkpoint)
            raise

    def validate_to_fixed_point(
        self,
        validator: BlockingValidator,
        saturate: Callable[[], None],
        *,
        token: CancellationToken | None = None,
        max_rounds: int = 1_024,
    ) -> tuple[ValidationPassResult, ...]:
        if not callable(saturate):
            raise TypeError("saturate must be callable")
        if isinstance(max_rounds, bool) or not isinstance(max_rounds, int) or max_rounds <= 0:
            raise ValueError("max_rounds must be a positive integer")
        results: list[ValidationPassResult] = []
        for _round in range(max_rounds):
            result = self.validation_pass(validator, token=token)
            results.append(result)
            if result.valid:
                return tuple(results)
            saturate()
            self.compute()
        raise ResourceLimitError(
            "blocking validation did not reach a fixed point",
            limit="blocking_validation_rounds",
            observed=max_rounds,
            allowed=max_rounds,
        )

    def ready_for_sat(self) -> bool:
        if not any(
            node.kind is NodeKind.TREE and node.lifecycle is NodeLifecycle.ACTIVE
            for node in self.session.nodes.existing_nodes()
        ):
            return True
        self.compute()
        labels = self._last_labels
        if labels is None:
            return False
        return (
            self.plan.manager_kind is not BlockingManagerKind.VALIDATED_ANYWHERE
            or self._validated_digest == labels.state_digest
        )

    def model_found(
        self,
        *,
        satisfiable: bool,
        completed: bool,
        has_nominals: bool,
        has_additional_ontology: bool,
        query_local_axioms: bool,
        aborted: bool = False,
    ) -> int:
        self.compute()
        if satisfiable and completed and not self.ready_for_sat():
            raise InternalInvariantError("SAT cannot be reported before blocking validation")
        if self.cache is None or not self.plan.cache_allowed:
            return 0
        labels = self._last_labels
        if labels is None:
            return 0
        signatures = (
            self.checker.signature(self.session, labels, node.handle)
            for node in sorted(
                self.session.nodes.existing_nodes(), key=lambda value: value.creation_id
            )
            if node.lifecycle is NodeLifecycle.ACTIVE
            and not self.is_blocked(node.handle)
            and self.checker.can_be_blocker(self.session, node.handle)
        )
        return self.cache.promote_model(
            signatures,
            satisfiable=satisfiable,
            completed=completed,
            has_nominals=has_nominals,
            has_additional_ontology=has_additional_ontology,
            query_local_axioms=query_local_axioms,
            aborted=aborted,
        )

    def check_invariants(
        self,
        *,
        labels: BlockingLabels | None = None,
        expected: tuple[BlockingAssignment, ...] | None = None,
    ) -> None:
        selected_labels = labels or BlockingLabels.from_session(
            self.session, self.checker.vocabulary
        )
        reference = expected or self.reference_assignments(selected_labels)
        for assignment in reference:
            node = self.session.nodes.get(assignment.node)
            actual = self._current_assignment(node)
            if actual != assignment:
                raise InternalInvariantError(
                    "incremental blocking state differs from full recomputation"
                )
            if assignment.blocker is not None:
                blocker = self.session.nodes.require_active(assignment.blocker)
                if blocker.creation_id >= node.creation_id:
                    raise InternalInvariantError("blocker does not precede blocked node")
                if assignment.directly and not self.checker.is_blocked_by(
                    self.session,
                    selected_labels,
                    assignment.blocker,
                    assignment.node,
                ):
                    raise InternalInvariantError("direct blocker signature is invalid")

    def logical_snapshot(self) -> dict[str, object]:
        labels = BlockingLabels.from_session(self.session, self.checker.vocabulary)
        assignments = self.reference_assignments(labels)
        return {
            "assignments": [assignment.as_dict() for assignment in assignments],
            "cache_fingerprints": [] if self.cache is None else list(self.cache.fingerprints()),
            "checker": self.checker.kind.value,
            "core_mode": self.plan.core_mode.value,
            "last_recomputed_from": self._last_recomputed_from,
            "manager": self.plan.manager_kind.value,
            "rejected_blocks": [
                {
                    "blocked": [blocked.slot, blocked.generation],
                    "blocker": [blocker.slot, blocker.generation],
                    "state_digest": digest,
                }
                for (blocked, blocker), digest in sorted(self._rejected_blocks.items())
                if digest == labels.state_digest
            ],
            "state_digest": labels.state_digest,
            "validated": self._validated_digest == labels.state_digest,
            "vocabulary": self.checker.vocabulary.fingerprint,
        }

    def canonical_snapshot(self) -> str:
        return json.dumps(
            self.logical_snapshot(),
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        )

    def trace_snapshot(self) -> str:
        return json.dumps(
            [event.as_dict() for event in self._trace],
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        )

    def _current_assignment(self, node: Node) -> BlockingAssignment:
        if node.handle in self._cache_blocks:
            return BlockingAssignment(node.handle, None, True, True)
        return BlockingAssignment(
            node.handle,
            node.blocker,
            node.directly_blocked if node.blocker is not None else False,
        )

    def _apply_assignment(
        self,
        assignment: BlockingAssignment,
        *,
        state_digest: str | None = None,
    ) -> None:
        node = self.session.nodes.require_active(assignment.node)
        if assignment.from_cache:
            if node.blocker is not None:
                self.session.nodes.set_blocked(node.handle, None, directly=False)
            self._cache_blocks.add(node.handle)
            self._record(
                BlockingEvent.CACHE_BLOCK,
                node=node.handle,
                state_digest=state_digest,
            )
            return
        was_cache_blocked = node.handle in self._cache_blocks
        self._cache_blocks.discard(node.handle)
        if node.blocker != assignment.blocker or (
            assignment.blocker is not None and node.directly_blocked != assignment.directly
        ):
            self.session.nodes.set_blocked(
                node.handle,
                assignment.blocker,
                directly=assignment.directly,
            )
            event = (
                BlockingEvent.UNBLOCKED
                if assignment.blocker is None
                else (
                    BlockingEvent.DIRECT_BLOCK
                    if assignment.directly
                    else BlockingEvent.INDIRECT_BLOCK
                )
            )
            self._record(
                event,
                node=node.handle,
                blocker=assignment.blocker,
                state_digest=state_digest,
            )
        elif was_cache_blocked:
            self._record(
                BlockingEvent.UNBLOCKED,
                node=node.handle,
                state_digest=state_digest,
            )

    def _trail_state(self, kind: str) -> None:
        cache_blocks = set(self._cache_blocks)
        dirty_creation_id = self._dirty_creation_id
        last_labels = self._last_labels
        last_recomputed_from = self._last_recomputed_from
        rejected_blocks = dict(self._rejected_blocks)
        validated_digest = self._validated_digest
        trace_length = len(self._trace)

        def undo() -> None:
            self._cache_blocks = set(cache_blocks)
            self._dirty_creation_id = dirty_creation_id
            self._last_labels = last_labels
            self._last_recomputed_from = last_recomputed_from
            self._rejected_blocks = dict(rejected_blocks)
            self._validated_digest = validated_digest
            del self._trace[trace_length:]

        self.session.trail.record(f"blocking.{kind}", undo)

    def _record(
        self,
        event: BlockingEvent,
        *,
        node: NodeHandle | None = None,
        blocker: NodeHandle | None = None,
        state_digest: str | None = None,
        details: tuple[int, ...] = (),
    ) -> None:
        if len(self._trace) >= self.max_trace_events:
            return
        self._trace.append(
            BlockingTraceEvent(
                len(self._trace),
                event,
                node,
                blocker,
                state_digest,
                details,
            )
        )

    def _reschedule_pending(self, handle: NodeHandle, *, force: bool = False) -> None:
        try:
            node = self.session.nodes.require_active(handle)
        except (KeyError, ValueError):
            return
        if not force and not node.unprocessed_existentials:
            return
        priority = (node.creation_id, handle.slot, handle.generation)
        self.session.existential_candidates.enqueue(handle, priority)


__all__ = [
    "BlockingAssignment",
    "BlockingEvent",
    "BlockingManager",
    "BlockingTraceEvent",
]
