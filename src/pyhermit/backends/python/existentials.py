"""Pure-Python minimum-cardinality satisfaction and witness expansion.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import hashlib
import itertools
from dataclasses import dataclass
from enum import Enum
from typing import Protocol, TypeVar, cast

from pyhermit.backends.python.rules import BranchTransition, GroundRuleAtom
from pyhermit.backends.python.state import (
    BranchChoiceKind,
    BranchingPoint,
    Clash,
    ClashKind,
    DependencySet,
    NodeHandle,
    NodeKind,
    NodeSort,
    TableauSession,
)
from pyhermit.clauses import ClauseProgram, Predicate, PredicateKind, SymbolKind, TermSort
from pyhermit.events import CancellationToken
from pyhermit.exceptions import InternalInvariantError, ResourceLimitError


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


_MapValueT = TypeVar("_MapValueT")


class ExpansionStrategy(_StringEnum):
    CREATION_ORDER = "creation_order"
    INDIVIDUAL_REUSE = "individual_reuse"


class ExpansionStatus(_StringEnum):
    NO_WORK = "no_work"
    BLOCKED = "blocked"
    SATISFIED = "satisfied"
    EXPANDED = "expanded"
    CLASHED = "clashed"


@dataclass(frozen=True, slots=True)
class ExpansionLimits:
    max_witnesses_per_obligation: int = 1_000_000
    max_distinct_search_steps: int = 10_000_000
    cancellation_interval: int = 256

    def __post_init__(self) -> None:
        for name in (
            "max_witnesses_per_obligation",
            "max_distinct_search_steps",
            "cancellation_interval",
        ):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
                raise ValueError(f"{name} must be a positive integer")


@dataclass(frozen=True, slots=True)
class ExpansionResult:
    status: ExpansionStatus
    root: NodeHandle | None = None
    existential_id: int | None = None
    witnesses: tuple[NodeHandle, ...] = ()


@dataclass(frozen=True, slots=True)
class _ReuseBranch:
    source_id: int
    root: NodeHandle
    predicate_id: int
    supports: tuple[DependencySet, ...]


class ExpansionRuleAccess(Protocol):
    @property
    def program(self) -> ClauseProgram: ...

    def dispatch_ground_atom(
        self,
        atom: GroundRuleAtom,
        dependency: DependencySet,
        *,
        core: bool = False,
        provenance_ids: tuple[int, ...] = (),
    ) -> bool: ...

    def register_node(
        self,
        handle: NodeHandle,
        dependency: DependencySet | None = None,
    ) -> None: ...

    def data_values_known_different(self, left: NodeHandle, right: NodeHandle) -> bool: ...

    def data_value_satisfies(
        self,
        handle: NodeHandle,
        predicate_id: int,
        token: CancellationToken,
    ) -> bool: ...


class ExistentialExpansionManager:
    """Expand queued compiled ``AtLeast`` predicates in stable creation order."""

    __slots__ = (
        "_access",
        "_data_roles",
        "_inequality_by_sort",
        "_limits",
        "_object_roles",
        "_reuse_branches",
        "_reuse_nodes",
        "_session",
        "_strategy",
        "_temporarily_disabled_reuse",
    )

    def __init__(
        self,
        session: TableauSession,
        access: ExpansionRuleAccess,
        *,
        strategy: ExpansionStrategy = ExpansionStrategy.CREATION_ORDER,
        limits: ExpansionLimits | None = None,
    ) -> None:
        if not isinstance(session, TableauSession):
            raise TypeError("session must be TableauSession")
        if not isinstance(strategy, ExpansionStrategy):
            raise TypeError("strategy must be ExpansionStrategy")
        selected_limits = ExpansionLimits() if limits is None else limits
        if not isinstance(selected_limits, ExpansionLimits):
            raise TypeError("limits must be ExpansionLimits or None")
        self._session = session
        self._access = access
        self._strategy = strategy
        self._limits = selected_limits
        self._object_roles = _role_predicates(access.program, PredicateKind.OBJECT_ROLE)
        self._data_roles = _role_predicates(access.program, PredicateKind.DATA_ROLE)
        self._inequality_by_sort = {
            predicate.argument_sorts[0]: predicate.predicate_id
            for predicate in access.program.predicates.predicates
            if predicate.kind is PredicateKind.INEQUALITY
        }
        self._reuse_nodes: dict[int, NodeHandle] = {}
        self._reuse_branches: dict[int, _ReuseBranch] = {}
        self._temporarily_disabled_reuse: set[int] = set()

    @property
    def strategy(self) -> ExpansionStrategy:
        return self._strategy

    def process_next(self, token: CancellationToken) -> ExpansionResult:
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        return self._session.run_with_recovery(token, lambda: self._process_next(token))

    def _process_next(self, token: CancellationToken) -> ExpansionResult:
        token.check()
        root = self._take_unblocked_candidate()
        if root is None:
            return (
                ExpansionResult(ExpansionStatus.BLOCKED)
                if self._session.existential_candidates.values()
                else ExpansionResult(ExpansionStatus.NO_WORK)
            )
        node = self._session.nodes.require_active(root)
        existential_id = min(node.unprocessed_existentials)
        predicate = self._access.program.predicates.predicate(existential_id)
        if predicate.kind not in {
            PredicateKind.AT_LEAST_OBJECT,
            PredicateKind.AT_LEAST_DATA,
        }:
            raise InternalInvariantError("existential queue contains a non-at-least predicate")
        supports = self._obligation_supports(predicate.predicate_id, root)
        if not supports:
            self._mark_processed(root, existential_id)
            return ExpansionResult(ExpansionStatus.SATISFIED, root, existential_id)
        if self.is_satisfied(predicate, root, token):
            self._mark_processed(root, existential_id)
            return ExpansionResult(ExpansionStatus.SATISFIED, root, existential_id)
        cardinality = predicate.cardinality
        if cardinality is None:
            raise InternalInvariantError("at-least predicate has no cardinality")
        if cardinality > self._limits.max_witnesses_per_obligation:
            raise ResourceLimitError(
                "existential witness limit exceeded",
                limit="max_witnesses_per_obligation",
                observed=cardinality,
                allowed=self._limits.max_witnesses_per_obligation,
            )
        if self._uses_bottom_role(predicate):
            dependency = min(supports, key=_dependency_rank)
            self._session.install_clash(
                Clash(
                    ClashKind.IMPOSSIBLE_CARDINALITY,
                    dependency,
                    (predicate.predicate_id,),
                )
            )
            return ExpansionResult(ExpansionStatus.CLASHED, root, existential_id)
        if self._can_reuse(predicate):
            return self._expand_with_reuse(predicate, root, supports, token)
        witnesses = (
            self._expand_object(predicate, root, supports, token)
            if predicate.kind is PredicateKind.AT_LEAST_OBJECT
            else self._expand_data(predicate, root, supports, token)
        )
        self._mark_processed(root, existential_id)
        return ExpansionResult(
            ExpansionStatus.EXPANDED,
            root,
            existential_id,
            witnesses,
        )

    def owns_branch(self, branch: BranchingPoint) -> bool:
        if not isinstance(branch, BranchingPoint):
            raise TypeError("branch must be BranchingPoint")
        return (
            branch.choice_kind is BranchChoiceKind.MERGE
            and branch.source_id in self._reuse_branches
        )

    def resolve_clash(self, token: CancellationToken) -> BranchTransition:
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        return self._session.run_with_recovery(token, lambda: self._resolve_clash(token))

    def _resolve_clash(self, token: CancellationToken) -> BranchTransition:
        token.check()
        clash = self._session.clashes.current
        if clash is None:
            return BranchTransition.NO_WORK
        level = clash.dependency.maximum
        if level is None:
            return BranchTransition.UNSAT
        if not 0 <= level < len(self._session.branches):
            raise InternalInvariantError("reuse clash target has no branching point")
        branch = self._session.branches[level]
        record = self._reuse_branches.get(branch.source_id)
        if record is None or branch.choice_kind is not BranchChoiceKind.MERGE:
            raise InternalInvariantError("clash is not owned by individual reuse")
        without_level = DependencySet(clash.dependency.bits & ~(1 << level))
        alternative = self._session.advance_branch(level, without_level)
        token.check()
        if alternative is not None:
            if alternative != 1:
                raise InternalInvariantError("individual-reuse alternative is malformed")
            self._trail_add(self._temporarily_disabled_reuse, record.predicate_id)
            current = self._session.branches[level]
            dependency = self._session.dependencies.union(
                current.base_dependency,
                without_level,
            ).add(level)
            predicate = self._access.program.predicates.predicate(record.predicate_id)
            witnesses = self._expand_object(
                predicate,
                record.root,
                (dependency,),
                token,
            )
            if len(witnesses) != 1:
                raise InternalInvariantError("reuse fallback must create one witness")
            return BranchTransition.ADVANCED
        self._trail_remove(self._reuse_branches, branch.source_id)
        propagated = self._session.dependencies.union(
            branch.base_dependency,
            branch.learned_dependency,
            without_level,
        )
        self._session.install_clash(
            Clash(
                ClashKind.EMPTY_HEAD,
                propagated,
                (branch.source_id,),
            )
        )
        return BranchTransition.EXHAUSTED

    def is_satisfied(
        self,
        predicate: Predicate,
        root: NodeHandle,
        token: CancellationToken,
    ) -> bool:
        if not isinstance(predicate, Predicate):
            raise TypeError("predicate must be Predicate")
        if not isinstance(root, NodeHandle):
            raise TypeError("root must be NodeHandle")
        cardinality = predicate.cardinality
        if cardinality is None:
            raise ValueError("predicate is not a cardinality predicate")
        if cardinality <= 0:
            return True
        if predicate.kind is PredicateKind.AT_LEAST_OBJECT:
            candidates = self._object_satisfiers(predicate, root)
            return self._contains_distinct_subset(
                candidates,
                cardinality,
                TermSort.OBJECT,
                token,
            )
        if predicate.kind is PredicateKind.AT_LEAST_DATA:
            roles = predicate.annotation
            if len(roles) > 1:
                return bool(self._data_tuple_satisfiers(predicate, root))
            candidates = self._data_satisfiers(predicate, root, token)
            return self._contains_distinct_subset(
                candidates,
                cardinality,
                TermSort.DATA,
                token,
            )
        raise ValueError("predicate is not an at-least predicate")

    def _take_unblocked_candidate(self) -> NodeHandle | None:
        deferred: list[NodeHandle] = []
        selected: NodeHandle | None = None
        for _index in range(len(self._session.existential_candidates)):
            handle = self._session.existential_candidates.pop()
            if handle is None:
                break
            try:
                node = self._session.nodes.require_active(handle)
            except (KeyError, ValueError):
                continue
            if not node.unprocessed_existentials:
                continue
            if node.blocker is not None:
                deferred.append(handle)
                continue
            selected = handle
            break
        for handle in deferred:
            node = self._session.nodes.require_active(handle)
            self._session.existential_candidates.enqueue(
                handle,
                (node.creation_id, handle.slot, handle.generation),
            )
        return selected

    def _can_reuse(self, predicate: Predicate) -> bool:
        if self._strategy is not ExpansionStrategy.INDIVIDUAL_REUSE:
            return False
        if predicate.kind is not PredicateKind.AT_LEAST_OBJECT or predicate.cardinality != 1:
            return False
        filler_id = _required(predicate.filler_predicate_id, "reuse filler")
        if predicate.predicate_id in self._temporarily_disabled_reuse:
            return False
        filler = self._access.program.predicates.predicate(filler_id)
        if filler.kind is not PredicateKind.CONCEPT or filler.symbol_id is None:
            return False
        symbol = self._access.program.symbols.domain(SymbolKind.CLASS_EXPRESSION).values[
            filler.symbol_id
        ]
        return not symbol.generated

    def _expand_with_reuse(
        self,
        predicate: Predicate,
        root: NodeHandle,
        supports: tuple[DependencySet, ...],
        token: CancellationToken,
    ) -> ExpansionResult:
        filler_id = _required(predicate.filler_predicate_id, "reuse filler")
        self._mark_processed(root, predicate.predicate_id)
        source_id = _reuse_source_id(root, predicate.predicate_id)
        if source_id in self._reuse_branches:
            raise InternalInvariantError("duplicate active individual-reuse branch")
        record = _ReuseBranch(source_id, root, predicate.predicate_id, supports)
        self._trail_set(self._reuse_branches, source_id, record)
        base = min(supports, key=_dependency_rank)
        branch = self._session.push_branch(
            BranchChoiceKind.MERGE,
            (0, 1),
            source_id=source_id,
            base_dependency=base,
        )
        dependency = base.add(branch.level)
        candidate = self._parent_reuse_candidate(predicate, root)
        if candidate is None:
            candidate = self._model_reuse_candidate(filler_id, dependency)
        representative, path = self._session.nodes.representative(candidate)
        dependency = self._session.dependencies.union(dependency, path)
        role_id = _required(predicate.role_id, "reuse role")
        if role_id != self._access.program.role_model.top_object_role_id:
            role_predicate = self._object_roles.get(role_id)
            if role_predicate is None:
                raise InternalInvariantError("reuse role predicate is absent")
            self._access.dispatch_ground_atom(
                GroundRuleAtom(role_predicate, (root, representative)),
                dependency,
                core=True,
            )
        token.check()
        return ExpansionResult(
            ExpansionStatus.EXPANDED,
            root,
            predicate.predicate_id,
            (representative,),
        )

    def _parent_reuse_candidate(
        self,
        predicate: Predicate,
        root: NodeHandle,
    ) -> NodeHandle | None:
        node = self._session.nodes.require_active(root)
        if node.parent is None:
            return None
        parent, _path = self._session.nodes.representative(node.parent)
        filler = _required(predicate.filler_predicate_id, "parent-reuse filler")
        return parent if _has_fact(self._session, filler, (parent,)) else None

    def _model_reuse_candidate(
        self,
        filler_id: int,
        dependency: DependencySet,
    ) -> NodeHandle:
        known = self._reuse_nodes.get(filler_id)
        if known is not None:
            try:
                representative, _path = self._session.nodes.representative(known)
                self._session.nodes.require_active(representative)
            except (KeyError, ValueError):
                self._trail_remove(self._reuse_nodes, filler_id)
            else:
                return representative
        witness = self._session.create_node(NodeKind.NI)
        self._access.register_node(witness, dependency)
        self._access.dispatch_ground_atom(
            GroundRuleAtom(filler_id, (witness,)),
            dependency,
            core=True,
        )
        self._trail_set(self._reuse_nodes, filler_id, witness)
        return witness

    def _trail_add(self, values: set[int], value: int) -> None:
        if value in values:
            return
        self._session.trail.record("existentials.reuse.disable", lambda: values.remove(value))
        values.add(value)

    def _trail_set(
        self,
        values: dict[int, _MapValueT],
        key: int,
        value: _MapValueT,
    ) -> None:
        if key in values:
            raise InternalInvariantError("reuse map key already exists")

        def undo() -> None:
            values.pop(key, None)

        self._session.trail.record("existentials.reuse.map", undo)
        values[key] = value

    def _trail_remove(self, values: dict[int, _MapValueT], key: int) -> None:
        if key not in values:
            return
        previous = values.pop(key)
        self._session.trail.record(
            "existentials.reuse.unmap",
            lambda: values.__setitem__(key, previous),
        )

    def _obligation_supports(
        self,
        predicate_id: int,
        root: NodeHandle,
    ) -> tuple[DependencySet, ...]:
        return tuple(
            support
            for row in self._session.extensions.retrieve(
                predicate_id,
                bindings={0: root},
            )
            for support in row.supports
        )

    def _mark_processed(self, root: NodeHandle, existential_id: int) -> None:
        self._session.nodes.mark_existential(root, existential_id, pending=False)
        node = self._session.nodes.require_active(root)
        if node.unprocessed_existentials:
            self._session.existential_candidates.enqueue(
                root,
                (node.creation_id, root.slot, root.generation),
            )

    def _object_satisfiers(
        self,
        predicate: Predicate,
        root: NodeHandle,
    ) -> tuple[NodeHandle, ...]:
        filler = _required(predicate.filler_predicate_id, "object at-least filler")
        role_id = _required(predicate.role_id, "object at-least role")
        role_model = self._access.program.role_model
        if role_id == role_model.bottom_object_role_id:
            return ()
        if role_id == role_model.top_object_role_id:
            targets = tuple(
                handle
                for handle in self._session.nodes.active_handles()
                if self._session.nodes.get(handle).sort is NodeSort.OBJECT
            )
        else:
            role_predicate = self._object_roles.get(role_id)
            if role_predicate is None:
                raise InternalInvariantError("at-least object role has no extension predicate")
            targets = tuple(
                row.key.arguments[1]
                for row in self._session.extensions.retrieve(
                    role_predicate,
                    bindings={0: root},
                )
            )
        result: set[NodeHandle] = set()
        for target in targets:
            representative, _path = self._session.nodes.representative(target)
            target_node = self._session.nodes.require_active(representative)
            if target_node.blocker is not None and target_node.parent != root:
                continue
            if _has_fact(self._session, filler, (representative,)):
                result.add(representative)
        return tuple(sorted(result, key=self._node_rank))

    def _data_satisfiers(
        self,
        predicate: Predicate,
        root: NodeHandle,
        token: CancellationToken,
    ) -> tuple[NodeHandle, ...]:
        filler = _required(predicate.filler_predicate_id, "data at-least filler")
        role_id = _required(predicate.role_id, "data at-least role")
        role_model = self._access.program.role_model
        if role_id == role_model.bottom_data_property_id:
            return ()
        if role_id == role_model.top_data_property_id:
            targets = tuple(
                handle
                for handle in self._session.nodes.active_handles()
                if self._session.nodes.get(handle).sort is NodeSort.DATA
            )
        else:
            role_predicate = self._data_roles.get(role_id)
            if role_predicate is None:
                raise InternalInvariantError("at-least data role has no extension predicate")
            targets = tuple(
                row.key.arguments[1]
                for row in self._session.extensions.retrieve(
                    role_predicate,
                    bindings={0: root},
                )
            )
        return tuple(
            sorted(
                {
                    self._session.nodes.representative(target)[0]
                    for target in targets
                    if _has_fact(
                        self._session,
                        filler,
                        (self._session.nodes.representative(target)[0],),
                    )
                    or self._access.data_value_satisfies(
                        self._session.nodes.representative(target)[0],
                        filler,
                        token,
                    )
                },
                key=self._node_rank,
            )
        )

    def _data_tuple_satisfiers(
        self,
        predicate: Predicate,
        root: NodeHandle,
    ) -> tuple[tuple[NodeHandle, ...], ...]:
        filler = _required(predicate.filler_predicate_id, "n-ary data at-least filler")
        role_model = self._access.program.role_model
        domains: list[set[NodeHandle]] = []
        for role_id in predicate.annotation:
            if role_id == role_model.bottom_data_property_id:
                return ()
            if role_id == role_model.top_data_property_id:
                domains.append(
                    {
                        handle
                        for handle in self._session.nodes.active_handles()
                        if self._session.nodes.get(handle).sort is NodeSort.DATA
                    }
                )
                continue
            role_predicate = self._data_roles.get(role_id)
            if role_predicate is None:
                raise InternalInvariantError("n-ary data role has no extension predicate")
            domains.append(
                {
                    self._session.nodes.representative(row.key.arguments[1])[0]
                    for row in self._session.extensions.retrieve(
                        role_predicate,
                        bindings={0: root},
                    )
                }
            )
        return tuple(
            row.key.arguments
            for row in self._session.extensions.retrieve(filler)
            if len(row.key.arguments) == len(domains)
            and all(
                value in domain for value, domain in zip(row.key.arguments, domains, strict=True)
            )
        )

    def _contains_distinct_subset(
        self,
        candidates: tuple[NodeHandle, ...],
        cardinality: int,
        sort: TermSort,
        token: CancellationToken,
    ) -> bool:
        if cardinality == 1:
            return bool(candidates)
        if len(candidates) < cardinality:
            return False
        selected: list[NodeHandle] = []
        next_indices = [0]
        steps = 0

        while next_indices:
            steps += 1
            if steps > self._limits.max_distinct_search_steps:
                raise ResourceLimitError(
                    "pairwise-distinct successor search limit exceeded",
                    limit="max_distinct_search_steps",
                    observed=steps,
                    allowed=self._limits.max_distinct_search_steps,
                )
            if steps % self._limits.cancellation_interval == 0:
                token.add_work(self._limits.cancellation_interval)
                token.check()
            index = next_indices[-1]
            if index >= len(candidates) or len(candidates) - index < cardinality - len(selected):
                next_indices.pop()
                if selected:
                    selected.pop()
                continue
            next_indices[-1] = index + 1
            candidate = candidates[index]
            if not all(self._known_different(candidate, value, sort) for value in selected):
                continue
            selected.append(candidate)
            if len(selected) == cardinality:
                token.add_work(steps % self._limits.cancellation_interval)
                return True
            next_indices.append(index + 1)

        token.add_work(steps % self._limits.cancellation_interval)
        return False

    def _known_different(
        self,
        left: NodeHandle,
        right: NodeHandle,
        sort: TermSort,
    ) -> bool:
        if left == right:
            return False
        inequality = self._inequality_by_sort.get(sort)
        if inequality is not None:
            first, second = sorted((left, right), key=self._node_rank)
            if _has_fact(self._session, inequality, (first, second)):
                return True
        return sort is TermSort.DATA and self._access.data_values_known_different(left, right)

    def _expand_object(
        self,
        predicate: Predicate,
        root: NodeHandle,
        supports: tuple[DependencySet, ...],
        token: CancellationToken,
    ) -> tuple[NodeHandle, ...]:
        cardinality = _required(predicate.cardinality, "object at-least cardinality")
        filler = _required(predicate.filler_predicate_id, "object at-least filler")
        role_id = _required(predicate.role_id, "object at-least role")
        top_role = role_id == self._access.program.role_model.top_object_role_id
        role_predicate = None if top_role else self._object_roles.get(role_id)
        if not top_role and role_predicate is None:
            raise InternalInvariantError("object witness role predicate is absent")
        witnesses: list[NodeHandle] = []
        for _index in range(cardinality):
            token.check()
            witness = self._session.create_node(NodeKind.TREE, parent=root)
            self._access.register_node(witness, min(supports, key=_dependency_rank))
            witnesses.append(witness)
            for support in supports:
                if role_predicate is not None:
                    self._access.dispatch_ground_atom(
                        GroundRuleAtom(role_predicate, (root, witness)),
                        support,
                        core=True,
                    )
                self._access.dispatch_ground_atom(
                    GroundRuleAtom(filler, (witness,)),
                    support,
                    core=True,
                )
        self._add_pairwise_inequalities(tuple(witnesses), TermSort.OBJECT, supports)
        return tuple(witnesses)

    def _expand_data(
        self,
        predicate: Predicate,
        root: NodeHandle,
        supports: tuple[DependencySet, ...],
        token: CancellationToken,
    ) -> tuple[NodeHandle, ...]:
        cardinality = _required(predicate.cardinality, "data at-least cardinality")
        filler = _required(predicate.filler_predicate_id, "data at-least filler")
        roles = predicate.annotation
        if len(roles) > 1 and cardinality != 1:
            raise InternalInvariantError("n-ary data existential must have cardinality one")
        count = cardinality if len(roles) == 1 else len(roles)
        witnesses: list[NodeHandle] = []
        for _index in range(count):
            token.check()
            witness = self._session.create_node(NodeKind.CONCRETE)
            self._access.register_node(witness, min(supports, key=_dependency_rank))
            witnesses.append(witness)
        for support in supports:
            for index, witness in enumerate(witnesses):
                role_id = roles[0] if len(roles) == 1 else roles[index]
                if role_id == self._access.program.role_model.top_data_property_id:
                    continue
                role_predicate = self._data_roles.get(role_id)
                if role_predicate is None:
                    raise InternalInvariantError("data witness role predicate is absent")
                self._access.dispatch_ground_atom(
                    GroundRuleAtom(role_predicate, (root, witness)),
                    support,
                    core=True,
                )
            self._access.dispatch_ground_atom(
                GroundRuleAtom(filler, tuple(witnesses) if len(roles) > 1 else (witnesses[0],)),
                support,
                core=True,
            )
            if len(roles) == 1:
                for witness in witnesses[1:]:
                    self._access.dispatch_ground_atom(
                        GroundRuleAtom(filler, (witness,)),
                        support,
                        core=True,
                    )
        if len(roles) == 1:
            self._add_pairwise_inequalities(tuple(witnesses), TermSort.DATA, supports)
        return tuple(witnesses)

    def _add_pairwise_inequalities(
        self,
        witnesses: tuple[NodeHandle, ...],
        sort: TermSort,
        supports: tuple[DependencySet, ...],
    ) -> None:
        if len(witnesses) < 2:
            return
        inequality = self._inequality_by_sort.get(sort)
        if inequality is None:
            raise InternalInvariantError("cardinality witnesses require an inequality predicate")
        for left, right in itertools.combinations(witnesses, 2):
            for support in supports:
                self._access.dispatch_ground_atom(
                    GroundRuleAtom(inequality, (left, right)),
                    support,
                    core=True,
                )

    def _uses_bottom_role(self, predicate: Predicate) -> bool:
        roles = self._access.program.role_model
        if predicate.kind is PredicateKind.AT_LEAST_OBJECT:
            return predicate.role_id == roles.bottom_object_role_id
        return roles.bottom_data_property_id in predicate.annotation

    def _node_rank(self, handle: NodeHandle) -> tuple[int, int, int]:
        node = self._session.nodes.get(handle)
        return node.creation_id, handle.slot, handle.generation


def _role_predicates(program: ClauseProgram, kind: PredicateKind) -> dict[int, int]:
    return {
        cast(int, predicate.role_id): predicate.predicate_id
        for predicate in program.predicates.predicates
        if predicate.kind is kind
    }


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


def _required(value: int | None, label: str) -> int:
    if value is None:
        raise InternalInvariantError(f"{label} is absent")
    return value


def _dependency_rank(value: DependencySet) -> tuple[int, int, int]:
    maximum = value.maximum
    return len(value), -1 if maximum is None else maximum, value.bits


def _reuse_source_id(root: NodeHandle, predicate_id: int) -> int:
    payload = f"pyhermit:individual-reuse:v1:{root.slot}:{root.generation}:{predicate_id}".encode()
    return int.from_bytes(hashlib.sha256(payload).digest(), "big")


__all__ = [
    "ExistentialExpansionManager",
    "ExpansionLimits",
    "ExpansionResult",
    "ExpansionRuleAccess",
    "ExpansionStatus",
    "ExpansionStrategy",
]
