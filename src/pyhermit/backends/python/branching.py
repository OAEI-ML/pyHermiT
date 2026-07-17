"""Ground-disjunction choice, dependency learning, and backjump transitions.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from typing import Protocol

from pyhermit.backends.python.state import (
    BranchChoiceKind,
    Clash,
    ClashKind,
    DependencySet,
    TableauSession,
)
from pyhermit.events import CancellationToken
from pyhermit.exceptions import InternalInvariantError

from .rules.model import BranchTransition, GroundRuleAtom


class GroundAtomAccess(Protocol):
    def atom_for_id(self, atom_id: int) -> GroundRuleAtom: ...

    def atom_is_satisfied(self, atom: GroundRuleAtom) -> bool: ...

    def atom_refutation_dependency(self, atom: GroundRuleAtom) -> DependencySet | None: ...

    def dispatch_ground_atom(
        self,
        atom: GroundRuleAtom,
        dependency: DependencySet,
        *,
        provenance_ids: tuple[int, ...] = (),
    ) -> bool: ...


class DisjunctionBrancher:
    """Apply one deterministic/branching transition at a time."""

    __slots__ = ("_access", "_learning", "_session")

    def __init__(
        self,
        session: TableauSession,
        access: GroundAtomAccess,
        *,
        learning: bool = True,
    ) -> None:
        if not isinstance(session, TableauSession):
            raise TypeError("session must be TableauSession")
        if not isinstance(learning, bool):
            raise TypeError("learning must be bool")
        self._session = session
        self._access = access
        self._learning = learning

    @property
    def learning(self) -> bool:
        return self._learning

    def process_next(self, token: CancellationToken) -> BranchTransition:
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        return self._session.run_with_recovery(token, lambda: self._process_next(token))

    def _process_next(self, token: CancellationToken) -> BranchTransition:
        token.check()
        record = self._session.take_ground_disjunction()
        if record is None:
            return BranchTransition.NO_WORK
        atoms = tuple(self._access.atom_for_id(value) for value in record.disjunct_ids)
        if any(self._access.atom_is_satisfied(atom) for atom in atoms):
            return BranchTransition.SATISFIED
        remaining: list[int] = []
        dependencies = [record.base_dependency]
        for atom_id, atom in zip(record.disjunct_ids, atoms, strict=True):
            refutation = self._access.atom_refutation_dependency(atom)
            if refutation is None:
                remaining.append(atom_id)
            else:
                dependencies.append(refutation)
        combined = self._session.dependencies.union(*dependencies)
        if not remaining:
            self._session.install_clash(
                Clash(
                    ClashKind.EMPTY_HEAD,
                    combined,
                    (record.disjunction_id,),
                )
            )
            return BranchTransition.DETERMINISTIC
        if len(remaining) == 1:
            self._access.dispatch_ground_atom(
                self._access.atom_for_id(remaining[0]),
                combined,
            )
            return BranchTransition.DETERMINISTIC
        branch = self._session.push_branch(
            BranchChoiceKind.GROUND_DISJUNCTION,
            tuple(remaining),
            source_id=record.disjunction_id,
            base_dependency=combined,
        )
        self._access.dispatch_ground_atom(
            self._access.atom_for_id(branch.current),
            combined.add(branch.level),
        )
        token.check()
        return BranchTransition.BRANCHED

    def resolve_clash(self, token: CancellationToken) -> BranchTransition:
        if not isinstance(token, CancellationToken):
            raise TypeError("token must be CancellationToken")
        return self._session.run_with_recovery(token, lambda: self._resolve_clash(token))

    def _resolve_clash(self, token: CancellationToken) -> BranchTransition:
        token.check()
        clash = self._session.clashes.current
        if clash is None:
            return BranchTransition.NO_WORK
        target = clash.dependency.maximum if self._learning else self._session.highest_branch_level
        if target is None:
            return BranchTransition.UNSAT
        if not 0 <= target < len(self._session.branches):
            raise InternalInvariantError("clash backjump level has no branching point")
        branch = self._session.branches[target]
        without_level = DependencySet(clash.dependency.bits & ~(1 << target))
        alternative = self._session.advance_branch(target, without_level)
        token.check()
        if alternative is not None:
            current = self._session.branches[target]
            self._access.dispatch_ground_atom(
                self._access.atom_for_id(alternative),
                current.base_dependency.add(target),
            )
            return BranchTransition.ADVANCED
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

    def resolve_until_choice_or_unsat(self, token: CancellationToken) -> BranchTransition:
        while True:
            transition = self.resolve_clash(token)
            if transition is not BranchTransition.EXHAUSTED:
                return transition


__all__ = ["DisjunctionBrancher", "GroundAtomAccess"]
