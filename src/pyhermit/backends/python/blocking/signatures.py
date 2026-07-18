# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Canonical direct-blocking labels and checkers.

SPDX-License-Identifier: LGPL-3.0-or-later

Source-guided behavior: pinned HermiT single/pairwise/validated direct checkers at
commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3.  Predicate categorization is supplied
by the compiled-IR owner; this module never guesses it from integer values.
"""

from __future__ import annotations

import hashlib
import struct
from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import Enum
from types import MappingProxyType
from typing import TYPE_CHECKING, Protocol, TypeVar, cast, runtime_checkable

from pyhermit.backends.python.state import (
    Node,
    NodeHandle,
    NodeKind,
    NodeLifecycle,
    NodeSort,
    TableauSession,
)
from pyhermit.exceptions import InternalInvariantError

if TYPE_CHECKING:
    from pyhermit.clauses import ClauseProgram


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class DirectCheckerKind(_StringEnum):
    SINGLE = "single"
    PAIRWISE = "pairwise"
    VALIDATED_SINGLE = "validated_single"
    VALIDATED_PAIRWISE = "validated_pairwise"


@dataclass(frozen=True, slots=True)
class BlockingVocabulary:
    """Exact compiled predicate categories relevant to object blocking."""

    atomic_concepts: frozenset[int]
    atomic_object_roles: frozenset[int]

    def __post_init__(self) -> None:
        concepts = frozenset(self.atomic_concepts)
        roles = frozenset(self.atomic_object_roles)
        for name, values in (("atomic_concepts", concepts), ("atomic_object_roles", roles)):
            if any(
                isinstance(value, bool) or not isinstance(value, int) or value < 0
                for value in values
            ):
                raise ValueError(f"{name} must contain nonnegative integer predicate IDs")
        if concepts & roles:
            raise ValueError("concept and object-role predicate IDs must be disjoint")
        object.__setattr__(self, "atomic_concepts", concepts)
        object.__setattr__(self, "atomic_object_roles", roles)

    @classmethod
    def from_program(cls, program: ClauseProgram) -> BlockingVocabulary:
        """Derive the exact blocking vocabulary from one compiled ontology.

        Negative concepts participate in a node label just like positive concepts.
        Negative object-role assertions do not participate in the pairwise edge label,
        matching the pinned direct checkers' ``AtomicRole`` boundary.
        """

        from pyhermit.clauses import ClauseProgram, PredicateKind

        if not isinstance(program, ClauseProgram):
            raise TypeError("program must be ClauseProgram")
        concept_kinds = frozenset(
            {
                PredicateKind.CONCEPT,
                PredicateKind.NEGATED_CONCEPT,
                PredicateKind.NOMINAL,
                PredicateKind.NEGATED_NOMINAL,
                PredicateKind.AUTOMATON_STATE,
                PredicateKind.DISJOINT_GUARD,
                PredicateKind.NAMED_INDIVIDUAL,
            }
        )
        return cls(
            frozenset(
                predicate.predicate_id
                for predicate in program.predicates.predicates
                if predicate.kind in concept_kinds
            ),
            frozenset(
                predicate.predicate_id
                for predicate in program.predicates.predicates
                if predicate.kind is PredicateKind.OBJECT_ROLE
            ),
        )

    @property
    def fingerprint(self) -> str:
        digest = hashlib.sha256(b"pyhermit:blocking-vocabulary:v1\0")
        for values in (self.atomic_concepts, self.atomic_object_roles):
            digest.update(struct.pack("<I", len(values)))
            for value in sorted(values):
                digest.update(struct.pack("<I", value))
        return digest.hexdigest()


@dataclass(frozen=True, slots=True)
class BlockingLabels:
    """One immutable O(nodes + relevant facts) extraction for a blocking pass."""

    concepts: MappingProxyType[NodeHandle, tuple[int, ...]]
    core_concepts: MappingProxyType[NodeHandle, tuple[int, ...]]
    roles: MappingProxyType[tuple[NodeHandle, NodeHandle], tuple[int, ...]]
    core_roles: MappingProxyType[tuple[NodeHandle, NodeHandle], tuple[int, ...]]
    nodes: MappingProxyType[
        NodeHandle,
        tuple[int, NodeKind, NodeLifecycle, NodeHandle | None],
    ]
    state_digest: str

    @classmethod
    def from_session(
        cls,
        session: TableauSession,
        vocabulary: BlockingVocabulary,
    ) -> BlockingLabels:
        if not isinstance(session, TableauSession):
            raise TypeError("session must be TableauSession")
        if not isinstance(vocabulary, BlockingVocabulary):
            raise TypeError("vocabulary must be BlockingVocabulary")
        concept_sets: dict[NodeHandle, set[int]] = {}
        core_concept_sets: dict[NodeHandle, set[int]] = {}
        role_sets: dict[tuple[NodeHandle, NodeHandle], set[int]] = {}
        core_role_sets: dict[tuple[NodeHandle, NodeHandle], set[int]] = {}
        digest = hashlib.sha256(b"pyhermit:blocking-label-state:v1\0")
        digest.update(bytes.fromhex(vocabulary.fingerprint))

        active_nodes = sorted(
            (
                node
                for node in session.nodes.existing_nodes()
                if node.lifecycle is NodeLifecycle.ACTIVE
            ),
            key=lambda node: node.creation_id,
        )
        node_records: dict[
            NodeHandle,
            tuple[int, NodeKind, NodeLifecycle, NodeHandle | None],
        ] = {}
        for node in active_nodes:
            parent = node.parent
            node_records[node.handle] = (
                node.creation_id,
                node.kind,
                node.lifecycle,
                parent,
            )
            digest.update(
                struct.pack(
                    "<IIQ",
                    node.handle.slot,
                    node.handle.generation,
                    node.creation_id,
                )
            )
            digest.update(node.kind.value.encode("ascii") + b"\0")
            if parent is None:
                digest.update(b"N")
            else:
                digest.update(b"P" + struct.pack("<II", parent.slot, parent.generation))

        relevant_rows = []
        for row in session.extensions.active_rows():
            predicate = row.key.predicate_id
            arguments = row.key.arguments
            if len(arguments) == 1 and predicate in vocabulary.atomic_concepts:
                node_key = arguments[0]
                concept_sets.setdefault(node_key, set()).add(predicate)
                if row.core:
                    core_concept_sets.setdefault(node_key, set()).add(predicate)
            elif len(arguments) == 2 and predicate in vocabulary.atomic_object_roles:
                role_key = (arguments[0], arguments[1])
                role_sets.setdefault(role_key, set()).add(predicate)
                if row.core:
                    core_role_sets.setdefault(role_key, set()).add(predicate)
            else:
                continue
            relevant_rows.append(row)

        for row in sorted(
            relevant_rows,
            key=lambda value: (
                value.key.predicate_id,
                value.key.arguments,
                value.core,
            ),
        ):
            predicate = row.key.predicate_id
            arguments = row.key.arguments
            digest.update(struct.pack("<IB", predicate, len(arguments)))
            for argument in arguments:
                digest.update(struct.pack("<II", argument.slot, argument.generation))
            digest.update(b"1" if row.core else b"0")

        return cls(
            MappingProxyType(_freeze_sets(concept_sets)),
            MappingProxyType(_freeze_sets(core_concept_sets)),
            MappingProxyType(_freeze_sets(role_sets)),
            MappingProxyType(_freeze_sets(core_role_sets)),
            MappingProxyType(node_records),
            digest.hexdigest(),
        )

    def earliest_difference(self, other: BlockingLabels) -> int | None:
        """Return the earliest creation ID whose blocking projection differs."""

        if not isinstance(other, BlockingLabels):
            raise TypeError("other must be BlockingLabels")
        changed: list[int] = []
        for handle in self.nodes.keys() | other.nodes.keys():
            before = self.nodes.get(handle)
            after = other.nodes.get(handle)
            if before != after:
                for record in (before, after):
                    if record is not None:
                        changed.append(record[0])
        concept_handles = _different_keys(self.concepts, other.concepts) | _different_keys(
            self.core_concepts, other.core_concepts
        )
        for handle in concept_handles:
            record = self.nodes.get(handle) or other.nodes.get(handle)
            if record is not None:
                changed.append(record[0])
        role_edges = _different_keys(self.roles, other.roles) | _different_keys(
            self.core_roles, other.core_roles
        )
        for edge in role_edges:
            for handle in edge:
                record = self.nodes.get(handle) or other.nodes.get(handle)
                if record is not None:
                    changed.append(record[0])
        return min(changed) if changed else None

    def concept_label(self, node: NodeHandle, *, core_only: bool = False) -> tuple[int, ...]:
        source = self.core_concepts if core_only else self.concepts
        return source.get(node, ())

    def role_label(
        self,
        source: NodeHandle,
        target: NodeHandle,
        *,
        core_only: bool = False,
    ) -> tuple[int, ...]:
        roles = self.core_roles if core_only else self.roles
        return roles.get((source, target), ())


KeyT = TypeVar("KeyT")


def _freeze_sets(values: dict[KeyT, set[int]]) -> dict[KeyT, tuple[int, ...]]:
    return {key: tuple(sorted(items)) for key, items in values.items()}


def _different_keys(
    left: MappingProxyType[KeyT, tuple[int, ...]],
    right: MappingProxyType[KeyT, tuple[int, ...]],
) -> set[KeyT]:
    return {key for key in left.keys() | right.keys() if left.get(key, ()) != right.get(key, ())}


@dataclass(frozen=True, slots=True)
class BlockingSignature:
    kind: DirectCheckerKind
    blocking_node_concepts: tuple[int, ...]
    blocking_parent_concepts: tuple[int, ...] = ()
    blocking_from_parent_roles: tuple[int, ...] = ()
    blocking_to_parent_roles: tuple[int, ...] = ()
    full_node_concepts: tuple[int, ...] = ()
    full_parent_concepts: tuple[int, ...] = ()
    full_from_parent_roles: tuple[int, ...] = ()
    full_to_parent_roles: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.kind, DirectCheckerKind):
            raise TypeError("kind must be DirectCheckerKind")
        for name in (
            "blocking_node_concepts",
            "blocking_parent_concepts",
            "blocking_from_parent_roles",
            "blocking_to_parent_roles",
            "full_node_concepts",
            "full_parent_concepts",
            "full_from_parent_roles",
            "full_to_parent_roles",
        ):
            values = tuple(getattr(self, name))
            if values != tuple(sorted(set(values))) or any(
                isinstance(value, bool) or not isinstance(value, int) or value < 0
                for value in values
            ):
                raise ValueError(f"{name} must be sorted unique nonnegative IDs")
            object.__setattr__(self, name, values)

    @property
    def blocking_key(self) -> tuple[object, ...]:
        return (
            self.kind.value,
            self.blocking_node_concepts,
            self.blocking_parent_concepts,
            self.blocking_from_parent_roles,
            self.blocking_to_parent_roles,
        )

    def blocks(self, other: BlockingSignature) -> bool:
        if not isinstance(other, BlockingSignature):
            raise TypeError("other must be BlockingSignature")
        return self.blocking_key == other.blocking_key

    def canonical_bytes(self) -> bytes:
        pieces = [b"PYHBLK1\0", self.kind.value.encode("ascii") + b"\0"]
        for values in (
            self.blocking_node_concepts,
            self.blocking_parent_concepts,
            self.blocking_from_parent_roles,
            self.blocking_to_parent_roles,
            self.full_node_concepts,
            self.full_parent_concepts,
            self.full_from_parent_roles,
            self.full_to_parent_roles,
        ):
            pieces.append(struct.pack("<I", len(values)))
            pieces.extend(struct.pack("<I", value) for value in values)
        return b"".join(pieces)

    @property
    def sha256(self) -> str:
        return hashlib.sha256(self.canonical_bytes()).hexdigest()

    def as_dict(self) -> dict[str, object]:
        return {
            "blocking_from_parent_roles": list(self.blocking_from_parent_roles),
            "blocking_node_concepts": list(self.blocking_node_concepts),
            "blocking_parent_concepts": list(self.blocking_parent_concepts),
            "blocking_to_parent_roles": list(self.blocking_to_parent_roles),
            "full_from_parent_roles": list(self.full_from_parent_roles),
            "full_node_concepts": list(self.full_node_concepts),
            "full_parent_concepts": list(self.full_parent_concepts),
            "full_to_parent_roles": list(self.full_to_parent_roles),
            "kind": self.kind.value,
            "sha256": self.sha256,
        }


@runtime_checkable
class DirectBlockingChecker(Protocol):
    kind: DirectCheckerKind
    vocabulary: BlockingVocabulary

    def can_be_blocker(self, session: TableauSession, node: NodeHandle) -> bool: ...

    def can_be_blocked(self, session: TableauSession, node: NodeHandle) -> bool: ...

    def signature(
        self,
        session: TableauSession,
        labels: BlockingLabels,
        node: NodeHandle,
    ) -> BlockingSignature: ...

    def is_blocked_by(
        self,
        session: TableauSession,
        labels: BlockingLabels,
        blocker: NodeHandle,
        blocked: NodeHandle,
    ) -> bool: ...


class _BaseChecker(ABC):
    kind: DirectCheckerKind

    __slots__ = ("vocabulary",)

    def __init__(self, vocabulary: BlockingVocabulary) -> None:
        if not isinstance(vocabulary, BlockingVocabulary):
            raise TypeError("vocabulary must be BlockingVocabulary")
        self.vocabulary = vocabulary

    def can_be_blocker(self, session: TableauSession, node: NodeHandle) -> bool:
        return self._eligible(session, node)

    def can_be_blocked(self, session: TableauSession, node: NodeHandle) -> bool:
        return self._eligible(session, node)

    def _eligible(self, session: TableauSession, node: NodeHandle) -> bool:
        value = session.nodes.get(node)
        return (
            value.lifecycle is NodeLifecycle.ACTIVE
            and value.kind is NodeKind.TREE
            and value.sort is NodeSort.OBJECT
        )

    def is_blocked_by(
        self,
        session: TableauSession,
        labels: BlockingLabels,
        blocker: NodeHandle,
        blocked: NodeHandle,
    ) -> bool:
        blocker_node = session.nodes.get(blocker)
        blocked_node = session.nodes.get(blocked)
        if (
            not self.can_be_blocker(session, blocker)
            or not self.can_be_blocked(session, blocked)
            or blocker_node.creation_id >= blocked_node.creation_id
            or blocker_node.blocker is not None
        ):
            return False
        return self.signature(session, labels, blocker).blocks(
            self.signature(session, labels, blocked)
        )

    @abstractmethod
    def signature(
        self,
        session: TableauSession,
        labels: BlockingLabels,
        node: NodeHandle,
    ) -> BlockingSignature:
        """Return the exact immutable signature for one eligible node."""

    @staticmethod
    def _parent(session: TableauSession, node: Node) -> Node:
        if node.parent is None:
            raise InternalInvariantError("tree blocking signature requires a parent")
        return session.nodes.get(node.parent)


class SingleDirectBlockingChecker(_BaseChecker):
    kind = DirectCheckerKind.SINGLE

    def signature(
        self,
        session: TableauSession,
        labels: BlockingLabels,
        node: NodeHandle,
    ) -> BlockingSignature:
        if not self.can_be_blocked(session, node):
            raise ValueError("node is not eligible for single blocking")
        concepts = labels.concept_label(node)
        return BlockingSignature(self.kind, concepts, full_node_concepts=concepts)


class PairwiseDirectBlockingChecker(_BaseChecker):
    kind = DirectCheckerKind.PAIRWISE

    def _eligible(self, session: TableauSession, node: NodeHandle) -> bool:
        if not super()._eligible(session, node):
            return False
        value = session.nodes.get(node)
        parent = self._parent(session, value)
        return parent.lifecycle is NodeLifecycle.ACTIVE and parent.kind is NodeKind.TREE

    def signature(
        self,
        session: TableauSession,
        labels: BlockingLabels,
        node: NodeHandle,
    ) -> BlockingSignature:
        if not self.can_be_blocked(session, node):
            raise ValueError("node is not eligible for pairwise blocking")
        value = session.nodes.get(node)
        parent = self._parent(session, value)
        concepts = labels.concept_label(node)
        parent_concepts = labels.concept_label(parent.handle)
        from_parent = labels.role_label(parent.handle, node)
        to_parent = labels.role_label(node, parent.handle)
        return BlockingSignature(
            self.kind,
            concepts,
            parent_concepts,
            from_parent,
            to_parent,
            concepts,
            parent_concepts,
            from_parent,
            to_parent,
        )


class _ValidatedChecker(_BaseChecker):
    __slots__ = ("has_inverses", "vocabulary")

    def __init__(self, vocabulary: BlockingVocabulary, *, has_inverses: bool) -> None:
        super().__init__(vocabulary)
        if not isinstance(has_inverses, bool):
            raise TypeError("has_inverses must be bool")
        self.has_inverses = has_inverses

    def _eligible(self, session: TableauSession, node: NodeHandle) -> bool:
        if not super()._eligible(session, node):
            return False
        if not self.has_inverses:
            return True
        value = session.nodes.get(node)
        return self._parent(session, value).kind is NodeKind.TREE

    def _labels(
        self,
        session: TableauSession,
        labels: BlockingLabels,
        node: NodeHandle,
    ) -> tuple[
        tuple[int, ...],
        tuple[int, ...],
        tuple[int, ...],
        tuple[int, ...],
        tuple[int, ...],
        tuple[int, ...],
    ]:
        value = session.nodes.get(node)
        parent = self._parent(session, value)
        return (
            labels.concept_label(node, core_only=True),
            labels.concept_label(parent.handle, core_only=True),
            labels.concept_label(node),
            labels.concept_label(parent.handle),
            labels.role_label(parent.handle, node),
            labels.role_label(node, parent.handle),
        )


class ValidatedSingleDirectBlockingChecker(_ValidatedChecker):
    kind = DirectCheckerKind.VALIDATED_SINGLE

    def signature(
        self,
        session: TableauSession,
        labels: BlockingLabels,
        node: NodeHandle,
    ) -> BlockingSignature:
        if not self.can_be_blocked(session, node):
            raise ValueError("node is not eligible for validated single blocking")
        core, _parent_core, full, parent_full, from_parent, to_parent = self._labels(
            session, labels, node
        )
        return BlockingSignature(
            self.kind,
            core,
            full_node_concepts=full,
            full_parent_concepts=parent_full,
            full_from_parent_roles=from_parent,
            full_to_parent_roles=to_parent,
        )


class ValidatedPairwiseDirectBlockingChecker(_ValidatedChecker):
    kind = DirectCheckerKind.VALIDATED_PAIRWISE

    def signature(
        self,
        session: TableauSession,
        labels: BlockingLabels,
        node: NodeHandle,
    ) -> BlockingSignature:
        if not self.can_be_blocked(session, node):
            raise ValueError("node is not eligible for validated pairwise blocking")
        core, parent_core, full, parent_full, from_parent, to_parent = self._labels(
            session, labels, node
        )
        return BlockingSignature(
            self.kind,
            core,
            parent_core,
            full_node_concepts=full,
            full_parent_concepts=parent_full,
            full_from_parent_roles=from_parent,
            full_to_parent_roles=to_parent,
        )


def create_direct_checker(
    kind: DirectCheckerKind,
    vocabulary: BlockingVocabulary,
    *,
    has_inverses: bool = False,
) -> DirectBlockingChecker:
    if not isinstance(kind, DirectCheckerKind):
        raise TypeError("kind must be DirectCheckerKind")
    if kind is DirectCheckerKind.SINGLE:
        return SingleDirectBlockingChecker(vocabulary)
    if kind is DirectCheckerKind.PAIRWISE:
        return PairwiseDirectBlockingChecker(vocabulary)
    if kind is DirectCheckerKind.VALIDATED_SINGLE:
        return ValidatedSingleDirectBlockingChecker(vocabulary, has_inverses=has_inverses)
    return ValidatedPairwiseDirectBlockingChecker(vocabulary, has_inverses=has_inverses)


__all__ = [
    "BlockingLabels",
    "BlockingSignature",
    "BlockingVocabulary",
    "DirectBlockingChecker",
    "DirectCheckerKind",
    "PairwiseDirectBlockingChecker",
    "SingleDirectBlockingChecker",
    "ValidatedPairwiseDirectBlockingChecker",
    "ValidatedSingleDirectBlockingChecker",
    "create_direct_checker",
]
