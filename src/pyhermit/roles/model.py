"""Immutable private role hierarchy, diagnostics, and NFA contracts.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import json
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from enum import Enum
from types import MappingProxyType
from typing import cast

from pyowl_core.model import (
    DataProperty,
    ObjectPropertyExpression,
)

from .graph import Reachability, reachability_contains


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class BuiltinRoleSemantics(_StringEnum):
    NORMAL = "normal"
    UNIVERSAL = "universal"
    EMPTY = "empty"


@dataclass(frozen=True, slots=True, order=True)
class RoleInclusion:
    sub_role_id: int
    super_role_id: int
    provenance_sha256: str | None = None
    builtin: bool = False


@dataclass(frozen=True, slots=True, order=True)
class DataRoleInclusion:
    sub_property_id: int
    super_property_id: int
    provenance_sha256: str | None = None
    builtin: bool = False


@dataclass(frozen=True, slots=True, order=True)
class ComplexRoleInclusion:
    chain_role_ids: tuple[int, ...]
    super_role_id: int
    provenance_sha256: str
    inverse_generated: bool = False

    def __post_init__(self) -> None:
        if len(self.chain_role_ids) < 2:
            raise ValueError("complex role chains require at least two roles")


@dataclass(frozen=True, slots=True, order=True)
class RoleComponent:
    component_id: int
    member_role_ids: tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.member_role_ids:
            raise ValueError("role components cannot be empty")


@dataclass(frozen=True, slots=True, order=True)
class RegularityViolation:
    code: str
    message: str
    super_role_id: int
    chain_role_ids: tuple[int, ...]
    provenance_sha256: str
    position: int | None = None
    component_cycle: tuple[int, ...] = ()


class RoleRegularityError(ValueError):
    def __init__(self, violations: Sequence[RegularityViolation]) -> None:
        frozen = tuple(violations)
        if not frozen:
            raise ValueError("RoleRegularityError requires at least one violation")
        self.violations = frozen
        codes = ", ".join(sorted({violation.code for violation in frozen}))
        super().__init__(f"object property hierarchy is not regular: {codes}")


@dataclass(frozen=True, slots=True, order=True)
class NFATransition:
    source_state: int
    target_state: int
    role_id: int | None

    def __post_init__(self) -> None:
        for name in ("source_state", "target_state"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")
        if self.role_id is not None and (
            isinstance(self.role_id, bool) or not isinstance(self.role_id, int) or self.role_id < 0
        ):
            raise ValueError("role_id must be a nonnegative integer or None")


@dataclass(frozen=True, slots=True)
class RoleAutomaton:
    target_component_id: int
    state_count: int
    initial_state: int
    final_states: tuple[int, ...]
    transitions: tuple[NFATransition, ...]

    def __post_init__(self) -> None:
        if self.state_count < 1:
            raise ValueError("role automata require at least one state")
        if self.initial_state < 0 or self.initial_state >= self.state_count:
            raise ValueError("initial_state is outside the automaton")
        finals = tuple(sorted(set(self.final_states)))
        if not finals or any(state < 0 or state >= self.state_count for state in finals):
            raise ValueError("final_states must identify states in the automaton")
        transitions = tuple(
            sorted(
                set(self.transitions),
                key=lambda item: (
                    item.source_state,
                    -1 if item.role_id is None else item.role_id,
                    item.target_state,
                ),
            )
        )
        if any(
            transition.source_state >= self.state_count
            or transition.target_state >= self.state_count
            for transition in transitions
        ):
            raise ValueError("transition state is outside the automaton")
        object.__setattr__(self, "final_states", finals)
        object.__setattr__(self, "transitions", transitions)

    def accepts_ids(self, word: Sequence[int]) -> bool:
        current = self._epsilon_closure(frozenset({self.initial_state}))
        by_source: dict[int, list[NFATransition]] = {}
        for transition in self.transitions:
            by_source.setdefault(transition.source_state, []).append(transition)
        for role_id in word:
            if isinstance(role_id, bool) or not isinstance(role_id, int) or role_id < 0:
                raise ValueError("word must contain nonnegative role IDs")
            following = {
                transition.target_state
                for state in current
                for transition in by_source.get(state, ())
                if transition.role_id == role_id
            }
            if not following:
                return False
            current = self._epsilon_closure(frozenset(following))
        return any(state in self.final_states for state in current)

    def _epsilon_closure(self, states: frozenset[int]) -> frozenset[int]:
        adjacency: dict[int, list[int]] = {}
        for transition in self.transitions:
            if transition.role_id is None:
                adjacency.setdefault(transition.source_state, []).append(transition.target_state)
        reached = set(states)
        pending = list(sorted(states, reverse=True))
        while pending:
            state = pending.pop()
            for target in adjacency.get(state, ()):
                if target not in reached:
                    reached.add(target)
                    pending.append(target)
        return frozenset(reached)


@dataclass(frozen=True, slots=True)
class RoleBuildLimits:
    max_object_roles: int = 1_000_000
    max_data_properties: int = 1_000_000
    max_chain_axioms: int = 1_000_000
    max_nfa_states: int = 5_000_000
    max_nfa_transitions: int = 20_000_000

    def __post_init__(self) -> None:
        for name in (
            "max_object_roles",
            "max_data_properties",
            "max_chain_axioms",
            "max_nfa_states",
            "max_nfa_transitions",
        ):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 1:
                raise ValueError(f"{name} must be a positive integer")


@dataclass(frozen=True, slots=True)
class RoleAxiomGraph:
    object_roles: tuple[ObjectPropertyExpression, ...]
    data_properties: tuple[DataProperty, ...]
    object_components: tuple[RoleComponent, ...]
    data_components: tuple[tuple[int, ...], ...]
    object_component_by_role: tuple[int, ...]
    data_component_by_property: tuple[int, ...]
    object_super_components: tuple[Reachability, ...]
    data_super_components: tuple[Reachability, ...]
    simple_inclusions: tuple[RoleInclusion, ...]
    data_inclusions: tuple[DataRoleInclusion, ...]
    complex_inclusions: tuple[ComplexRoleInclusion, ...]
    non_simple_components: frozenset[int]
    regularity_violations: tuple[RegularityViolation, ...]
    automata: Mapping[int, RoleAutomaton]
    inverse_role_ids: tuple[int, ...]
    top_object_role_id: int
    bottom_object_role_id: int
    top_data_property_id: int
    bottom_data_property_id: int
    source_axiom_count: int

    def __post_init__(self) -> None:
        object.__setattr__(self, "automata", MappingProxyType(dict(self.automata)))

    @property
    def regular(self) -> bool:
        return not self.regularity_violations

    def require_regular(self) -> None:
        if self.regularity_violations:
            raise RoleRegularityError(self.regularity_violations)

    def object_role_id(self, role: ObjectPropertyExpression) -> int:
        from .builder import canonical_object_role

        canonical = canonical_object_role(role)
        key = canonical.canonical_bytes()
        low = 0
        high = len(self.object_roles)
        while low < high:
            middle = (low + high) // 2
            candidate = self.object_roles[middle].canonical_bytes()
            if candidate < key:
                low = middle + 1
            else:
                high = middle
        if low >= len(self.object_roles) or self.object_roles[low].canonical_bytes() != key:
            raise KeyError("object role is not present in this role model")
        return low

    def data_property_id(self, property: DataProperty) -> int:
        if not isinstance(property, DataProperty):
            raise TypeError("property must be a pyowl_core DataProperty")
        key = property.canonical_bytes()
        low = 0
        high = len(self.data_properties)
        while low < high:
            middle = (low + high) // 2
            candidate = self.data_properties[middle].canonical_bytes()
            if candidate < key:
                low = middle + 1
            else:
                high = middle
        if low >= len(self.data_properties) or self.data_properties[low].canonical_bytes() != key:
            raise KeyError("data property is not present in this role model")
        return low

    def inverse_id(self, role_id: int) -> int:
        return self.inverse_role_ids[role_id]

    def equivalent_object_roles(
        self, role: ObjectPropertyExpression
    ) -> tuple[ObjectPropertyExpression, ...]:
        role_id = self.object_role_id(role)
        component = self.object_components[self.object_component_by_role[role_id]]
        return tuple(self.object_roles[index] for index in component.member_role_ids)

    def equivalent_data_properties(self, property: DataProperty) -> tuple[DataProperty, ...]:
        property_id = self.data_property_id(property)
        component = self.data_components[self.data_component_by_property[property_id]]
        return tuple(self.data_properties[index] for index in component)

    def is_sub_object_role(
        self,
        sub: ObjectPropertyExpression,
        sup: ObjectPropertyExpression,
    ) -> bool:
        sub_id = self.object_role_id(sub)
        sup_id = self.object_role_id(sup)
        if sub_id == self.bottom_object_role_id or sup_id == self.top_object_role_id:
            return True
        sub_component = self.object_component_by_role[sub_id]
        sup_component = self.object_component_by_role[sup_id]
        return reachability_contains(self.object_super_components[sub_component], sup_component)

    def is_sub_data_property(self, sub: DataProperty, sup: DataProperty) -> bool:
        sub_id = self.data_property_id(sub)
        sup_id = self.data_property_id(sup)
        if sub_id == self.bottom_data_property_id or sup_id == self.top_data_property_id:
            return True
        sub_component = self.data_component_by_property[sub_id]
        sup_component = self.data_component_by_property[sup_id]
        return reachability_contains(self.data_super_components[sub_component], sup_component)

    def is_simple(self, role: ObjectPropertyExpression) -> bool:
        role_id = self.object_role_id(role)
        return self.object_component_by_role[role_id] not in self.non_simple_components

    def builtin_object_semantics(self, role: ObjectPropertyExpression) -> BuiltinRoleSemantics:
        role_id = self.object_role_id(role)
        if role_id == self.top_object_role_id:
            return BuiltinRoleSemantics.UNIVERSAL
        if role_id == self.bottom_object_role_id:
            return BuiltinRoleSemantics.EMPTY
        return BuiltinRoleSemantics.NORMAL

    def builtin_data_semantics(self, property: DataProperty) -> BuiltinRoleSemantics:
        property_id = self.data_property_id(property)
        if property_id == self.top_data_property_id:
            return BuiltinRoleSemantics.UNIVERSAL
        if property_id == self.bottom_data_property_id:
            return BuiltinRoleSemantics.EMPTY
        return BuiltinRoleSemantics.NORMAL

    def accepts(
        self,
        target: ObjectPropertyExpression,
        word: Sequence[ObjectPropertyExpression],
    ) -> bool:
        target_id = self.object_role_id(target)
        word_ids = tuple(self.object_role_id(role) for role in word)
        # Every relational composition containing the empty relation is empty and
        # therefore a subrelation of every target.  Keep this out of each NFA to
        # avoid an O(role-count * automaton-count) transition expansion.
        if self.bottom_object_role_id in word_ids:
            return True
        component = self.object_component_by_role[target_id]
        automaton = self.automata.get(component)
        if automaton is None:
            return len(word) == 1 and self.is_sub_object_role(word[0], target)
        return automaton.accepts_ids(word_ids)

    def slow_accepts(
        self,
        target: ObjectPropertyExpression,
        word: Sequence[ObjectPropertyExpression],
        *,
        max_partitions: int = 1_000_000,
    ) -> bool:
        """Evaluate a bounded word with the independent role-grammar oracle."""

        from .automata import AutomatonProduction, slow_word_implies

        target_id = self.object_role_id(target)
        word_ids = tuple(self.object_role_id(role) for role in word)
        if self.bottom_object_role_id in word_ids:
            return True
        if target_id == self.top_object_role_id:
            return bool(word)
        productions = tuple(
            AutomatonProduction(
                self.object_component_by_role[inclusion.super_role_id],
                tuple(
                    self.object_component_by_role[role_id] for role_id in inclusion.chain_role_ids
                ),
            )
            for inclusion in self.complex_inclusions
        )
        return slow_word_implies(
            target_component=self.object_component_by_role[target_id],
            word_role_ids=word_ids,
            component_by_role=self.object_component_by_role,
            super_components=self.object_super_components,
            productions=productions,
            max_partitions=max_partitions,
        )

    def canonical_snapshot(self) -> str:
        payload = {
            "automata": {
                str(component): {
                    "final": list(automaton.final_states),
                    "initial": automaton.initial_state,
                    "states": automaton.state_count,
                    "target": automaton.target_component_id,
                    "transitions": [
                        [
                            transition.source_state,
                            transition.role_id,
                            transition.target_state,
                        ]
                        for transition in automaton.transitions
                    ],
                }
                for component, automaton in sorted(self.automata.items())
            },
            "complex": [
                [
                    list(inclusion.chain_role_ids),
                    inclusion.super_role_id,
                    inclusion.provenance_sha256,
                    inclusion.inverse_generated,
                ]
                for inclusion in self.complex_inclusions
            ],
            "data_components": [list(component) for component in self.data_components],
            "data_roles": [value.iri.value for value in self.data_properties],
            "non_simple": sorted(self.non_simple_components),
            "object_components": [
                list(component.member_role_ids) for component in self.object_components
            ],
            "object_roles": [value.canonical_bytes().hex() for value in self.object_roles],
            "regularity": [violation.code for violation in self.regularity_violations],
        }
        return json.dumps(payload, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


__all__ = [
    "BuiltinRoleSemantics",
    "ComplexRoleInclusion",
    "DataRoleInclusion",
    "NFATransition",
    "RegularityViolation",
    "RoleAutomaton",
    "RoleAxiomGraph",
    "RoleBuildLimits",
    "RoleComponent",
    "RoleInclusion",
    "RoleRegularityError",
]
