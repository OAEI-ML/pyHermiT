# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Deterministic epsilon-NFA construction for regular object-role inclusions.

SPDX-License-Identifier: LGPL-3.0-or-later

The construction follows the language shape of pinned HermiT's
``ObjectPropertyInclusionManager`` while retaining epsilon NFAs.  In particular, it
does not invoke the historically disabled determinizer/minimizer.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass

from .graph import Reachability, reachability_members, topological_order
from .model import NFATransition, RoleAutomaton, RoleBuildLimits


@dataclass(frozen=True, slots=True)
class AutomatonProduction:
    target_component: int
    chain_components: tuple[int, ...]


class _MutableNFA:
    __slots__ = ("_limits", "state_count", "transitions")

    def __init__(self, limits: RoleBuildLimits) -> None:
        self._limits = limits
        self.state_count = 0
        self.transitions: set[tuple[int, int | None, int]] = set()

    def state(self) -> int:
        result = self.state_count
        self.state_count += 1
        if self.state_count > self._limits.max_nfa_states:
            raise ValueError("role NFA state limit exceeded")
        return result

    def transition(self, source: int, label: int | None, target: int) -> None:
        self.transitions.add((source, label, target))
        if len(self.transitions) > self._limits.max_nfa_transitions:
            raise ValueError("role NFA transition limit exceeded")

    def copy_between(
        self,
        automaton: RoleAutomaton,
        source: int,
        target: int,
    ) -> None:
        mapping = {state: self.state() for state in range(automaton.state_count)}
        self.transition(source, None, mapping[automaton.initial_state])
        for transition in automaton.transitions:
            self.transition(
                mapping[transition.source_state],
                transition.role_id,
                mapping[transition.target_state],
            )
        for final in automaton.final_states:
            self.transition(mapping[final], None, target)


def build_role_automata(
    *,
    component_count: int,
    component_members: Sequence[tuple[int, ...]],
    dependencies: Mapping[int, frozenset[int] | set[int]],
    subrole_dependencies: Mapping[int, frozenset[int] | set[int]],
    productions: Iterable[AutomatonProduction],
    selected_components: frozenset[int],
    top_component: int,
    all_role_ids: Sequence[int],
    limits: RoleBuildLimits,
) -> dict[int, RoleAutomaton]:
    """Build one complete NFA per role SCC in dependency order."""

    frozen_productions = tuple(
        sorted(
            set(productions),
            key=lambda value: (value.target_component, value.chain_components),
        )
    )
    by_target: dict[int, list[AutomatonProduction]] = {}
    for production in frozen_productions:
        by_target.setdefault(production.target_component, []).append(production)
    order = topological_order(component_count, dependencies)
    complete: dict[int, RoleAutomaton] = {}
    total_states = 0
    total_transitions = 0
    for component in order:
        if component not in selected_components:
            continue
        mutable = _MutableNFA(limits)
        initial = mutable.state()
        final = mutable.state()
        if component == top_component:
            for role_id in all_role_ids:
                mutable.transition(initial, role_id, final)
            mutable.transition(final, None, initial)
        else:
            for role_id in component_members[component]:
                mutable.transition(initial, role_id, final)
            for dependency in sorted(subrole_dependencies.get(component, ())):
                mutable.copy_between(complete[dependency], initial, final)
            for production in by_target.get(component, ()):
                _add_production(
                    mutable,
                    complete,
                    component,
                    production.chain_components,
                    initial,
                    final,
                )
        automaton = _freeze_automaton(component, mutable, initial, frozenset({final}))
        total_states += automaton.state_count
        total_transitions += len(automaton.transitions)
        if total_states > limits.max_nfa_states:
            raise ValueError("aggregate role NFA state limit exceeded")
        if total_transitions > limits.max_nfa_transitions:
            raise ValueError("aggregate role NFA transition limit exceeded")
        complete[component] = automaton
    return complete


def _add_production(
    mutable: _MutableNFA,
    complete: Mapping[int, RoleAutomaton],
    target_component: int,
    chain: tuple[int, ...],
    initial: int,
    final: int,
) -> None:
    target_positions = tuple(
        index for index, component in enumerate(chain) if component == target_component
    )
    if target_positions == (0, 1) and len(chain) == 2:
        mutable.transition(final, None, initial)
        return
    if target_positions == (0,):
        _copy_sequence(mutable, complete, chain[1:], final, final)
        return
    if target_positions == (len(chain) - 1,):
        _copy_sequence(mutable, complete, chain[:-1], initial, initial)
        return
    if target_positions:
        raise ValueError("irregular recursive production reached NFA construction")
    _copy_sequence(mutable, complete, chain, initial, final)


def _copy_sequence(
    mutable: _MutableNFA,
    complete: Mapping[int, RoleAutomaton],
    components: tuple[int, ...],
    source: int,
    target: int,
) -> None:
    if not components:
        mutable.transition(source, None, target)
        return
    current = source
    for offset, component in enumerate(components):
        following = target if offset == len(components) - 1 else mutable.state()
        mutable.copy_between(complete[component], current, following)
        current = following


def _freeze_automaton(
    component: int,
    mutable: _MutableNFA,
    initial: int,
    finals: frozenset[int],
) -> RoleAutomaton:
    outgoing: dict[int, list[tuple[int | None, int]]] = {}
    incoming: dict[int, list[int]] = {}
    for source, label, target in mutable.transitions:
        outgoing.setdefault(source, []).append((label, target))
        incoming.setdefault(target, []).append(source)

    reachable = {initial}
    pending = [initial]
    while pending:
        state = pending.pop()
        for _label, target in outgoing.get(state, ()):
            if target not in reachable:
                reachable.add(target)
                pending.append(target)
    co_reachable = set(finals)
    pending = list(finals)
    while pending:
        state = pending.pop()
        for source in incoming.get(state, ()):
            if source not in co_reachable:
                co_reachable.add(source)
                pending.append(source)
    retained = reachable & co_reachable
    if initial not in retained or not retained & finals:
        raise ValueError("role NFA has no accepting path")

    order: list[int] = []
    queued = {initial}
    pending = [initial]
    while pending:
        state = pending.pop(0)
        order.append(state)
        adjacent = sorted(
            ((label, target) for label, target in outgoing.get(state, ()) if target in retained),
            key=lambda item: (-1 if item[0] is None else item[0], item[1]),
        )
        for _label, target in adjacent:
            if target not in queued:
                queued.add(target)
                pending.append(target)
    mapping = {old: new for new, old in enumerate(order)}
    transitions = tuple(
        NFATransition(mapping[source], mapping[target], label)
        for source, label, target in mutable.transitions
        if source in retained and target in retained
    )
    return RoleAutomaton(
        target_component_id=component,
        state_count=len(order),
        initial_state=mapping[initial],
        final_states=tuple(mapping[state] for state in finals if state in retained),
        transitions=transitions,
    )


def slow_word_implies(
    *,
    target_component: int,
    word_role_ids: Sequence[int],
    component_by_role: Sequence[int],
    super_components: Sequence[Reachability],
    productions: Iterable[AutomatonProduction],
    max_partitions: int = 1_000_000,
) -> bool:
    """Bounded grammar oracle independent of NFA construction."""

    if not word_role_ids:
        return False
    chart: dict[tuple[int, int], set[int]] = {}
    for offset, role_id in enumerate(word_role_ids):
        component = component_by_role[role_id]
        chart[(offset, offset + 1)] = set(reachability_members(super_components[component]))
    frozen_productions = tuple(productions)
    partition_count = 0
    for length in range(2, len(word_role_ids) + 1):
        for start in range(0, len(word_role_ids) - length + 1):
            end = start + length
            implied: set[int] = set()
            for production in frozen_productions:
                arity = len(production.chain_components)
                for cuts in _partitions(start, end, arity):
                    partition_count += 1
                    if partition_count > max_partitions:
                        raise ValueError("slow role-language oracle partition limit exceeded")
                    if all(
                        expected in chart.get((cuts[index], cuts[index + 1]), ())
                        for index, expected in enumerate(production.chain_components)
                    ):
                        implied.update(
                            reachability_members(super_components[production.target_component])
                        )
                        break
            chart[(start, end)] = implied
    return target_component in chart.get((0, len(word_role_ids)), ())


def _partitions(start: int, end: int, arity: int) -> Iterable[tuple[int, ...]]:
    if arity < 1 or end - start < arity:
        return ()

    def generate(prefix: tuple[int, ...], remaining: int) -> Iterable[tuple[int, ...]]:
        if remaining == 1:
            yield (*prefix, end)
            return
        minimum = prefix[-1] + 1
        maximum = end - remaining + 1
        for cut in range(minimum, maximum + 1):
            yield from generate((*prefix, cut), remaining - 1)

    return generate((start,), arity)


__all__ = ["AutomatonProduction", "build_role_automata", "slow_word_implies"]
