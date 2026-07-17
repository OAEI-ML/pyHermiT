from __future__ import annotations

import copy
import random
from dataclasses import dataclass

import pytest

from pyhermit.backends.python.state import (
    Checkpoint,
    DependencyPool,
    DependencySet,
    ExtensionStore,
    NodeArena,
    NodeHandle,
    NodeKind,
    Trail,
)


@dataclass
class _ReferenceRow:
    key: tuple[int, tuple[NodeHandle, ...]]
    supports: tuple[int, ...]
    core: bool
    active: bool
    generation: int


@dataclass
class _SlowReference:
    rows: list[_ReferenceRow]
    by_key: dict[tuple[int, tuple[NodeHandle, ...]], int]
    read_generation: int = 0
    write_generation: int = 0

    @classmethod
    def empty(cls) -> _SlowReference:
        return cls([], {})

    def add(
        self,
        predicate: int,
        arguments: tuple[NodeHandle, ...],
        support: int,
        *,
        core: bool,
    ) -> None:
        key = predicate, arguments
        row_id = self.by_key.get(key)
        if row_id is None:
            row = _ReferenceRow(key, (support,), core, True, self.write_generation)
            self.by_key[key] = len(self.rows)
            self.rows.append(row)
            return
        row = self.rows[row_id]
        if not any(existing & ~support == 0 for existing in row.supports):
            retained = tuple(existing for existing in row.supports if support & ~existing != 0)
            row.supports = tuple(sorted((*retained, support)))
        row.core = row.core or core

    def deactivate(self, row_id: int) -> None:
        row = self.rows[row_id]
        row.active = False
        self.by_key.pop(row.key)

    def prepare_next_delta(self) -> None:
        if self.write_generation == self.read_generation:
            self.write_generation += 1
        else:
            self.read_generation = self.write_generation
            self.write_generation += 1

    def logical(self) -> tuple[tuple[object, ...], ...]:
        return tuple(
            (
                row.key[0],
                tuple((handle.slot, handle.generation) for handle in row.key[1]),
                row.supports,
                row.core,
                row.generation,
            )
            for row in self.rows
            if row.active
        )


def _actual(store: ExtensionStore) -> tuple[tuple[object, ...], ...]:
    return tuple(
        (
            row.key.predicate_id,
            tuple((handle.slot, handle.generation) for handle in row.key.arguments),
            tuple(support.bits for support in row.supports),
            row.core,
            row.derivation_generation,
        )
        for row in store.active_rows()
    )


@pytest.mark.parametrize("seed", range(24))
def test_random_operation_machine_matches_persistent_slow_reference(seed: int) -> None:
    randomizer = random.Random(seed)
    trail = Trail()
    dependencies = DependencyPool()
    nodes = NodeArena(trail, dependencies)
    handles = tuple(nodes.create(NodeKind.ROOT) for _ in range(3))
    store = ExtensionStore(trail, nodes, dependencies)
    reference = _SlowReference.empty()
    checkpoints: list[tuple[Checkpoint, _SlowReference]] = []

    for step in range(180):
        action = randomizer.randrange(6)
        if action in (0, 1, 2):
            predicate = randomizer.randrange(4)
            arity = randomizer.choice((1, 2))
            arguments = tuple(randomizer.choice(handles) for _ in range(arity))
            levels = [level for level in range(4) if randomizer.randrange(2)]
            dependency = DependencySet.of(levels)
            core = bool(randomizer.randrange(2))
            store.add(predicate, arguments, dependency, core=core)
            reference.add(predicate, arguments, dependency.bits, core=core)
        elif action == 3:
            active = [row.row_id for row in store.active_rows()]
            if active:
                row_id = randomizer.choice(active)
                store.deactivate(row_id)
                reference.deactivate(row_id)
        elif action == 4:
            store.prepare_next_delta()
            reference.prepare_next_delta()
        else:
            if checkpoints and randomizer.randrange(3) == 0:
                checkpoint, saved = checkpoints.pop()
                trail.rollback(checkpoint)
                reference = saved
            else:
                checkpoints.append(
                    (trail.checkpoint(f"seed-{seed}-step-{step}"), copy.deepcopy(reference))
                )
                store.register_index(randomizer.choice(((), (0,), (1,), (0, 1))))

        store.check_invariants(highest_branch_level=3)
        assert _actual(store) == reference.logical()
        assert (store.read_generation, store.write_generation) == (
            reference.read_generation,
            reference.write_generation,
        )

    while checkpoints:
        checkpoint, saved = checkpoints.pop()
        trail.rollback(checkpoint)
        reference = saved
        store.check_invariants(highest_branch_level=3)
        assert _actual(store) == reference.logical()
