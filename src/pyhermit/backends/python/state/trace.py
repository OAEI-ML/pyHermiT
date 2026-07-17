"""Canonical language-neutral operation traces for the Python/Rust state kernels.

SPDX-License-Identifier: LGPL-3.0-or-later

The v1 trace uses named node aliases and JSON primitives only.  It is intentionally a
test/replay boundary, not the compiled-ontology wire format or a public reasoner API.
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from types import MappingProxyType
from typing import cast

from .dependencies import DependencySet
from .disjunctions import Clash, ClashKind
from .nodes import NodeHandle, NodeKind
from .session import BranchChoiceKind, TableauSession

STATE_TRACE_MAGIC = "PYHERMIT-STATE-TRACE"
STATE_TRACE_VERSION = 1

_FIELDS: dict[str, tuple[frozenset[str], frozenset[str]]] = {
    "add_disjunction": (frozenset({"dependency", "disjunct_ids"}), frozenset()),
    "add_fact": (
        frozenset({"arguments", "dependency", "predicate_id"}),
        frozenset({"core", "provenance_id"}),
    ),
    "advance_branch": (frozenset({"dependency", "level"}), frozenset()),
    "backtrack": (frozenset({"level"}), frozenset()),
    "begin_operation": (frozenset(), frozenset()),
    "check": (frozenset(), frozenset()),
    "create_node": (
        frozenset({"kind", "name"}),
        frozenset(
            {
                "cardinality_tag",
                "is_owl_named_individual",
                "nominal_level",
                "parent",
                "source_individual_id",
            }
        ),
    ),
    "enqueue": (frozenset({"priority", "queue", "value"}), frozenset()),
    "install_clash": (
        frozenset({"dependency", "kind"}),
        frozenset({"participants", "provenance_id"}),
    ),
    "mark_existential": (
        frozenset({"existential_id", "node", "pending"}),
        frozenset(),
    ),
    "merge": (frozenset({"dependency", "left", "right"}), frozenset()),
    "prepare_delta": (frozenset(), frozenset()),
    "prune": (frozenset({"root"}), frozenset()),
    "push_branch": (
        frozenset({"alternatives", "choice_kind", "dependency", "source_id"}),
        frozenset(),
    ),
    "set_blocked": (
        frozenset({"blocker", "directly", "node"}),
        frozenset(),
    ),
    "take_disjunction": (frozenset(), frozenset()),
}


def _freeze(value: object, *, path: str) -> object:
    if value is None or isinstance(value, (str, bool)):
        return value
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        raise TypeError(f"{path} must not contain floating-point values")
    if isinstance(value, Mapping):
        clean: dict[str, object] = {}
        for key, item in value.items():
            if not isinstance(key, str) or not key:
                raise TypeError(f"{path} mapping keys must be nonempty strings")
            clean[key] = _freeze(item, path=f"{path}.{key}")
        return MappingProxyType(dict(sorted(clean.items())))
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        return tuple(_freeze(item, path=f"{path}[]") for item in value)
    raise TypeError(f"{path} contains non-JSON state value {type(value).__name__}")


def _thaw(value: object) -> object:
    if isinstance(value, Mapping):
        return {key: _thaw(item) for key, item in value.items()}
    if isinstance(value, tuple):
        return [_thaw(item) for item in value]
    return value


@dataclass(frozen=True, slots=True)
class StateOperation:
    kind: str
    arguments: Mapping[str, object]

    def __post_init__(self) -> None:
        if self.kind not in _FIELDS:
            raise ValueError(f"unknown state operation {self.kind!r}")
        frozen = _freeze(self.arguments, path=f"operation.{self.kind}")
        if not isinstance(frozen, Mapping):
            raise TypeError("operation arguments must be a mapping")
        required, optional = _FIELDS[self.kind]
        names = frozenset(frozen)
        missing = required - names
        unknown = names - required - optional
        if missing:
            raise ValueError(f"operation {self.kind} is missing fields: {sorted(missing)}")
        if unknown:
            raise ValueError(f"operation {self.kind} has unknown fields: {sorted(unknown)}")
        object.__setattr__(self, "arguments", frozen)

    def as_dict(self) -> dict[str, object]:
        return {"arguments": cast(dict[str, object], _thaw(self.arguments)), "kind": self.kind}


@dataclass(frozen=True, slots=True)
class StateTrace:
    operations: tuple[StateOperation, ...]
    version: int = STATE_TRACE_VERSION

    def __post_init__(self) -> None:
        if self.version != STATE_TRACE_VERSION:
            raise ValueError(f"state trace version must be {STATE_TRACE_VERSION}")
        operations = tuple(self.operations)
        if not all(isinstance(operation, StateOperation) for operation in operations):
            raise TypeError("operations must contain StateOperation values")
        object.__setattr__(self, "operations", operations)

    def as_dict(self) -> dict[str, object]:
        return {
            "magic": STATE_TRACE_MAGIC,
            "operations": [operation.as_dict() for operation in self.operations],
            "version": self.version,
        }

    def canonical_json(self) -> str:
        return json.dumps(
            self.as_dict(),
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        )

    @property
    def sha256(self) -> str:
        return hashlib.sha256(self.canonical_json().encode("utf-8")).hexdigest()

    @classmethod
    def from_json(cls, payload: str | bytes) -> StateTrace:
        if not isinstance(payload, (str, bytes)):
            raise TypeError("state trace payload must be str or bytes")

        def unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
            result: dict[str, object] = {}
            for key, value in pairs:
                if key in result:
                    raise ValueError(f"duplicate JSON key {key!r}")
                result[key] = value
            return result

        document = json.loads(payload, object_pairs_hook=unique_object)
        if not isinstance(document, dict):
            raise ValueError("state trace must be a JSON object")
        if set(document) != {"magic", "operations", "version"}:
            raise ValueError("state trace top-level fields are not exact")
        if document["magic"] != STATE_TRACE_MAGIC:
            raise ValueError("state trace magic is invalid")
        if document["version"] != STATE_TRACE_VERSION:
            raise ValueError("state trace version is unsupported")
        raw_operations = document["operations"]
        if not isinstance(raw_operations, list):
            raise ValueError("state trace operations must be a list")
        operations: list[StateOperation] = []
        for raw in raw_operations:
            if not isinstance(raw, dict) or set(raw) != {"arguments", "kind"}:
                raise ValueError("each state operation must contain kind and arguments")
            if not isinstance(raw["kind"], str) or not isinstance(raw["arguments"], dict):
                raise ValueError("state operation kind/arguments have invalid types")
            operations.append(StateOperation(raw["kind"], raw["arguments"]))
        return cls(tuple(operations))


class StateTraceRunner:
    """Replay v1 mechanics and return a canonical snapshot after every operation."""

    __slots__ = ("aliases", "session")

    def __init__(self) -> None:
        self.session = TableauSession()
        self.aliases: dict[str, NodeHandle] = {}

    def run(self, trace: StateTrace) -> tuple[str, ...]:
        if not isinstance(trace, StateTrace):
            raise TypeError("trace must be StateTrace")
        snapshots: list[str] = []
        for operation in trace.operations:
            self.apply(operation)
            self.session.check_invariants()
            snapshots.append(self.session.canonical_snapshot())
        return tuple(snapshots)

    def apply(self, operation: StateOperation) -> None:
        arguments = operation.arguments
        handlers: dict[str, Callable[[Mapping[str, object]], None]] = {
            "add_disjunction": self._add_disjunction,
            "add_fact": self._add_fact,
            "advance_branch": self._advance_branch,
            "backtrack": self._backtrack,
            "begin_operation": self._begin_operation,
            "check": self._check,
            "create_node": self._create_node,
            "enqueue": self._enqueue,
            "install_clash": self._install_clash,
            "mark_existential": self._mark_existential,
            "merge": self._merge,
            "prepare_delta": self._prepare_delta,
            "prune": self._prune,
            "push_branch": self._push_branch,
            "set_blocked": self._set_blocked,
            "take_disjunction": self._take_disjunction,
        }
        handler = handlers[operation.kind]
        handler(arguments)

    def _create_node(self, values: Mapping[str, object]) -> None:
        name = self._string(values, "name")
        if name in self.aliases:
            raise ValueError(f"node alias {name!r} already exists")
        parent_value = values.get("parent")
        parent = None if parent_value is None else self._alias(parent_value)
        handle = self.session.nodes.create(
            NodeKind(self._string(values, "kind")),
            parent=parent,
            is_owl_named_individual=self._boolean(values, "is_owl_named_individual", default=False),
            source_individual_id=self._optional_integer(values, "source_individual_id"),
            creation_checkpoint=self.session.highest_branch_level or 0,
            nominal_level=self._optional_integer(values, "nominal_level"),
            cardinality_tag=self._optional_integer(values, "cardinality_tag"),
        )
        self.aliases[name] = handle

    def _add_fact(self, values: Mapping[str, object]) -> None:
        aliases = self._sequence(values, "arguments")
        self.session.extensions.add(
            self._integer(values, "predicate_id"),
            tuple(self._alias(alias) for alias in aliases),
            self._dependency(values),
            core=self._boolean(values, "core", default=False),
            provenance_id=self._optional_integer(values, "provenance_id"),
        )

    def _prepare_delta(self, _values: Mapping[str, object]) -> None:
        self.session.extensions.prepare_next_delta()

    def _push_branch(self, values: Mapping[str, object]) -> None:
        self.session.push_branch(
            BranchChoiceKind(self._string(values, "choice_kind")),
            self._integer_tuple(values, "alternatives"),
            source_id=self._integer(values, "source_id"),
            base_dependency=self._dependency(values),
        )

    def _advance_branch(self, values: Mapping[str, object]) -> None:
        self.session.advance_branch(self._integer(values, "level"), self._dependency(values))

    def _backtrack(self, values: Mapping[str, object]) -> None:
        self.session.backtrack_to(self._integer(values, "level"))

    def _merge(self, values: Mapping[str, object]) -> None:
        self.session.merge_nodes(
            self._alias(values["left"]),
            self._alias(values["right"]),
            self._dependency(values),
        )

    def _prune(self, values: Mapping[str, object]) -> None:
        self.session.prune_subtree(self._alias(values["root"]))

    def _add_disjunction(self, values: Mapping[str, object]) -> None:
        self.session.add_ground_disjunction(
            self._integer_tuple(values, "disjunct_ids"), self._dependency(values)
        )

    def _take_disjunction(self, _values: Mapping[str, object]) -> None:
        self.session.take_ground_disjunction()

    def _install_clash(self, values: Mapping[str, object]) -> None:
        self.session.install_clash(
            Clash(
                ClashKind(self._string(values, "kind")),
                self._dependency(values),
                self._integer_tuple(values, "participants", default=()),
                self._optional_integer(values, "provenance_id"),
            )
        )

    def _enqueue(self, values: Mapping[str, object]) -> None:
        name = self._string(values, "queue")
        priority = self._integer_tuple(values, "priority")
        value = values["value"]
        integer_queues = {
            "annotated_equalities": self.session.annotated_equalities,
            "datatype_components": self.session.datatype_components,
            "delta_rows": self.session.delta_rows,
        }
        node_queues = {
            "blocking_invalidations": self.session.blocking_invalidations,
            "existential_candidates": self.session.existential_candidates,
        }
        if name in integer_queues:
            integer_queues[name].enqueue(self._as_integer(value, "queue.value"), priority)
            return
        if name in node_queues:
            node_queues[name].enqueue(self._alias(value), priority)
            return
        raise ValueError(f"unknown trace queue {name!r}")

    def _mark_existential(self, values: Mapping[str, object]) -> None:
        self.session.nodes.mark_existential(
            self._alias(values["node"]),
            self._integer(values, "existential_id"),
            pending=self._boolean(values, "pending"),
        )

    def _set_blocked(self, values: Mapping[str, object]) -> None:
        blocker_value = values["blocker"]
        blocker = None if blocker_value is None else self._alias(blocker_value)
        self.session.nodes.set_blocked(
            self._alias(values["node"]),
            blocker,
            directly=self._boolean(values, "directly"),
        )

    def _begin_operation(self, _values: Mapping[str, object]) -> None:
        self.session.begin_operation()

    def _check(self, _values: Mapping[str, object]) -> None:
        self.session.check_invariants()

    def _alias(self, value: object) -> NodeHandle:
        if not isinstance(value, str):
            raise TypeError("node aliases must be strings")
        try:
            return self.aliases[value]
        except KeyError as exc:
            raise ValueError(f"unknown node alias {value!r}") from exc

    @staticmethod
    def _sequence(values: Mapping[str, object], name: str) -> tuple[object, ...]:
        value = values[name]
        if not isinstance(value, tuple):
            raise TypeError(f"{name} must be an array")
        return value

    @classmethod
    def _integer_tuple(
        cls,
        values: Mapping[str, object],
        name: str,
        *,
        default: tuple[int, ...] | None = None,
    ) -> tuple[int, ...]:
        if name not in values:
            if default is None:
                raise KeyError(name)
            return default
        return tuple(cls._as_integer(item, name) for item in cls._sequence(values, name))

    @staticmethod
    def _as_integer(value: object, name: str) -> int:
        if isinstance(value, bool) or not isinstance(value, int) or value < 0:
            raise TypeError(f"{name} must contain nonnegative integers")
        return value

    @classmethod
    def _integer(cls, values: Mapping[str, object], name: str) -> int:
        return cls._as_integer(values[name], name)

    @staticmethod
    def _string(values: Mapping[str, object], name: str) -> str:
        value = values[name]
        if not isinstance(value, str) or not value:
            raise TypeError(f"{name} must be a nonempty string")
        return value

    @staticmethod
    def _boolean(
        values: Mapping[str, object],
        name: str,
        *,
        default: bool | None = None,
    ) -> bool:
        if name not in values:
            if default is None:
                raise KeyError(name)
            return default
        value = values[name]
        if not isinstance(value, bool):
            raise TypeError(f"{name} must be bool")
        return value

    @classmethod
    def _optional_integer(cls, values: Mapping[str, object], name: str) -> int | None:
        value = values.get(name)
        return None if value is None else cls._as_integer(value, name)

    @classmethod
    def _dependency(cls, values: Mapping[str, object]) -> DependencySet:
        return DependencySet.of(cls._integer_tuple(values, "dependency"))


__all__ = [
    "STATE_TRACE_MAGIC",
    "STATE_TRACE_VERSION",
    "StateOperation",
    "StateTrace",
    "StateTraceRunner",
]
