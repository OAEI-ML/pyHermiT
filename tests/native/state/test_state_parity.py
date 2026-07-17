"""Exact Python/Rust state-trace parity tests."""

# SPDX-License-Identifier: LGPL-3.0-or-later

from __future__ import annotations

import hashlib
import json
import random
from pathlib import Path

import pytest
from tests.native.wire._builder import valid_documents

import pyhermit._native as native
from pyhermit.backends.python.state import StateOperation, StateTrace, StateTraceRunner
from pyhermit.exceptions import BackendMismatchError, BackendVersionError, ResourceLimitError

TRACE = Path(__file__).parents[2] / "data" / "state" / "trace-v1.json"
SNAPSHOTS_SHA256 = "0ba539d31e8e6d274711af380f669ad6723515950e35c694f88c6371e03753c9"


def make_session() -> native.NativeSession:
    ontology, config = valid_documents()
    return native.create_session(ontology, config, native.CancellationHandle())


def assert_trace_parity(trace: StateTrace) -> None:
    expected = StateTraceRunner().run(trace)
    session = make_session()
    actual = session._debug_replay_state_trace(trace.canonical_json().encode())
    session.close()
    assert actual == list(expected)


def test_canonical_wp08_golden_matches_after_every_operation() -> None:
    payload = TRACE.read_bytes().strip()
    trace = StateTrace.from_json(payload)
    expected = StateTraceRunner().run(trace)
    session = make_session()
    actual = session._debug_replay_state_trace(payload)
    session.close()
    assert actual == list(expected)
    digest_payload = ("\n".join(actual) + "\n").encode()
    assert hashlib.sha256(digest_payload).hexdigest() == SNAPSHOTS_SHA256


def _mechanics_traces() -> tuple[StateTrace, ...]:
    prune_and_queues = StateTrace(
        (
            StateOperation("create_node", {"kind": "root", "name": "r"}),
            StateOperation("create_node", {"kind": "root", "name": "blocker"}),
            StateOperation("create_node", {"kind": "tree", "name": "c", "parent": "r"}),
            StateOperation("create_node", {"kind": "tree", "name": "d", "parent": "c"}),
            StateOperation("begin_operation", {}),
            StateOperation(
                "add_fact",
                {"arguments": ["d"], "dependency": [], "predicate_id": 7},
            ),
            StateOperation(
                "set_blocked",
                {"blocker": "blocker", "directly": True, "node": "c"},
            ),
            StateOperation(
                "enqueue",
                {"priority": [1, 41], "queue": "annotated_equalities", "value": 41},
            ),
            StateOperation(
                "enqueue",
                {"priority": [2, 42], "queue": "datatype_components", "value": 42},
            ),
            StateOperation(
                "enqueue",
                {"priority": [3, 43], "queue": "delta_rows", "value": 43},
            ),
            StateOperation(
                "enqueue",
                {"priority": [4, 3], "queue": "blocking_invalidations", "value": "d"},
            ),
            StateOperation(
                "mark_existential",
                {"existential_id": 9, "node": "d", "pending": True},
            ),
            StateOperation("prune", {"root": "c"}),
            StateOperation("check", {}),
        )
    )
    supports_and_rollback = StateTrace(
        (
            StateOperation("create_node", {"kind": "root", "name": "r"}),
            StateOperation("begin_operation", {}),
            StateOperation(
                "push_branch",
                {
                    "alternatives": [1, 2],
                    "choice_kind": "ground_disjunction",
                    "dependency": [],
                    "source_id": 1,
                },
            ),
            StateOperation(
                "push_branch",
                {
                    "alternatives": [3, 4],
                    "choice_kind": "merge",
                    "dependency": [0],
                    "source_id": 2,
                },
            ),
            StateOperation(
                "add_fact",
                {"arguments": ["r"], "dependency": [0], "predicate_id": 8},
            ),
            StateOperation(
                "add_fact",
                {"arguments": ["r"], "dependency": [1], "predicate_id": 8},
            ),
            StateOperation(
                "add_disjunction",
                {"dependency": [1], "disjunct_ids": [50, 51]},
            ),
            StateOperation("take_disjunction", {}),
            StateOperation(
                "install_clash",
                {"dependency": [0, 1], "kind": "bottom", "participants": [8]},
            ),
            StateOperation("backtrack", {"level": 1}),
            StateOperation("check", {}),
        )
    )
    delta = StateTrace(
        (
            StateOperation("create_node", {"kind": "root", "name": "a"}),
            StateOperation("create_node", {"kind": "root", "name": "b"}),
            StateOperation(
                "add_fact",
                {"arguments": ["a"], "dependency": [], "predicate_id": 1},
            ),
            StateOperation("prepare_delta", {}),
            StateOperation(
                "add_fact",
                {"arguments": ["a", "b"], "dependency": [], "predicate_id": 2},
            ),
            StateOperation("check", {}),
        )
    )
    return prune_and_queues, supports_and_rollback, delta


@pytest.mark.parametrize("trace", _mechanics_traces())
def test_hand_built_mechanics_traces_match_exactly(trace: StateTrace) -> None:
    assert_trace_parity(trace)


@pytest.mark.parametrize("seed", range(16))
def test_deterministic_generated_fact_delta_and_disjunction_traces(seed: int) -> None:
    randomizer = random.Random(seed)
    operations = [
        StateOperation("create_node", {"kind": "root", "name": f"n{index}"})
        for index in range(4)
    ]
    operations.append(StateOperation("begin_operation", {}))
    for index in range(24):
        arity = randomizer.choice((1, 2))
        arguments = [f"n{randomizer.randrange(4)}" for _ in range(arity)]
        operations.append(
            StateOperation(
                "add_fact",
                {
                    "arguments": arguments,
                    "core": bool(randomizer.randrange(2)),
                    "dependency": [],
                    "predicate_id": randomizer.randrange(1, 7),
                    "provenance_id": randomizer.randrange(8),
                },
            )
        )
        if index in {7, 15}:
            operations.append(StateOperation("prepare_delta", {}))
    operations.extend(
        (
            StateOperation(
                "add_disjunction",
                {"dependency": [], "disjunct_ids": [100 + seed * 2, 101 + seed * 2]},
            ),
            StateOperation("take_disjunction", {}),
            StateOperation("check", {}),
        )
    )
    assert_trace_parity(StateTrace(tuple(operations)))


@pytest.mark.parametrize(
    ("payload", "error_type"),
    (
        (
            b'{"magic":"x","magic":"y","operations":[],"version":1}',
            BackendMismatchError,
        ),
        (
            b'{"magic":"PYHERMIT-STATE-TRACE","operations":[],"version":2}',
            BackendVersionError,
        ),
        (
            b'{"magic":"PYHERMIT-STATE-TRACE","operations":[{"arguments":{},'
            b'"kind":"unknown"}],"version":1}',
            BackendVersionError,
        ),
        (
            b'{"magic":"PYHERMIT-STATE-TRACE","operations":[{"arguments":'
            b'{"priority":[1.5],"queue":"delta_rows","value":0},'
            b'"kind":"enqueue"}],"version":1}',
            BackendMismatchError,
        ),
    ),
)
def test_malformed_trace_is_rejected_without_poisoning(
    payload: bytes,
    error_type: type[Exception],
) -> None:
    session = make_session()
    with pytest.raises(error_type):
        session._debug_replay_state_trace(payload)
    empty = json.dumps(
        {"magic": "PYHERMIT-STATE-TRACE", "operations": [], "version": 1},
        separators=(",", ":"),
        sort_keys=True,
    ).encode()
    assert session._debug_replay_state_trace(empty) == []
    assert not session.poisoned
    session.close()


def test_trace_operation_claim_is_capped_before_snapshot_allocation() -> None:
    operation = {"arguments": {}, "kind": "check"}
    payload = json.dumps(
        {
            "magic": "PYHERMIT-STATE-TRACE",
            "operations": [operation] * 10_001,
            "version": 1,
        },
        separators=(",", ":"),
        sort_keys=True,
    ).encode()
    session = make_session()
    with pytest.raises(ResourceLimitError) as captured:
        session._debug_replay_state_trace(payload)
    assert captured.value.limit == "state_trace_operations"
    assert captured.value.observed == 10_001
    assert captured.value.allowed == 10_000
    assert not session.poisoned
    session.close()
