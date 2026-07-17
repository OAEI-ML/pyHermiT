from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from pyhermit.backends.python.state import StateOperation, StateTrace, StateTraceRunner

TRACE = Path(__file__).parents[2] / "data" / "state" / "trace-v1.json"
TRACE_SHA256 = "501e99b619d88567fe22dfc155f9929e2f980c6ddccdb052c529f17bf479690f"
SNAPSHOTS_SHA256 = "c50db3510ac32b605741731e54ef8fc7ca5a98926e47b607e29a107f21fc8196"


def test_golden_trace_is_canonical_round_trippable_and_replayable() -> None:
    payload = TRACE.read_text(encoding="utf-8").strip()
    trace = StateTrace.from_json(payload)
    assert trace.canonical_json() == payload
    assert trace.sha256 == TRACE_SHA256
    first = StateTraceRunner().run(trace)
    second = StateTraceRunner().run(StateTrace.from_json(trace.canonical_json()))
    assert first == second
    assert len(first) == len(trace.operations)
    snapshots_payload = ("\n".join(first) + "\n").encode()
    assert hashlib.sha256(snapshots_payload).hexdigest() == SNAPSHOTS_SHA256
    assert '"lifecycle":"merged"' in first[-1]
    assert '"next_alternative":1' in first[-1]


def test_trace_rejects_unknown_fields_floats_duplicates_and_runtime_objects() -> None:
    with pytest.raises(ValueError, match="unknown fields"):
        StateOperation("check", {"surprise": 1})
    with pytest.raises(TypeError, match="floating-point"):
        StateOperation("enqueue", {"priority": [1.5], "queue": "delta_rows", "value": 0})
    with pytest.raises(TypeError, match="non-JSON"):
        StateOperation("check", {"bad": object()})
    with pytest.raises(ValueError, match="duplicate JSON key"):
        StateTrace.from_json('{"magic":"x","magic":"y","operations":[],"version":1}')


def test_trace_envelope_is_exact_and_versioned() -> None:
    document = json.loads(TRACE.read_text(encoding="utf-8"))
    document["extra"] = True
    with pytest.raises(ValueError, match="top-level"):
        StateTrace.from_json(json.dumps(document))
    document.pop("extra")
    document["version"] = 2
    with pytest.raises(ValueError, match="unsupported"):
        StateTrace.from_json(json.dumps(document))
