from __future__ import annotations

import json
import sys
from pathlib import Path

if sys.version_info >= (3, 11):
    import tomllib
else:
    import tomli as tomllib

from benchmarks import run_release as release_benchmark
from benchmarks.run_release import (
    PHASES,
    SEED,
    WORKLOADS,
    _result_digest,
    generated_taxonomy,
    run_benchmark,
)
from pyowl_core import IRI, Class

from pyhermit import BackendName, Hierarchy, ReasonerTimeoutError

from .test_wp17_reports import _load, _validate

ROOT = Path(__file__).resolve().parents[2]


def _assert_outcome_consistency(result: dict[str, object]) -> None:
    outcome = result["outcome"]
    assert isinstance(outcome, dict)
    samples = result["samples"]
    medians = result["medians"]
    assert isinstance(samples, list) and samples
    assert isinstance(medians, dict)
    if outcome["kind"] == "success":
        assert outcome == {
            "kind": "success",
            "error_type": None,
            "error_code": None,
            "message": None,
        }
        assert isinstance(result["result_sha256"], str)
        assert all(sample[phase] is not None for sample in samples for phase in PHASES)
        assert all(medians[phase] is not None for phase in PHASES)
    else:
        assert result["result_sha256"] is None
        assert isinstance(outcome["error_type"], str) and outcome["error_type"]
        assert isinstance(outcome["message"], str) and outcome["message"]


def test_workload_and_target_manifests_are_exact_and_fail_closed() -> None:
    workload = tomllib.loads(
        (ROOT / "benchmarks/workloads/generated-taxonomy-v1.toml").read_text(encoding="utf-8")
    )
    assert workload["schema"] == 1
    assert workload["seed"] == SEED
    assert {
        item["id"]: (item["classes"], item["individuals"]) for item in workload["size"]
    } == WORKLOADS
    assert all(item["must_not_regress"] is True for item in workload["size"])

    targets = tomllib.loads((ROOT / "benchmarks/targets.toml").read_text(encoding="utf-8"))
    assert targets["schema"] == 1
    assert targets["status"] == "provisional-awaiting-dedicated-calibration"
    assert targets["result_hash_required"] is True
    assert targets["raw_samples_required"] is True
    assert targets["dedicated_runner_required"] is True
    assert set(targets["calibration"].values()) == {""}
    assert [path.name for path in (ROOT / "benchmarks/baselines").iterdir()] == ["README.md"]


def test_python_smoke_emits_hash_bound_phase_evidence() -> None:
    first_source = generated_taxonomy(*WORKLOADS["small"])
    second_source = generated_taxonomy(*WORKLOADS["small"])
    assert first_source == second_source

    result = run_benchmark(size="small", backend=BackendName.PYTHON, samples=1)
    schema = json.loads(
        (ROOT / "benchmarks/schema/release-result-v1.schema.json").read_text(encoding="utf-8")
    )
    assert set(schema["required"]) == set(result)
    assert result["schema"] == "pyhermit.release-benchmark/1"
    assert result["status"] == "informational-local"
    assert result["outcome"] == {
        "kind": "success",
        "error_type": None,
        "error_code": None,
        "message": None,
    }
    _assert_outcome_consistency(result)
    assert result["backend"]["requested"] == "python"  # type: ignore[index]
    assert result["backend"]["selected"] == "python"  # type: ignore[index]
    assert len(result["input_sha256"]) == 64  # type: ignore[arg-type]
    assert len(result["result_sha256"]) == 64  # type: ignore[arg-type]
    samples = result["samples"]
    assert isinstance(samples, list) and len(samples) == 1
    assert set(samples[0]) == set(PHASES)
    assert all(samples[0][phase] >= 0 for phase in PHASES)
    medians = result["medians"]
    assert isinstance(medians, dict)
    assert all(medians[phase] == samples[0][phase] for phase in PHASES)


def test_result_digest_preserves_realization_group_boundaries() -> None:
    left = Class(IRI("urn:wp17-digest#left"))
    right = Class(IRI("urn:wp17-digest#right"))
    hierarchy = Hierarchy(
        nodes=(frozenset((left, right)),),
        edges=frozenset(),
        top_node=0,
        bottom_node=0,
    )
    grouped = frozenset((frozenset((left, right)),))
    split = frozenset((frozenset((left,)), frozenset((right,))))
    assert _result_digest(True, hierarchy, grouped) != _result_digest(True, hierarchy, split)


def test_runner_retains_timeout_as_a_structured_partial_result(monkeypatch) -> None:
    def time_out(*_args: object, **_kwargs: object) -> None:
        raise ReasonerTimeoutError("bounded load timed out")

    monkeypatch.setattr(release_benchmark, "load_snapshot", time_out)
    result = release_benchmark.run_benchmark(size="small", backend=BackendName.PYTHON, samples=3)
    schema = _load(ROOT / "benchmarks/schema/release-result-v1.schema.json")
    _validate(schema, result, schema, "timeout-benchmark")
    assert result["outcome"] == {
        "kind": "timeout",
        "error_type": "ReasonerTimeoutError",
        "error_code": "REASONER_TIMEOUT",
        "message": "bounded load timed out",
    }
    assert result["result_sha256"] is None
    assert result["backend"]["selected"] is None  # type: ignore[index]
    assert len(result["samples"]) == 1  # type: ignore[arg-type]
    assert set(result["samples"][0].values()) == {None}  # type: ignore[index,union-attr]
    _assert_outcome_consistency(result)


def test_committed_local_samples_conform_and_have_exact_parity() -> None:
    schema = _load(ROOT / "benchmarks/schema/release-result-v1.schema.json")
    python = _load(ROOT / "benchmarks/evidence/wp17-local-python.json")
    native = _load(ROOT / "benchmarks/evidence/wp17-local-native.json")
    _validate(schema, python, schema, "python-benchmark")
    _validate(schema, native, schema, "native-benchmark")
    _assert_outcome_consistency(python)
    _assert_outcome_consistency(native)

    assert python["status"] == native["status"] == "informational-local"
    assert python["input_sha256"] == native["input_sha256"]
    assert python["result_sha256"] == native["result_sha256"]
    assert python["backend"]["selected"] == "python"
    assert native["backend"]["selected"] == "native"
