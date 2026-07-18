from __future__ import annotations

import json
import sys
from pathlib import Path

if sys.version_info >= (3, 11):
    import tomllib
else:
    import tomli as tomllib

from benchmarks.run_release import PHASES, SEED, WORKLOADS, generated_taxonomy, run_benchmark

from pyhermit import BackendName

from .test_wp17_reports import _load, _validate

ROOT = Path(__file__).resolve().parents[2]


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


def test_committed_local_samples_conform_and_have_exact_parity() -> None:
    schema = _load(ROOT / "benchmarks/schema/release-result-v1.schema.json")
    python = _load(ROOT / "benchmarks/evidence/wp17-local-python.json")
    native = _load(ROOT / "benchmarks/evidence/wp17-local-native.json")
    _validate(schema, python, schema, "python-benchmark")
    _validate(schema, native, schema, "native-benchmark")

    assert python["status"] == native["status"] == "informational-local"
    assert python["input_sha256"] == native["input_sha256"]
    assert python["result_sha256"] == native["result_sha256"]
    assert python["backend"]["selected"] == "python"
    assert native["backend"]["selected"] == "native"
