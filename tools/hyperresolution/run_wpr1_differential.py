#!/usr/bin/env python3
"""Run both WP09 implementations against the shared WPR1 transition contract.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
TRACE = ROOT / "tests" / "data" / "hyperresolution" / "trace-v1.json"
TRACE_SHA256 = "e1b31962360bbafa8a134ca67d70d7653dfc98e07192f7b95223b4e05a51aea5"


def _command(argv: list[str], *, environment: dict[str, str]) -> dict[str, Any]:
    started = time.perf_counter()
    completed = subprocess.run(
        argv,
        cwd=ROOT,
        env=environment,
        check=False,
    )
    return {
        "argv": argv,
        "duration_seconds": round(time.perf_counter() - started, 6),
        "returncode": completed.returncode,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--python", default=sys.executable)
    parser.add_argument("--cargo", default="cargo")
    arguments = parser.parse_args()

    trace_bytes = TRACE.read_bytes()
    trace_sha256 = hashlib.sha256(trace_bytes).hexdigest()
    payload = json.loads(trace_bytes)
    case_ids = [case["id"] for case in payload.get("cases", [])]
    contract_valid = (
        trace_sha256 == TRACE_SHA256
        and payload.get("magic") == "PYHERMIT-HYPERRESOLUTION-TRACE"
        and payload.get("version") == 1
        and case_ids == ["semi-naive-chain", "branch-exhaustion"]
    )

    environment = dict(os.environ)
    environment["PYO3_PYTHON"] = str(Path(arguments.python).resolve())
    python_paths = [str(ROOT / "src"), str(ROOT.parent / "pyOWLCore" / "src")]
    if environment.get("PYTHONPATH"):
        python_paths.append(environment["PYTHONPATH"])
    environment["PYTHONPATH"] = os.pathsep.join(python_paths)
    cargo_parent = str(Path(arguments.cargo).resolve().parent)
    environment["PATH"] = os.pathsep.join([cargo_parent, environment.get("PATH", os.defpath)])
    python_gate = _command(
        [
            arguments.python,
            "-m",
            "pytest",
            "-q",
            "tests/unit/hyperresolution/test_rules.py::test_language_neutral_wp09_trace_fixture",
        ],
        environment=environment,
    )
    rust_gate = _command(
        [
            arguments.cargo,
            "test",
            "--locked",
            "--offline",
            "--no-default-features",
            "--manifest-path",
            "native/Cargo.toml",
        ],
        environment=environment,
    )
    oracle_gate = _command(
        [
            arguments.cargo,
            "test",
            "--locked",
            "--offline",
            "--no-default-features",
            "--manifest-path",
            "native/Cargo.toml",
            "rules::joins::tests::generated_indexed_and_naive_matches_are_differentially_equal",
        ],
        environment=environment,
    )
    report = {
        "case_ids": case_ids,
        "contract_valid": contract_valid,
        "gates": {
            "python_trace": python_gate,
            "rust_trace": rust_gate,
            "rust_naive_oracle": oracle_gate,
        },
        "schema": "pyhermit-wpr1-differential/1",
        "trace_sha256": trace_sha256,
    }
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return int(
        not contract_valid
        or python_gate["returncode"] != 0
        or rust_gate["returncode"] != 0
        or oracle_gate["returncode"] != 0
    )


if __name__ == "__main__":
    raise SystemExit(main())
