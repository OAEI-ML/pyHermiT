#!/usr/bin/env python3
"""Reproducible complete-tableau throughput and cancellation probe for WP12."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import statistics
import time
import tracemalloc
from collections.abc import Callable, Sequence
from dataclasses import dataclass

import pyowl_core.model as owl

from pyhermit.backends.python.state import NodeLifecycle
from pyhermit.backends.python.tableau import PythonTableau
from pyhermit.clauses import ClauseProgram, compile_normalized
from pyhermit.config import ReasonerConfig
from pyhermit.events import CancellationSource
from pyhermit.exceptions import ReasoningAbortedError
from pyhermit.normalize import normalize_axioms


@dataclass(frozen=True, slots=True)
class RunResult:
    digest: str
    elapsed_seconds: float
    nodes: int
    facts: int
    scheduler_steps: int


def _workload(individuals: int, depth: int) -> ClauseProgram:
    chain = tuple(
        owl.Class(owl.IRI(f"urn:bench:wp12:class:{index:04d}")) for index in range(depth + 1)
    )
    axioms: list[owl.AxiomNode] = [
        owl.SubClassOf(chain[index], chain[index + 1]) for index in range(depth)
    ]
    for index in range(individuals):
        individual = owl.NamedIndividual(owl.IRI(f"urn:bench:wp12:i:{index:09d}"))
        axioms.append(owl.ClassAssertion(chain[0], individual))
    logical = hashlib.sha256(b"pyhermit/wp12/tableau-workload/v1\0").hexdigest()
    return compile_normalized(normalize_axioms(tuple(axioms), logical_fingerprint=logical))


def _state_digest(tableau: PythonTableau) -> str:
    digest = hashlib.sha256(b"pyhermit/wp12/complete-state/v1\0")
    for node in tableau.session.nodes.existing_nodes():
        digest.update(node.handle.slot.to_bytes(4, "little"))
        digest.update(node.handle.generation.to_bytes(4, "little"))
        digest.update(node.lifecycle.value.encode("ascii"))
    for row in tableau.session.extensions.active_rows():
        digest.update(row.key.predicate_id.to_bytes(4, "little"))
        for argument in row.key.arguments:
            digest.update(argument.slot.to_bytes(4, "little"))
            digest.update(argument.generation.to_bytes(4, "little"))
    return digest.hexdigest()


def _run(program: ClauseProgram) -> RunResult:
    token = CancellationSource().token
    started = time.perf_counter()
    tableau = PythonTableau(program, ReasonerConfig(), token)
    result = tableau.run(token)
    elapsed = time.perf_counter() - started
    if not result.satisfiable:
        raise AssertionError("the benchmark ontology unexpectedly became inconsistent")
    nodes = tuple(
        value
        for value in tableau.session.nodes.existing_nodes()
        if value.lifecycle is NodeLifecycle.ACTIVE
    )
    return RunResult(
        _state_digest(tableau),
        elapsed,
        len(nodes),
        len(tableau.session.extensions.active_rows()),
        result.statistics.scheduler_steps,
    )


def _samples(
    operation: Callable[[], RunResult],
    count: int,
) -> tuple[list[RunResult], RunResult]:
    operation()
    values = [operation() for _index in range(count)]
    expected = values[0]
    identity = (expected.digest, expected.nodes, expected.facts, expected.scheduler_steps)
    if any(
        (value.digest, value.nodes, value.facts, value.scheduler_steps) != identity
        for value in values[1:]
    ):
        raise AssertionError("complete-tableau result changed between samples")
    return values, expected


def _percentile(values: Sequence[float], percentile: float) -> float:
    ordered = sorted(values)
    return ordered[max(0, math.ceil(percentile * len(ordered)) - 1)]


def _cancellation(program: ClauseProgram, timeout_ms: float) -> dict[str, float | int]:
    tableau = PythonTableau(program, ReasonerConfig(), CancellationSource().token)
    operation_root = tableau.session.canonical_snapshot()
    token = CancellationSource(timeout=timeout_ms / 1_000).token
    started = time.perf_counter()
    try:
        tableau.run(token)
    except ReasoningAbortedError:
        elapsed = time.perf_counter() - started
    else:
        raise AssertionError("cancellation workload completed before its deadline")
    if tableau.session.canonical_snapshot() != operation_root:
        raise AssertionError("cancellation did not restore the initialized operation root")
    return {
        "elapsed_seconds": elapsed,
        "latency_after_deadline_seconds": max(0.0, elapsed - timeout_ms / 1_000),
        "work": token.work,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--individuals", type=int, default=10_000)
    parser.add_argument("--depth", type=int, default=4)
    parser.add_argument("--samples", type=int, default=3)
    parser.add_argument("--cancellation-individuals", type=int, default=30_000)
    parser.add_argument("--cancellation-timeout-ms", type=float, default=1.0)
    arguments = parser.parse_args()
    for name in ("individuals", "depth", "samples", "cancellation_individuals"):
        value = getattr(arguments, name)
        if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
            parser.error(f"{name.replace('_', '-')} must be a positive integer")
    if (
        not math.isfinite(arguments.cancellation_timeout_ms)
        or arguments.cancellation_timeout_ms <= 0
    ):
        parser.error("cancellation-timeout-ms must be positive and finite")

    program = _workload(arguments.individuals, arguments.depth)
    measured, expected = _samples(lambda: _run(program), arguments.samples)
    elapsed = [value.elapsed_seconds for value in measured]

    tracemalloc.start()
    _run(program)
    _current, peak_bytes = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    cancellation_program = _workload(arguments.cancellation_individuals, arguments.depth)
    payload = {
        "schema": "pyhermit-wp12-tableau-benchmark/1",
        "environment": {
            "implementation": platform.python_implementation(),
            "machine": platform.machine(),
            "platform": platform.platform(),
            "python": platform.python_version(),
        },
        "configuration": {
            "depth": arguments.depth,
            "individuals": arguments.individuals,
            "samples": arguments.samples,
            "warmup_samples": 1,
        },
        "result": {
            "digest": expected.digest,
            "facts": expected.facts,
            "nodes": expected.nodes,
            "scheduler_steps": expected.scheduler_steps,
        },
        "tableau": {
            "median_seconds": statistics.median(elapsed),
            "p95_seconds": _percentile(elapsed, 0.95),
            "source_individuals_per_second": (arguments.individuals / statistics.median(elapsed)),
        },
        "tracemalloc_peak_bytes": peak_bytes,
        "cancellation": _cancellation(
            cancellation_program,
            arguments.cancellation_timeout_ms,
        ),
    }
    print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
