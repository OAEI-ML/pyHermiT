#!/usr/bin/env python3
"""Reproducible indexed-hyperresolution throughput probe for WP09."""

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

from pyhermit.backends.python.rules import HyperresolutionEngine
from pyhermit.backends.python.state import NodeKind, TableauSession
from pyhermit.clauses import ClauseProgram, SymbolKind, compile_normalized
from pyhermit.events import CancellationSource
from pyhermit.exceptions import ReasoningAbortedError
from pyhermit.normalize import normalize_axioms


@dataclass(frozen=True, slots=True)
class RunResult:
    digest: str
    generations: int
    rows: int
    initialize_seconds: float
    saturate_seconds: float


def _workload(facts: int, depth: int) -> ClauseProgram:
    left = owl.Class(owl.IRI("urn:bench:wp09:left"))
    right = owl.Class(owl.IRI("urn:bench:wp09:right"))
    chain = tuple(
        owl.Class(owl.IRI(f"urn:bench:wp09:chain:{index:04d}")) for index in range(depth + 1)
    )
    axioms: list[owl.AxiomNode] = [
        owl.SubClassOf(
            owl.ObjectIntersectionOf(owl.CanonicalSet((left, right))),
            chain[0],
        )
    ]
    axioms.extend(owl.SubClassOf(chain[index], chain[index + 1]) for index in range(depth))
    for index in range(facts):
        individual = owl.NamedIndividual(owl.IRI(f"urn:bench:wp09:i:{index:09d}"))
        axioms.append(owl.ClassAssertion(left, individual))
        axioms.append(owl.ClassAssertion(right, individual))
    logical = hashlib.sha256(b"pyhermit/wp09/indexed-join-workload/v1\0").hexdigest()
    return compile_normalized(normalize_axioms(tuple(axioms), logical_fingerprint=logical))


def _new_engine(program: ClauseProgram) -> tuple[TableauSession, HyperresolutionEngine]:
    session = TableauSession()
    source_nodes = {}
    for identifier, value in enumerate(program.symbols.domain(SymbolKind.INDIVIDUAL).values):
        named = value.display.startswith("named_individual:")
        source_nodes[identifier] = session.create_node(
            NodeKind.ROOT,
            is_owl_named_individual=named,
            source_individual_id=identifier if named else None,
        )
    data_nodes = {
        identifier: session.create_node(NodeKind.CONCRETE)
        for identifier, _value in enumerate(program.symbols.domain(SymbolKind.DATA_VALUE).values)
    }
    return session, HyperresolutionEngine(
        program,
        session,
        source_nodes=source_nodes,
        data_nodes=data_nodes,
    )


def _state_digest(session: TableauSession) -> str:
    digest = hashlib.sha256(b"pyhermit/wp09/saturated-state/v1\0")
    for row in session.extensions.active_rows():
        digest.update(row.key.predicate_id.to_bytes(4, "little"))
        digest.update(len(row.key.arguments).to_bytes(1, "little"))
        for argument in row.key.arguments:
            digest.update(argument.slot.to_bytes(4, "little"))
            digest.update(argument.generation.to_bytes(4, "little"))
        for support in row.supports:
            encoded = support.bits.to_bytes(max(1, (support.bits.bit_length() + 7) // 8), "little")
            digest.update(len(encoded).to_bytes(4, "little"))
            digest.update(encoded)
    return digest.hexdigest()


def _run(program: ClauseProgram) -> RunResult:
    session, engine = _new_engine(program)
    token = CancellationSource().token
    started = time.perf_counter()
    engine.initialize(token)
    initialized = time.perf_counter()
    generations = engine.saturate_hyperresolution(token)
    finished = time.perf_counter()
    session.check_invariants()
    return RunResult(
        _state_digest(session),
        generations,
        len(session.extensions.active_rows()),
        initialized - started,
        finished - initialized,
    )


def _samples(
    operation: Callable[[], RunResult],
    count: int,
) -> tuple[list[RunResult], RunResult]:
    operation()
    values = [operation() for _index in range(count)]
    expected = values[0]
    identity = (expected.digest, expected.generations, expected.rows)
    if any((value.digest, value.generations, value.rows) != identity for value in values[1:]):
        raise AssertionError("hyperresolution result changed between measured samples")
    return values, expected


def _percentile(values: Sequence[float], percentile: float) -> float:
    ordered = sorted(values)
    return ordered[max(0, math.ceil(percentile * len(ordered)) - 1)]


def _timings(values: Sequence[float]) -> dict[str, float]:
    return {
        "median_seconds": statistics.median(values),
        "p95_seconds": _percentile(values, 0.95),
    }


def _cancellation(program: ClauseProgram, timeout_ms: float) -> dict[str, float | int]:
    session, engine = _new_engine(program)
    engine.initialize(CancellationSource().token)
    operation_root = session.canonical_snapshot()
    token = CancellationSource(timeout=timeout_ms / 1_000).token
    started = time.perf_counter()
    try:
        engine.saturate_hyperresolution(token)
    except ReasoningAbortedError:
        elapsed = time.perf_counter() - started
    else:
        raise AssertionError("workload completed before cancellation was observed")
    if session.canonical_snapshot() != operation_root:
        raise AssertionError("cancellation failed to restore the operation root")
    return {
        "elapsed_seconds": elapsed,
        "latency_after_deadline_seconds": max(0.0, elapsed - timeout_ms / 1_000),
        "work": token.work,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--facts", type=int, default=10_000)
    parser.add_argument("--depth", type=int, default=4)
    parser.add_argument("--samples", type=int, default=3)
    parser.add_argument("--cancellation-timeout-ms", type=float, default=1.0)
    arguments = parser.parse_args()
    for name in ("facts", "depth", "samples"):
        value = getattr(arguments, name)
        if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
            parser.error(f"{name} must be a positive integer")
    if (
        not math.isfinite(arguments.cancellation_timeout_ms)
        or arguments.cancellation_timeout_ms <= 0
    ):
        parser.error("cancellation-timeout-ms must be positive and finite")

    program = _workload(arguments.facts, arguments.depth)
    measured, expected = _samples(lambda: _run(program), arguments.samples)
    initialize = [value.initialize_seconds for value in measured]
    saturation = [value.saturate_seconds for value in measured]

    tracemalloc.start()
    _run(program)
    _current, peak_bytes = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    payload = {
        "schema": "pyhermit-wp09-hyperresolution-benchmark/1",
        "environment": {
            "implementation": platform.python_implementation(),
            "machine": platform.machine(),
            "platform": platform.platform(),
            "python": platform.python_version(),
        },
        "configuration": {
            "depth": arguments.depth,
            "facts": arguments.facts,
            "samples": arguments.samples,
            "warmup_samples": 1,
        },
        "result": {
            "digest": expected.digest,
            "generations": expected.generations,
            "rows": expected.rows,
        },
        "initialization": _timings(initialize),
        "saturation": {
            **_timings(saturation),
            "saturated_rows_per_second": expected.rows / statistics.median(saturation),
        },
        "tracemalloc_peak_bytes": peak_bytes,
        "cancellation": _cancellation(program, arguments.cancellation_timeout_ms),
    }
    print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
