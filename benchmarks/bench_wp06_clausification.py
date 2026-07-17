#!/usr/bin/env python3
"""Reproducible scale smoke benchmark for WP06 clausification.

Normalization is performed once outside the measured region.  Each measured sample
compiles the same immutable normalized ontology, validates the resulting IR during
construction, and hashes its canonical bytes so performance cannot be reported for
an empty or nondeterministic result.  The separate n-ary disjoint case guards the
linear shared-guard encoding and the cancellation case exercises record-boundary
polling under sustained compilation work.
"""

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
from typing import TypeAlias

import pyowl_core.model as owl

from pyhermit.clauses import ClauseProgram, compile_normalized
from pyhermit.exceptions import ReasonerInterruptedError
from pyhermit.normalize import NormalizedOntology, normalize_axioms

OperationResult: TypeAlias = tuple[str, tuple[int, int, int, int]]


def _class(index: int) -> owl.Class:
    return owl.Class(owl.IRI(f"urn:bench:wp06:class:{index:08d}"))


def _workload(count: int) -> NormalizedOntology:
    role = owl.ObjectProperty(owl.IRI("urn:bench:wp06:role"))
    axioms: list[owl.AxiomNode] = []
    for index in range(count):
        source = _class(index)
        target = _class(index + 1)
        if index % 4 == 0:
            superclass: owl.ClassExpression = target
        elif index % 4 == 1:
            superclass = owl.ObjectAllValuesFrom(role, target)
        elif index % 4 == 2:
            superclass = owl.ObjectSomeValuesFrom(role, target)
        else:
            superclass = owl.ObjectMaxCardinality(1, role, target)
        axioms.append(owl.SubClassOf(source, superclass))
    logical = hashlib.sha256(b"pyhermit/wp06/scale-source/v1\0").hexdigest()
    return normalize_axioms(tuple(axioms), logical_fingerprint=logical)


def _disjoint_workload(count: int) -> NormalizedOntology:
    axiom = owl.DisjointClasses(owl.CanonicalSet(tuple(_class(index) for index in range(count))))
    logical = hashlib.sha256(b"pyhermit/wp06/disjoint-source/v1\0").hexdigest()
    return normalize_axioms((axiom,), logical_fingerprint=logical)


def _result(program: ClauseProgram) -> OperationResult:
    counts = (
        len(program.predicates.predicates),
        len(program.clauses),
        len(program.positive_facts) + len(program.negative_facts),
        len(program.ground_disjunctions),
    )
    return hashlib.sha256(program.canonical_bytes()).hexdigest(), counts


def _compile_once(normalized: NormalizedOntology) -> OperationResult:
    return _result(compile_normalized(normalized))


def _samples(
    operation: Callable[[], OperationResult], count: int
) -> tuple[list[float], OperationResult]:
    operation()
    elapsed: list[float] = []
    expected: OperationResult | None = None
    for _ in range(count):
        started = time.perf_counter()
        result = operation()
        elapsed.append(time.perf_counter() - started)
        if expected is None:
            expected = result
        elif result != expected:
            raise AssertionError("benchmark result changed between measured samples")
    if expected is None:
        raise AssertionError("benchmark requires at least one sample")
    return elapsed, expected


def _percentile(values: Sequence[float], percentile: float) -> float:
    ordered = sorted(values)
    index = max(0, math.ceil(percentile * len(ordered)) - 1)
    return ordered[index]


def _deadline_callback(deadline: float) -> Callable[[], bool]:
    def reached() -> bool:
        return time.perf_counter() >= deadline

    return reached


def _cancellation_samples(
    normalized: NormalizedOntology,
    count: int,
    delay_seconds: float,
) -> list[float]:
    elapsed: list[float] = []
    for _ in range(count):
        started = time.perf_counter()
        deadline = started + delay_seconds
        try:
            compile_normalized(
                normalized,
                cancelled=_deadline_callback(deadline),
            )
        except ReasonerInterruptedError:
            elapsed.append(time.perf_counter() - started)
        else:
            raise AssertionError("clausification completed before observing cancellation")
    return elapsed


def _timing_payload(times: Sequence[float]) -> dict[str, float]:
    return {
        "median_seconds": statistics.median(times),
        "p95_seconds": _percentile(times, 0.95),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--axioms", type=int, default=10_000)
    parser.add_argument("--disjoint-classes", type=int, default=10_000)
    parser.add_argument("--samples", type=int, default=5)
    parser.add_argument("--cancellation-axioms", type=int, default=20_000)
    parser.add_argument("--cancellation-delay-ms", type=float, default=5.0)
    arguments = parser.parse_args()
    for name in ("axioms", "disjoint_classes", "samples", "cancellation_axioms"):
        value = getattr(arguments, name)
        if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
            parser.error(f"{name.replace('_', '-')} must be a positive integer")
    if not math.isfinite(arguments.cancellation_delay_ms) or arguments.cancellation_delay_ms <= 0:
        parser.error("cancellation-delay-ms must be a positive finite number")

    normalized = _workload(arguments.axioms)
    disjoint = _disjoint_workload(arguments.disjoint_classes)
    cancellation = _workload(arguments.cancellation_axioms)

    compile_times, (compile_digest, compile_counts) = _samples(
        lambda: _compile_once(normalized), arguments.samples
    )
    disjoint_times, (disjoint_digest, disjoint_counts) = _samples(
        lambda: _compile_once(disjoint), arguments.samples
    )

    tracemalloc.start()
    _compile_once(normalized)
    _current_bytes, peak_bytes = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    cancellation_times = _cancellation_samples(
        cancellation,
        arguments.samples,
        arguments.cancellation_delay_ms / 1_000.0,
    )
    cancellation_latency = tuple(
        max(0.0, value - arguments.cancellation_delay_ms / 1_000.0) for value in cancellation_times
    )

    result = {
        "schema": "pyhermit-wp06-clausification-benchmark/1",
        "environment": {
            "implementation": platform.python_implementation(),
            "machine": platform.machine(),
            "platform": platform.platform(),
            "python": platform.python_version(),
        },
        "configuration": {
            "axioms": arguments.axioms,
            "cancellation_axioms": arguments.cancellation_axioms,
            "cancellation_delay_ms": arguments.cancellation_delay_ms,
            "disjoint_classes": arguments.disjoint_classes,
            "samples": arguments.samples,
            "warmup_samples": 1,
        },
        "compile": {
            **_timing_payload(compile_times),
            "throughput_axioms_per_second": arguments.axioms / statistics.median(compile_times),
            "tracemalloc_peak_bytes": peak_bytes,
            "digest": compile_digest,
            "predicates": compile_counts[0],
            "clauses": compile_counts[1],
            "facts": compile_counts[2],
            "ground_disjunctions": compile_counts[3],
        },
        "linear_disjoint": {
            **_timing_payload(disjoint_times),
            "digest": disjoint_digest,
            "predicates": disjoint_counts[0],
            "clauses": disjoint_counts[1],
            "facts": disjoint_counts[2],
            "ground_disjunctions": disjoint_counts[3],
            "clause_to_class_ratio": disjoint_counts[1] / arguments.disjoint_classes,
        },
        "cancellation": {
            "observed_samples": len(cancellation_times),
            "median_total_seconds": statistics.median(cancellation_times),
            "p95_total_seconds": _percentile(cancellation_times, 0.95),
            "p95_latency_after_deadline_seconds": _percentile(cancellation_latency, 0.95),
        },
    }
    print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
