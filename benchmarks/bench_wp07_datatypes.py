#!/usr/bin/env python3
"""Reproducible smoke benchmark for the WP07 numeric/Boolean foundation.

This is a component benchmark, not a tableau or Java comparison.  It uses ten
measured samples by default, validates result digests, and enforces the provisional
pure-Python CI budget plus the project-wide 250 ms cancellation-latency gate.
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
from collections.abc import Sequence

from pyowl_core.model import IRI, Datatype, Literal

from pyhermit.datatypes import (
    OWL_RATIONAL,
    XSD_BOOLEAN,
    XSD_DECIMAL,
    XSD_INTEGER,
    DatatypeLimits,
    NumericComparison,
    NumericDomain,
    NumericRange,
    compile_literal,
)
from pyhermit.events import CancellationSource
from pyhermit.exceptions import ReasonerTimeoutError


def _literal(lexical: str, datatype_iri: str) -> Literal:
    return Literal(lexical, Datatype(IRI(datatype_iri)))


def _literal_workload(count: int) -> tuple[Literal, ...]:
    values: list[Literal] = []
    for index in range(count):
        variant = index % 4
        value = index // 4 - count // 8
        if variant == 0:
            values.append(_literal(f"{value:+08d}", XSD_INTEGER))
        elif variant == 1:
            values.append(_literal(f"{value}.2500", XSD_DECIMAL))
        elif variant == 2:
            values.append(_literal(f"{value * 3}/3", OWL_RATIONAL))
        else:
            values.append(_literal("true" if value % 2 else "0", XSD_BOOLEAN))
    return tuple(values)


def _compile_once(values: Sequence[Literal]) -> tuple[str, int]:
    digest = hashlib.sha256(b"pyhermit/wp07/compile-benchmark/v1\0")
    for source in values:
        compiled = compile_literal(source)
        digest.update(
            json.dumps(
                compiled.as_tagged(),
                ensure_ascii=False,
                separators=(",", ":"),
                sort_keys=True,
            ).encode("utf-8")
        )
        digest.update(b"\n")
    return digest.hexdigest(), len(values)


def _range_once(operations: int) -> tuple[str, int]:
    digest = hashlib.sha256(b"pyhermit/wp07/range-benchmark/v1\0")
    hits = 0
    for index in range(operations):
        lower = NumericComparison((index % 101) - 50, 10)
        upper = NumericComparison((index % 101) + 50, 10)
        dense = NumericRange.between(
            NumericDomain.DECIMAL,
            lower=lower,
            lower_inclusive=bool(index & 1),
            upper=upper,
            upper_inclusive=bool(index & 2),
        )
        integers = NumericRange.between(
            NumericDomain.INTEGER,
            lower=NumericComparison(-3),
            lower_inclusive=True,
            upper=NumericComparison(3),
            upper_inclusive=True,
        )
        result = dense.intersection(integers.complement())
        if result.contains(NumericComparison(index % 11 - 5)):
            hits += 1
    digest.update(str(hits).encode("ascii"))
    return digest.hexdigest(), hits


def _samples(operation, count: int) -> tuple[list[float], str, int]:
    operation()
    times: list[float] = []
    expected: tuple[str, int] | None = None
    for _ in range(count):
        started = time.perf_counter()
        result = operation()
        times.append(time.perf_counter() - started)
        if expected is None:
            expected = result
        elif result != expected:
            raise AssertionError("benchmark result digest changed between samples")
    if expected is None:
        raise AssertionError("benchmark requires at least one sample")
    return times, expected[0], expected[1]


def _percentile(values: Sequence[float], percentile: float) -> float:
    ordered = sorted(values)
    index = max(0, math.ceil(percentile * len(ordered)) - 1)
    return ordered[index]


def _cancellation_samples(count: int, digits: int) -> list[float]:
    lexical = "9" * digits
    source = _literal(lexical, XSD_INTEGER)
    limits = DatatypeLimits(
        max_lexical_characters=digits,
        max_numeric_digits=digits,
        cancellation_poll_stride=8,
    )
    values: list[float] = []
    for _ in range(count):
        cancellation = CancellationSource(timeout=0.005)
        started = time.perf_counter()
        try:
            compile_literal(source, limits=limits, cancellation=cancellation.token)
        except ReasonerTimeoutError:
            values.append(time.perf_counter() - started)
        else:
            raise AssertionError("large numeric parse completed without observing timeout")
    return values


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--literals", type=int, default=10_000)
    parser.add_argument("--range-operations", type=int, default=10_000)
    parser.add_argument("--samples", type=int, default=10)
    parser.add_argument("--large-digits", type=int, default=10_000)
    parser.add_argument("--cancellation-digits", type=int, default=100_000)
    arguments = parser.parse_args()
    for name, value in vars(arguments).items():
        if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
            parser.error(f"{name} must be a positive integer")

    literals = _literal_workload(arguments.literals)
    compile_times, compile_digest, compiled_count = _samples(
        lambda: _compile_once(literals), arguments.samples
    )
    range_times, range_digest, range_hits = _samples(
        lambda: _range_once(arguments.range_operations), arguments.samples
    )
    large = _literal("9" * arguments.large_digits, XSD_INTEGER)
    large_limits = DatatypeLimits(
        max_lexical_characters=arguments.large_digits,
        max_numeric_digits=arguments.large_digits,
    )
    large_times, large_digest, _ = _samples(
        lambda: (
            hashlib.sha256(
                json.dumps(
                    compile_literal(large, limits=large_limits).as_tagged(),
                    separators=(",", ":"),
                    sort_keys=True,
                ).encode("utf-8")
            ).hexdigest(),
            arguments.large_digits,
        ),
        arguments.samples,
    )
    cancellation_times = _cancellation_samples(arguments.samples, arguments.cancellation_digits)

    tracemalloc.start()
    _compile_once(literals)
    _current_bytes, peak_bytes = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    result = {
        "schema": "pyhermit-wp07-foundation-benchmark/1",
        "environment": {
            "implementation": platform.python_implementation(),
            "machine": platform.machine(),
            "platform": platform.platform(),
            "python": platform.python_version(),
        },
        "configuration": {
            "cancellation_digits": arguments.cancellation_digits,
            "large_digits": arguments.large_digits,
            "literals": arguments.literals,
            "range_operations": arguments.range_operations,
            "samples": arguments.samples,
            "warmup_samples": 1,
        },
        "compile": {
            "count": compiled_count,
            "digest": compile_digest,
            "median_seconds": statistics.median(compile_times),
            "p95_seconds": _percentile(compile_times, 0.95),
            "throughput_per_second": compiled_count / statistics.median(compile_times),
            "tracemalloc_peak_bytes": peak_bytes,
        },
        "range": {
            "digest": range_digest,
            "hits": range_hits,
            "median_seconds": statistics.median(range_times),
            "p95_seconds": _percentile(range_times, 0.95),
        },
        "large_integer": {
            "digest": large_digest,
            "digits": arguments.large_digits,
            "median_seconds": statistics.median(large_times),
            "p95_seconds": _percentile(large_times, 0.95),
        },
        "cancellation": {
            "all_samples_aborted": len(cancellation_times) == arguments.samples,
            "median_seconds": statistics.median(cancellation_times),
            "p95_seconds": _percentile(cancellation_times, 0.95),
            "required_p95_seconds": 0.250,
        },
        "scope": "pure-Python datatype component; no tableau/native/Java comparison",
    }
    print(json.dumps(result, indent=2, sort_keys=True))

    if statistics.median(compile_times) > 5.0:
        raise SystemExit("compile smoke budget exceeded 5 seconds")
    if statistics.median(range_times) > 5.0:
        raise SystemExit("range smoke budget exceeded 5 seconds")
    if statistics.median(large_times) > 2.0:
        raise SystemExit("large-integer smoke budget exceeded 2 seconds")
    if _percentile(cancellation_times, 0.95) >= 0.250:
        raise SystemExit("datatype cancellation p95 exceeded 250 ms")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
