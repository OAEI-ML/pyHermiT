#!/usr/bin/env python3
"""Reproducible WP07 language/witness/constraint-solver smoke benchmark.

The workload exercises deterministic reconstruction over infinite concrete domains. It
is a pure-Python component benchmark: no tableau, native extension, Java, or network is
used.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import statistics
import time
from collections.abc import Callable, Sequence
from typing import TypeAlias

import pyowl_core.model as owl

from pyhermit.datatypes import (
    OWL_RATIONAL,
    OWL_REAL,
    XSD_STRING,
    DataDomainRange,
    DatatypeConstraintComponent,
    DatatypeConstraintSolver,
    InequalityConstraint,
    LanguageTagRange,
    RangeConstraint,
    XSDRegex,
    compile_datatype_semantic_model,
)

OperationResult: TypeAlias = tuple[str, int]


def _datatype(iri: str) -> owl.Datatype:
    return owl.Datatype(owl.IRI(iri))


def _domain(root: owl.DataRange) -> DataDomainRange:
    model = compile_datatype_semantic_model((root,))
    return DataDomainRange.from_model(model, 0)


def _complete_component(domain: DataDomainRange, width: int) -> DatatypeConstraintComponent:
    return DatatypeConstraintComponent(
        variables=tuple(range(width)),
        ranges=tuple(RangeConstraint(variable, domain) for variable in range(width)),
        inequalities=tuple(
            InequalityConstraint(left, right)
            for left in range(width)
            for right in range(left + 1, width)
        ),
    )


def _language_once(operations: int) -> OperationResult:
    language = LanguageTagRange.basic("en").intersection(
        LanguageTagRange.basic("en-x").complement()
    )
    regex = XSDRegex.compile("[ab]*")
    digest = hashlib.sha256(b"pyhermit/wp07/language-witness/v1\0")
    for _ in range(operations):
        digest.update(language.first_tag(excluding=("en", "en-a", "en-x-a")).encode())
        digest.update(b"\0")
        digest.update(regex.first_string(excluding=("", "a", "b", "aa")).encode())
        digest.update(b"\n")
    return digest.hexdigest(), operations * 2


def _solver_once(
    solver: DatatypeConstraintSolver,
    components: Sequence[DatatypeConstraintComponent],
    repetitions: int,
) -> OperationResult:
    digest = hashlib.sha256(b"pyhermit/wp07/infinite-solver/v1\0")
    assignments = 0
    for _ in range(repetitions):
        for component in components:
            result = solver.solve(component)
            if not result.satisfiable:
                raise AssertionError("infinite witness benchmark component became unsatisfiable")
            values = tuple(assignment.value for assignment in result.assignments)
            if len(set(values)) != len(values):
                raise AssertionError("inequality clique received duplicate witnesses")
            for value in values:
                digest.update(repr(value.as_tagged()).encode("ascii"))
                digest.update(b"\n")
            assignments += len(values)
    return digest.hexdigest(), assignments


def _samples(
    operation: Callable[[], OperationResult],
    count: int,
) -> tuple[list[float], str, int]:
    operation()
    times: list[float] = []
    expected: OperationResult | None = None
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
    return ordered[max(0, math.ceil(percentile * len(ordered)) - 1)]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--language-operations", type=int, default=1_000)
    parser.add_argument("--solver-repetitions", type=int, default=20)
    parser.add_argument("--samples", type=int, default=10)
    parser.add_argument("--width", type=int, default=12)
    arguments = parser.parse_args()
    for name, value in vars(arguments).items():
        if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
            parser.error(f"{name.replace('_', '-')} must be a positive integer")

    string_domain = _domain(_datatype(XSD_STRING))
    irrational_domain = _domain(
        owl.DataIntersectionOf(
            owl.CanonicalSet(
                (
                    _datatype(OWL_REAL),
                    owl.DataComplementOf(_datatype(OWL_RATIONAL)),
                )
            )
        )
    )
    components = (
        _complete_component(string_domain, arguments.width),
        _complete_component(irrational_domain, arguments.width),
    )
    solver = DatatypeConstraintSolver()
    language_times, language_digest, language_witnesses = _samples(
        lambda: _language_once(arguments.language_operations), arguments.samples
    )
    solver_times, solver_digest, assignments = _samples(
        lambda: _solver_once(solver, components, arguments.solver_repetitions),
        arguments.samples,
    )

    result = {
        "schema": "pyhermit-wp07-constraints-benchmark/1",
        "environment": {
            "implementation": platform.python_implementation(),
            "machine": platform.machine(),
            "platform": platform.platform(),
            "python": platform.python_version(),
        },
        "configuration": {
            "language_operations": arguments.language_operations,
            "samples": arguments.samples,
            "solver_repetitions": arguments.solver_repetitions,
            "warmup_samples": 1,
            "width": arguments.width,
        },
        "language_witnesses": {
            "count": language_witnesses,
            "digest": language_digest,
            "median_seconds": statistics.median(language_times),
            "p95_seconds": _percentile(language_times, 0.95),
        },
        "solver": {
            "assignments": assignments,
            "digest": solver_digest,
            "median_seconds": statistics.median(solver_times),
            "p95_seconds": _percentile(solver_times, 0.95),
        },
        "scope": "pure-Python datatype component; no tableau/native/Java/network",
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    if statistics.median(language_times) > 5.0:
        raise SystemExit("language witness smoke budget exceeded 5 seconds")
    if statistics.median(solver_times) > 5.0:
        raise SystemExit("constraint solver smoke budget exceeded 5 seconds")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
