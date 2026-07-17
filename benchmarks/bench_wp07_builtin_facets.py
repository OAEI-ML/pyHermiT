#!/usr/bin/env python3
"""Reproducible smoke benchmark for WP07 built-in values and facets."""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import math
import platform
import statistics
import time
import tracemalloc
from collections.abc import Callable, Sequence
from typing import Any, TypeAlias

from pyowl_core.model import IRI, Datatype, Literal

from pyhermit.datatypes import (
    RDF_LANG_RANGE,
    RDF_PLAIN_LITERAL,
    RDF_XML_LITERAL,
    XSD_ANY_URI,
    XSD_BASE64_BINARY,
    XSD_DATE_TIME,
    XSD_DOUBLE,
    XSD_FLOAT,
    XSD_HEX_BINARY,
    XSD_INTEGER,
    XSD_LENGTH,
    XSD_MAX_INCLUSIVE,
    XSD_MAX_LENGTH,
    XSD_MIN_INCLUSIVE,
    XSD_MIN_LENGTH,
    XSD_NCNAME,
    XSD_PATTERN,
    XSD_STRING,
    XSD_TOKEN,
    CompiledLiteral,
    FacetRestriction,
    XSDRegex,
    compile_literal,
    restrict_datatype,
)

OperationResult: TypeAlias = tuple[str, int]


def _literal(lexical: str, datatype_iri: str, language: str | None = None) -> Literal:
    return Literal(lexical, Datatype(IRI(datatype_iri)), language)


def _workload(count: int) -> tuple[Literal, ...]:
    values: list[Literal] = []
    for index in range(count):
        variant = index % 10
        if variant == 0:
            values.append(_literal(f"{index % 1000}.125e-2", XSD_FLOAT))
        elif variant == 1:
            values.append(_literal(f"-{index % 1000}.5e12", XSD_DOUBLE))
        elif variant == 2:
            values.append(_literal(f"  token\t{index % 100}  ", XSD_TOKEN))
        elif variant == 3:
            values.append(_literal(f"label {index % 100}", RDF_PLAIN_LITERAL, "en-GB"))
        elif variant == 4:
            values.append(_literal(format(index % 65536, "04x"), XSD_HEX_BINARY))
        elif variant == 5:
            payload = (index % 65536).to_bytes(2, "big")
            values.append(_literal(base64.b64encode(payload).decode("ascii"), XSD_BASE64_BINARY))
        elif variant == 6:
            values.append(_literal(f"../ontology/{index % 100}#C", XSD_ANY_URI))
        elif variant == 7:
            values.append(_literal(f"2000-01-{index % 28 + 1:02d}T12:34:56.125Z", XSD_DATE_TIME))
        elif variant == 8:
            values.append(_literal(f'<v n="{index % 100}">text</v>', RDF_XML_LITERAL))
        else:
            values.append(_literal(f"Name_{index % 100}", XSD_NCNAME))
    return tuple(values)


def _compile_once(values: Sequence[Literal]) -> OperationResult:
    digest = hashlib.sha256(b"pyhermit/wp07/builtin-compile/v1\0")
    for source in values:
        digest.update(
            json.dumps(
                compile_literal(source).as_tagged(),
                ensure_ascii=False,
                separators=(",", ":"),
                sort_keys=True,
            ).encode("utf-8")
        )
        digest.update(b"\n")
    return digest.hexdigest(), len(values)


def _compiled(lexical: str, datatype_iri: str) -> CompiledLiteral:
    return compile_literal(_literal(lexical, datatype_iri))


def _ranges() -> tuple[Any, ...]:
    return (
        restrict_datatype(
            XSD_FLOAT,
            (
                FacetRestriction(XSD_MIN_INCLUSIVE, _compiled("-100", XSD_FLOAT)),
                FacetRestriction(XSD_MAX_INCLUSIVE, _compiled("100", XSD_FLOAT)),
            ),
        ),
        restrict_datatype(
            XSD_STRING,
            (
                FacetRestriction(XSD_MIN_LENGTH, _compiled("2", XSD_INTEGER)),
                FacetRestriction(XSD_MAX_LENGTH, _compiled("12", XSD_INTEGER)),
                FacetRestriction(XSD_PATTERN, _compiled("[a-z]+", XSD_STRING)),
            ),
        ),
        restrict_datatype(
            RDF_PLAIN_LITERAL,
            (FacetRestriction(RDF_LANG_RANGE, _compiled("en", XSD_STRING)),),
        ),
        restrict_datatype(
            XSD_HEX_BINARY,
            (FacetRestriction(XSD_LENGTH, _compiled("2", XSD_INTEGER)),),
        ),
        restrict_datatype(
            XSD_ANY_URI,
            (FacetRestriction(XSD_PATTERN, _compiled(".*#C", XSD_STRING)),),
        ),
        restrict_datatype(
            XSD_DATE_TIME,
            (
                FacetRestriction(
                    XSD_MIN_INCLUSIVE,
                    _compiled("2000-01-01T00:00:00Z", XSD_DATE_TIME),
                ),
                FacetRestriction(
                    XSD_MAX_INCLUSIVE,
                    _compiled("2000-12-31T23:59:59Z", XSD_DATE_TIME),
                ),
            ),
        ),
    )


def _range_candidates() -> tuple[tuple[CompiledLiteral, CompiledLiteral], ...]:
    return (
        (_compiled("1", XSD_FLOAT), _compiled("1000", XSD_FLOAT)),
        (_compiled("letters", XSD_STRING), _compiled("A", XSD_STRING)),
        (
            compile_literal(_literal("label", RDF_PLAIN_LITERAL, "en-GB")),
            compile_literal(_literal("label", RDF_PLAIN_LITERAL, "fr")),
        ),
        (_compiled("00ff", XSD_HEX_BINARY), _compiled("ff", XSD_HEX_BINARY)),
        (_compiled("ontology#C", XSD_ANY_URI), _compiled("ontology", XSD_ANY_URI)),
        (
            _compiled("2000-06-01T00:00:00Z", XSD_DATE_TIME),
            _compiled("2001-01-01T00:00:00Z", XSD_DATE_TIME),
        ),
    )


def _range_once(
    ranges: Sequence[Any],
    candidates: Sequence[tuple[CompiledLiteral, CompiledLiteral]],
    operations: int,
) -> OperationResult:
    digest = hashlib.sha256(b"pyhermit/wp07/builtin-ranges/v1\0")
    hits = 0
    for index in range(operations):
        range_index = index % len(ranges)
        range_ = ranges[range_index]
        value = candidates[range_index][(index // len(ranges)) & 1]
        if range_.contains(value):
            hits += 1
    regex = XSDRegex.compile("[a-z-[aeiou]]+").intersection(XSDRegex.compile(".{2,8}"))
    if regex.intersection(regex.complement()).is_empty_exact():
        digest.update(b"regex-empty\n")
    digest.update(str(hits).encode("ascii"))
    return digest.hexdigest(), hits


def _samples(operation: Callable[[], OperationResult], count: int) -> tuple[list[float], str, int]:
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
    index = max(0, math.ceil(percentile * len(ordered)) - 1)
    return ordered[index]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--literals", type=int, default=10_000)
    parser.add_argument("--range-operations", type=int, default=20_000)
    parser.add_argument("--samples", type=int, default=10)
    arguments = parser.parse_args()
    for name, value in vars(arguments).items():
        if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
            parser.error(f"{name} must be a positive integer")

    literals = _workload(arguments.literals)
    ranges = _ranges()
    candidates = _range_candidates()
    compile_times, compile_digest, compiled_count = _samples(
        lambda: _compile_once(literals), arguments.samples
    )
    range_times, range_digest, range_hits = _samples(
        lambda: _range_once(ranges, candidates, arguments.range_operations),
        arguments.samples,
    )

    tracemalloc.start()
    _compile_once(literals)
    _current_bytes, peak_bytes = tracemalloc.get_traced_memory()
    tracemalloc.stop()

    result = {
        "schema": "pyhermit-wp07-builtins-facets-benchmark/1",
        "environment": {
            "implementation": platform.python_implementation(),
            "machine": platform.machine(),
            "platform": platform.platform(),
            "python": platform.python_version(),
        },
        "configuration": {
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
        "scope": "pure-Python built-in datatype/facet component; no tableau/native/Java",
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    if statistics.median(compile_times) > 5.0:
        raise SystemExit("built-in compile smoke budget exceeded 5 seconds")
    if statistics.median(range_times) > 5.0:
        raise SystemExit("facet/range smoke budget exceeded 5 seconds")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
