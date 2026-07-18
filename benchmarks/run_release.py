#!/usr/bin/env python3
"""Run the generated WP17 phase probe and emit hash-bound JSON evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import statistics
import sys
import time
import tracemalloc
from collections.abc import Sequence
from pathlib import Path

from pyowl_core import (
    BackendPreference,
    Class,
    ImportPolicy,
    LoadOptions,
    NamedIndividual,
    load_snapshot,
)

from pyhermit import BackendName, Hierarchy, Reasoner, ReasonerConfig

WORKLOADS = {
    "small": (8, 8),
    "medium": (200, 2_000),
    "large": (2_000, 20_000),
}
SEED = 1729
PHASES = (
    "load_seconds",
    "compile_seconds",
    "consistency_seconds",
    "classification_seconds",
    "realization_seconds",
)


def generated_taxonomy(classes: int, individuals: int) -> bytes:
    if classes < 1 or individuals < 0:
        raise ValueError("classes must be positive and individuals nonnegative")
    body = [f"Declaration(Class(:C{index}))" for index in range(classes)]
    body.extend(f"SubClassOf(:C{index} :C{index + 1})" for index in range(classes - 1))
    for index in range(individuals):
        body.append(f"Declaration(NamedIndividual(:I{index}))")
        body.append(f"ClassAssertion(:C0 :I{index})")
    return (
        "Prefix(:=<urn:pyhermit:benchmark#>) "
        "Ontology(<urn:pyhermit:benchmark:generated-taxonomy> " + " ".join(body) + ")"
    ).encode()


def _result_digest(
    consistent: bool,
    hierarchy: Hierarchy[Class],
    realized: frozenset[frozenset[Class]],
) -> str:
    digest = hashlib.sha256(b"pyhermit:release-benchmark-result:v1\x00")
    digest.update(bytes((int(consistent),)))
    for node in hierarchy.nodes:
        encoded = sorted(item.canonical_bytes() for item in node)
        digest.update(len(encoded).to_bytes(8, "big"))
        for item in encoded:
            digest.update(len(item).to_bytes(8, "big"))
            digest.update(item)
    for child, parent in sorted(hierarchy.edges):
        digest.update(child.to_bytes(8, "big"))
        digest.update(parent.to_bytes(8, "big"))
    for group in sorted(
        tuple(sorted(item.canonical_bytes() for item in group)) for group in realized
    ):
        for item in group:
            digest.update(len(item).to_bytes(8, "big"))
            digest.update(item)
    return digest.hexdigest()


def _peak_rss_bytes() -> int | None:
    try:
        import resource
    except ImportError:
        return None
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return int(value if sys.platform == "darwin" else value * 1024)


def run_benchmark(*, size: str, backend: BackendName, samples: int) -> dict[str, object]:
    if size not in WORKLOADS:
        raise ValueError(f"unknown workload size: {size}")
    if backend is BackendName.AUTO:
        raise ValueError("release evidence requires an explicitly forced backend")
    if isinstance(samples, bool) or not isinstance(samples, int) or samples < 1:
        raise ValueError("samples must be a positive integer")
    classes, individuals = WORKLOADS[size]
    source = generated_taxonomy(classes, individuals)
    input_sha256 = hashlib.sha256(source).hexdigest()
    options = LoadOptions(imports=ImportPolicy.IGNORE, backend=BackendPreference.PYTHON)
    config = ReasonerConfig(backend=backend, deterministic=True)
    timings: list[dict[str, float]] = []
    result_sha256: str | None = None
    selected_backend = None

    tracemalloc.start()
    try:
        for _index in range(samples):
            started = time.perf_counter()
            snapshot = load_snapshot(source, options=options)
            loaded = time.perf_counter()
            reasoner = Reasoner(snapshot, config=config)
            compiled = time.perf_counter()
            try:
                consistent = reasoner.is_consistent()
                checked = time.perf_counter()
                hierarchy = reasoner.class_hierarchy()
                classified = time.perf_counter()
                first = next(
                    item for item in snapshot.signature() if isinstance(item, NamedIndividual)
                )
                realized = reasoner.types(first)
                finished = time.perf_counter()
                candidate = _result_digest(consistent, hierarchy, realized)
                if result_sha256 is not None and candidate != result_sha256:
                    raise AssertionError("benchmark result changed between samples")
                result_sha256 = candidate
                if selected_backend is not None and reasoner.backend != selected_backend:
                    raise AssertionError("backend selection changed between samples")
                selected_backend = reasoner.backend
                if reasoner.ontology is not snapshot:
                    raise AssertionError("reasoner copied or replaced the shared snapshot")
            finally:
                reasoner.dispose()
            timings.append(
                {
                    "load_seconds": loaded - started,
                    "compile_seconds": compiled - loaded,
                    "consistency_seconds": checked - compiled,
                    "classification_seconds": classified - checked,
                    "realization_seconds": finished - classified,
                }
            )
        _current, peak_python_bytes = tracemalloc.get_traced_memory()
    finally:
        tracemalloc.stop()

    assert result_sha256 is not None and selected_backend is not None
    medians = {phase: statistics.median(sample[phase] for sample in timings) for phase in PHASES}
    return {
        "schema": "pyhermit.release-benchmark/1",
        "status": "informational-local",
        "environment": {
            "python": platform.python_version(),
            "implementation": platform.python_implementation(),
            "platform": platform.platform(),
            "machine": platform.machine(),
            "processor": platform.processor(),
        },
        "workload": {
            "family": "generated-taxonomy",
            "size": size,
            "classes": classes,
            "individuals": individuals,
            "seed": SEED,
        },
        "backend": {
            "requested": backend.value,
            "selected": selected_backend.name,
            "accelerated": selected_backend.accelerated,
            "implementation_version": selected_backend.implementation_version,
        },
        "input_sha256": input_sha256,
        "result_sha256": result_sha256,
        "samples": timings,
        "medians": medians,
        "peak_python_bytes": peak_python_bytes,
        "peak_rss_bytes": _peak_rss_bytes(),
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--size", choices=tuple(WORKLOADS), default="small")
    parser.add_argument(
        "--backend",
        choices=(BackendName.PYTHON.value, BackendName.NATIVE.value, BackendName.VERIFY.value),
        default=BackendName.PYTHON.value,
    )
    parser.add_argument("--samples", type=int, default=3)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    result = run_benchmark(
        size=args.size,
        backend=BackendName(args.backend),
        samples=args.samples,
    )
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(rendered, end="")
    else:
        args.output.write_text(rendered, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
