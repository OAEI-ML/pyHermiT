"""Build the pinned HermiT datatype-method coverage inventory.

The input is project-generated metadata from the fetch-only reference tree.  No Java
source or ontology body is read or copied by this tool.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any

from tools.reference._util import write_json

REFERENCE_COMMIT = "37ec30aced32ac81ebecc5e33fad255ddefcb4c3"

_LANES = {
    "AnyURITest.java": (
        "datatype-library-WP07",
        "mapped-current-workpackage",
        "tests/unit/datatypes/test_nonnumeric_semantics.py",
    ),
    "BinaryDataTest.java": (
        "datatype-library-WP07",
        "mapped-current-workpackage",
        "tests/unit/datatypes/test_nonnumeric_semantics.py",
    ),
    "DateTimeTest.java": (
        "datatype-library-WP07",
        "mapped-current-workpackage",
        "tests/unit/datatypes/test_nonnumeric_semantics.py",
    ),
    "FloatDoubleTest.java": (
        "datatype-library-WP07",
        "mapped-current-workpackage",
        "tests/unit/datatypes/test_ieee_semantics.py",
    ),
    "NumericsTest.java": (
        "datatype-library-WP07",
        "mapped-current-workpackage",
        "tests/unit/datatypes/test_ranges.py",
    ),
    "RDFPlainLiteralTest.java": (
        "datatype-library-WP07",
        "mapped-current-workpackage",
        "tests/unit/datatypes/test_nonnumeric_semantics.py",
    ),
    "XMLLiteralTest.java": (
        "datatype-library-WP07",
        "mapped-current-workpackage",
        "tests/unit/datatypes/test_nonnumeric_semantics.py",
    ),
    "DatatypesTest.java": (
        "ontology-tableau-WP12",
        "deferred-to-tableau-integration",
        "specs/workpackages/WP12-python-tableau.md",
    ),
    "ClausificationDatatypesTest.java": (
        "clausification-WP06",
        "mapped-completed-workpackage",
        "tools/clausification/WP06-EVIDENCE.md",
    ),
}


def build_inventory(upstream_inventory_path: Path) -> dict[str, Any]:
    """Select and classify every pinned datatype-related upstream test method."""

    upstream = json.loads(upstream_inventory_path.read_text())
    reference = upstream.get("reference")
    if not isinstance(reference, dict) or reference.get("commit") != REFERENCE_COMMIT:
        raise ValueError("upstream inventory does not describe the pinned HermiT commit")
    upstream_files = upstream.get("files")
    if not isinstance(upstream_files, list):
        raise ValueError("upstream inventory files must be a list")

    selected: list[dict[str, Any]] = []
    lane_counts: Counter[str] = Counter()
    method_ids: set[str] = set()
    for suffix, (lane, status, evidence) in _LANES.items():
        matches = [
            entry
            for entry in upstream_files
            if isinstance(entry, dict) and Path(str(entry.get("path", ""))).name == suffix
        ]
        if len(matches) != 1:
            raise ValueError(f"expected one pinned inventory entry for {suffix}")
        source = matches[0]
        path = source.get("path")
        digest = source.get("sha256")
        methods = source.get("methods")
        if (
            not isinstance(path, str)
            or not isinstance(digest, str)
            or not isinstance(methods, list)
            or not all(isinstance(method, str) for method in methods)
        ):
            raise ValueError(f"malformed pinned inventory entry for {suffix}")
        for method in methods:
            method_id = f"{path}::{method}"
            if method_id in method_ids:
                raise ValueError(f"duplicate datatype method id {method_id}")
            method_ids.add(method_id)
            lane_counts[lane] += 1
        selected.append(
            {
                "coverage_evidence": evidence,
                "coverage_lane": lane,
                "coverage_status": status,
                "methods": methods,
                "path": path,
                "sha256": digest,
            }
        )

    selected.sort(key=lambda item: item["path"])
    if len(method_ids) != 256:
        raise ValueError(f"pinned datatype method count changed: {len(method_ids)}")
    return {
        "counts": {
            "files": len(selected),
            "methods": len(method_ids),
            "methods_by_lane": dict(sorted(lane_counts.items())),
        },
        "coverage_policy": {
            "mapped-current-workpackage": (
                "Mapped to the Python datatype family matrix; exact semantic projections are "
                "also executed where listed in ontology-component-cases-v1.json."
            ),
            "mapped-completed-workpackage": (
                "Owned by an already evidenced workpackage; retained here so no upstream "
                "datatype method disappears between inventories."
            ),
            "deferred-to-tableau-integration": (
                "Requires ontology rules or tableau propagation. It is explicitly not claimed "
                "as completed by component-level datatype tests."
            ),
        },
        "files": selected,
        "reference": {
            "commit": reference["commit"],
            "repository": reference["repository"],
            "tree": reference["tree"],
            "upstream_inventory": "tests/data/reference/upstream-test-inventory.json",
        },
        "schema_version": "1.0",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--upstream-inventory",
        type=Path,
        default=Path("tests/data/reference/upstream-test-inventory.json"),
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("tests/data/datatypes/hermit-datatype-inventory-v1.json"),
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    inventory = build_inventory(args.upstream_inventory)
    if args.check:
        if json.loads(args.output.read_text()) != inventory:
            raise SystemExit(f"stale generated inventory: {args.output}")
    else:
        write_json(args.output, inventory)


if __name__ == "__main__":
    main()
