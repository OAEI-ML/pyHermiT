"""Rebuild the complete pinned ``src/test`` inventory without copying upstream files."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from collections import Counter
from pathlib import Path
from typing import Any

from tools.reference._util import sha256_file, write_json

REFERENCE_COMMIT = "37ec30aced32ac81ebecc5e33fad255ddefcb4c3"
REFERENCE_TREE = "576db18fd8152be24d577b24c99e2af0d31ceef8"
METHOD_RE = re.compile(r"^\s*public\s+void\s+(test[A-Za-z0-9_]*)\s*\(", re.MULTILINE)


def _method_fate(path: str) -> str:
    if path.endswith("/reasoner/RulesTest.java"):
        return "excluded-extra-rules"
    if path.endswith("/reasoner/DatalogEngineTest.java"):
        return "excluded-extra-datalog"
    if path.endswith("/graph/GraphTest.java"):
        return "excluded-description-graph"
    if "/owl_wg_tests/" in path:
        return "excluded-upstream-java-harness"
    if path.endswith("/reasoner/OWLLinkTest.java"):
        return "retained-semantic-api-core"
    return "retained-hermit-behavior"


def _file_fate(path: str, methods: list[str]) -> tuple[str, str]:
    if methods:
        fate = _method_fate(path)
        return fate, "excluded" if fate.startswith("excluded-") else "in-scope"
    if path.startswith("src/test/testreports/"):
        return "historical-observation-fetch-only", "observation"
    if "/owl_wg_tests/" in path:
        if path.endswith(".java"):
            return "excluded-upstream-java-harness-support", "excluded"
        return "w3c-corpus-fetch-only", "in-scope"
    if "/graph/" in path:
        return "excluded-description-graph-support", "excluded"
    if "/OWLLink/" in path:
        return "owllink-semantic-core-fetch-only", "in-scope"
    if path.endswith(".java"):
        return "retained-test-support-source", "in-scope"
    return "hermit-regression-resource-fetch-only", "in-scope"


def build_inventory(reference_root: Path) -> dict[str, Any]:
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=reference_root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    tree = subprocess.run(
        ["git", "rev-parse", "HEAD^{tree}"],
        cwd=reference_root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    if commit != REFERENCE_COMMIT or tree != REFERENCE_TREE:
        raise ValueError(f"wrong reference identity: commit={commit}, tree={tree}")
    paths = subprocess.run(
        ["git", "ls-files", "src/test"],
        cwd=reference_root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()
    entries: list[dict[str, Any]] = []
    methods: list[dict[str, str]] = []
    for relative in sorted(paths):
        path = reference_root / relative
        file_methods: list[str] = []
        if path.suffix == ".java":
            file_methods = METHOD_RE.findall(path.read_text(encoding="utf-8", errors="replace"))
        fate, scope = _file_fate(relative, file_methods)
        for method in file_methods:
            methods.append(
                {
                    "id": f"{relative}::{method}",
                    "path": relative,
                    "method": method,
                    "fate": fate,
                }
            )
        entries.append(
            {
                "path": relative,
                "bytes": path.stat().st_size,
                "sha256": sha256_file(path),
                "methods": file_methods,
                "fate": fate,
                "scope": scope,
            }
        )
    if len(entries) != 186 or len(methods) != 598:
        raise ValueError(f"pinned counts changed: files={len(entries)}, methods={len(methods)}")
    extensions = Counter(Path(entry["path"]).suffix.removeprefix(".") for entry in entries)
    fates = Counter(method["fate"] for method in methods)
    owllink = [method for method in methods if method["path"].endswith("OWLLinkTest.java")]
    return {
        "schema_version": "1.0",
        "reference": {
            "repository": "https://github.com/phillord/hermit-reasoner.git",
            "commit": commit,
            "tree": tree,
        },
        "counts": {
            "files": len(entries),
            "static_test_methods": len(methods),
            "extensions": dict(sorted(extensions.items())),
            "method_fates": dict(sorted(fates.items())),
        },
        "scope_decisions": {
            "owllink_test": {
                "decision": "retain semantic and OWLAPI lifecycle cases",
                "method_ids": [method["id"] for method in owllink],
                "transport_exclusion": (
                    "OWLlink HTTP/XML protocol transport is outside pyHermiT scope; the pinned "
                    "OWLLinkTest methods do not implement that transport and are retained as "
                    "core cases."
                ),
            },
            "extras": {
                "rules": "inventoried; excluded from OWL 2 DL parity",
                "datalog": "inventoried; excluded from OWL 2 DL parity",
                "description_graph": "inventoried; excluded from OWL 2 DL parity",
                "upstream_w3c_java_harness": (
                    "inventoried; never copied or executed by the independent Python executor"
                ),
            },
        },
        # Method ids are represented once, nested under their owning file; callers can flatten
        # ``files[*].methods`` without a 598-row duplication.
        "files": entries,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reference-root", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    inventory = build_inventory(args.reference_root)
    if args.output:
        write_json(args.output, inventory)
    else:
        print(json.dumps(inventory, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
