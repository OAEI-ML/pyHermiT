"""Semantic-diff oracle regeneration; committed goldens are never silently overwritten."""

from __future__ import annotations

import argparse
import difflib
import json
from pathlib import Path
from typing import Any

from tools.reference.canonicalize import semantic_projection


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def projected_json(records: list[dict[str, Any]]) -> str:
    projected = [semantic_projection(record) for record in records]
    projected.sort(key=lambda record: record.get("request_id", ""))
    return json.dumps(projected, ensure_ascii=False, indent=2, sort_keys=True) + "\n"


def semantic_diff(committed: Path, candidate: Path) -> str:
    before = projected_json(load_jsonl(committed)).splitlines(keepends=True)
    after = projected_json(load_jsonl(candidate)).splitlines(keepends=True)
    return "".join(
        difflib.unified_diff(before, after, fromfile=str(committed), tofile=str(candidate))
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("committed", type=Path)
    parser.add_argument("candidate", type=Path)
    args = parser.parse_args()
    diff = semantic_diff(args.committed, args.candidate)
    if diff:
        print(diff, end="")
        raise SystemExit(1)
    print("semantic projections match")


if __name__ == "__main__":
    main()
