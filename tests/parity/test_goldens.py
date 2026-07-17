from __future__ import annotations

import json
from pathlib import Path

from tools.reference.goldens import load_jsonl, semantic_diff

ROOT = Path(__file__).parents[2]
GOLDENS = ROOT / "tests/data/reference/goldens-v1.jsonl"


def test_initial_goldens_cover_empty_builtins_and_error_shapes(tmp_path: Path) -> None:
    records = {record["request_id"]: record for record in load_jsonl(GOLDENS)}
    assert records["empty-consistency"]["outcome"] == "SAT"
    assert records["inconsistent-consistency"]["outcome"] == "UNSAT"
    assert records["builtins-class-hierarchy"]["value"]["kind"] == "hierarchy"
    assert records["malformed-error"]["error"]["category"] == "ERROR"
    candidate = tmp_path / "candidate.jsonl"
    candidate.write_text(GOLDENS.read_text())
    assert semantic_diff(GOLDENS, candidate) == ""


def test_regeneration_diff_does_not_overwrite_committed_goldens(tmp_path: Path) -> None:
    before = GOLDENS.read_bytes()
    records = load_jsonl(GOLDENS)
    records[0]["value"] = False
    candidate = tmp_path / "candidate.jsonl"
    candidate.write_text("\n".join(json.dumps(record) for record in records) + "\n")
    assert '-    "value": true' in semantic_diff(GOLDENS, candidate)
    assert GOLDENS.read_bytes() == before
