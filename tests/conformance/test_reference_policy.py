from __future__ import annotations

import json
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - Python 3.10
    import tomli as tomllib

from tools.reference._util import sha256_file
from tools.reference.oracle import _validate_request

ROOT = Path(__file__).parents[2]


def test_requests_are_versioned_local_and_hash_bound() -> None:
    requests = [
        _validate_request(json.loads(line))
        for line in (ROOT / "tests/data/reference/requests-v1.jsonl").read_text().splitlines()
    ]
    assert {request["request_id"] for request in requests} == {
        "empty-consistency",
        "inconsistent-consistency",
        "builtins-class-hierarchy",
        "malformed-error",
        "structural-normalization",
        "atomic-structural-normalization",
    }
    for request in requests:
        path = ROOT / "tests/data/reference/inputs" / request["input"]["document"]
        assert sha256_file(path) == request["input"]["sha256"]
        assert request["input"]["imports"] == []


def test_every_data_artifact_has_an_acquisition_decision() -> None:
    provenance = tomllib.loads((ROOT / "tests/data/PROVENANCE.toml").read_text())
    sources = {source["id"]: source for source in provenance["source"]}
    assert sources["hermit-37ec30a"]["decision"] == "fetch-only"
    assert sources["w3c-owl2-test-export-in-hermit"]["decision"] == "fetch-only"
    artifacts = {artifact["path"]: artifact for artifact in provenance["artifact"]}
    data_files = {
        path.relative_to(ROOT).as_posix()
        for directory in (
            ROOT / "tests/data/clauses",
            ROOT / "tests/data/datatypes",
            ROOT / "tests/data/hyperresolution",
            ROOT / "tests/data/reference",
            ROOT / "tests/data/w3c",
        )
        for path in directory.rglob("*")
        if path.is_file()
    }
    assert set(artifacts) == data_files
    assert all("origin" in artifact and "sha256" in artifact for artifact in artifacts.values())
    assert all(
        sha256_file(ROOT / path) == artifact["sha256"] for path, artifact in artifacts.items()
    )


def test_reference_code_and_java_artifacts_are_excluded_from_distributions() -> None:
    manifest = (ROOT / "MANIFEST.in").read_text()
    assert "tools/reference" not in manifest
    assert "global-exclude *.jar" in manifest
    assert "global-exclude *.class" in manifest
    assert "global-exclude *.java" in manifest
    pyproject = (ROOT / "pyproject.toml").read_text()
    assert 'package-dir = { "" = "src" }' in pyproject


def test_dependency_lock_is_complete_content_addressed_metadata() -> None:
    lock_path = ROOT / "tools/reference/dependencies.lock.json"
    lock = json.loads(lock_path.read_text())
    dependencies = lock["dependencies"]
    assert len(dependencies) == 79
    assert len({entry["path"] for entry in dependencies}) == 79
    assert all(not entry["path"].startswith("/") for entry in dependencies)
    assert all(set(entry) == {"bytes", "path", "sha256"} for entry in dependencies)
    owlapi = next(
        entry for entry in dependencies if entry["path"].endswith("owlapi-distribution-4.2.8.jar")
    )
    assert owlapi["sha256"] == ("ae5eb861d74fd5d10706477d23547f4c4a5c30d8c851acdbfadf9a31d0f26d23")
