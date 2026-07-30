from __future__ import annotations

import hashlib
from pathlib import Path, PurePosixPath
from typing import Any

from tools.specs._compat import load_toml
from tools.specs.check_release_gate import release_status

ROOT = Path(__file__).resolve().parents[2]
INVENTORY = ROOT / "reports" / "licensing" / "adapted-files.toml"
REFERENCE_COMMIT = "37ec30aced32ac81ebecc5e33fad255ddefcb4c3"
COPYRIGHT = "Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory"
MODIFICATIONS = "Modifications Copyright 2026 pyHermiT contributors"
SPDX = "SPDX-License-Identifier: LGPL-3.0-or-later"

_WP11_PORT_FILES = {
    "src/pyhermit/backends/python/blocking/cache.py",
    "src/pyhermit/backends/python/blocking/manager.py",
    "src/pyhermit/backends/python/blocking/signatures.py",
    "src/pyhermit/backends/python/blocking/strategy.py",
    "src/pyhermit/backends/python/blocking/validation.py",
}
_SOURCE_ADAPTATION_MARKERS = (
    "Adapted from HermiT commit",
    "HermiT-compatible",
    "HermiT-style",
    "Source-guided behavior",
    "Source-guided compatibility",
    "source-guided by HermiT",
    "port of the pinned",
    "translation follows the structural shapes of pinned HermiT",
    "follows the language shape of pinned HermiT",
    "follows the NI side conditions in the pinned HermiT",
    "`HermiT` core-blocking checks",
    "`HermiT` mechanics",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _adapted_entries() -> list[dict[str, Any]]:
    value = load_toml(INVENTORY).get("adapted_file")
    assert isinstance(value, list)
    assert all(isinstance(item, dict) for item in value)
    return value


def test_adapted_file_inventory_is_hash_bound_and_header_complete() -> None:
    inventory = load_toml(INVENTORY)
    reference = load_toml(ROOT / "tools" / "reference" / "manifest.toml")["reference"]
    assert inventory["schema"] == 1
    assert inventory["gate_id"] == "LIC-001"
    assert inventory["status"] == "repository-audited-awaiting-owner-legal-review"
    assert inventory["project_license"] == "LGPL-3.0-or-later"
    assert inventory["reference_repository"] == reference["repository"]
    assert inventory["reference_commit"] == reference["commit"]
    assert inventory["reference_tree"] == reference["tree"]
    assert inventory["reference_license"] == reference["license_expression"]
    assert inventory["legal_review"] == "pending"

    entries = _adapted_entries()
    assert len(entries) == 32
    paths = [item["path"] for item in entries]
    assert paths == sorted(set(paths))
    assert set(paths) >= _WP11_PORT_FILES

    for item in entries:
        relative = item["path"]
        assert isinstance(relative, str)
        logical = PurePosixPath(relative)
        assert not logical.is_absolute() and ".." not in logical.parts
        assert relative.startswith(("src/pyhermit/", "native/src/", "tests/unit/expansion/"))
        assert relative.endswith((".py", ".rs"))
        source = ROOT / relative
        assert source.is_file()
        assert item["sha256"] == _sha256(source)
        assert isinstance(item["adaptation"], str) and item["adaptation"].strip()
        components = item["upstream_components"]
        assert isinstance(components, list) and components
        for component in components:
            assert isinstance(component, str)
            upstream = PurePosixPath(component)
            assert not upstream.is_absolute() and ".." not in upstream.parts
            assert component.startswith(
                ("src/main/java/org/semanticweb/HermiT/", "src/test/java/org/semanticweb/HermiT/")
            )
            assert component.endswith(".java")

        header = source.read_text(encoding="utf-8")[:2_000]
        for notice in (COPYRIGHT, MODIFICATIONS, SPDX, REFERENCE_COMMIT):
            assert notice in header, f"{relative} lacks {notice}"
        assert "reports/licensing/adapted-files.toml" in header


def test_every_explicit_adaptation_admission_is_inventoried() -> None:
    inventoried = {item["path"] for item in _adapted_entries()}
    discovered: set[str] = set()
    for root in (
        ROOT / "src" / "pyhermit",
        ROOT / "native" / "src",
        ROOT / "tests" / "unit" / "expansion",
    ):
        for source in (*root.rglob("*.py"), *root.rglob("*.rs")):
            text = source.read_text(encoding="utf-8")
            if any(marker in text for marker in _SOURCE_ADAPTATION_MARKERS):
                discovered.add(source.relative_to(ROOT).as_posix())
    assert discovered == inventoried


def test_licensing_reports_are_finalized_but_do_not_claim_legal_signoff() -> None:
    reports = (
        ROOT / "reports" / "licensing" / "adapted-file-header-audit.md",
        ROOT / "reports" / "licensing" / "package-license-audit.md",
        ROOT / "reports" / "release" / "artifact-audit.md",
    )
    for report in reports:
        text = report.read_text(encoding="utf-8")
        assert "PENDING_" not in text
        assert "owner/legal" in text
        assert "not legal advice" in text.lower()
        assert "publish_allowed" in text or "publication" in text


def test_lic_001_records_owner_waiver_without_claiming_legal_signoff() -> None:
    allowed, pending = release_status(ROOT / "tools" / "specs" / "licensing.toml")
    assert allowed
    assert pending == ()
    override = (ROOT / "reports/release/0.1.2-owner-release-override.md").read_text(
        encoding="utf-8"
    )
    assert "not an owner/legal-review signoff" in override
    assert "not legal advice" in override
