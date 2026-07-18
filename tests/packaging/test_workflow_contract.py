"""Static regression tests for fail-closed packaging workflow contracts."""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_wheel_workflow_has_all_tier_one_targets_and_no_publish_action() -> None:
    workflow = (ROOT / ".github/workflows/wheels.yml").read_text(encoding="utf-8")
    for token in (
        "cp310-{manylinux,musllinux}_x86_64",
        "cp310-{manylinux,musllinux}_aarch64",
        "cp310-macosx_x86_64",
        "cp310-macosx_arm64",
        "cp310-win_amd64",
        "cp310-win_arm64",
        "abi3audit==0.0.26",
        "auditwheel==6.7.0",
        "delocate==0.13.0",
        "delvewheel==1.13.0",
        "path: rebuild-source",
        "package-dir: rebuild-source",
        "cargo package --manifest-path native/Cargo.toml --locked --allow-dirty --list",
        "EmbarkStudios/cargo-deny-action@bb137d7af7e4fb67e5f82a49c4fce4fad40782fe",
        "manifest-path: native/Cargo.toml",
        "arguments: --all-features --locked",
    ):
        assert token in workflow
    assert "gh-action-pypi-publish" not in workflow


def test_release_cannot_publish_while_licensing_gate_is_open() -> None:
    workflow = (ROOT / ".github/workflows/release.yml").read_text(encoding="utf-8")
    gate = "python -m tools.specs.check_release_gate --require-publishable"
    assert gate in workflow
    assert "actions/attest-build-provenance@" in workflow
    assert workflow.index(gate) < workflow.index("actions/attest-build-provenance@")
    assert "gh-action-pypi-publish" not in workflow
