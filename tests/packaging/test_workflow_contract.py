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


def test_native_wheel_runs_bounded_wp18_encoded_public_dispatch_contract() -> None:
    command = (
        "python -m pytest -q -p no:cacheprovider "
        "{project}/tests/differential/encoded_compiler/test_permanent_program_assembly.py"
        "::test_facade_constructs_encoded_services_without_scalar_service_context"
    )
    metadata = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
    workflow = (ROOT / ".github/workflows/wheels.yml").read_text(encoding="utf-8")
    contract = (
        ROOT / "tests/differential/encoded_compiler/test_permanent_program_assembly.py"
    ).read_text(encoding="utf-8")
    provenance = (ROOT / "tools/packaging_probe/release_manifest.py").read_text(encoding="utf-8")

    assert metadata.count(command) == 1
    assert workflow.count("uses: pypa/cibuildwheel@") == 2
    assert workflow.count('CIBW_TEST_COMMAND: ""') == 1
    assert "def test_facade_constructs_encoded_services_without_scalar_service_context" in contract
    assert 'diagnostics["ingestion_path"] == "encoded-native"' in contract
    assert "assert ENCODED_NATIVE_FEATURE not in native.FEATURES" in contract
    assert '"tests/differential/encoded_compiler/test_permanent_program_assembly.py"' in provenance


def test_release_cannot_publish_while_licensing_gate_is_open() -> None:
    workflow = (ROOT / ".github/workflows/release.yml").read_text(encoding="utf-8")
    gate = "python -m tools.specs.check_release_gate --require-publishable"
    assert gate in workflow
    assert "actions/attest-build-provenance@" in workflow
    assert workflow.index(gate) < workflow.index("actions/attest-build-provenance@")
    assert "gh-action-pypi-publish" not in workflow
