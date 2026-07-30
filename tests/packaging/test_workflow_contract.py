"""Static regression tests for fail-closed packaging workflow contracts."""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def test_checkout_preserves_hash_bound_fixture_bytes_across_platforms() -> None:
    attributes = (ROOT / ".gitattributes").read_text(encoding="utf-8")

    assert "* text=auto eol=lf" in attributes.splitlines()


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


def test_abi3_matrix_matches_the_approved_pyowl_core_native_platforms() -> None:
    workflow = (ROOT / ".github/workflows/wheels.yml").read_text(encoding="utf-8")
    abi3 = workflow.split("  abi3-python312:\n", 1)[1].split("  musllinux-python312:\n", 1)[0]

    assert abi3.count("core_backend: native") == 5
    assert abi3.count("core_backend: python") == 1
    assert (
        "- id: windows-arm64\n"
        "            runner: windows-11-arm\n"
        '            pattern: "*win_arm64.whl"\n'
        "            core_backend: python"
    ) in abi3
    assert '--expected-core-backend "$EXPECTED_CORE_BACKEND"' in abi3


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
    assert "assert ENCODED_NATIVE_FEATURE in native.FEATURES" in contract
    assert '"tests/differential/encoded_compiler/test_permanent_program_assembly.py"' in provenance


def test_pure_ci_excludes_native_only_test_trees() -> None:
    workflow = (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8")

    assert "--ignore=tests/differential/encoded_compiler" in workflow
    assert "--ignore-glob='tests/native/**'" in workflow


def test_native_wheel_test_dependencies_use_python_module_launcher() -> None:
    metadata = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
    requirements = (ROOT / "tests/packaging/wheel-requirements.txt").read_text(encoding="utf-8")

    assert "test-requires" not in metadata
    assert "python -m pip install -r {project}/tests/packaging/wheel-requirements.txt" in metadata
    assert "tomli>=2.0,<3" in requirements
    assert "python_version" not in requirements


def test_setup_preserves_musl_and_macos_linker_requirements() -> None:
    setup = (ROOT / "setup.py").read_text(encoding="utf-8")

    assert 'host_gnu_type.endswith("-linux-musl")' in setup
    assert 'rust_flags.append("-Ctarget-feature=-crt-static")' in setup
    assert 'rust_flags.append("-Clink-arg=/Brepro")' in setup
    assert "normalize_macho_binary" in setup
    assert "org.oaeiml.pyhermit._native" in (ROOT / "pyhermit_build.py").read_text(encoding="utf-8")
    assert "no_uuid" not in setup


def test_installed_suite_loads_runtime_before_repository_test_support() -> None:
    runner = (ROOT / "tests/packaging/run_installed_suite.py").read_text(encoding="utf-8")

    assert runner.index("import pyhermit") < runner.index("sys.path.insert(0, {str(root)!r})")


def test_release_requires_gates_attestation_and_atomic_trusted_publication() -> None:
    workflow = (ROOT / ".github/workflows/release.yml").read_text(encoding="utf-8")
    gate = "python -m tools.specs.check_release_gate --require-publishable"
    attestation = "actions/attest-build-provenance@"
    publish = "pypa/gh-action-pypi-publish@"
    assert gate in workflow
    assert attestation in workflow
    assert publish in workflow
    assert workflow.index(gate) < workflow.index(attestation) < workflow.index(publish)
    assert "needs: attest-candidate" in workflow
    assert "if: github.event_name == 'workflow_dispatch' && inputs.publish" in workflow
    assert 'assert os.environ["RELEASE_REF"].startswith("refs/tags/v")' in workflow
    assert 'os.environ["RELEASE_TAG"] == f"v{match.group(1)}"' in workflow
    assert "(len(native), len(pure), len(sdist)) == (8, 1, 1)" in workflow
    assert "skip-existing: false" in workflow
