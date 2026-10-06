"""The CI native-core prerequisite neither skips failures nor upgrades core."""

from __future__ import annotations

import os
import runpy
import subprocess
import sys
import sysconfig
from pathlib import Path
from typing import Any

import pytest

HELPER = Path(__file__).with_name("ensure_native_core.py")


def _runner() -> dict[str, Any]:
    return runpy.run_path(str(HELPER))


def test_existing_native_core_needs_only_one_fresh_probe(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[tuple[list[str], dict[str, Any]]] = []

    def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        calls.append((command, kwargs))
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(subprocess, "run", run)
    monkeypatch.setenv("PYTHONPATH", "/untrusted/source")

    assert _runner()["main"]() == 0
    assert len(calls) == 1
    command, options = calls[0]
    assert command[:3] == [sys.executable, "-I", "-c"]
    assert options["check"] is False
    assert "PYTHONPATH" not in options["env"]
    assert options["env"]["PYTHONSAFEPATH"] == "1"
    assert os.environ["PYTHONPATH"] == "/untrusted/source"


def test_missing_native_core_builds_pinned_sdist_and_probes_again(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[tuple[list[str], dict[str, Any]]] = []

    def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        calls.append((command, kwargs))
        return subprocess.CompletedProcess(command, 3 if len(calls) == 1 else 0)

    monkeypatch.setattr(subprocess, "run", run)
    monkeypatch.setenv("PYOWL_CORE_BUILD_NATIVE", "0")

    assert _runner()["main"]() == 0
    assert len(calls) == 3
    assert calls[1][0] == [
        sys.executable,
        "-m",
        "pip",
        "install",
        "--no-cache-dir",
        "--no-deps",
        "--no-binary=pyowl-core",
        "--force-reinstall",
        "pyowl-core==0.2.1",
    ]
    assert calls[1][1]["env"]["PYOWL_CORE_BUILD_NATIVE"] == "1"
    assert calls[1][1]["check"] is True
    assert calls[2][0] == calls[0][0]
    assert calls[2][1]["check"] is True
    assert calls[2][1]["env"] == calls[0][1]["env"]
    assert os.environ["PYOWL_CORE_BUILD_NATIVE"] == "0"


@pytest.mark.parametrize("returncode", (1, 2, -9))
def test_unexpected_probe_failure_does_not_install(
    monkeypatch: pytest.MonkeyPatch, returncode: int
) -> None:
    calls: list[list[str]] = []

    def run(command: list[str], **_kwargs: Any) -> subprocess.CompletedProcess[str]:
        calls.append(command)
        return subprocess.CompletedProcess(command, returncode)

    monkeypatch.setattr(subprocess, "run", run)
    with pytest.raises(subprocess.CalledProcessError) as caught:
        _runner()["main"]()
    assert caught.value.returncode == returncode
    assert len(calls) == 1


@pytest.mark.parametrize("failing_call", (2, 3), ids=("build", "post-install-probe"))
def test_installation_or_post_install_probe_failure_is_fatal(
    monkeypatch: pytest.MonkeyPatch, failing_call: int
) -> None:
    calls: list[list[str]] = []

    def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        calls.append(command)
        if len(calls) == failing_call:
            assert kwargs["check"] is True
            raise subprocess.CalledProcessError(3, command)
        return subprocess.CompletedProcess(command, 3 if len(calls) == 1 else 0)

    monkeypatch.setattr(subprocess, "run", run)
    with pytest.raises(subprocess.CalledProcessError) as caught:
        _runner()["main"]()
    assert caught.value.returncode == 3
    assert len(calls) == failing_call


@pytest.mark.parametrize("encoded", (False, True), ids=("plain-flags", "encoded-flags"))
def test_musl_build_keeps_rust_flags_and_selects_dynamic_crt(
    monkeypatch: pytest.MonkeyPatch, encoded: bool
) -> None:
    environment = {"RUSTFLAGS": '-Copt-level=2 --cfg "native core"'}
    if encoded:
        environment["CARGO_ENCODED_RUSTFLAGS"] = "-Copt-level=3\x1f--cfg\x1fnative core"
    original = environment.copy()
    monkeypatch.setattr(sysconfig, "get_config_var", lambda _name: "aarch64-unknown-linux-musl")

    result = _runner()["_build_environment"](environment)

    assert result["PYOWL_CORE_BUILD_NATIVE"] == "1"
    assert result["CARGO_ENCODED_RUSTFLAGS"].split("\x1f") == [
        f"-Copt-level={3 if encoded else 2}",
        "--cfg",
        "native core",
        "-Ctarget-feature=-crt-static",
    ]
    assert "RUSTFLAGS" not in result
    assert environment == original
