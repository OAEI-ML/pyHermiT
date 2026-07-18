#!/usr/bin/env python3
"""Install one local artifact offline with compilers and Java hidden."""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import tempfile
from pathlib import Path


def _venv_executable(root: Path, name: str) -> Path:
    scripts = "Scripts" if os.name == "nt" else "bin"
    suffix = ".exe" if os.name == "nt" else ""
    return root / scripts / f"{name}{suffix}"


def _set_read_only(root: Path, *, read_only: bool) -> None:
    if os.name == "nt":
        return
    for path in sorted(root.rglob("*"), reverse=True):
        mode = (0o555 if read_only else 0o755) if path.is_dir() else (0o444 if read_only else 0o644)
        path.chmod(mode)
    root.chmod(0o555 if read_only else 0o755)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifact", type=Path)
    parser.add_argument("--python", type=Path, required=True)
    parser.add_argument("--wheelhouse", type=Path, required=True)
    parser.add_argument("--expected-backend", choices=("python", "native"), required=True)
    parser.add_argument(
        "--expected-core-backend",
        choices=("python", "native", "either"),
        default="either",
    )
    parser.add_argument("--semantic-suite", action="store_true")
    args = parser.parse_args()

    artifact = args.artifact.resolve()
    wheelhouse = args.wheelhouse.resolve()
    smoke = Path(__file__).with_name("installed_smoke.py").resolve()
    with tempfile.TemporaryDirectory(prefix="pyhermit-installed-") as temporary:
        environment = Path(temporary) / "venv"
        subprocess.run([str(args.python), "-m", "venv", str(environment)], check=True)
        python = _venv_executable(environment, "python")
        pip = [str(python), "-m", "pip"]
        env = os.environ.copy()
        env.pop("PYTHONPATH", None)
        env["PATH"] = str(python.parent)
        env["CARGO"] = str(Path(temporary) / "unavailable-cargo")
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        assert all(
            shutil.which(command, path=env["PATH"]) is None
            for command in ("java", "javac", "cargo", "rustc", "cc", "gcc", "clang")
        )
        if artifact.name.endswith(".tar.gz"):
            subprocess.run(
                [
                    *pip,
                    "install",
                    "--no-index",
                    "--find-links",
                    str(wheelhouse),
                    "setuptools==83.0.0",
                    "setuptools-rust==1.13.0",
                    "wheel==0.46.3",
                ],
                check=True,
                cwd=temporary,
                env=env,
            )
        if args.semantic_suite:
            subprocess.run(
                [
                    *pip,
                    "install",
                    "--no-index",
                    "--find-links",
                    str(wheelhouse),
                    "hypothesis",
                    "packaging",
                    "pytest",
                    "tomli; python_version < '3.11'",
                ],
                check=True,
                cwd=temporary,
                env=env,
            )
        subprocess.run(
            [
                *pip,
                "install",
                "--no-index",
                "--find-links",
                str(wheelhouse),
                "--no-cache-dir",
                "--no-build-isolation",
                str(artifact),
            ],
            check=True,
            cwd=temporary,
            env=env,
        )
        site_paths = {
            Path(value)
            for value in subprocess.check_output(
                [
                    str(python),
                    "-c",
                    (
                        "import sysconfig; "
                        "print(sysconfig.get_path('purelib')); "
                        "print(sysconfig.get_path('platlib'))"
                    ),
                ],
                text=True,
                env=env,
            ).splitlines()
        }
        package_roots = [
            site_path / package
            for site_path in sorted(site_paths)
            for package in ("pyhermit", "pyowl_core")
            if (site_path / package).is_dir()
        ]
        read_only_cwd = Path(temporary) / "read-only"
        read_only_cwd.mkdir()
        try:
            for package_root in package_roots:
                _set_read_only(package_root, read_only=True)
            if os.name != "nt":
                read_only_cwd.chmod(0o555)
            subprocess.run(
                [
                    str(python),
                    str(smoke),
                    "--expected-backend",
                    args.expected_backend,
                    "--expected-core-backend",
                    args.expected_core_backend,
                ],
                check=True,
                cwd=read_only_cwd,
                env=env,
            )
            if args.semantic_suite:
                suite = Path(__file__).with_name("run_installed_suite.py").resolve()
                subprocess.run(
                    [str(python), str(suite), "--backend", args.expected_backend],
                    check=True,
                    cwd=read_only_cwd,
                    env=env,
                )
        finally:
            if os.name != "nt":
                read_only_cwd.chmod(0o755)
            for package_root in package_roots:
                _set_read_only(package_root, read_only=False)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
