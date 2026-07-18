#!/usr/bin/env python3
"""Prove pip prefers compatible native wheels and falls back to the universal wheel."""

from __future__ import annotations

import argparse
import subprocess
import sys
import tempfile
from pathlib import Path


def _download(index: Path, destination: Path, version: str, platform: str) -> Path:
    destination.mkdir(parents=True)
    subprocess.run(
        [
            sys.executable,
            "-m",
            "pip",
            "download",
            "--no-index",
            "--find-links",
            str(index),
            "--only-binary=:all:",
            "--no-deps",
            "--dest",
            str(destination),
            "--platform",
            platform,
            "--implementation",
            "cp",
            "--python-version",
            "310",
            "--abi",
            "cp310",
            f"pyHermiT=={version}",
        ],
        check=True,
    )
    wheels = tuple(destination.glob("*.whl"))
    if len(wheels) != 1:
        raise RuntimeError(f"expected one selected wheel, found {wheels}")
    return wheels[0]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--index", type=Path, required=True)
    args = parser.parse_args()
    pure = tuple(args.index.glob("pyhermit-*-py3-none-any.whl"))
    if len(pure) != 1:
        raise RuntimeError(f"cannot infer version from fallback wheel: {pure}")
    version = pure[0].name.removeprefix("pyhermit-").removesuffix("-py3-none-any.whl")
    with tempfile.TemporaryDirectory(prefix="pyhermit-index-") as temporary:
        root = Path(temporary)
        compatible = _download(args.index, root / "compatible", version, "manylinux2014_x86_64")
        unsupported = _download(args.index, root / "unsupported", version, "win32")
    if "-cp310-abi3-" not in compatible.name:
        raise RuntimeError(f"compatible resolution did not prefer native: {compatible.name}")
    if not unsupported.name.endswith("-py3-none-any.whl"):
        raise RuntimeError(f"unsupported resolution did not use fallback: {unsupported.name}")
    print(f"pip preference passed: native={compatible.name}, fallback={unsupported.name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
