"""Exercise compiler-free build modes and same-version wheel tag preference."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import zipfile
from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from pathlib import Path

from packaging.tags import Tag, sys_tags
from packaging.utils import parse_wheel_filename

PROBE_VERSION = "0.1.1"


class ProbeError(RuntimeError):
    """The packaging strategy did not exhibit its required behavior."""


@dataclass(frozen=True, slots=True)
class BuildObservation:
    mode: str
    succeeded: bool
    wheels: tuple[str, ...]
    output: str


def _project_root() -> Path:
    return Path(__file__).resolve().parent / "project"


def _build(mode: str, project: Path, output: Path) -> BuildObservation:
    environment = os.environ.copy()
    environment["PYHERMIT_BUILD_NATIVE"] = mode
    unavailable_toolchain = output / "unavailable-toolchain"
    unavailable_toolchain.mkdir()
    cargo = unavailable_toolchain / "cargo"
    rustc = unavailable_toolchain / "rustc"
    if cargo.exists() or rustc.exists():
        raise ProbeError("compiler-free probe unexpectedly found a configured Rust tool")
    environment["CARGO"] = str(cargo)
    environment["RUSTC"] = str(rustc)
    environment["PATH"] = str(unavailable_toolchain)
    command = [
        sys.executable,
        "-m",
        "build",
        "--wheel",
        "--no-isolation",
        "--outdir",
        str(output),
        str(project),
    ]
    result = subprocess.run(
        command,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        env=environment,
    )
    wheels = tuple(sorted(path.name for path in output.glob("*.whl")))
    return BuildObservation(mode, result.returncode == 0, wheels, result.stdout)


def _wheel_has_native(path: Path) -> bool:
    with zipfile.ZipFile(path) as archive:
        return any(
            name.lower().endswith((".so", ".pyd", ".dll", ".dylib")) for name in archive.namelist()
        )


def _candidate_tags(filename: str) -> frozenset[Tag]:
    _, version, _, tags = parse_wheel_filename(filename)
    if str(version) != PROBE_VERSION:
        raise ProbeError(f"probe wheel version drift: {filename}")
    return frozenset(tags)


def select_best(candidates: Iterable[str], supported: Sequence[Tag]) -> str:
    """Select a wheel using the same ordered compatibility tags pip consumes."""

    ranks = {tag: index for index, tag in enumerate(supported)}
    ranked: list[tuple[int, str]] = []
    for candidate in candidates:
        matching = _candidate_tags(candidate) & ranks.keys()
        if matching:
            ranked.append((min(ranks[tag] for tag in matching), candidate))
    if not ranked:
        raise ProbeError("no compatible wheel candidate")
    return min(ranked)[1]


def prove_same_version_tag_preference() -> dict[str, str]:
    supported = tuple(sys_tags())
    native_tag = next(
        (
            tag
            for tag in supported
            if tag.interpreter == "cp310" and tag.abi == "abi3" and tag.platform != "any"
        ),
        None,
    )
    if native_tag is None:
        raise ProbeError("current CPython does not advertise a cp310-abi3 platform tag")
    pure = f"pyhermit_build_probe-{PROBE_VERSION}-py3-none-any.whl"
    native = (
        f"pyhermit_build_probe-{PROBE_VERSION}-"
        f"{native_tag.interpreter}-{native_tag.abi}-{native_tag.platform}.whl"
    )
    selected = select_best((pure, native), supported)
    if selected != native:
        raise ProbeError("compatible native wheel did not outrank the universal wheel")
    simulated_python_only = (
        Tag("pp310", "pypy310_pp73", "manylinux_2_17_x86_64"),
        Tag("py3", "none", "any"),
    )
    selected_python_only = select_best((pure, native), simulated_python_only)
    if selected_python_only != pure:
        raise ProbeError("unavailable native tag did not fall back to the universal wheel")
    return {"supported": selected, "python_only": selected_python_only}


def run_probe() -> dict[str, object]:
    source = _project_root()
    if not source.is_dir():
        raise ProbeError(f"probe project is missing: {source}")
    observations: dict[str, BuildObservation] = {}
    with tempfile.TemporaryDirectory(prefix="pyhermit-build-probe-") as temporary:
        root = Path(temporary)
        for mode in ("0", "auto", "1"):
            project = root / f"project-{mode}"
            output = root / f"dist-{mode}"
            shutil.copytree(source, project)
            output.mkdir()
            observations[mode] = _build(mode, project, output)

        pure = observations["0"]
        automatic = observations["auto"]
        forced = observations["1"]
        if not pure.succeeded or len(pure.wheels) != 1:
            raise ProbeError(f"pure build failed:\n{pure.output}")
        if not pure.wheels[0].endswith("-py3-none-any.whl"):
            raise ProbeError(f"pure build has the wrong wheel tag: {pure.wheels[0]}")
        if _wheel_has_native(root / "dist-0" / pure.wheels[0]):
            raise ProbeError("mode 0 wheel unexpectedly contains a native extension")
        if not automatic.succeeded or len(automatic.wheels) != 1:
            raise ProbeError(f"optional build did not survive missing Cargo:\n{automatic.output}")
        if _wheel_has_native(root / "dist-auto" / automatic.wheels[0]):
            raise ProbeError("auto wheel contains native output despite forced compiler absence")
        if forced.succeeded or forced.wheels:
            raise ProbeError("forced native build did not fail loudly")

    preference = prove_same_version_tag_preference()
    return {
        "builds": {
            mode: {
                "succeeded": observation.succeeded,
                "wheels": observation.wheels,
            }
            for mode, observation in observations.items()
        },
        "tag_preference": preference,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    try:
        summary = run_probe()
    except (OSError, ProbeError, subprocess.SubprocessError, zipfile.BadZipFile) as error:
        print(f"packaging probe failed: {error}")
        return 1
    if args.json:
        print(json.dumps(summary, sort_keys=True))
    else:
        print("packaging probe passed: pure/auto succeed, forced native fails")
        print("same-version tag preference passed: compatible native, universal fallback")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
