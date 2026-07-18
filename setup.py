"""Conditional declaration of pyHermiT's private Rust extension."""

from __future__ import annotations

import gzip
import os
import shlex
import shutil
import tarfile
from pathlib import Path

from setuptools import setup
from setuptools.command.sdist import sdist as _sdist

_VALID_MODES = frozenset({"auto", "0", "1"})


def _native_mode() -> str:
    value = os.environ.get("PYHERMIT_BUILD_NATIVE", "auto")
    if value not in _VALID_MODES:
        expected = "auto, 0, or 1"
        raise RuntimeError(f"PYHERMIT_BUILD_NATIVE must be {expected}; got {value!r}")
    return value


def _cargo_available() -> bool:
    """Return whether the configured Cargo executable can be launched."""

    return shutil.which(os.environ.get("CARGO", "cargo")) is not None


def _source_date_epoch() -> int:
    value = os.environ.get("SOURCE_DATE_EPOCH", "946684800")
    try:
        epoch = int(value)
    except ValueError as error:
        raise RuntimeError(
            f"SOURCE_DATE_EPOCH must be a non-negative integer; got {value!r}"
        ) from error
    if epoch < 0:
        raise RuntimeError(f"SOURCE_DATE_EPOCH must be a non-negative integer; got {value!r}")
    return epoch


def _normalize_sdist(path: Path) -> None:
    """Rewrite a gzip-compressed sdist with stable order and ownership metadata."""

    if not path.name.endswith(".tar.gz"):
        raise RuntimeError(f"unsupported sdist format for reproducible build: {path.name}")
    temporary = path.with_name(f".{path.name}.normalized")
    with tarfile.open(path, "r:gz") as source:
        members = sorted(source.getmembers(), key=lambda member: member.name)
        with (
            temporary.open("wb") as raw_output,
            gzip.GzipFile(
                fileobj=raw_output, mode="wb", filename="", mtime=_source_date_epoch()
            ) as compressed,
            tarfile.open(fileobj=compressed, mode="w", format=tarfile.PAX_FORMAT) as target,
        ):
            for member in members:
                member.uid = 0
                member.gid = 0
                member.uname = ""
                member.gname = ""
                member.mtime = _source_date_epoch()
                member.pax_headers = {}
                payload = source.extractfile(member) if member.isfile() else None
                target.addfile(member, payload)
    os.replace(temporary, path)


class ReproducibleSdist(_sdist):
    """Create the normal setuptools sdist, then normalize its tar/gzip metadata."""

    def run(self) -> None:
        super().run()
        for archive in self.archive_files:
            _normalize_sdist(Path(archive))


mode = _native_mode()
manifest = Path("native/Cargo.toml")
rust_extensions = []

if mode != "0" and manifest.is_file() and (mode == "1" or _cargo_available()):
    from setuptools_rust import Binding, RustExtension

    encoded_flags = os.environ.get("CARGO_ENCODED_RUSTFLAGS")
    rust_flags = (
        encoded_flags.split("\x1f")
        if encoded_flags
        else shlex.split(os.environ.get("RUSTFLAGS", ""))
    )
    root = Path(__file__).resolve().parent
    cargo_home = Path(os.environ.get("CARGO_HOME", Path.home() / ".cargo")).resolve()
    rust_flags.extend(
        (
            f"--remap-path-prefix={root}=pyhermit-src",
            f"--remap-path-prefix={cargo_home}=cargo-home",
        )
    )
    rust_environment = os.environ.copy()
    rust_environment["CARGO_ENCODED_RUSTFLAGS"] = "\x1f".join(rust_flags)
    rust_extensions.append(
        RustExtension(
            "pyhermit._native",
            path=str(manifest),
            binding=Binding.PyO3,
            optional=mode == "auto",
            cargo_manifest_args=("--locked",),
            env=rust_environment,
        )
    )
elif mode == "1" and not manifest.is_file():
    raise RuntimeError("native build required but native/Cargo.toml is missing")

setup(cmdclass={"sdist": ReproducibleSdist}, rust_extensions=rust_extensions, zip_safe=False)
