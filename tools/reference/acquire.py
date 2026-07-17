"""Explicit, hash-verifying acquisition of the quarantined HermiT reference checkout."""

from __future__ import annotations

import argparse
import subprocess
from pathlib import Path

from tools.reference._util import sha256_file

REPOSITORY = "https://github.com/phillord/hermit-reasoner.git"
COMMIT = "37ec30aced32ac81ebecc5e33fad255ddefcb4c3"
TREE = "576db18fd8152be24d577b24c99e2af0d31ceef8"
ARCHIVE_SHA256 = "41e389ddaf63dcff32bd3b5e360d000c15fccb328ddc749fd8464894f9c29dd7"


def run(args: list[str], *, cwd: Path | None = None) -> str:
    return subprocess.run(args, cwd=cwd, check=True, capture_output=True, text=True).stdout.strip()


def acquire(destination: Path, archive: Path, *, allow_network: bool) -> None:
    if not destination.exists():
        if not allow_network:
            raise RuntimeError(
                "checkout is absent; repeat with --allow-network for explicit acquisition"
            )
        destination.parent.mkdir(parents=True, exist_ok=True)
        run(["git", "clone", "--no-checkout", REPOSITORY, str(destination)])
    if run(["git", "-C", str(destination), "cat-file", "-t", COMMIT]) != "commit":
        if not allow_network:
            raise RuntimeError("pinned commit is absent; repeat with --allow-network")
        run(["git", "-C", str(destination), "fetch", "origin", COMMIT])
    run(["git", "-C", str(destination), "checkout", "--detach", COMMIT])
    actual_commit = run(["git", "-C", str(destination), "rev-parse", "HEAD"])
    actual_tree = run(["git", "-C", str(destination), "rev-parse", "HEAD^{tree}"])
    if actual_commit != COMMIT or actual_tree != TREE:
        raise RuntimeError(f"reference identity mismatch: {actual_commit} / {actual_tree}")
    archive.parent.mkdir(parents=True, exist_ok=True)
    with archive.open("wb") as stream:
        subprocess.run(
            ["git", "-C", str(destination), "archive", "--format=tar", COMMIT],
            check=True,
            stdout=stream,
        )
    actual_archive_hash = sha256_file(archive)
    if actual_archive_hash != ARCHIVE_SHA256:
        raise RuntimeError(f"archive hash mismatch: {actual_archive_hash}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--destination", type=Path, required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--allow-network", action="store_true")
    args = parser.parse_args()
    acquire(args.destination, args.archive, allow_network=args.allow_network)
    print(f"verified {COMMIT} ({TREE}) and archive {ARCHIVE_SHA256}")


if __name__ == "__main__":
    main()
