"""Build the development-only Java oracle in an ignored quarantine directory.

Nothing runs implicitly.  Maven network resolution requires the explicit ``--allow-network``
flag; ordinary tests and package builds never call this module.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
from pathlib import Path

from tools.reference._util import sha256_file, write_json

COMMIT = "37ec30aced32ac81ebecc5e33fad255ddefcb4c3"


def checked(args: list[str], *, cwd: Path, env: dict[str, str] | None = None) -> None:
    subprocess.run(args, cwd=cwd, env=env, check=True)


def build(args: argparse.Namespace) -> None:
    source = args.source.resolve()
    worktree = args.worktree.resolve()
    local_repo = args.maven_repo.resolve()
    classpath_file = args.classpath_file.resolve()
    oracle_classes = args.oracle_classes.resolve()
    patch = args.patch.resolve()
    if not source.exists():
        raise RuntimeError("reference checkout is absent; run acquire.py explicitly")
    if (
        subprocess.run(
            ["git", "-C", str(source), "rev-parse", "HEAD"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        != COMMIT
    ):
        raise RuntimeError("reference checkout is not at the pinned commit")
    if worktree.exists():
        checked(["git", "worktree", "remove", "--force", str(worktree)], cwd=source)
    checked(["git", "worktree", "add", "--detach", str(worktree), COMMIT], cwd=source)
    checked(["git", "apply", "--check", str(patch)], cwd=worktree)
    checked(["git", "apply", str(patch)], cwd=worktree)

    java_home = args.java_home.resolve()
    java = java_home / "bin/java"
    javac = java_home / "bin/javac"
    if not java.exists() or not javac.exists():
        raise RuntimeError(f"invalid JDK home: {java_home}")
    env = dict(os.environ)
    env["JAVA_HOME"] = str(java_home)
    env["PATH"] = f"{java_home / 'bin'}:{Path(args.maven).resolve().parent}:/usr/bin:/bin"
    local_repo.mkdir(parents=True, exist_ok=True)
    maven_common = [
        str(Path(args.maven).resolve()),
        f"-Dmaven.repo.local={local_repo}",
        "-DskipTests",
    ]
    if not args.allow_network:
        maven_common.append("--offline")
    checked([*maven_common, "test-compile"], cwd=worktree, env=env)
    checked(
        [
            *maven_common,
            "dependency:build-classpath",
            "-Dmdep.includeScope=test",
            "-Dmdep.outputAbsoluteArtifactFilename=true",
            f"-Dmdep.outputFile={classpath_file}",
        ],
        cwd=worktree,
        env=env,
    )
    dependencies = classpath_file.read_text().strip().split(os.pathsep)
    compile_classpath = os.pathsep.join([str(worktree / "target/classes"), *dependencies])
    oracle_classes.mkdir(parents=True, exist_ok=True)
    java_sources = sorted(args.java_source.resolve().parent.glob("*.java"))
    if not java_sources:
        raise RuntimeError("oracle adapter Java sources are absent")
    checked(
        [
            str(javac),
            "-encoding",
            "UTF-8",
            "-source",
            "8",
            "-target",
            "8",
            "-cp",
            compile_classpath,
            "-d",
            str(oracle_classes),
            *(str(source) for source in java_sources),
        ],
        cwd=worktree,
        env=env,
    )
    lock_entries = []
    for dependency in dependencies:
        dependency_path = Path(dependency)
        try:
            name = str(dependency_path.resolve().relative_to(local_repo))
        except ValueError:
            try:
                name = "reference-worktree/" + str(dependency_path.resolve().relative_to(worktree))
            except ValueError:
                name = dependency_path.name
        lock_entries.append(
            {
                "path": name,
                "bytes": dependency_path.stat().st_size,
                "sha256": sha256_file(dependency_path),
            }
        )
    write_json(
        args.lock_file.resolve(),
        {
            "schema_version": "1.0",
            "reference_commit": COMMIT,
            "java": {"sha256": sha256_file(java)},
            "javac": {"sha256": sha256_file(javac)},
            "maven": {
                "sha256": sha256_file(Path(args.maven).resolve()),
            },
            "dependencies": sorted(lock_entries, key=lambda item: item["path"]),
        },
    )
    print(json.dumps({"oracle_classes": str(oracle_classes), "dependencies": len(dependencies)}))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--worktree", type=Path, required=True)
    parser.add_argument("--maven-repo", type=Path, required=True)
    parser.add_argument("--classpath-file", type=Path, required=True)
    parser.add_argument("--lock-file", type=Path, required=True)
    parser.add_argument("--oracle-classes", type=Path, required=True)
    parser.add_argument("--patch", type=Path, required=True)
    parser.add_argument("--java-source", type=Path, required=True)
    parser.add_argument("--java-home", type=Path, required=True)
    parser.add_argument("--maven", type=Path, required=True)
    parser.add_argument("--allow-network", action="store_true")
    build(parser.parse_args())


if __name__ == "__main__":
    main()
