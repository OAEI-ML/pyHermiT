"""Create a deterministic SPDX 2.3 SBOM from pyHermiT's locked dependency inputs."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
from collections.abc import Mapping, Sequence
from pathlib import Path

from tools.packaging_probe.check_artifact import _runtime_version
from tools.specs._compat import (
    load_toml,
    repository_root,
    require_int,
    require_list,
    require_mapping,
    require_str,
)

_CRATES_IO_INDEX = "registry+https://github.com/rust-lang/crates.io-index"


def _spdx_id(name: str, version: str) -> str:
    token = re.sub(r"[^A-Za-z0-9.-]", "-", f"{name}-{version}")
    digest = hashlib.sha256(f"{name}\0{version}".encode()).hexdigest()[:12]
    return f"SPDXRef-Package-{token}-{digest}"


def _manifest_dependency_names(
    manifest: Mapping[str, object],
    table_names: Sequence[str],
) -> set[str]:
    names: set[str] = set()

    def collect(raw: object, context: str) -> None:
        table = require_mapping(raw, context)
        for alias, value in table.items():
            if not isinstance(alias, str):
                raise ValueError(f"{context} contains a non-string dependency name")
            dependency = (
                require_str(value.get("package"), f"{context}.{alias}.package")
                if isinstance(value, Mapping) and "package" in value
                else alias
            )
            names.add(dependency)

    for table_name in table_names:
        collect(manifest.get(table_name, {}), f"Cargo.toml {table_name}")
    targets = require_mapping(manifest.get("target", {}), "Cargo.toml target")
    for target_name, raw_target in targets.items():
        target = require_mapping(raw_target, f"Cargo.toml target.{target_name}")
        for table_name in table_names:
            collect(
                target.get(table_name, {}),
                f"Cargo.toml target.{target_name}.{table_name}",
            )
    return names


def _locked_packages(lock: Mapping[str, object]) -> dict[str, Mapping[str, object]]:
    packages: dict[str, Mapping[str, object]] = {}
    for raw in require_list(lock.get("package"), "Cargo.lock package"):
        package = require_mapping(raw, "Cargo.lock package item")
        name = require_str(package.get("name"), "Cargo package name")
        if name in packages:
            raise ValueError(
                f"Cargo.lock contains multiple versions of {name}; "
                "the release inventory requires an unambiguous production closure"
            )
        packages[name] = package
    return packages


def _production_lock_packages(
    manifest: Mapping[str, object],
    lock: Mapping[str, object],
    root_name: str,
) -> list[Mapping[str, object]]:
    locked = _locked_packages(lock)
    root = locked.get(root_name)
    if root is None:
        raise ValueError(f"Cargo.lock does not contain the native root package {root_name}")
    direct = _manifest_dependency_names(manifest, ("dependencies", "build-dependencies"))
    root_dependencies = {
        require_str(value, "native root locked dependency").split(" ", 1)[0]
        for value in require_list(root.get("dependencies"), "native root dependencies")
    }
    if not direct <= root_dependencies:
        raise ValueError(
            f"Cargo.lock omits production dependencies: {sorted(direct - root_dependencies)}"
        )

    selected: dict[str, Mapping[str, object]] = {}
    pending = sorted(direct, reverse=True)
    while pending:
        name = pending.pop()
        if name in selected:
            continue
        package = locked.get(name)
        if package is None:
            raise ValueError(f"Cargo.lock dependency is dangling: {name}")
        selected[name] = package
        dependencies = require_list(
            package.get("dependencies", []),
            f"Cargo.lock {name} dependencies",
        )
        pending.extend(
            require_str(value, f"Cargo.lock {name} dependency").split(" ", 1)[0]
            for value in dependencies
        )
    return [selected[name] for name in sorted(selected)]


def _cargo_packages(root: Path) -> list[dict[str, object]]:
    pyproject = load_toml(root / "pyproject.toml")
    tool = require_mapping(pyproject.get("tool"), "pyproject tool")
    pyhermit = require_mapping(tool.get("pyhermit"), "pyproject tool.pyhermit")
    inventory_path = root / require_str(
        pyhermit.get("rust_production_license_manifest"),
        "tool.pyhermit.rust_production_license_manifest",
    )
    inventory = load_toml(inventory_path)
    if require_int(inventory.get("schema"), "Rust license inventory schema") != 1:
        raise ValueError("Rust license inventory schema must be 1")
    if require_str(inventory.get("closure"), "Rust dependency closure") != "normal-and-build":
        raise ValueError("Rust license inventory must describe the normal-and-build closure")
    manifest_path = root / require_str(inventory.get("manifest"), "Rust manifest path")
    lock_path = root / require_str(inventory.get("lockfile"), "Rust lockfile path")
    root_name = require_str(inventory.get("root"), "Rust root package")
    production = _production_lock_packages(
        load_toml(manifest_path),
        load_toml(lock_path),
        root_name,
    )
    audited: dict[tuple[str, str], tuple[str, str]] = {}
    for raw in require_list(inventory.get("package"), "Rust license inventory package"):
        audited_package = require_mapping(raw, "Rust license inventory package item")
        name = require_str(audited_package.get("name"), "audited Rust package name")
        version = require_str(audited_package.get("version"), "audited Rust package version")
        checksum = require_str(audited_package.get("checksum"), "audited Rust package checksum")
        license_expression = require_str(
            audited_package.get("license"), "audited Rust package license"
        )
        key = (name, version)
        if key in audited:
            raise ValueError(f"duplicate audited Rust package: {name} {version}")
        if not re.fullmatch(r"[0-9a-f]{64}", checksum):
            raise ValueError(f"invalid audited Rust checksum: {name} {version}")
        if license_expression == "NOASSERTION":
            raise ValueError(f"Rust package has no declared license: {name} {version}")
        audited[key] = (checksum, license_expression)

    locked_keys = {
        (
            require_str(package.get("name"), "locked production package name"),
            require_str(package.get("version"), "locked production package version"),
        )
        for package in production
    }
    if set(audited) != locked_keys:
        raise ValueError(
            "Rust license inventory differs from the locked production closure; "
            f"missing={sorted(locked_keys - audited.keys())}, "
            f"extra={sorted(audited.keys() - locked_keys)}"
        )

    packages: list[dict[str, object]] = []
    for locked_package in production:
        name = require_str(locked_package.get("name"), "Cargo package name")
        version = require_str(locked_package.get("version"), "Cargo package version")
        source = require_str(locked_package.get("source"), f"Cargo package source for {name}")
        checksum = require_str(locked_package.get("checksum"), f"Cargo package checksum for {name}")
        audited_checksum, license_expression = audited[(name, version)]
        if source != _CRATES_IO_INDEX:
            raise ValueError(f"production Rust package has an unaudited source: {name} {source}")
        if checksum != audited_checksum:
            raise ValueError(f"Rust package checksum differs from its audit: {name} {version}")
        record: dict[str, object] = {
            "SPDXID": _spdx_id(name, version),
            "name": name,
            "versionInfo": version,
            "downloadLocation": f"https://crates.io/api/v1/crates/{name}/{version}/download",
            "copyrightText": "NOASSERTION",
            "filesAnalyzed": False,
            "licenseConcluded": license_expression,
            "licenseDeclared": license_expression,
            "primaryPackagePurpose": "LIBRARY",
            "checksums": [{"algorithm": "SHA256", "checksumValue": checksum}],
            "externalRefs": [
                {
                    "referenceCategory": "PACKAGE-MANAGER",
                    "referenceType": "purl",
                    "referenceLocator": f"pkg:cargo/{name}@{version}",
                }
            ],
        }
        packages.append(record)
    return sorted(packages, key=lambda item: (str(item["name"]), str(item["versionInfo"])))


def verify_cargo_metadata(root: Path) -> int:
    """Match the audited lock traversal to Cargo's independent normal/build graph."""

    command = [
        os.environ.get("CARGO", "cargo"),
        "metadata",
        "--manifest-path",
        str(root / "native/Cargo.toml"),
        "--locked",
        "--format-version",
        "1",
    ]
    completed = subprocess.run(
        command,
        cwd=root,
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        details = completed.stderr.strip() or completed.stdout.strip()
        raise ValueError(f"Cargo metadata could not verify the Rust production closure: {details}")
    try:
        metadata = require_mapping(json.loads(completed.stdout), "Cargo metadata")
    except json.JSONDecodeError as error:
        raise ValueError("Cargo metadata returned malformed JSON") from error
    resolve = require_mapping(metadata.get("resolve"), "Cargo metadata resolve")
    root_id = require_str(resolve.get("root"), "Cargo metadata root")
    nodes = {
        require_str(node.get("id"), "Cargo metadata node ID"): node
        for node in (
            require_mapping(raw, "Cargo metadata node")
            for raw in require_list(resolve.get("nodes"), "Cargo metadata nodes")
        )
    }
    metadata_packages = {
        require_str(package.get("id"), "Cargo metadata package ID"): package
        for package in (
            require_mapping(raw, "Cargo metadata package")
            for raw in require_list(metadata.get("packages"), "Cargo metadata packages")
        )
    }
    selected: set[str] = set()
    pending = [root_id]
    while pending:
        package_id = pending.pop()
        if package_id in selected:
            continue
        node = nodes.get(package_id)
        if node is None:
            raise ValueError(f"Cargo metadata dependency node is dangling: {package_id}")
        selected.add(package_id)
        for raw in require_list(node.get("deps"), f"Cargo metadata {package_id} dependencies"):
            dependency = require_mapping(raw, "Cargo metadata dependency")
            kinds = [
                require_mapping(value, "Cargo metadata dependency kind")
                for value in require_list(
                    dependency.get("dep_kinds"),
                    "Cargo metadata dependency kinds",
                )
            ]
            if any(kind.get("kind") != "dev" for kind in kinds):
                pending.append(require_str(dependency.get("pkg"), "Cargo metadata dependency ID"))

    root_package = metadata_packages.get(root_id)
    if root_package is None:
        raise ValueError("Cargo metadata omits its root package")
    root_key = (
        require_str(root_package.get("name"), "Cargo metadata root name"),
        require_str(root_package.get("version"), "Cargo metadata root version"),
    )
    actual: dict[tuple[str, str], str] = {}
    license_aliases = {"MIT/Apache-2.0": "MIT OR Apache-2.0"}
    for package_id in selected:
        package = metadata_packages.get(package_id)
        if package is None:
            raise ValueError(f"Cargo metadata package is dangling: {package_id}")
        key = (
            require_str(package.get("name"), "Cargo metadata package name"),
            require_str(package.get("version"), "Cargo metadata package version"),
        )
        if key == root_key:
            continue
        license_expression = require_str(
            package.get("license"),
            f"Cargo metadata package license for {key[0]}",
        )
        actual[key] = license_aliases.get(license_expression, license_expression)

    audited = {
        (str(package["name"]), str(package["versionInfo"])): str(package["licenseDeclared"])
        for package in _cargo_packages(root)
    }
    if actual != audited:
        license_mismatches = sorted(
            key for key in actual.keys() & audited.keys() if actual[key] != audited[key]
        )
        raise ValueError(
            "Cargo metadata differs from the audited Rust production closure; "
            f"missing={sorted(actual.keys() - audited.keys())}, "
            f"extra={sorted(audited.keys() - actual.keys())}, "
            f"licenses={license_mismatches}"
        )
    return len(actual)


def create_sbom(root: Path, namespace: str) -> dict[str, object]:
    """Return a deterministic SPDX document for the Python and locked Rust components."""

    if not namespace.startswith("https://") or any(character.isspace() for character in namespace):
        raise ValueError("SBOM namespace must be a whitespace-free HTTPS URL")
    version = _runtime_version((root / "src/pyhermit/_version.py").read_bytes())
    root_id = _spdx_id("pyHermiT", version)
    core_id = _spdx_id("pyowl-core", ">=0.1,<0.2")
    packages: list[dict[str, object]] = [
        {
            "SPDXID": root_id,
            "name": "pyHermiT",
            "versionInfo": version,
            "downloadLocation": "https://github.com/OAEI-ML/pyHermiT",
            "copyrightText": "NOASSERTION",
            "filesAnalyzed": False,
            "licenseConcluded": "LGPL-3.0-or-later",
            "licenseDeclared": "LGPL-3.0-or-later",
            "primaryPackagePurpose": "LIBRARY",
            "externalRefs": [
                {
                    "referenceCategory": "PACKAGE-MANAGER",
                    "referenceType": "purl",
                    "referenceLocator": f"pkg:pypi/pyhermit@{version}",
                }
            ],
        },
        {
            "SPDXID": core_id,
            "name": "pyowl-core",
            "versionInfo": ">=0.1,<0.2",
            "downloadLocation": "https://github.com/OAEI-ML/pyOWLCore",
            "copyrightText": "NOASSERTION",
            "filesAnalyzed": False,
            "licenseConcluded": "Apache-2.0",
            "licenseDeclared": "Apache-2.0",
            "primaryPackagePurpose": "LIBRARY",
        },
    ]
    cargo = _cargo_packages(root)
    packages.extend(cargo)
    relationships = [
        {
            "spdxElementId": "SPDXRef-DOCUMENT",
            "relationshipType": "DESCRIBES",
            "relatedSpdxElement": root_id,
        },
        {
            "spdxElementId": root_id,
            "relationshipType": "DEPENDS_ON",
            "relatedSpdxElement": core_id,
        },
    ]
    relationships.extend(
        {
            "spdxElementId": root_id,
            "relationshipType": "DEPENDS_ON",
            "relatedSpdxElement": str(package["SPDXID"]),
        }
        for package in cargo
    )
    return {
        "SPDXID": "SPDXRef-DOCUMENT",
        "spdxVersion": "SPDX-2.3",
        "dataLicense": "CC0-1.0",
        "name": f"pyHermiT-{version}-release-sbom",
        "documentNamespace": namespace,
        "creationInfo": {
            "created": "2000-01-01T00:00:00Z",
            "creators": ["Tool: pyHermiT-WPP0-SPDX-generator"],
        },
        "packages": packages,
        "relationships": relationships,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--namespace", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--verify-cargo-metadata",
        action="store_true",
        help="independently compare the audited closure with locked Cargo metadata",
    )
    args = parser.parse_args(argv)
    try:
        if args.verify_cargo_metadata:
            verify_cargo_metadata(repository_root())
        document = create_sbom(repository_root(), args.namespace)
        args.output.write_text(
            json.dumps(document, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    except (OSError, ValueError) as error:
        print(f"SBOM generation failed: {error}")
        return 1
    print(f"SPDX SBOM written: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
