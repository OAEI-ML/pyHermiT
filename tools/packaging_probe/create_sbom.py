"""Create a deterministic SPDX 2.3 SBOM from pyHermiT's locked dependency inputs."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections.abc import Mapping, Sequence
from pathlib import Path

from tools.packaging_probe.check_artifact import _runtime_version
from tools.specs._compat import (
    load_toml,
    repository_root,
    require_list,
    require_mapping,
    require_str,
)


def _spdx_id(name: str, version: str) -> str:
    token = re.sub(r"[^A-Za-z0-9.-]", "-", f"{name}-{version}")
    digest = hashlib.sha256(f"{name}\0{version}".encode()).hexdigest()[:12]
    return f"SPDXRef-Package-{token}-{digest}"


def _cargo_packages(lock: Mapping[str, object]) -> list[dict[str, object]]:
    packages: list[dict[str, object]] = []
    for raw in require_list(lock.get("package"), "Cargo.lock package"):
        package = require_mapping(raw, "Cargo.lock package item")
        name = require_str(package.get("name"), "Cargo package name")
        version = require_str(package.get("version"), "Cargo package version")
        source = package.get("source")
        checksum = package.get("checksum")
        record: dict[str, object] = {
            "SPDXID": _spdx_id(name, version),
            "name": name,
            "versionInfo": version,
            "downloadLocation": source.removeprefix("registry+")
            if isinstance(source, str)
            else "NOASSERTION",
            "copyrightText": "NOASSERTION",
            "filesAnalyzed": False,
            "licenseConcluded": "NOASSERTION",
            "licenseDeclared": "NOASSERTION",
            "primaryPackagePurpose": "LIBRARY",
        }
        if isinstance(checksum, str) and re.fullmatch(r"[0-9a-f]{64}", checksum):
            record["checksums"] = [{"algorithm": "SHA256", "checksumValue": checksum}]
        if isinstance(source, str) and source.startswith("registry+"):
            record["externalRefs"] = [
                {
                    "referenceCategory": "PACKAGE-MANAGER",
                    "referenceType": "purl",
                    "referenceLocator": f"pkg:cargo/{name}@{version}",
                }
            ]
        packages.append(record)
    return sorted(packages, key=lambda item: (str(item["name"]), str(item["versionInfo"])))


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
    cargo = _cargo_packages(load_toml(root / "native/Cargo.lock"))
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
    args = parser.parse_args(argv)
    try:
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
