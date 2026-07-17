"""Independent reader/materializer for the pinned W3C OWL 2 test export.

This module uses only the public RDF vocabulary represented in ``all.rdf``.  It neither imports
nor copies the upstream Java/AGPL-era harness.  Inventories contain identifiers and content
hashes, never the ontology bodies whose redistribution status has not been established.
"""

from __future__ import annotations

import argparse
import json
import xml.etree.ElementTree as ET
from collections import Counter
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from tools.reference._util import sha256_bytes, sha256_file, write_json

ALL_RDF_SHA256 = "a703d36b774f55f14c0758cf20f2bdd635677045f7ba55053199660c10d6fefc"
RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
TEST = "http://www.w3.org/2007/OWL/testOntology#"
CHECK_TYPES = (
    "ConsistencyTest",
    "InconsistencyTest",
    "PositiveEntailmentTest",
    "NegativeEntailmentTest",
)
BODY_FIELDS = (
    "fsPremiseOntology",
    "fsConclusionOntology",
    "rdfXmlPremiseOntology",
    "rdfXmlConclusionOntology",
)


def _resources(element: ET.Element, name: str) -> set[str]:
    return {
        child.attrib[f"{{{RDF}}}resource"]
        for child in element.findall(f"{{{TEST}}}{name}")
        if f"{{{RDF}}}resource" in child.attrib
    }


def _local(value: str) -> str:
    return value.rsplit("#", 1)[-1]


def _body_metadata(case: ET.Element) -> dict[str, Any]:
    bodies: dict[str, Any] = {}
    for field in BODY_FIELDS:
        child = case.find(f"{{{TEST}}}{field}")
        if child is not None and child.text is not None:
            encoded = child.text.encode("utf-8")
            bodies[field] = {"bytes": len(encoded), "sha256": sha256_bytes(encoded)}
    return bodies


def parse_export(path: Path) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    actual_hash = sha256_file(path)
    if actual_hash != ALL_RDF_SHA256:
        raise ValueError(f"all.rdf SHA-256 mismatch: {actual_hash}")
    root = ET.parse(path).getroot()
    cases: list[dict[str, Any]] = []
    checks: list[dict[str, Any]] = []
    for case in root.findall(f"{{{TEST}}}TestCase"):
        case_iri = case.attrib.get(f"{{{RDF}}}about")
        if not case_iri:
            continue
        statuses = _resources(case, "status")
        semantics = _resources(case, "semantics")
        species = _resources(case, "species")
        if (
            f"{TEST}Approved" not in statuses
            or f"{TEST}DIRECT" not in semantics
            or f"{TEST}DL" not in species
        ):
            continue
        types = sorted(
            _local(child.attrib[f"{{{RDF}}}resource"])
            for child in case.findall(f"{{{RDF}}}type")
            if f"{{{RDF}}}resource" in child.attrib
        )
        identifier_element = case.find(f"{{{TEST}}}identifier")
        identifier = identifier_element.text if identifier_element is not None else None
        bodies = _body_metadata(case)
        case_checks = [kind for kind in CHECK_TYPES if kind in types]
        record = {
            "iri": case_iri,
            "identifier": identifier,
            "check_types": case_checks,
            "normative_syntax": sorted(
                _local(value) for value in _resources(case, "normativeSyntax")
            ),
            "body_metadata": bodies,
        }
        cases.append(record)
        for kind in case_checks:
            checks.append(
                {
                    "id": f"{case_iri}#{kind}",
                    "case_iri": case_iri,
                    "kind": kind,
                    "expected": {
                        "ConsistencyTest": "SAT",
                        "InconsistencyTest": "UNSAT",
                        "PositiveEntailmentTest": "ENTAILED",
                        "NegativeEntailmentTest": "NOT_ENTAILED",
                    }[kind],
                    "body_metadata": bodies,
                }
            )
    cases.sort(key=lambda item: item["iri"])
    checks.sort(key=lambda item: item["id"])
    if len(cases) != 266 or len(checks) != 350:
        raise ValueError(f"pinned W3C counts changed: cases={len(cases)}, checks={len(checks)}")
    return cases, checks


def build_inventory(path: Path) -> dict[str, Any]:
    cases, checks = parse_export(path)
    check_counts = Counter(check["kind"] for check in checks)
    return {
        "schema_version": "1.0",
        "source": {
            "path_at_reference": (
                "src/test/resources/org/semanticweb/HermiT/owl_wg_tests/ontologies/all.rdf"
            ),
            "sha256": sha256_file(path),
            "acquisition": "fetch-only; redistribution rights unresolved",
        },
        "selection": {
            "status": f"{TEST}Approved",
            "semantics": f"{TEST}DIRECT",
            "species": f"{TEST}DL",
        },
        "counts": {
            "cases": len(cases),
            "checks": len(checks),
            "check_types": dict(sorted(check_counts.items())),
        },
        # Every check is represented by the unique (case IRI, check type) pair in each case.
        # Keeping it there avoids duplicating 350 rows and their body hashes.
        "cases": cases,
    }


@dataclass(frozen=True)
class MaterializedCheck:
    check_id: str
    kind: str
    expected: str
    premise: bytes
    premise_suffix: str
    conclusion: bytes | None
    conclusion_suffix: str | None


def _materialize_element(case: ET.Element, kind: str) -> MaterializedCheck:
    case_iri = case.attrib.get(f"{{{RDF}}}about", "")
    check_id = f"{case_iri}#{kind}"
    functional = case.find(f"{{{TEST}}}fsPremiseOntology")
    rdfxml = case.find(f"{{{TEST}}}rdfXmlPremiseOntology")
    premise_element = functional if functional is not None else rdfxml
    if premise_element is None or premise_element.text is None:
        raise ValueError(f"selected check has no premise body: {check_id}")
    conclusion_element = case.find(f"{{{TEST}}}fsConclusionOntology")
    conclusion_suffix = ".ofn"
    if conclusion_element is None:
        conclusion_element = case.find(f"{{{TEST}}}rdfXmlConclusionOntology")
        conclusion_suffix = ".rdf"
    return MaterializedCheck(
        check_id=check_id,
        kind=kind,
        expected={
            "ConsistencyTest": "SAT",
            "InconsistencyTest": "UNSAT",
            "PositiveEntailmentTest": "ENTAILED",
            "NegativeEntailmentTest": "NOT_ENTAILED",
        }[kind],
        premise=premise_element.text.encode("utf-8"),
        premise_suffix=".ofn" if functional is not None else ".rdf",
        conclusion=(
            conclusion_element.text.encode("utf-8")
            if conclusion_element is not None and conclusion_element.text is not None
            else None
        ),
        conclusion_suffix=conclusion_suffix if conclusion_element is not None else None,
    )


def materialize_check(path: Path, check_id: str) -> MaterializedCheck:
    """Extract one case in memory/on explicit request; never writes into the repository."""

    # Verify the same selection/count invariants before extracting content.
    _cases, checks = parse_export(path)
    if check_id not in {check["id"] for check in checks}:
        raise KeyError(check_id)
    case_iri, kind = check_id.rsplit("#", 1)
    root = ET.parse(path).getroot()
    for case in root.findall(f"{{{TEST}}}TestCase"):
        if case.attrib.get(f"{{{RDF}}}about") == case_iri:
            return _materialize_element(case, kind)
    raise KeyError(check_id)


CheckRunner = Callable[[MaterializedCheck], str]


def execute_checks(
    path: Path,
    runner: CheckRunner,
    *,
    check_ids: Iterable[str] | None = None,
) -> list[dict[str, Any]]:
    """Execute selected manifest checks through a backend-neutral callback.

    The callback receives bytes plus expected result and returns one of ``SAT``, ``UNSAT``,
    ``ENTAILED``, or ``NOT_ENTAILED``.  This keeps manifest semantics independent of both the
    historical Java harness and any particular pyHermiT backend.
    """

    _cases, checks = parse_export(path)
    selected = set(check_ids) if check_ids is not None else {check["id"] for check in checks}
    known = {check["id"] for check in checks}
    unknown = selected - known
    if unknown:
        raise KeyError(f"unknown W3C check ids: {sorted(unknown)}")
    root = ET.parse(path).getroot()
    elements = {
        case.attrib[f"{{{RDF}}}about"]: case
        for case in root.findall(f"{{{TEST}}}TestCase")
        if f"{{{RDF}}}about" in case.attrib
    }
    results: list[dict[str, Any]] = []
    for check in checks:
        if check["id"] not in selected:
            continue
        materialized = _materialize_element(elements[check["case_iri"]], check["kind"])
        try:
            observed = runner(materialized)
            status = "PASS" if observed == materialized.expected else "FAIL"
            results.append(
                {
                    "check_id": materialized.check_id,
                    "expected": materialized.expected,
                    "observed": observed,
                    "status": status,
                }
            )
        except Exception as error:  # runner boundary: preserve one result per check
            results.append(
                {
                    "check_id": materialized.check_id,
                    "expected": materialized.expected,
                    "status": "ERROR",
                    "error_type": type(error).__name__,
                }
            )
    return results


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("all_rdf", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    inventory = build_inventory(args.all_rdf)
    if args.output:
        write_json(args.output, inventory)
    else:
        print(json.dumps(inventory, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
