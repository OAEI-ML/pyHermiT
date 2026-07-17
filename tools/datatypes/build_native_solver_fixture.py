"""Build WPR3's shared Python/Rust datatype-component fixture.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import argparse
import json
import random
from pathlib import Path
from typing import Any

import pyowl_core.model as owl

from pyhermit.datatypes import (
    XSD_BOOLEAN,
    XSD_INTEGER,
    XSD_STRING,
    DataDomainRange,
    DatatypeConstraintComponent,
    DomainCardinalityConstraint,
    EqualityConstraint,
    FixedValueConstraint,
    InequalityConstraint,
    RangeConstraint,
    compile_literal,
    compile_literal_semantic_payload,
    solve_datatype_constraints,
    solve_datatype_constraints_exhaustive,
)

DEFAULT_OUTPUT = Path("tests/data/datatypes/wpr3-native-solver-v1.json")
SEED = 0x57A3_2026


def _literal(lexical: str, datatype_iri: str) -> owl.Literal:
    return owl.Literal(lexical, owl.Datatype(owl.IRI(datatype_iri)))


def _palette() -> tuple[Any, ...]:
    sources = (
        ("-2", XSD_INTEGER),
        ("-1", XSD_INTEGER),
        ("-0", XSD_INTEGER),
        ("0", XSD_INTEGER),
        ("01", XSD_INTEGER),
        ("+1", XSD_INTEGER),
        ("2", XSD_INTEGER),
        ("3", XSD_INTEGER),
        ("4", XSD_INTEGER),
        ("true", XSD_BOOLEAN),
        ("false", XSD_BOOLEAN),
        ("alpha", XSD_STRING),
        ("beta", XSD_STRING),
    )
    return tuple(compile_literal(_literal(*source)) for source in sources)


def _record(variable: int, dependencies: list[int], **values: Any) -> dict[str, Any]:
    return {"dependencies": dependencies, "variable": variable, **values}


def _binary(left: int, right: int, dependencies: list[int]) -> dict[str, Any]:
    return {"dependencies": dependencies, "left": left, "right": right}


def _blank(name: str, count: int) -> dict[str, Any]:
    return {
        "cardinalities": [],
        "domains": [],
        "equalities": [],
        "fixed_values": [],
        "inequalities": [],
        "name": name,
        "variables": list(range(count)),
    }


def _crafted_cases() -> list[dict[str, Any]]:
    cases: list[dict[str, Any]] = []

    case = _blank("equality-inequality", 2)
    case["equalities"].append(_binary(0, 1, [1]))
    case["inequalities"].append(_binary(0, 1, [2]))
    cases.append(case)

    case = _blank("conflicting-fixed-values", 2)
    case["equalities"].append(_binary(0, 1, [3]))
    case["fixed_values"].extend(
        [_record(0, [4], value=2), _record(1, [5], value=4)]
    )
    cases.append(case)

    case = _blank("empty-domain-intersection", 1)
    case["domains"].extend(
        [
            _record(0, [6], kind="finite", values=[2]),
            _record(0, [7], kind="finite", values=[4]),
        ]
    )
    cases.append(case)

    case = _blank("fixed-outside-domain", 1)
    case["domains"].append(_record(0, [8], kind="finite", values=[2]))
    case["fixed_values"].append(_record(0, [9], value=4))
    cases.append(case)

    case = _blank("insufficient-cardinality", 1)
    case["domains"].append(_record(0, [10], kind="finite", values=[2, 4]))
    case["cardinalities"].append(_record(0, [11], minimum=3))
    cases.append(case)

    case = _blank("fixed-neighbours-share-an-identity", 2)
    case["fixed_values"].extend(
        [_record(0, [12], value=4), _record(1, [13], value=5)]
    )
    case["inequalities"].append(_binary(0, 1, [14]))
    cases.append(case)

    for name, colours in (("two-colour-triangle", [2, 4]), ("three-colour-triangle", [2, 4, 6])):
        case = _blank(name, 3)
        for variable in case["variables"]:
            case["domains"].append(
                _record(variable, [20 + variable], kind="finite", values=colours)
            )
        case["inequalities"].extend(
            [_binary(0, 1, [30]), _binary(1, 2, [31]), _binary(0, 2, [32])]
        )
        cases.append(case)

    case = _blank("unbounded-complement-domain", 2)
    case["domains"].append(
        _record(0, [40], kind="complement-finite", values=[2, 4])
    )
    case["inequalities"].append(_binary(0, 1, [41]))
    case["cardinalities"].append(_record(0, [42], minimum=4_294_967_295))
    cases.append(case)

    case = _blank("duplicate-edge-selects-smallest-dependency-set", 2)
    case["fixed_values"].extend(
        [_record(0, [43], value=4), _record(1, [44], value=5)]
    )
    case["inequalities"].extend(
        [_binary(0, 1, [50, 51]), _binary(0, 1, [49])]
    )
    cases.append(case)

    case = _blank("elimination-preserves-minimal-active-clash", 4)
    for variable in range(3):
        case["domains"].append(
            _record(variable, [60 + variable], kind="finite", values=[2, 4])
        )
    case["domains"].append(
        _record(3, [63], kind="finite", values=[2, 4, 6, 7])
    )
    case["inequalities"].extend(
        [
            _binary(0, 1, [64]),
            _binary(1, 2, [65]),
            _binary(0, 2, [66]),
            _binary(0, 3, [67]),
        ]
    )
    cases.append(case)

    case = _blank("complement-excludes-fixed-value", 1)
    case["domains"].append(
        _record(0, [70], kind="complement-finite", values=[4])
    )
    case["fixed_values"].append(_record(0, [71], value=5))
    cases.append(case)

    case = _blank("lexical-aliases-share-data-identity", 2)
    case["equalities"].append(_binary(0, 1, [72]))
    case["fixed_values"].extend(
        [_record(0, [73], value=2), _record(1, [74], value=3)]
    )
    cases.append(case)

    case = _blank("explicit-empty-enumeration", 1)
    case["domains"].append(_record(0, [75], kind="finite", values=[]))
    cases.append(case)
    return cases


def _random_finite_cases(rng: random.Random, count: int) -> list[dict[str, Any]]:
    cases: list[dict[str, Any]] = []
    palette_indexes = list(range(13))
    for index in range(count):
        size = rng.randint(1, 6)
        case = _blank(f"generated-finite-{index:03d}", size)
        dependency = 1_000 + index * 100
        for variable in case["variables"]:
            value_count = rng.randint(0, 5)
            values = sorted(rng.sample(palette_indexes, value_count))
            case["domains"].append(
                _record(variable, [dependency], kind="finite", values=values)
            )
            dependency += 1
            if rng.random() < 0.18:
                second_count = rng.randint(0, 4)
                second = sorted(rng.sample(palette_indexes, second_count))
                case["domains"].append(
                    _record(variable, [dependency], kind="finite", values=second)
                )
                dependency += 1
            if rng.random() < 0.22:
                case["fixed_values"].append(
                    _record(variable, [dependency], value=rng.choice(palette_indexes))
                )
                dependency += 1
            if rng.random() < 0.24:
                case["cardinalities"].append(
                    _record(variable, [dependency], minimum=rng.randint(0, 6))
                )
                dependency += 1
        for left in range(size):
            for right in range(left + 1, size):
                if rng.random() < 0.12:
                    case["equalities"].append(_binary(left, right, [dependency]))
                    dependency += 1
                if rng.random() < 0.32:
                    case["inequalities"].append(_binary(left, right, [dependency]))
                    dependency += 1
        cases.append(case)
    return cases


def _random_complement_cases(rng: random.Random, count: int) -> list[dict[str, Any]]:
    cases: list[dict[str, Any]] = []
    palette_indexes = list(range(13))
    for index in range(count):
        size = rng.randint(1, 7)
        case = _blank(f"generated-complement-{index:03d}", size)
        dependency = 100_000 + index * 100
        for variable in case["variables"]:
            excluded = sorted(rng.sample(palette_indexes, rng.randint(0, 4)))
            case["domains"].append(
                _record(
                    variable,
                    [dependency],
                    kind="complement-finite",
                    values=excluded,
                )
            )
            dependency += 1
            if rng.random() < 0.20:
                finite = sorted(rng.sample(palette_indexes, rng.randint(0, 5)))
                case["domains"].append(
                    _record(variable, [dependency], kind="finite", values=finite)
                )
                dependency += 1
            if rng.random() < 0.20:
                case["fixed_values"].append(
                    _record(variable, [dependency], value=rng.choice(palette_indexes))
                )
                dependency += 1
            if rng.random() < 0.20:
                case["cardinalities"].append(
                    _record(variable, [dependency], minimum=rng.randint(0, 8))
                )
                dependency += 1
        for left in range(size):
            for right in range(left + 1, size):
                if rng.random() < 0.10:
                    case["equalities"].append(_binary(left, right, [dependency]))
                    dependency += 1
                if rng.random() < 0.34:
                    case["inequalities"].append(_binary(left, right, [dependency]))
                    dependency += 1
        cases.append(case)
    return cases


def _component(case: dict[str, Any], palette: tuple[Any, ...]) -> DatatypeConstraintComponent:
    ranges = tuple(
        RangeConstraint(
            constraint["variable"],
            DataDomainRange.enumeration(palette[index] for index in constraint["values"]),
            positive=constraint["kind"] == "finite",
            dependencies=frozenset(constraint["dependencies"]),
        )
        for constraint in case["domains"]
    )
    return DatatypeConstraintComponent(
        variables=tuple(case["variables"]),
        ranges=ranges,
        fixed_values=tuple(
            FixedValueConstraint(
                value["variable"],
                palette[value["value"]],
                frozenset(value["dependencies"]),
            )
            for value in case["fixed_values"]
        ),
        equalities=tuple(
            EqualityConstraint(
                value["left"],
                value["right"],
                frozenset(value["dependencies"]),
            )
            for value in case["equalities"]
        ),
        inequalities=tuple(
            InequalityConstraint(
                value["left"],
                value["right"],
                frozenset(value["dependencies"]),
            )
            for value in case["inequalities"]
        ),
        cardinalities=tuple(
            DomainCardinalityConstraint(
                value["variable"],
                value["minimum"],
                frozenset(value["dependencies"]),
            )
            for value in case["cardinalities"]
        ),
    )


def _expected(case: dict[str, Any], palette: tuple[Any, ...]) -> dict[str, Any]:
    component = _component(case, palette)
    result = solve_datatype_constraints(component)
    if all(value["kind"] == "finite" for value in case["domains"]):
        exhaustive = solve_datatype_constraints_exhaustive(component)
        if result.satisfiable != exhaustive.satisfiable:
            raise AssertionError(f"optimized/exhaustive disagreement for {case['name']}")
    if result.clash is None:
        return {"clash": None, "satisfiable": True}
    return {
        "clash": {
            "dependencies": sorted(result.clash.dependencies),
            "kind": str(result.clash.kind),
            "variables": list(result.clash.variables),
        },
        "satisfiable": False,
    }


def build_fixture() -> dict[str, Any]:
    palette = _palette()
    rng = random.Random(SEED)
    cases = [
        *_crafted_cases(),
        *_random_finite_cases(rng, 256),
        *_random_complement_cases(rng, 96),
    ]
    for case in cases:
        case["expected"] = _expected(case, palette)
    literals = [
        {
            "payload_json": compile_literal_semantic_payload(value).canonical_bytes().decode(),
            "source_literal_id": index,
        }
        for index, value in enumerate(palette)
    ]
    return {
        "case_count": len(cases),
        "cases": cases,
        "generator_seed": SEED,
        "literal_count": len(literals),
        "literals": literals,
        "schema_version": 1,
    }


def canonical_bytes() -> bytes:
    return (
        json.dumps(build_fixture(), ensure_ascii=False, separators=(",", ":"), sort_keys=True)
        + "\n"
    ).encode()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    generated = canonical_bytes()
    if arguments.check:
        return 0 if arguments.output.read_bytes() == generated else 1
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_bytes(generated)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
