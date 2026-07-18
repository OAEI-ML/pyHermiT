"""Build the WPR3 Python/Rust semantic datatype-component oracle.

SPDX-License-Identifier: LGPL-3.0-or-later

The fixture is produced only through the production semantic-model adapter and exact
Python component solver.  It deliberately mixes dense range IDs, custom aliases,
negative assertions, fixed lexical aliases, finite colouring, infinite elimination,
and private symbolic witnesses.
"""

from __future__ import annotations

import argparse
import json
import random
from pathlib import Path
from typing import Any

import pyowl_core.model as owl

from pyhermit.datatypes import (
    OWL_RATIONAL,
    OWL_REAL,
    XSD_BOOLEAN,
    XSD_DECIMAL,
    XSD_INTEGER,
    XSD_MAX_INCLUSIVE,
    XSD_MIN_INCLUSIVE,
    XSD_STRING,
    DatatypeConstraintSolver,
    DomainCardinalityConstraint,
    EqualityConstraint,
    InequalityConstraint,
    SemanticDatatypeConstraintComponent,
    SemanticFixedValueConstraint,
    SemanticRangeConstraint,
    SymbolicDataWitness,
    compile_datatype_constraint_component,
    compile_datatype_semantic_model,
    compile_literal_semantic_payload,
)

DEFAULT_OUTPUT = Path("tests/data/datatypes/wpr3-native-semantic-solver-v1.json")
SEED = 0x5E6A_2026

SMALL = "urn:pyhermit:semantic-solver:small"
WITHOUT_ONE = "urn:pyhermit:semantic-solver:without-one"
NESTED_ALIAS = "urn:pyhermit:semantic-solver:nested-alias"


def _datatype(iri: str) -> owl.Datatype:
    return owl.Datatype(owl.IRI(iri))


def _literal(lexical: str, datatype_iri: str) -> owl.Literal:
    return owl.Literal(lexical, _datatype(datatype_iri))


def _facet(iri: str, lexical: str) -> owl.FacetRestriction:
    return owl.FacetRestriction(owl.IRI(iri), _literal(lexical, XSD_INTEGER))


def _bounded_integer(lower: str, upper: str) -> owl.DatatypeRestriction:
    return owl.DatatypeRestriction(
        _datatype(XSD_INTEGER),
        owl.CanonicalSet(
            (
                _facet(XSD_MIN_INCLUSIVE, lower),
                _facet(XSD_MAX_INCLUSIVE, upper),
            )
        ),
    )


def _one_of(*values: tuple[str, str]) -> owl.DataOneOf:
    return owl.DataOneOf(
        owl.CanonicalSet(tuple(_literal(lexical, datatype) for lexical, datatype in values))
    )


def _intersection(*values: owl.DataRange) -> owl.DataIntersectionOf:
    return owl.DataIntersectionOf(owl.CanonicalSet(values))


def _union(*values: owl.DataRange) -> owl.DataUnionOf:
    return owl.DataUnionOf(owl.CanonicalSet(values))


def _model() -> tuple[Any, tuple[str, ...]]:
    zero_one = _one_of(("0", XSD_INTEGER), ("1", XSD_INTEGER))
    true_only = _one_of(("true", XSD_BOOLEAN))
    mixed_three = _one_of(
        ("0", XSD_INTEGER),
        ("false", XSD_BOOLEAN),
        ("a", XSD_STRING),
    )
    aliases_one = _one_of(("1", XSD_INTEGER), ("1.0", XSD_DECIMAL))
    aliases_zero = _one_of(("0", XSD_INTEGER), ("-0", XSD_INTEGER))
    definitions = (
        owl.DatatypeDefinition(_datatype(SMALL), _bounded_integer("0", "3")),
        owl.DatatypeDefinition(
            _datatype(WITHOUT_ONE),
            _intersection(
                _datatype(SMALL),
                owl.DataComplementOf(_one_of(("1", XSD_INTEGER))),
            ),
        ),
        owl.DatatypeDefinition(_datatype(NESTED_ALIAS), _datatype(WITHOUT_ONE)),
    )
    labels = (
        "boolean",
        "zero-one",
        "true-only",
        "zero-through-two",
        "integer",
        "string",
        "mixed-three",
        "mixed-infinite",
        "nested-numeric-alias",
        "nonrational-real",
        "integer-string-empty",
        "not-boolean",
        "aliases-one",
        "aliases-zero",
    )
    roots: tuple[owl.DataRange, ...] = (
        _datatype(XSD_BOOLEAN),
        zero_one,
        true_only,
        _bounded_integer("0", "2"),
        _datatype(XSD_INTEGER),
        _datatype(XSD_STRING),
        mixed_three,
        _union(_datatype(XSD_INTEGER), _datatype(XSD_STRING)),
        _datatype(NESTED_ALIAS),
        _intersection(
            _datatype(OWL_REAL),
            owl.DataComplementOf(_datatype(OWL_RATIONAL)),
        ),
        _intersection(_datatype(XSD_INTEGER), _datatype(XSD_STRING)),
        owl.DataComplementOf(_datatype(XSD_BOOLEAN)),
        aliases_one,
        aliases_zero,
    )
    return compile_datatype_semantic_model(roots, definitions=definitions), labels


def _literal_sources() -> tuple[tuple[str, str, str], ...]:
    return (
        ("integer-zero", "0", XSD_INTEGER),
        ("integer-negative-zero", "-0", XSD_INTEGER),
        ("integer-padded-zero", "00", XSD_INTEGER),
        ("integer-one", "1", XSD_INTEGER),
        ("decimal-one", "1.0", XSD_DECIMAL),
        ("integer-two", "2", XSD_INTEGER),
        ("integer-three", "3", XSD_INTEGER),
        ("boolean-false", "false", XSD_BOOLEAN),
        ("boolean-true", "true", XSD_BOOLEAN),
        ("string-a", "a", XSD_STRING),
        ("string-b", "b", XSD_STRING),
    )


def _dependencies(*levels: int) -> list[int]:
    return sorted(set(levels))


def _blank(name: str, count: int, *, exhaustive: bool) -> dict[str, Any]:
    return {
        "cardinalities": [],
        "equalities": [],
        "exhaustive": exhaustive,
        "fixed_values": [],
        "inequalities": [],
        "name": name,
        "ranges": [],
        "variables": list(range(count)),
    }


def _range(
    variable: int,
    data_range_id: int,
    dependency: int,
    *,
    positive: bool = True,
) -> dict[str, Any]:
    return {
        "data_range_id": data_range_id,
        "dependencies": [dependency],
        "positive": positive,
        "variable": variable,
    }


def _fixed(variable: int, literal_id: int, dependency: int) -> dict[str, Any]:
    return {
        "dependencies": [dependency],
        "literal_id": literal_id,
        "variable": variable,
    }


def _binary(left: int, right: int, *dependencies: int) -> dict[str, Any]:
    return {
        "dependencies": _dependencies(*dependencies),
        "left": left,
        "right": right,
    }


def _cardinality(variable: int, minimum: int, dependency: int) -> dict[str, Any]:
    return {
        "dependencies": [dependency],
        "minimum": minimum,
        "variable": variable,
    }


def _crafted_cases() -> list[dict[str, Any]]:
    cases: list[dict[str, Any]] = []

    case = _blank("finite-boolean-edge", 2, exhaustive=True)
    case["ranges"] = [_range(0, 0, 10), _range(1, 0, 11)]
    case["inequalities"] = [_binary(0, 1, 12)]
    cases.append(case)

    case = _blank("finite-two-colour-triangle", 3, exhaustive=True)
    case["ranges"] = [_range(variable, 1, 20 + variable) for variable in range(3)]
    case["inequalities"] = [
        _binary(0, 1, 23),
        _binary(1, 2, 24),
        _binary(0, 2, 25),
    ]
    cases.append(case)

    case = _blank("finite-three-colour-triangle", 3, exhaustive=True)
    case["ranges"] = [_range(variable, 3, 30 + variable) for variable in range(3)]
    case["inequalities"] = [
        _binary(0, 1, 33),
        _binary(1, 2, 34),
        _binary(0, 2, 35),
    ]
    cases.append(case)

    case = _blank("mixed-family-three-colour-triangle", 3, exhaustive=True)
    case["ranges"] = [_range(variable, 6, 40 + variable) for variable in range(3)]
    case["inequalities"] = [
        _binary(0, 1, 43),
        _binary(1, 2, 44),
        _binary(0, 2, 45),
    ]
    cases.append(case)

    case = _blank("negative-range-selects-false", 1, exhaustive=True)
    case["ranges"] = [_range(0, 0, 50), _range(0, 2, 51, positive=False)]
    case["fixed_values"] = [_fixed(0, 7, 52)]
    cases.append(case)

    case = _blank("positive-negative-range-clash", 1, exhaustive=False)
    case["ranges"] = [_range(0, 1, 60), _range(0, 1, 61, positive=False)]
    cases.append(case)

    case = _blank("infinite-integer-clique-elimination", 4, exhaustive=False)
    case["ranges"] = [_range(variable, 4, 70 + variable) for variable in range(4)]
    case["inequalities"] = [
        _binary(left, right, 80 + left * 4 + right)
        for left in range(4)
        for right in range(left + 1, 4)
    ]
    case["cardinalities"] = [_cardinality(0, 100_000, 99)]
    cases.append(case)

    case = _blank("mixed-infinite-inequality", 2, exhaustive=False)
    case["ranges"] = [_range(0, 7, 100), _range(1, 7, 101)]
    case["inequalities"] = [_binary(0, 1, 102)]
    cases.append(case)

    case = _blank("private-symbolic-nonrational-witnesses", 2, exhaustive=False)
    case["ranges"] = [_range(0, 9, 110), _range(1, 9, 111)]
    case["inequalities"] = [_binary(0, 1, 112)]
    cases.append(case)

    case = _blank("nested-alias-cardinality", 1, exhaustive=True)
    case["ranges"] = [_range(0, 8, 120)]
    case["cardinalities"] = [_cardinality(0, 3, 121)]
    cases.append(case)

    case = _blank("nested-alias-cardinality-clash", 1, exhaustive=True)
    case["ranges"] = [_range(0, 8, 130)]
    case["cardinalities"] = [_cardinality(0, 4, 131)]
    cases.append(case)

    case = _blank("fixed-outside-nested-alias", 1, exhaustive=True)
    case["ranges"] = [_range(0, 8, 140)]
    case["fixed_values"] = [_fixed(0, 3, 141)]
    cases.append(case)

    case = _blank("lexical-aliases-collapse-under-equality", 2, exhaustive=True)
    case["ranges"] = [_range(0, 4, 150), _range(1, 4, 151)]
    case["fixed_values"] = [_fixed(0, 3, 152), _fixed(1, 4, 153)]
    case["equalities"] = [_binary(0, 1, 154)]
    cases.append(case)

    case = _blank("lexical-aliases-clash-under-inequality", 2, exhaustive=True)
    case["fixed_values"] = [_fixed(0, 3, 160), _fixed(1, 4, 161)]
    case["inequalities"] = [_binary(0, 1, 162)]
    cases.append(case)

    case = _blank("conflicting-fixed-values-after-equality", 2, exhaustive=True)
    case["fixed_values"] = [_fixed(0, 0, 170), _fixed(1, 3, 171)]
    case["equalities"] = [_binary(0, 1, 172)]
    cases.append(case)

    case = _blank("equality-inequality-clash", 2, exhaustive=True)
    case["equalities"] = [_binary(0, 1, 180)]
    case["inequalities"] = [_binary(0, 1, 181)]
    cases.append(case)

    case = _blank("equality-collapse-empty-intersection", 2, exhaustive=False)
    case["ranges"] = [_range(0, 0, 190), _range(1, 5, 191)]
    case["equalities"] = [_binary(0, 1, 192)]
    cases.append(case)

    case = _blank("explicit-mixed-family-empty-range", 1, exhaustive=False)
    case["ranges"] = [_range(0, 10, 200)]
    cases.append(case)

    case = _blank("family-complement-fixed-string", 1, exhaustive=False)
    case["ranges"] = [_range(0, 11, 210)]
    case["fixed_values"] = [_fixed(0, 9, 211)]
    cases.append(case)

    case = _blank("duplicate-edge-minimal-support", 2, exhaustive=True)
    case["fixed_values"] = [_fixed(0, 3, 220), _fixed(1, 4, 221)]
    case["inequalities"] = [_binary(0, 1, 222, 223), _binary(0, 1, 224)]
    cases.append(case)

    case = _blank("alias-enumeration-counts-data-identities", 1, exhaustive=True)
    case["ranges"] = [_range(0, 12, 230)]
    case["cardinalities"] = [_cardinality(0, 2, 231)]
    cases.append(case)

    case = _blank("zero-alias-enumeration-counts-once", 1, exhaustive=True)
    case["ranges"] = [_range(0, 13, 240)]
    case["cardinalities"] = [_cardinality(0, 2, 241)]
    cases.append(case)

    case = _blank("rollback-stable-base", 2, exhaustive=True)
    case["ranges"] = [_range(0, 1, 250), _range(1, 1, 251)]
    case["inequalities"] = [_binary(0, 1, 252)]
    cases.append(case)

    case = _blank("rollback-transient-clash", 2, exhaustive=True)
    case["ranges"] = [_range(0, 1, 250), _range(1, 1, 251)]
    case["inequalities"] = [_binary(0, 1, 252)]
    case["equalities"] = [_binary(0, 1, 253)]
    cases.append(case)

    return cases


def _generated_cases(rng: random.Random, count: int) -> list[dict[str, Any]]:
    finite_ranges = (0, 1, 3, 6, 8, 12, 13)
    fixed_literals = tuple(range(len(_literal_sources())))
    cases: list[dict[str, Any]] = []
    for index in range(count):
        size = rng.randint(1, 6)
        case = _blank(f"generated-finite-{index:03d}", size, exhaustive=True)
        dependency = 10_000 + index * 100
        for variable in range(size):
            case["ranges"].append(
                _range(variable, rng.choice(finite_ranges), dependency)
            )
            dependency += 1
            if rng.random() < 0.22:
                case["ranges"].append(
                    _range(variable, rng.choice(finite_ranges), dependency)
                )
                dependency += 1
            if rng.random() < 0.18:
                case["fixed_values"].append(
                    _fixed(variable, rng.choice(fixed_literals), dependency)
                )
                dependency += 1
            if rng.random() < 0.24:
                case["cardinalities"].append(
                    _cardinality(variable, rng.randint(0, 4), dependency)
                )
                dependency += 1
        for left in range(size):
            for right in range(left + 1, size):
                if rng.random() < 0.12:
                    case["equalities"].append(_binary(left, right, dependency))
                    dependency += 1
                if rng.random() < 0.34:
                    case["inequalities"].append(_binary(left, right, dependency))
                    dependency += 1
        cases.append(case)
    return cases


def _component(
    case: dict[str, Any],
    literal_payloads: tuple[Any, ...],
) -> SemanticDatatypeConstraintComponent:
    return SemanticDatatypeConstraintComponent(
        variables=tuple(case["variables"]),
        ranges=tuple(
            SemanticRangeConstraint(
                value["variable"],
                value["data_range_id"],
                value["positive"],
                frozenset(value["dependencies"]),
            )
            for value in case["ranges"]
        ),
        fixed_values=tuple(
            SemanticFixedValueConstraint(
                value["variable"],
                literal_payloads[value["literal_id"]],
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


def _witness(value: Any) -> dict[str, Any]:
    if isinstance(value, SymbolicDataWitness):
        return {
            "domain_digest": value.domain_digest,
            "family": value.family,
            "kind": "symbolic",
            "ordinal": value.ordinal,
        }
    return {"identity": list(value.as_tagged()), "kind": "concrete"}


def _result(value: Any) -> dict[str, Any]:
    if value.clash is not None:
        return {
            "assignments": [],
            "clash": {
                "dependencies": sorted(value.clash.dependencies),
                "kind": str(value.clash.kind),
                "variables": list(value.clash.variables),
            },
            "satisfiable": False,
        }
    return {
        "assignments": [
            {"value": _witness(assignment.value), "variable": assignment.variable}
            for assignment in value.assignments
        ],
        "clash": None,
        "satisfiable": True,
    }


def build_fixture() -> dict[str, Any]:
    model, range_labels = _model()
    literal_payloads = tuple(
        compile_literal_semantic_payload(_literal(lexical, datatype))
        for _label, lexical, datatype in _literal_sources()
    )
    cases = [*_crafted_cases(), *_generated_cases(random.Random(SEED), 64)]
    solver = DatatypeConstraintSolver()
    solved: dict[str, Any] = {}
    for case in cases:
        semantic = _component(case, literal_payloads)
        executable = compile_datatype_constraint_component(model, semantic)
        result = solver.solve(executable)
        if solver.solve(executable) != result:
            raise AssertionError(f"nondeterministic production result for {case['name']}")
        if case["exhaustive"]:
            exhaustive = solver.solve_exhaustive(executable)
            if exhaustive.satisfiable != result.satisfiable:
                raise AssertionError(
                    f"optimized/exhaustive disagreement for {case['name']}"
                )
        case["expected"] = _result(result)
        solved[case["name"]] = result

    baseline = next(case for case in cases if case["name"] == "rollback-stable-base")
    transient = next(case for case in cases if case["name"] == "rollback-transient-clash")
    baseline_component = compile_datatype_constraint_component(
        model, _component(baseline, literal_payloads)
    )
    transient_component = compile_datatype_constraint_component(
        model, _component(transient, literal_payloads)
    )
    before = solver.solve(baseline_component)
    branch = solver.solve(transient_component)
    after = solver.solve(baseline_component)
    if before != after or branch.satisfiable:
        raise AssertionError("production solver is not rollback-order stable")

    literals = [
        {
            "label": label,
            "payload_json": payload.canonical_bytes().decode(),
            "source_literal_id": index,
        }
        for index, ((label, _lexical, _datatype_iri), payload) in enumerate(
            zip(_literal_sources(), literal_payloads, strict=True)
        )
    ]
    return {
        "case_count": len(cases),
        "cases": cases,
        "generator_seed": SEED,
        "literal_count": len(literals),
        "literals": literals,
        "model_json": model.canonical_bytes().decode(),
        "range_labels": list(range_labels),
        "rollback_checks": [
            {
                "baseline": "rollback-stable-base",
                "transient": "rollback-transient-clash",
            }
        ],
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
