from __future__ import annotations

import itertools
import random

import pyowl_core.model as owl
import pytest

from pyhermit.datatypes import (
    XSD_DECIMAL,
    XSD_INTEGER,
    XSD_STRING,
    CompiledLiteral,
    DataDomainRange,
    DatatypeClashKind,
    DatatypeConstraintComponent,
    DatatypeConstraintSolver,
    DatatypeLimits,
    DomainCardinalityConstraint,
    EqualityConstraint,
    FixedValueConstraint,
    InequalityConstraint,
    RangeConstraint,
    SymbolicDataWitness,
    compile_datatype_semantic_model,
    compile_literal,
)
from pyhermit.events import CancellationSource
from pyhermit.exceptions import ReasonerInterruptedError, ResourceLimitError


def datatype(iri: str) -> owl.Datatype:
    return owl.Datatype(owl.IRI(iri))


def compiled(lexical: str, iri: str = XSD_INTEGER) -> CompiledLiteral:
    return compile_literal(owl.Literal(lexical, datatype(iri)))


def enumeration(*values: CompiledLiteral) -> DataDomainRange:
    return DataDomainRange.enumeration(values)


def builtin(iri: str) -> DataDomainRange:
    model = compile_datatype_semantic_model((datatype(iri),))
    return DataDomainRange.from_model(model, 0)


def test_equality_uses_data_identity_and_clash_dependencies_survive_branch_removal() -> None:
    first = compiled("01", XSD_INTEGER)
    alias = compiled("1.0", XSD_DECIMAL)
    equalities = (EqualityConstraint(0, 1, frozenset({2})),)
    fixed_values = (
        FixedValueConstraint(0, first, frozenset({3})),
        FixedValueConstraint(1, alias, frozenset({4})),
    )
    base = DatatypeConstraintComponent(
        variables=(0, 1),
        equalities=equalities,
        fixed_values=fixed_values,
    )
    solver = DatatypeConstraintSolver()
    assert solver.solve(base).satisfiable

    branched = DatatypeConstraintComponent(
        variables=(0, 1),
        equalities=equalities,
        fixed_values=fixed_values,
        inequalities=(InequalityConstraint(0, 1, frozenset({7})),),
    )
    result = solver.solve(branched)
    assert not result.satisfiable
    assert result.clash is not None
    assert result.clash.kind is DatatypeClashKind.EQUALITY_INEQUALITY
    assert result.clash.dependencies == frozenset({2, 7})

    # Rolling back the branch-local inequality removes the contradiction.
    assert solver.solve(base).satisfiable


def test_conflicting_constants_and_fixed_value_outside_range_report_sufficient_support() -> None:
    conflict = DatatypeConstraintComponent(
        variables=(0, 1),
        equalities=(EqualityConstraint(0, 1, frozenset({10})),),
        fixed_values=(
            FixedValueConstraint(0, compiled("1"), frozenset({11})),
            FixedValueConstraint(1, compiled("2"), frozenset({12})),
        ),
    )
    result = DatatypeConstraintSolver().solve(conflict)
    assert result.clash is not None
    assert result.clash.kind is DatatypeClashKind.CONFLICTING_FIXED_VALUES
    assert result.clash.dependencies == frozenset({10, 11, 12})

    outside = DatatypeConstraintComponent(
        variables=(0,),
        ranges=(RangeConstraint(0, builtin(XSD_STRING), dependencies=frozenset({20})),),
        fixed_values=(FixedValueConstraint(0, compiled("1"), frozenset({21})),),
    )
    result = DatatypeConstraintSolver().solve(outside)
    assert result.clash is not None
    assert result.clash.kind is DatatypeClashKind.FIXED_VALUE_OUTSIDE_DOMAIN
    assert result.clash.dependencies == frozenset({20, 21})


def test_negative_ranges_empty_intersections_and_domain_cardinality_are_exact() -> None:
    integers = builtin(XSD_INTEGER)
    empty = DatatypeConstraintComponent(
        variables=(0,),
        ranges=(
            RangeConstraint(0, integers, dependencies=frozenset({30})),
            RangeConstraint(0, integers, positive=False, dependencies=frozenset({31})),
        ),
    )
    result = DatatypeConstraintSolver().solve(empty)
    assert result.clash is not None
    assert result.clash.kind is DatatypeClashKind.EMPTY_DOMAIN
    assert result.clash.dependencies == frozenset({30, 31})

    two_values = enumeration(compiled("1"), compiled("2"))
    too_small = DatatypeConstraintComponent(
        variables=(0,),
        ranges=(RangeConstraint(0, two_values, dependencies=frozenset({32})),),
        cardinalities=(DomainCardinalityConstraint(0, 3, frozenset({33})),),
    )
    result = DatatypeConstraintSolver().solve(too_small)
    assert result.clash is not None
    assert result.clash.kind is DatatypeClashKind.INSUFFICIENT_CARDINALITY
    assert result.clash.dependencies == frozenset({32, 33})


def test_finite_inequality_core_is_exact_and_returns_concrete_assignments() -> None:
    two_values = enumeration(compiled("0"), compiled("1"))
    ranges = tuple(RangeConstraint(variable, two_values) for variable in range(3))
    path = DatatypeConstraintComponent(
        variables=(0, 1, 2),
        ranges=ranges,
        inequalities=(InequalityConstraint(0, 1), InequalityConstraint(1, 2)),
    )
    result = DatatypeConstraintSolver().solve(path)
    assert result.satisfiable
    assignments = {item.variable: item.value for item in result.assignments}
    assert all(value is not None for value in assignments.values())
    assert assignments[0] != assignments[1]
    assert assignments[1] != assignments[2]

    triangle = DatatypeConstraintComponent(
        variables=(0, 1, 2),
        ranges=ranges,
        inequalities=(
            InequalityConstraint(0, 1, frozenset({40})),
            InequalityConstraint(1, 2, frozenset({41})),
            InequalityConstraint(0, 2, frozenset({42})),
        ),
    )
    result = DatatypeConstraintSolver().solve(triangle)
    assert result.clash is not None
    assert result.clash.kind is DatatypeClashKind.UNSATISFIABLE_INEQUALITIES
    assert result.clash.dependencies == frozenset({40, 41, 42})


def test_infinite_domains_are_eliminated_without_materialization() -> None:
    strings = builtin(XSD_STRING)
    component = DatatypeConstraintComponent(
        variables=(0, 1, 2),
        ranges=tuple(RangeConstraint(variable, strings) for variable in range(3)),
        inequalities=(
            InequalityConstraint(0, 1),
            InequalityConstraint(1, 2),
            InequalityConstraint(0, 2),
        ),
    )
    solver = DatatypeConstraintSolver()
    result = solver.solve(component)
    assert result.satisfiable
    assignments = {item.variable: item.value for item in result.assignments}
    assert len(set(assignments.values())) == 3
    assert result == solver.solve(component)
    assert not any(isinstance(value, SymbolicDataWitness) for value in assignments.values())
    with pytest.raises(ValueError, match="requires finite"):
        solver.solve_exhaustive(component)


def test_optimized_solver_agrees_with_exhaustive_oracle_on_generated_finite_components() -> None:
    values = (compiled("0"), compiled("1"), compiled("2"))
    domains = tuple(
        enumeration(*(value for value, selected in zip(values, mask, strict=True) if selected))
        for mask in itertools.product((False, True), repeat=3)
    )
    edges = ((0, 1), (0, 2), (1, 2))
    randomizer = random.Random(7727)
    solver = DatatypeConstraintSolver()
    for _ in range(160):
        selected_domains = tuple(randomizer.choice(domains) for _variable in range(3))
        selected_edges = tuple(
            InequalityConstraint(*edge) for edge in edges if randomizer.choice((False, True))
        )
        component = DatatypeConstraintComponent(
            variables=(0, 1, 2),
            ranges=tuple(
                RangeConstraint(variable, selected_domains[variable]) for variable in range(3)
            ),
            inequalities=selected_edges,
        )
        assert solver.solve(component).satisfiable is solver.solve_exhaustive(component).satisfiable


def test_solver_limits_cancellation_and_component_boundaries_are_enforced() -> None:
    with pytest.raises(ValueError, match="outside"):
        DatatypeConstraintComponent(
            variables=(0,),
            inequalities=(InequalityConstraint(0, 1),),
        )
    with pytest.raises(TypeError, match="dependencies"):
        EqualityConstraint(0, 1, frozenset({True}))

    component = DatatypeConstraintComponent(
        variables=(0, 1),
        inequalities=(InequalityConstraint(0, 1),),
    )
    with pytest.raises(ResourceLimitError) as limited:
        DatatypeConstraintSolver(limits=DatatypeLimits(max_solver_steps=1)).solve(component)
    assert limited.value.limit == "max_solver_steps"

    cancellation = CancellationSource()
    cancellation.interrupt("datatype solver test")
    with pytest.raises(ReasonerInterruptedError, match="datatype solver test"):
        DatatypeConstraintSolver().solve(component, cancellation=cancellation.token)
