"""Semantic-model adapter for backend-independent datatype components.

SPDX-License-Identifier: LGPL-3.0-or-later

Normalization and clausification identify data ranges by dense integer IDs.  This
module is the narrow executable boundary between those canonical semantic records and
the datatype solver: it resolves each referenced range once, restores compiled literal
semantics without lexical reparsing, and deliberately knows nothing about tableau
nodes, branches, or backend state.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass

from pyhermit.events import CancellationToken
from pyhermit.exceptions import UnsupportedDatatypeError

from .domain import DataDomainRange
from .model import DatatypeLimits
from .semantic import (
    BackendLiteralSemanticPayload,
    DatatypeSemanticModelPayload,
    LiteralSemanticPayload,
    OpaqueLiteralSemanticPayload,
)
from .solver import (
    ConstraintDependencies,
    DatatypeConstraintComponent,
    DomainCardinalityConstraint,
    EqualityConstraint,
    FixedValueConstraint,
    InequalityConstraint,
    RangeConstraint,
)


@dataclass(frozen=True, slots=True)
class SemanticRangeConstraint:
    """Positive or negative assertion against a dense semantic-model range ID."""

    variable: int
    data_range_id: int
    positive: bool = True
    dependencies: ConstraintDependencies = frozenset()

    def __post_init__(self) -> None:
        _variable(self.variable)
        if isinstance(self.data_range_id, bool) or not isinstance(self.data_range_id, int):
            raise TypeError("data_range_id must be int")
        if self.data_range_id < 0:
            raise ValueError("data_range_id must be nonnegative")
        if not isinstance(self.positive, bool):
            raise TypeError("positive must be bool")
        object.__setattr__(self, "dependencies", _dependencies(self.dependencies))


@dataclass(frozen=True, slots=True)
class SemanticFixedValueConstraint:
    """Fixed value carried across the backend boundary as canonical semantics."""

    variable: int
    value: BackendLiteralSemanticPayload
    dependencies: ConstraintDependencies = frozenset()

    def __post_init__(self) -> None:
        _variable(self.variable)
        if not isinstance(self.value, (LiteralSemanticPayload, OpaqueLiteralSemanticPayload)):
            raise TypeError("value must be a backend literal semantic payload")
        object.__setattr__(self, "dependencies", _dependencies(self.dependencies))


@dataclass(frozen=True, slots=True)
class SemanticDatatypeConstraintComponent:
    """One datatype component whose ranges and literals use canonical wire records.

    Equality, inequality, and minimum-cardinality records are already independent of
    model representation, so the same immutable solver records are shared directly.
    """

    variables: tuple[int, ...]
    ranges: tuple[SemanticRangeConstraint, ...] = ()
    fixed_values: tuple[SemanticFixedValueConstraint, ...] = ()
    equalities: tuple[EqualityConstraint, ...] = ()
    inequalities: tuple[InequalityConstraint, ...] = ()
    cardinalities: tuple[DomainCardinalityConstraint, ...] = ()

    def __post_init__(self) -> None:
        variables = tuple(self.variables)
        if not all(_is_variable(value) for value in variables):
            raise TypeError("variables must contain nonnegative integer IDs")
        if len(set(variables)) != len(variables):
            raise ValueError("variables must be unique")
        variables = tuple(sorted(variables))
        object.__setattr__(self, "variables", variables)
        expected = (
            ("ranges", SemanticRangeConstraint),
            ("fixed_values", SemanticFixedValueConstraint),
            ("equalities", EqualityConstraint),
            ("inequalities", InequalityConstraint),
            ("cardinalities", DomainCardinalityConstraint),
        )
        known = frozenset(variables)
        for name, item_type in expected:
            try:
                items = tuple(getattr(self, name))
            except TypeError as error:
                raise TypeError(f"{name} must be an iterable of constraints") from error
            if not all(isinstance(item, item_type) for item in items):
                raise TypeError(f"{name} contains an invalid constraint")
            object.__setattr__(self, name, items)
            for item in items:
                referenced = (
                    (item.left, item.right)
                    if isinstance(item, (EqualityConstraint, InequalityConstraint))
                    else (item.variable,)
                )
                if any(value not in known for value in referenced):
                    raise ValueError(f"{name} references a variable outside the component")


def compile_datatype_constraint_component(
    model: DatatypeSemanticModelPayload,
    component: SemanticDatatypeConstraintComponent,
    *,
    limits: DatatypeLimits | None = None,
    cancellation: CancellationToken | None = None,
) -> DatatypeConstraintComponent:
    """Resolve canonical model IDs into one executable datatype solver component.

    A local cache guarantees that repeated assertions of the same dense range ID do
    not repeat data-range algebra.  Opaque ranges and literals fail closed because
    assigning invented equality or membership semantics would be unsound.
    """

    if not isinstance(model, DatatypeSemanticModelPayload):
        raise TypeError("model must be DatatypeSemanticModelPayload")
    if not isinstance(component, SemanticDatatypeConstraintComponent):
        raise TypeError("component must be SemanticDatatypeConstraintComponent")
    selected = limits or DatatypeLimits()
    if not isinstance(selected, DatatypeLimits):
        raise TypeError("limits must be DatatypeLimits or None")
    if cancellation is not None and not isinstance(cancellation, CancellationToken):
        raise TypeError("cancellation must be CancellationToken or None")
    if cancellation is not None:
        cancellation.check()

    range_cache: dict[int, DataDomainRange] = {}
    ranges: list[RangeConstraint] = []
    for range_assertion in component.ranges:
        data_range = range_cache.get(range_assertion.data_range_id)
        if data_range is None:
            data_range = DataDomainRange.from_model(
                model,
                range_assertion.data_range_id,
                limits=selected,
                cancellation=cancellation,
            )
            range_cache[range_assertion.data_range_id] = data_range
        ranges.append(
            RangeConstraint(
                range_assertion.variable,
                data_range,
                range_assertion.positive,
                range_assertion.dependencies,
            )
        )

    fixed_values: list[FixedValueConstraint] = []
    for fixed_assertion in component.fixed_values:
        if isinstance(fixed_assertion.value, OpaqueLiteralSemanticPayload):
            raise UnsupportedDatatypeError(
                "opaque literal semantics cannot constrain a datatype component",
                context={"datatype_iri": fixed_assertion.value.datatype_iri},
            )
        fixed_values.append(
            FixedValueConstraint(
                fixed_assertion.variable,
                fixed_assertion.value.to_compiled(),
                fixed_assertion.dependencies,
            )
        )

    if cancellation is not None:
        cancellation.check()
    return DatatypeConstraintComponent(
        variables=component.variables,
        ranges=tuple(ranges),
        fixed_values=tuple(fixed_values),
        equalities=component.equalities,
        inequalities=component.inequalities,
        cardinalities=component.cardinalities,
    )


def _dependencies(value: Iterable[int]) -> ConstraintDependencies:
    try:
        result = frozenset(value)
    except TypeError as error:
        raise TypeError("dependencies must be an iterable of integers") from error
    if not all(_is_variable(item) for item in result):
        raise TypeError("dependencies must contain nonnegative integers")
    return result


def _is_variable(value: object) -> bool:
    return not isinstance(value, bool) and isinstance(value, int) and value >= 0


def _variable(value: object) -> None:
    if not _is_variable(value):
        raise TypeError("variable must be a nonnegative integer")


__all__ = [
    "SemanticDatatypeConstraintComponent",
    "SemanticFixedValueConstraint",
    "SemanticRangeConstraint",
    "compile_datatype_constraint_component",
]
