"""Exact, backend-independent datatype constraint component solver.

SPDX-License-Identifier: LGPL-3.0-or-later

The tableau-facing adapter can translate its node and dependency records into these
immutable constraints without importing tableau state here.  Equality classes are
collapsed first, family-spanning ranges are intersected exactly, and the remaining
finite inequality core is solved as a deterministic list-colouring problem.  Variables
whose domain has more values than unequal neighbours are eliminated soundly, which
keeps infinite OWL value spaces symbolic.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, cast

from pyhermit.events import CancellationToken
from pyhermit.exceptions import ResourceLimitError

from .domain import DataDomainRange
from .model import (
    BinaryIdentity,
    BooleanIdentity,
    CompiledLiteral,
    DataIdentity,
    DatatypeLimits,
    DateTimeIdentity,
    IEEEIdentity,
    NumericIdentity,
    StringIdentity,
    URIIdentity,
    XMLIdentity,
)

ConstraintDependencies: TypeAlias = frozenset[int]
_DATA_IDENTITIES = (
    BinaryIdentity,
    BooleanIdentity,
    DateTimeIdentity,
    IEEEIdentity,
    NumericIdentity,
    StringIdentity,
    URIIdentity,
    XMLIdentity,
)


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class DatatypeClashKind(_StringEnum):
    """Stable categories for sufficient datatype contradictions."""

    EQUALITY_INEQUALITY = "equality-inequality"
    CONFLICTING_FIXED_VALUES = "conflicting-fixed-values"
    EMPTY_DOMAIN = "empty-domain"
    FIXED_VALUE_OUTSIDE_DOMAIN = "fixed-value-outside-domain"
    INSUFFICIENT_CARDINALITY = "insufficient-cardinality"
    UNSATISFIABLE_INEQUALITIES = "unsatisfiable-inequalities"


@dataclass(frozen=True, slots=True)
class RangeConstraint:
    """Positive or negative data-range assertion on one concrete variable."""

    variable: int
    data_range: DataDomainRange
    positive: bool = True
    dependencies: ConstraintDependencies = frozenset()

    def __post_init__(self) -> None:
        _validate_variable(self.variable)
        if not isinstance(self.data_range, DataDomainRange):
            raise TypeError("data_range must be DataDomainRange")
        if not isinstance(self.positive, bool):
            raise TypeError("positive must be bool")
        object.__setattr__(self, "dependencies", _freeze_dependencies(self.dependencies))


@dataclass(frozen=True, slots=True)
class FixedValueConstraint:
    """Assign one source-preserving compiled literal to a concrete variable."""

    variable: int
    value: CompiledLiteral
    dependencies: ConstraintDependencies = frozenset()

    def __post_init__(self) -> None:
        _validate_variable(self.variable)
        if not isinstance(self.value, CompiledLiteral):
            raise TypeError("value must be CompiledLiteral")
        object.__setattr__(self, "dependencies", _freeze_dependencies(self.dependencies))


@dataclass(frozen=True, slots=True)
class EqualityConstraint:
    """Require two concrete variables to denote one data-domain identity."""

    left: int
    right: int
    dependencies: ConstraintDependencies = frozenset()

    def __post_init__(self) -> None:
        _validate_variable(self.left)
        _validate_variable(self.right)
        if self.right < self.left:
            left, right = self.right, self.left
            object.__setattr__(self, "left", left)
            object.__setattr__(self, "right", right)
        object.__setattr__(self, "dependencies", _freeze_dependencies(self.dependencies))


@dataclass(frozen=True, slots=True)
class InequalityConstraint:
    """Require two concrete variables to denote different data identities."""

    left: int
    right: int
    dependencies: ConstraintDependencies = frozenset()

    def __post_init__(self) -> None:
        _validate_variable(self.left)
        _validate_variable(self.right)
        if self.right < self.left:
            left, right = self.right, self.left
            object.__setattr__(self, "left", left)
            object.__setattr__(self, "right", right)
        object.__setattr__(self, "dependencies", _freeze_dependencies(self.dependencies))


@dataclass(frozen=True, slots=True)
class DomainCardinalityConstraint:
    """Require a variable's allowed value space to contain ``minimum`` identities."""

    variable: int
    minimum: int
    dependencies: ConstraintDependencies = frozenset()

    def __post_init__(self) -> None:
        _validate_variable(self.variable)
        if isinstance(self.minimum, bool) or not isinstance(self.minimum, int):
            raise TypeError("minimum must be int")
        if self.minimum < 0:
            raise ValueError("minimum must be nonnegative")
        object.__setattr__(self, "dependencies", _freeze_dependencies(self.dependencies))


@dataclass(frozen=True, slots=True)
class DatatypeConstraintComponent:
    """One closed concrete-node component, independent of backend node handles."""

    variables: tuple[int, ...]
    ranges: tuple[RangeConstraint, ...] = ()
    fixed_values: tuple[FixedValueConstraint, ...] = ()
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
            ("ranges", RangeConstraint),
            ("fixed_values", FixedValueConstraint),
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


@dataclass(frozen=True, slots=True)
class DatatypeClash:
    """A sufficient contradictory subset suitable for backend backjumping."""

    kind: DatatypeClashKind
    dependencies: ConstraintDependencies
    variables: tuple[int, ...]
    message: str

    def __post_init__(self) -> None:
        if not isinstance(self.kind, DatatypeClashKind):
            raise TypeError("kind must be DatatypeClashKind")
        object.__setattr__(self, "dependencies", _freeze_dependencies(self.dependencies))
        variables = tuple(sorted(set(self.variables)))
        if not all(_is_variable(value) for value in variables):
            raise TypeError("clash variables must be nonnegative integer IDs")
        object.__setattr__(self, "variables", variables)
        if not isinstance(self.message, str) or not self.message:
            raise ValueError("message must be a nonempty string")


@dataclass(frozen=True, slots=True)
class DatatypeVariableAssignment:
    """Concrete identity, or ``None`` for a sound symbolic existential witness."""

    variable: int
    value: DataIdentity | None

    def __post_init__(self) -> None:
        _validate_variable(self.variable)
        if self.value is not None and not isinstance(self.value, _DATA_IDENTITIES):
            raise TypeError("value must be a data-domain identity or None")


@dataclass(frozen=True, slots=True)
class DatatypeSolveResult:
    """Immutable SAT certificate or datatype clash."""

    satisfiable: bool
    assignments: tuple[DatatypeVariableAssignment, ...] = ()
    clash: DatatypeClash | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.satisfiable, bool):
            raise TypeError("satisfiable must be bool")
        assignments = tuple(self.assignments)
        if not all(isinstance(value, DatatypeVariableAssignment) for value in assignments):
            raise TypeError("assignments must contain DatatypeVariableAssignment values")
        if tuple(sorted(value.variable for value in assignments)) != tuple(
            value.variable for value in assignments
        ):
            raise ValueError("assignments must be ordered by variable")
        if len({value.variable for value in assignments}) != len(assignments):
            raise ValueError("assignments must have unique variables")
        object.__setattr__(self, "assignments", assignments)
        if self.satisfiable:
            if self.clash is not None:
                raise ValueError("a satisfiable result cannot contain a clash")
        elif self.clash is None:
            raise ValueError("an unsatisfiable result must contain a clash")


@dataclass(slots=True)
class _Fixed:
    value: CompiledLiteral
    dependencies: set[int]


@dataclass(slots=True)
class _Prepared:
    component: DatatypeConstraintComponent
    representatives: tuple[int, ...]
    representative_by_variable: dict[int, int]
    members: dict[int, tuple[int, ...]]
    equality_dependencies: dict[int, set[int]]
    domains: dict[int, DataDomainRange]
    domain_dependencies: dict[int, set[int]]
    fixed: dict[int, _Fixed]
    adjacency: dict[int, set[int]]
    edge_dependencies: dict[tuple[int, int], set[int]]


class _UnionFind:
    __slots__ = ("parent",)

    def __init__(self, variables: tuple[int, ...]) -> None:
        self.parent = {value: value for value in variables}

    def find(self, value: int) -> int:
        root = value
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[value] != value:
            parent = self.parent[value]
            self.parent[value] = root
            value = parent
        return root

    def union(self, left: int, right: int) -> None:
        first = self.find(left)
        second = self.find(right)
        if first == second:
            return
        root, child = (first, second) if first < second else (second, first)
        self.parent[child] = root


@dataclass(slots=True)
class _Work:
    limits: DatatypeLimits
    cancellation: CancellationToken | None
    steps: int = 0

    def add(self, amount: int = 1) -> None:
        self.steps += amount
        if self.steps > self.limits.max_solver_steps:
            raise ResourceLimitError(
                "datatype component solving exceeds the configured step limit",
                limit="max_solver_steps",
                observed=self.steps,
                allowed=self.limits.max_solver_steps,
            )
        if self.cancellation is not None:
            self.cancellation.add_work(amount)
            if self.steps % self.limits.cancellation_poll_stride == 0:
                self.cancellation.check()


@dataclass(slots=True)
class _SearchFrame:
    variable: int
    values: tuple[DataIdentity, ...]
    next_index: int = 0


class DatatypeConstraintSolver:
    """Readable exact solver with a separate finite exhaustive oracle mode."""

    __slots__ = ("limits",)

    def __init__(self, *, limits: DatatypeLimits | None = None) -> None:
        selected = limits or DatatypeLimits()
        if not isinstance(selected, DatatypeLimits):
            raise TypeError("limits must be DatatypeLimits or None")
        self.limits = selected

    def solve(
        self,
        component: DatatypeConstraintComponent,
        *,
        cancellation: CancellationToken | None = None,
    ) -> DatatypeSolveResult:
        """Solve one component, retaining infinite domains symbolically."""

        return self._solve(component, cancellation=cancellation, exhaustive=False)

    def solve_exhaustive(
        self,
        component: DatatypeConstraintComponent,
        *,
        cancellation: CancellationToken | None = None,
    ) -> DatatypeSolveResult:
        """Slow finite-domain oracle used by generated property tests.

        ``ValueError`` is raised if any unfixed representative has an infinite domain.
        """

        return self._solve(component, cancellation=cancellation, exhaustive=True)

    def _solve(
        self,
        component: DatatypeConstraintComponent,
        *,
        cancellation: CancellationToken | None,
        exhaustive: bool,
    ) -> DatatypeSolveResult:
        if not isinstance(component, DatatypeConstraintComponent):
            raise TypeError("component must be DatatypeConstraintComponent")
        if cancellation is not None and not isinstance(cancellation, CancellationToken):
            raise TypeError("cancellation must be CancellationToken or None")
        if cancellation is not None:
            cancellation.check()
        work = _Work(self.limits, cancellation)
        prepared = _prepare(component, self.limits, cancellation, work)
        if isinstance(prepared, DatatypeSolveResult):
            return prepared
        return _colour(prepared, self.limits, cancellation, work, exhaustive=exhaustive)


def solve_datatype_constraints(
    component: DatatypeConstraintComponent,
    *,
    limits: DatatypeLimits | None = None,
    cancellation: CancellationToken | None = None,
) -> DatatypeSolveResult:
    """Functional facade for the optimized exact solver."""

    return DatatypeConstraintSolver(limits=limits).solve(component, cancellation=cancellation)


def solve_datatype_constraints_exhaustive(
    component: DatatypeConstraintComponent,
    *,
    limits: DatatypeLimits | None = None,
    cancellation: CancellationToken | None = None,
) -> DatatypeSolveResult:
    """Functional facade for the finite exhaustive oracle."""

    return DatatypeConstraintSolver(limits=limits).solve_exhaustive(
        component,
        cancellation=cancellation,
    )


def _prepare(
    component: DatatypeConstraintComponent,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
    work: _Work,
) -> _Prepared | DatatypeSolveResult:
    union_find = _UnionFind(component.variables)
    for equality in component.equalities:
        work.add()
        union_find.union(equality.left, equality.right)
    representative_by_variable = {
        variable: union_find.find(variable) for variable in component.variables
    }
    members_mutable: dict[int, list[int]] = {}
    for variable, representative in representative_by_variable.items():
        members_mutable.setdefault(representative, []).append(variable)
    members = {
        representative: tuple(values) for representative, values in sorted(members_mutable.items())
    }
    representatives = tuple(members)
    equality_dependencies: dict[int, set[int]] = {value: set() for value in representatives}
    for equality in component.equalities:
        equality_dependencies[representative_by_variable[equality.left]].update(
            equality.dependencies
        )

    domains = {value: DataDomainRange.all() for value in representatives}
    domain_dependencies: dict[int, set[int]] = {value: set() for value in representatives}
    for range_constraint in component.ranges:
        work.add()
        representative = representative_by_variable[range_constraint.variable]
        selected = (
            range_constraint.data_range
            if range_constraint.positive
            else range_constraint.data_range.complement(
                limits=limits,
                cancellation=cancellation,
            )
        )
        domains[representative] = domains[representative].intersection(
            selected,
            limits=limits,
            cancellation=cancellation,
        )
        domain_dependencies[representative].update(range_constraint.dependencies)

    fixed: dict[int, _Fixed] = {}
    for fixed_constraint in component.fixed_values:
        work.add()
        representative = representative_by_variable[fixed_constraint.variable]
        prior = fixed.get(representative)
        if prior is None:
            fixed[representative] = _Fixed(
                fixed_constraint.value,
                set(fixed_constraint.dependencies),
            )
        elif prior.value.data_identity != fixed_constraint.value.data_identity:
            return _clash(
                DatatypeClashKind.CONFLICTING_FIXED_VALUES,
                prior.dependencies
                | set(fixed_constraint.dependencies)
                | equality_dependencies[representative],
                members[representative],
                "equal concrete variables have conflicting fixed data identities",
            )
        else:
            prior.dependencies.update(fixed_constraint.dependencies)

    for representative in representatives:
        work.add()
        if domains[representative].is_empty_exact(
            limits=limits,
            cancellation=cancellation,
        ):
            return _clash(
                DatatypeClashKind.EMPTY_DOMAIN,
                domain_dependencies[representative] | equality_dependencies[representative],
                members[representative],
                "the intersection of data-range assertions is empty",
            )
        assigned = fixed.get(representative)
        if assigned is not None and not domains[representative].contains(
            assigned.value,
            cancellation=cancellation,
        ):
            return _clash(
                DatatypeClashKind.FIXED_VALUE_OUTSIDE_DOMAIN,
                assigned.dependencies
                | domain_dependencies[representative]
                | equality_dependencies[representative],
                members[representative],
                "a fixed data identity is outside the variable's asserted ranges",
            )

    for requirement in component.cardinalities:
        work.add()
        representative = representative_by_variable[requirement.variable]
        if not domains[representative].cardinality_at_least(
            requirement.minimum,
            limits=limits,
            cancellation=cancellation,
        ):
            return _clash(
                DatatypeClashKind.INSUFFICIENT_CARDINALITY,
                set(requirement.dependencies)
                | domain_dependencies[representative]
                | equality_dependencies[representative],
                members[representative],
                "the allowed data range has too few distinct identities",
            )

    adjacency: dict[int, set[int]] = {value: set() for value in representatives}
    edge_dependencies: dict[tuple[int, int], set[int]] = {}
    for inequality in component.inequalities:
        work.add()
        left = representative_by_variable[inequality.left]
        right = representative_by_variable[inequality.right]
        if left == right:
            return _clash(
                DatatypeClashKind.EQUALITY_INEQUALITY,
                set(inequality.dependencies) | equality_dependencies[left],
                members[left],
                "equal concrete variables are also asserted unequal",
            )
        edge = (left, right) if left < right else (right, left)
        adjacency[left].add(right)
        adjacency[right].add(left)
        prior_dependencies = edge_dependencies.get(edge)
        current_dependencies = set(inequality.dependencies)
        if prior_dependencies is None or _dependency_key(current_dependencies) < _dependency_key(
            prior_dependencies
        ):
            edge_dependencies[edge] = current_dependencies

    for left, right in edge_dependencies:
        first = fixed.get(left)
        second = fixed.get(right)
        if (
            first is not None
            and second is not None
            and first.value.data_identity == second.value.data_identity
        ):
            return _clash(
                DatatypeClashKind.UNSATISFIABLE_INEQUALITIES,
                edge_dependencies[(left, right)]
                | first.dependencies
                | second.dependencies
                | equality_dependencies[left]
                | equality_dependencies[right],
                members[left] + members[right],
                "unequal concrete variables have the same fixed data identity",
            )

    return _Prepared(
        component,
        representatives,
        representative_by_variable,
        members,
        equality_dependencies,
        domains,
        domain_dependencies,
        fixed,
        adjacency,
        edge_dependencies,
    )


def _colour(
    prepared: _Prepared,
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
    work: _Work,
    *,
    exhaustive: bool,
) -> DatatypeSolveResult:
    fixed_identities = {
        representative: value.value.data_identity
        for representative, value in prepared.fixed.items()
    }
    unfixed = set(prepared.representatives) - set(fixed_identities)
    forbidden_by_fixed = {
        variable: {
            fixed_identities[neighbour]
            for neighbour in prepared.adjacency[variable]
            if neighbour in fixed_identities
        }
        for variable in unfixed
    }
    active = set(unfixed)
    eliminated: list[int] = []
    if not exhaustive:
        changed = True
        while changed:
            changed = False
            for variable in sorted(active):
                work.add()
                degree = sum(neighbour in active for neighbour in prepared.adjacency[variable])
                required = degree + len(forbidden_by_fixed[variable]) + 1
                if prepared.domains[variable].cardinality_at_least(
                    required,
                    limits=limits,
                    cancellation=cancellation,
                ):
                    active.remove(variable)
                    eliminated.append(variable)
                    changed = True
                    break

    candidates: dict[int, tuple[DataIdentity, ...]] = {}
    for variable in sorted(active):
        work.add()
        try:
            values = prepared.domains[variable].enumerate_identities(
                limits=limits,
                cancellation=cancellation,
            )
        except ValueError as error:
            if exhaustive:
                raise ValueError(
                    "the exhaustive datatype solver requires finite variable domains"
                ) from error
            raise AssertionError(
                "a non-eliminable inequality variable must have a finite domain"
            ) from error
        candidates[variable] = tuple(
            value for value in values if value not in forbidden_by_fixed[variable]
        )
        if not candidates[variable]:
            return _search_clash(prepared, active)

    colouring = _search_colouring(candidates, prepared.adjacency, work)
    if colouring is None:
        return _search_clash(prepared, active)

    values_by_representative: dict[int, DataIdentity | None] = {
        **fixed_identities,
        **colouring,
    }
    for variable in reversed(eliminated):
        values_by_representative[variable] = _finite_eliminated_witness(
            variable,
            prepared,
            values_by_representative,
            limits,
            cancellation,
            work,
        )
    assignments = tuple(
        DatatypeVariableAssignment(
            variable,
            values_by_representative.get(prepared.representative_by_variable[variable]),
        )
        for variable in prepared.component.variables
    )
    return DatatypeSolveResult(True, assignments)


def _search_colouring(
    candidates: dict[int, tuple[DataIdentity, ...]],
    adjacency: dict[int, set[int]],
    work: _Work,
) -> dict[int, DataIdentity] | None:
    assignment: dict[int, DataIdentity] = {}
    stack: list[_SearchFrame] = []
    while len(assignment) < len(candidates):
        unassigned = set(candidates) - set(assignment)
        available = {
            variable: tuple(
                value
                for value in candidates[variable]
                if all(assignment.get(neighbour) != value for neighbour in adjacency[variable])
            )
            for variable in unassigned
        }
        variable = min(
            unassigned,
            key=lambda item: (
                len(available[item]),
                -sum(neighbour in unassigned for neighbour in adjacency[item]),
                item,
            ),
        )
        stack.append(_SearchFrame(variable, available[variable]))
        if not _advance_search(stack, assignment, adjacency, work):
            return None
    return assignment


def _advance_search(
    stack: list[_SearchFrame],
    assignment: dict[int, DataIdentity],
    adjacency: dict[int, set[int]],
    work: _Work,
) -> bool:
    while stack:
        frame = stack[-1]
        assignment.pop(frame.variable, None)
        while frame.next_index < len(frame.values):
            value = frame.values[frame.next_index]
            frame.next_index += 1
            work.add()
            if all(assignment.get(neighbour) != value for neighbour in adjacency[frame.variable]):
                assignment[frame.variable] = value
                return True
        stack.pop()
    return False


def _finite_eliminated_witness(
    variable: int,
    prepared: _Prepared,
    assigned: dict[int, DataIdentity | None],
    limits: DatatypeLimits,
    cancellation: CancellationToken | None,
    work: _Work,
) -> DataIdentity | None:
    cardinality = prepared.domains[variable].finite_cardinality(
        limits=limits,
        cancellation=cancellation,
    )
    if cardinality is None or cardinality > limits.max_enumeration_values:
        return None
    forbidden = {
        value
        for neighbour in prepared.adjacency[variable]
        if (value := assigned.get(neighbour)) is not None
    }
    for value in prepared.domains[variable].enumerate_identities(
        limits=limits,
        cancellation=cancellation,
    ):
        work.add()
        if value not in forbidden:
            return value
    raise AssertionError("elimination cardinality proof did not leave a witness")


def _search_clash(
    prepared: _Prepared,
    active: set[int],
) -> DatatypeSolveResult:
    dependencies: set[int] = set()
    variables: list[int] = []
    relevant = set(active)
    for representative in relevant:
        variables.extend(prepared.members[representative])
        dependencies.update(prepared.domain_dependencies[representative])
        dependencies.update(prepared.equality_dependencies[representative])
        fixed = prepared.fixed.get(representative)
        if fixed is not None:
            dependencies.update(fixed.dependencies)
        for neighbour in prepared.adjacency[representative]:
            if neighbour in relevant or neighbour in prepared.fixed:
                edge = (
                    (representative, neighbour)
                    if representative < neighbour
                    else (neighbour, representative)
                )
                dependencies.update(prepared.edge_dependencies[edge])
                if neighbour in prepared.fixed:
                    dependencies.update(prepared.fixed[neighbour].dependencies)
                    dependencies.update(prepared.equality_dependencies[neighbour])
                    variables.extend(prepared.members[neighbour])
    return _clash(
        DatatypeClashKind.UNSATISFIABLE_INEQUALITIES,
        dependencies,
        variables,
        "the finite inequality core has no satisfying data-value assignment",
    )


def _clash(
    kind: DatatypeClashKind,
    dependencies: Iterable[int],
    variables: Iterable[int],
    message: str,
) -> DatatypeSolveResult:
    return DatatypeSolveResult(
        False,
        clash=DatatypeClash(
            kind,
            _freeze_dependencies(dependencies),
            tuple(variables),
            message,
        ),
    )


def _freeze_dependencies(value: Iterable[int]) -> ConstraintDependencies:
    try:
        dependencies = frozenset(value)
    except TypeError as error:
        raise TypeError("dependencies must be an iterable of integers") from error
    if not all(_is_variable(item) for item in dependencies):
        raise TypeError("dependencies must contain nonnegative integers")
    return dependencies


def _dependency_key(value: set[int]) -> tuple[int, tuple[int, ...]]:
    return (len(value), tuple(sorted(value)))


def _is_variable(value: object) -> bool:
    return not isinstance(value, bool) and isinstance(value, int) and value >= 0


def _validate_variable(value: object) -> None:
    if not _is_variable(value):
        raise TypeError("variable must be a nonnegative integer")


__all__ = [
    "ConstraintDependencies",
    "DatatypeClash",
    "DatatypeClashKind",
    "DatatypeConstraintComponent",
    "DatatypeConstraintSolver",
    "DatatypeSolveResult",
    "DatatypeVariableAssignment",
    "DomainCardinalityConstraint",
    "EqualityConstraint",
    "FixedValueConstraint",
    "InequalityConstraint",
    "RangeConstraint",
    "solve_datatype_constraints",
    "solve_datatype_constraints_exhaustive",
]
