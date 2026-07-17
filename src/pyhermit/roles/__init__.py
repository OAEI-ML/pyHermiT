"""Pure-Python OWL 2 role hierarchy, regularity, and automata."""

from __future__ import annotations

from .builder import (
    build_role_axiom_graph,
    canonical_object_role,
    inverse_object_role,
)
from .model import (
    BuiltinRoleSemantics,
    ComplexRoleInclusion,
    DataRoleInclusion,
    NFATransition,
    RegularityViolation,
    RoleAutomaton,
    RoleAxiomGraph,
    RoleBuildLimits,
    RoleComponent,
    RoleInclusion,
    RoleRegularityError,
)

__all__ = [
    "BuiltinRoleSemantics",
    "ComplexRoleInclusion",
    "DataRoleInclusion",
    "NFATransition",
    "RegularityViolation",
    "RoleAutomaton",
    "RoleAxiomGraph",
    "RoleBuildLimits",
    "RoleComponent",
    "RoleInclusion",
    "RoleRegularityError",
    "build_role_axiom_graph",
    "canonical_object_role",
    "inverse_object_role",
]
