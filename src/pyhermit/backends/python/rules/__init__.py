"""Indexed hyperresolution rules for the pure-Python backend."""

from __future__ import annotations

from .engine import HyperresolutionEngine
from .joins import IndexedJoinEvaluator, NaiveJoinEvaluator
from .model import (
    BranchTransition,
    GroundRuleAtom,
    JoinMatch,
    PendingAnnotatedEquality,
    RuleLimits,
    VariableBinding,
)
from .plans import ClauseJoinPlan, JoinProgram, JoinStep, compile_join_program

__all__ = [
    "BranchTransition",
    "ClauseJoinPlan",
    "GroundRuleAtom",
    "HyperresolutionEngine",
    "IndexedJoinEvaluator",
    "JoinMatch",
    "JoinProgram",
    "JoinStep",
    "NaiveJoinEvaluator",
    "PendingAnnotatedEquality",
    "RuleLimits",
    "VariableBinding",
    "compile_join_program",
]
