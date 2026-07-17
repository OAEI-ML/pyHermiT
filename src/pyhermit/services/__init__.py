"""Backend-neutral logical services over immutable compiled HermiT state."""

from __future__ import annotations

from .checks import CompiledQueryExecutor, QueryPlan, TemporaryQueryChecker
from .classification import ClassificationDomain, ClassificationService
from .entailment import ENTAILMENT_REDUCTION_TYPES, EntailmentService

__all__ = [
    "ENTAILMENT_REDUCTION_TYPES",
    "ClassificationDomain",
    "ClassificationService",
    "CompiledQueryExecutor",
    "EntailmentService",
    "QueryPlan",
    "TemporaryQueryChecker",
]
