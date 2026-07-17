"""Exact immutable hierarchy construction and classification algorithms."""

from __future__ import annotations

from .builder import build_hierarchy, hierarchy_from_partition, relation_closure
from .classifier import (
    ClassificationMode,
    ClassificationResult,
    ClassificationStatistics,
    IncrementalClassifier,
    SlowAllPairsClassifier,
    SubsumptionOracle,
    canonical_structural_key,
)
from .model import HierarchyIndex

__all__ = [
    "ClassificationMode",
    "ClassificationResult",
    "ClassificationStatistics",
    "HierarchyIndex",
    "IncrementalClassifier",
    "SlowAllPairsClassifier",
    "SubsumptionOracle",
    "build_hierarchy",
    "canonical_structural_key",
    "hierarchy_from_partition",
    "relation_closure",
]
