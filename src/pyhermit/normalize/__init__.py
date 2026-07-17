"""Deterministic OWL normalization over exact pyowl-core structural values."""

from __future__ import annotations

from .expressions import (
    ExpressionDepthError,
    ExpressionNormalizationCancelled,
    ExpressionNormalizer,
    UnknownExpressionError,
)
from .model import (
    NORMALIZATION_SCHEMA_VERSION,
    DataRangeInclusion,
    DefinitionRecord,
    NormalizedFamily,
    NormalizedOntology,
    NormalizedQuery,
    NormalizedRecord,
    Polarity,
)
from .normalizer import (
    AXIOM_HANDLER_TABLE,
    NormalizationLimits,
    UnknownAxiomError,
    UnsupportedNormalizationError,
    normalize_axioms,
    normalize_query,
    normalize_view,
)

__all__ = [
    "AXIOM_HANDLER_TABLE",
    "NORMALIZATION_SCHEMA_VERSION",
    "DataRangeInclusion",
    "DefinitionRecord",
    "ExpressionDepthError",
    "ExpressionNormalizationCancelled",
    "ExpressionNormalizer",
    "NormalizationLimits",
    "NormalizedFamily",
    "NormalizedOntology",
    "NormalizedQuery",
    "NormalizedRecord",
    "Polarity",
    "UnknownAxiomError",
    "UnknownExpressionError",
    "UnsupportedNormalizationError",
    "normalize_axioms",
    "normalize_query",
    "normalize_view",
]
