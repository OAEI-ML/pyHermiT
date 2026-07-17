"""Pure-Python direct, ancestor, anywhere, and validated blocking."""

from __future__ import annotations

from .cache import BlockingCacheNamespace, BlockingSignatureCache
from .manager import BlockingAssignment, BlockingManager
from .signatures import (
    BlockingLabels,
    BlockingSignature,
    BlockingVocabulary,
    DirectBlockingChecker,
    DirectCheckerKind,
    PairwiseDirectBlockingChecker,
    SingleDirectBlockingChecker,
    ValidatedPairwiseDirectBlockingChecker,
    ValidatedSingleDirectBlockingChecker,
    create_direct_checker,
)
from .strategy import (
    BlockingManagerKind,
    BlockingPlan,
    BlockingRequirements,
    CoreBlockingMode,
    select_blocking_plan,
)
from .validation import BlockingValidator, ValidationDecision, ValidationPassResult

__all__ = [
    "BlockingAssignment",
    "BlockingCacheNamespace",
    "BlockingLabels",
    "BlockingManager",
    "BlockingManagerKind",
    "BlockingPlan",
    "BlockingRequirements",
    "BlockingSignature",
    "BlockingSignatureCache",
    "BlockingValidator",
    "BlockingVocabulary",
    "CoreBlockingMode",
    "DirectBlockingChecker",
    "DirectCheckerKind",
    "PairwiseDirectBlockingChecker",
    "SingleDirectBlockingChecker",
    "ValidatedPairwiseDirectBlockingChecker",
    "ValidatedSingleDirectBlockingChecker",
    "ValidationDecision",
    "ValidationPassResult",
    "create_direct_checker",
    "select_blocking_plan",
]
