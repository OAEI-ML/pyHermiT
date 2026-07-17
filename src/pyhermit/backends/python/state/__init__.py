"""Invariant-checked mutable state for the pure-Python hypertableau."""

from __future__ import annotations

from .dependencies import DependencyPool, DependencySet
from .disjunctions import (
    Clash,
    ClashKind,
    ClashStore,
    GroundDisjunction,
    GroundDisjunctionStore,
)
from .extensions import (
    AddFactOutcome,
    DeltaView,
    ExtensionStore,
    FactKey,
    FactRow,
    IndexPattern,
)
from .nodes import Node, NodeArena, NodeHandle, NodeKind, NodeLifecycle, NodeSort
from .queues import QueueEntry, StableQueue
from .session import BranchChoiceKind, BranchingPoint, TableauSession
from .trace import (
    STATE_TRACE_MAGIC,
    STATE_TRACE_VERSION,
    StateOperation,
    StateTrace,
    StateTraceRunner,
)
from .trail import Checkpoint, Trail

__all__ = [
    "STATE_TRACE_MAGIC",
    "STATE_TRACE_VERSION",
    "AddFactOutcome",
    "BranchChoiceKind",
    "BranchingPoint",
    "Checkpoint",
    "Clash",
    "ClashKind",
    "ClashStore",
    "DeltaView",
    "DependencyPool",
    "DependencySet",
    "ExtensionStore",
    "FactKey",
    "FactRow",
    "GroundDisjunction",
    "GroundDisjunctionStore",
    "IndexPattern",
    "Node",
    "NodeArena",
    "NodeHandle",
    "NodeKind",
    "NodeLifecycle",
    "NodeSort",
    "QueueEntry",
    "StableQueue",
    "StateOperation",
    "StateTrace",
    "StateTraceRunner",
    "TableauSession",
    "Trail",
]
