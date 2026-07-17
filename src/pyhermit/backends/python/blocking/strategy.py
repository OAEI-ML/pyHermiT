"""Deterministic blocking strategy selection.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import cast

from pyhermit.config import BlockingMode

from .signatures import DirectCheckerKind


class _StringEnum(str, Enum):
    def __str__(self) -> str:
        return cast(str, self.value)


class BlockingManagerKind(_StringEnum):
    ANCESTOR = "ancestor"
    ANYWHERE = "anywhere"
    VALIDATED_ANYWHERE = "validated_anywhere"


class CoreBlockingMode(_StringEnum):
    NONE = "none"
    SIMPLE = "simple"
    COMPLEX = "complex"


@dataclass(frozen=True, slots=True)
class BlockingRequirements:
    has_inverse_roles: bool = False
    has_nominals: bool = False
    requires_validated_core: bool = False
    complex_core: bool = False
    has_additional_ontology: bool = False
    query_local_axioms: bool = False

    def __post_init__(self) -> None:
        for name in (
            "has_inverse_roles",
            "has_nominals",
            "requires_validated_core",
            "complex_core",
            "has_additional_ontology",
            "query_local_axioms",
        ):
            if not isinstance(getattr(self, name), bool):
                raise TypeError(f"{name} must be bool")
        if self.complex_core and not self.requires_validated_core:
            raise ValueError("complex_core requires validated core blocking")


@dataclass(frozen=True, slots=True)
class BlockingPlan:
    manager_kind: BlockingManagerKind
    direct_checker_kind: DirectCheckerKind
    core_mode: CoreBlockingMode
    cache_allowed: bool

    @property
    def validated(self) -> bool:
        return self.manager_kind is BlockingManagerKind.VALIDATED_ANYWHERE


def select_blocking_plan(
    mode: BlockingMode,
    requirements: BlockingRequirements,
) -> BlockingPlan:
    if not isinstance(mode, BlockingMode):
        raise TypeError("mode must be BlockingMode")
    if not isinstance(requirements, BlockingRequirements):
        raise TypeError("requirements must be BlockingRequirements")

    validated = mode is BlockingMode.VALIDATED_ANYWHERE or (
        mode is BlockingMode.AUTO and requirements.requires_validated_core
    )
    if validated:
        manager = BlockingManagerKind.VALIDATED_ANYWHERE
        direct = DirectCheckerKind.VALIDATED_SINGLE
        core = CoreBlockingMode.COMPLEX if requirements.complex_core else CoreBlockingMode.SIMPLE
    else:
        manager = (
            BlockingManagerKind.ANCESTOR
            if mode is BlockingMode.ANCESTOR
            else BlockingManagerKind.ANYWHERE
        )
        direct = (
            DirectCheckerKind.PAIRWISE
            if requirements.has_inverse_roles
            else DirectCheckerKind.SINGLE
        )
        core = CoreBlockingMode.NONE
    cache_allowed = not (
        validated
        or requirements.has_nominals
        or requirements.has_additional_ontology
        or requirements.query_local_axioms
    )
    return BlockingPlan(manager, direct, core, cache_allowed)


__all__ = [
    "BlockingManagerKind",
    "BlockingPlan",
    "BlockingRequirements",
    "CoreBlockingMode",
    "select_blocking_plan",
]
