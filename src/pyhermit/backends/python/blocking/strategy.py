# Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory
# Modifications Copyright 2026 pyHermiT contributors
# Adapted from HermiT commit 37ec30aced32ac81ebecc5e33fad255ddefcb4c3;
# see reports/licensing/adapted-files.toml.

"""Deterministic blocking strategy selection.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TYPE_CHECKING, cast

from pyhermit.config import BlockingMode

from .signatures import DirectCheckerKind

if TYPE_CHECKING:
    from pyhermit.clauses import ClauseProgram


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
    direct_checker_kind: DirectCheckerKind | None = None

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
        if self.direct_checker_kind is not None and not isinstance(
            self.direct_checker_kind, DirectCheckerKind
        ):
            raise TypeError("direct_checker_kind must be DirectCheckerKind or None")

    @classmethod
    def from_program(
        cls,
        program: ClauseProgram,
        *,
        has_inverse_roles: bool | None = None,
        has_nominals: bool | None = None,
        requires_validated_core: bool = False,
        complex_core: bool = False,
        has_additional_ontology: bool = False,
        query_local_axioms: bool = False,
        direct_checker_kind: DirectCheckerKind | None = None,
    ) -> BlockingRequirements:
        from pyhermit.clauses import ClauseProgram

        if not isinstance(program, ClauseProgram):
            raise TypeError("program must be ClauseProgram")
        for name, value in (
            ("has_inverse_roles", has_inverse_roles),
            ("has_nominals", has_nominals),
        ):
            if value is not None and not isinstance(value, bool):
                raise TypeError(f"{name} must be bool or None")
        return cls(
            has_inverse_roles=(
                program.expressivity.inverse_roles
                if has_inverse_roles is None
                else has_inverse_roles
            ),
            has_nominals=(program.expressivity.nominals if has_nominals is None else has_nominals),
            requires_validated_core=requires_validated_core,
            complex_core=complex_core,
            has_additional_ontology=has_additional_ontology,
            query_local_axioms=query_local_axioms,
            direct_checker_kind=direct_checker_kind,
        )


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
        if requirements.direct_checker_kind in {
            DirectCheckerKind.PAIRWISE,
            DirectCheckerKind.VALIDATED_PAIRWISE,
        }:
            direct = DirectCheckerKind.VALIDATED_PAIRWISE
        else:
            direct = DirectCheckerKind.VALIDATED_SINGLE
        core = CoreBlockingMode.COMPLEX if requirements.complex_core else CoreBlockingMode.SIMPLE
    else:
        manager = (
            BlockingManagerKind.ANCESTOR
            if mode is BlockingMode.ANCESTOR
            else BlockingManagerKind.ANYWHERE
        )
        if requirements.direct_checker_kind in {
            DirectCheckerKind.VALIDATED_SINGLE,
            DirectCheckerKind.VALIDATED_PAIRWISE,
        }:
            raise ValueError("validated direct checkers require validated-anywhere blocking")
        direct = requirements.direct_checker_kind or (
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
