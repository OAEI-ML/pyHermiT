"""Immutable OWL 2 DL validation diagnostics over a captured core view.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from pyhermit.exceptions import OntologyProfileError
from pyhermit.roles import RoleAxiomGraph


class ProfileSeverity(str, Enum):
    INFO = "info"
    WARNING = "warning"
    ERROR = "error"


@dataclass(frozen=True, slots=True, order=True)
class ProfileIssue:
    rule_id: str
    severity: ProfileSeverity
    message: str
    constructor: str | None = None
    document_keys: tuple[str, ...] = ()
    provenance_sha256: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.rule_id, str) or not self.rule_id:
            raise ValueError("rule_id must be a nonempty string")
        if not isinstance(self.severity, ProfileSeverity):
            raise TypeError("severity must be ProfileSeverity")
        if not isinstance(self.message, str) or not self.message:
            raise ValueError("message must be a nonempty string")
        if self.constructor is not None and (
            not isinstance(self.constructor, str) or not self.constructor
        ):
            raise ValueError("constructor must be a nonempty string or None")
        keys = tuple(sorted(set(self.document_keys)))
        if not all(isinstance(value, str) and value for value in keys):
            raise TypeError("document_keys must contain nonempty strings")
        if self.provenance_sha256 is not None and (
            not isinstance(self.provenance_sha256, str)
            or len(self.provenance_sha256) != 64
            or any(value not in "0123456789abcdef" for value in self.provenance_sha256)
        ):
            raise ValueError("provenance_sha256 must be a SHA-256 hex digest or None")
        object.__setattr__(self, "document_keys", keys)


@dataclass(frozen=True, slots=True)
class OWL2DLReport:
    issues: tuple[ProfileIssue, ...]
    role_graph: RoleAxiomGraph
    axioms_checked: int
    extensions_checked: int
    complete: bool = True

    def __post_init__(self) -> None:
        issues = tuple(self.issues)
        if not all(isinstance(value, ProfileIssue) for value in issues):
            raise TypeError("issues must contain ProfileIssue values")
        issues = tuple(sorted(set(issues)))
        if not isinstance(self.role_graph, RoleAxiomGraph):
            raise TypeError("role_graph must be RoleAxiomGraph")
        for name in ("axioms_checked", "extensions_checked"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")
        if not isinstance(self.complete, bool):
            raise TypeError("complete must be bool")
        object.__setattr__(self, "issues", issues)

    @property
    def conforms(self) -> bool:
        return self.complete and not any(
            issue.severity is ProfileSeverity.ERROR for issue in self.issues
        )

    def raise_for_errors(self) -> None:
        if self.conforms:
            return
        errors = tuple(
            issue for issue in self.issues if issue.severity is ProfileSeverity.ERROR
        )
        codes = ", ".join(sorted({issue.rule_id for issue in errors}))
        raise OntologyProfileError(
            f"ontology is outside OWL 2 DL: {codes or 'incomplete validation'}",
            code="OWL2DL_PROFILE_VIOLATION",
            context={
                "issue_count": len(errors),
                "rule_ids": codes or None,
            },
        )


__all__ = ["OWL2DLReport", "ProfileIssue", "ProfileSeverity"]
