"""Compilation and execution boundary for isolated satisfiability queries.

The permanent normalized ontology, compiled program, and backend session are retained by
identity.  Overlay-safe queries use ``CompiledQuery``.  A query that changes role/schema
or tableau strategy is delegated to a caller-owned temporary checker; the public facade
can implement that checker with a zero-copy pyowl-core overlay and a short-lived backend
session, so no ontology document is parsed again.
"""

from __future__ import annotations

import hashlib
from collections import OrderedDict
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, replace
from typing import Protocol, cast, runtime_checkable

import pyowl_core.model as owl

from pyhermit.backends.protocol import (
    BackendSession,
    CheckResult,
)
from pyhermit.backends.protocol import (
    CompiledQuery as BackendCompiledQuery,
)
from pyhermit.clauses import (
    ClauseProgram,
    CompiledQuery,
    compile_query_program,
    prepare_query_compilation,
)
from pyhermit.exceptions import FeatureNotImplementedError
from pyhermit.normalize import NormalizedOntology, normalize_query

_DEFAULT_QUERY_CACHE_SIZE = 4_096


@dataclass(frozen=True, slots=True)
class QueryPlan:
    """One consistency reduction and its private result interpretation labels."""

    axioms: tuple[owl.AxiomNode, ...]
    interpretation: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        axioms = tuple(self.axioms)
        interpretation = tuple(self.interpretation)
        if not axioms:
            raise ValueError("a query plan requires at least one axiom")
        if not all(isinstance(value, owl.AxiomNode) for value in axioms):
            raise TypeError("query plan axioms must contain exact core AxiomNode values")
        if not all(isinstance(value, str) and value for value in interpretation):
            raise TypeError("query interpretation labels must be nonempty strings")
        object.__setattr__(self, "axioms", axioms)
        object.__setattr__(self, "interpretation", interpretation)


@runtime_checkable
class TemporaryQueryChecker(Protocol):
    """Execute query axioms in a temporary full compiled ontology.

    Implementations must combine the immutable permanent ontology with ``axioms``
    without reparsing source documents, create an isolated backend session, and close
    that session after returning (or raising).
    """

    def __call__(self, axioms: tuple[owl.AxiomNode, ...]) -> CheckResult: ...


class CompiledQueryExecutor:
    """Compile, cache, and execute immutable operation-local query reductions."""

    __slots__ = (
        "_cache",
        "_cache_size",
        "_cancelled",
        "_normalized",
        "_permanent_digest",
        "_program",
        "_query_context",
        "_session",
        "_temporary_check",
    )

    def __init__(
        self,
        normalized: NormalizedOntology,
        program: ClauseProgram,
        session: BackendSession,
        *,
        temporary_check: TemporaryQueryChecker | None = None,
        cancelled: Callable[[], bool] | None = None,
        cache_size: int = _DEFAULT_QUERY_CACHE_SIZE,
    ) -> None:
        if not isinstance(normalized, NormalizedOntology):
            raise TypeError("normalized must be NormalizedOntology")
        if not isinstance(program, ClauseProgram):
            raise TypeError("program must be ClauseProgram")
        required_session_methods = ("check", "check_many", "reset_query_state")
        if not all(callable(getattr(session, name, None)) for name in required_session_methods):
            raise TypeError("session must satisfy BackendSession")
        if temporary_check is not None and not callable(temporary_check):
            raise TypeError("temporary_check must be callable or None")
        if cancelled is not None and not callable(cancelled):
            raise TypeError("cancelled must be callable or None")
        if isinstance(cache_size, bool) or not isinstance(cache_size, int) or cache_size < 0:
            raise ValueError("cache_size must be a nonnegative integer")
        self._normalized = normalized
        self._program = program
        self._session = session
        self._temporary_check = temporary_check
        self._cancelled = cancelled
        self._cache_size = cache_size
        self._cache: OrderedDict[str, CompiledQuery] = OrderedDict()
        # This is deliberately the only permanent-program serialization on this path.
        self._permanent_digest = hashlib.sha256(program.canonical_bytes()).hexdigest()
        self._query_context = prepare_query_compilation(
            program,
            normalized,
            permanent_program_sha256=self._permanent_digest,
            cancelled=cancelled,
        )

    @property
    def normalized(self) -> NormalizedOntology:
        return self._normalized

    @property
    def program(self) -> ClauseProgram:
        return self._program

    @property
    def session(self) -> BackendSession:
        return self._session

    @property
    def permanent_program_sha256(self) -> str:
        return self._permanent_digest

    def check_permanent(self) -> CheckResult:
        result = self._session.check()
        return _require_result(result)

    def compile(self, plan: QueryPlan) -> CompiledQuery:
        if not isinstance(plan, QueryPlan):
            raise TypeError("plan must be QueryPlan")
        key = _plan_key(plan)
        retained = self._cache.get(key)
        if retained is not None:
            self._cache.move_to_end(key)
            return retained
        normalized_query = normalize_query(
            self._normalized,
            plan.axioms,
            cancelled=self._cancelled,
        )
        compiled = compile_query_program(
            self._program,
            self._normalized,
            normalized_query,
            cancelled=self._cancelled,
            permanent_program_sha256=self._permanent_digest,
            verify_immutable=False,
            query_context=self._query_context,
        )
        if plan.interpretation and not compiled.requires_rebuild:
            compiled = replace(compiled, interpretation=plan.interpretation)
        if self._cache_size:
            self._cache[key] = compiled
            self._cache.move_to_end(key)
            while len(self._cache) > self._cache_size:
                self._cache.popitem(last=False)
        return compiled

    def check(self, plan: QueryPlan) -> CheckResult:
        compiled = self.compile(plan)
        if compiled.requires_rebuild:
            return self._check_temporary(plan, compiled)
        try:
            return _require_result(self._session.check(cast(BackendCompiledQuery, compiled)))
        finally:
            self._session.reset_query_state()

    def check_many(
        self,
        plans: Sequence[QueryPlan] | Iterable[QueryPlan],
    ) -> tuple[CheckResult, ...]:
        """Execute a materialized batch without allowing query state to cross checks."""

        values = tuple(plans)
        if not all(isinstance(value, QueryPlan) for value in values):
            raise TypeError("plans must contain QueryPlan values")
        if not values:
            return ()
        compiled = tuple(self.compile(value) for value in values)
        results: list[CheckResult | None] = [None] * len(values)
        overlay_indexes = tuple(
            index for index, value in enumerate(compiled) if not value.requires_rebuild
        )
        if overlay_indexes:
            overlays = tuple(compiled[index] for index in overlay_indexes)
            try:
                checked = tuple(
                    self._session.check_many(cast(Sequence[BackendCompiledQuery], overlays))
                )
            finally:
                self._session.reset_query_state()
            if len(checked) != len(overlays):
                raise RuntimeError("backend returned the wrong number of batch check results")
            for index, result in zip(overlay_indexes, checked, strict=True):
                results[index] = _require_result(result)
        for index, value in enumerate(compiled):
            if value.requires_rebuild:
                results[index] = self._check_temporary(values[index], value)
        if any(value is None for value in results):
            raise RuntimeError("query batch left an unresolved result slot")
        return tuple(value for value in results if value is not None)

    def clear_cache(self) -> None:
        self._cache.clear()

    def _check_temporary(self, plan: QueryPlan, compiled: CompiledQuery) -> CheckResult:
        checker = self._temporary_check
        if checker is None:
            reason = compiled.reason or "query changes compiled strategy or schema"
            raise FeatureNotImplementedError(
                f"temporary full-ontology query checker is required: {reason}",
                feature_id="temporary-full-query-check",
            )
        return _require_result(checker(plan.axioms))


def _plan_key(plan: QueryPlan) -> str:
    digest = hashlib.sha256(b"pyhermit:query-plan:v1\x00")
    for axiom in plan.axioms:
        encoded = axiom.canonical_bytes()
        digest.update(len(encoded).to_bytes(8, "big"))
        digest.update(encoded)
    for label in plan.interpretation:
        encoded = label.encode("utf-8")
        digest.update(len(encoded).to_bytes(8, "big"))
        digest.update(encoded)
    return digest.hexdigest()


def _require_result(value: object) -> CheckResult:
    if not isinstance(value, CheckResult):
        raise TypeError("query checker must return CheckResult")
    return value


__all__ = ["CompiledQueryExecutor", "QueryPlan", "TemporaryQueryChecker"]
