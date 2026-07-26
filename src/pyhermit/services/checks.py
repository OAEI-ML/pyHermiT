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
from typing import Protocol, TypeVar, cast, runtime_checkable

import pyowl_core.model as owl

from pyhermit.backends.native_context import NativeServiceContext
from pyhermit.backends.native_mapping import CompiledResultMapper, MappedRealization
from pyhermit.backends.protocol import (
    BackendSession,
    CheckResult,
    Hierarchy,
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
_T = TypeVar("_T")


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


class EncodedQueryExecutor:
    """Execute query-local core overlays without constructing scalar compiler records."""

    __slots__ = (
        "_cache",
        "_cache_size",
        "_cancelled",
        "_class_hierarchy",
        "_context",
        "_data_hierarchy",
        "_mapper",
        "_object_hierarchy",
        "_realization",
        "_session",
        "_temporary_check",
    )

    def __init__(
        self,
        context: NativeServiceContext,
        session: BackendSession,
        *,
        temporary_check: TemporaryQueryChecker,
        cancelled: Callable[[], bool] | None = None,
        cache_size: int = _DEFAULT_QUERY_CACHE_SIZE,
    ) -> None:
        if not isinstance(context, NativeServiceContext):
            raise TypeError("context must be NativeServiceContext")
        required_session_methods = ("check", "check_many", "reset_query_state")
        if not all(callable(getattr(session, name, None)) for name in required_session_methods):
            raise TypeError("session must satisfy BackendSession")
        if not callable(temporary_check):
            raise TypeError("temporary_check must be callable")
        if cancelled is not None and not callable(cancelled):
            raise TypeError("cancelled must be callable or None")
        if isinstance(cache_size, bool) or not isinstance(cache_size, int) or cache_size < 0:
            raise ValueError("cache_size must be a nonnegative integer")
        self._context = context
        self._mapper = context.result_mapper()
        self._session = session
        self._temporary_check = temporary_check
        self._cancelled = cancelled
        self._cache_size = cache_size
        self._cache: OrderedDict[str, CheckResult] = OrderedDict()
        self._class_hierarchy: Hierarchy[owl.Class] | None = None
        self._object_hierarchy: Hierarchy[owl.ObjectPropertyExpression] | None = None
        self._data_hierarchy: Hierarchy[owl.DataProperty] | None = None
        self._realization: MappedRealization | None = None

    @property
    def service_context(self) -> NativeServiceContext:
        return self._context

    @property
    def session(self) -> BackendSession:
        return self._session

    @property
    def result_mapper(self) -> CompiledResultMapper:
        return self._mapper

    @property
    def permanent_program_sha256(self) -> str:
        return self._context.permanent_program_sha256

    def check_permanent(self) -> CheckResult:
        return _require_result(self._session.check())

    def check(self, plan: QueryPlan) -> CheckResult:
        if not isinstance(plan, QueryPlan):
            raise TypeError("plan must be QueryPlan")
        key = _plan_key(plan)
        retained = self._cache.get(key)
        if retained is not None:
            self._cache.move_to_end(key)
            return retained
        _raise_if_cancelled(self._cancelled)
        result = _require_result(self._temporary_check(plan.axioms))
        _raise_if_cancelled(self._cancelled)
        if self._cache_size:
            self._cache[key] = result
            self._cache.move_to_end(key)
            while len(self._cache) > self._cache_size:
                self._cache.popitem(last=False)
        return result

    def check_many(
        self,
        plans: Sequence[QueryPlan] | Iterable[QueryPlan],
    ) -> tuple[CheckResult, ...]:
        values = tuple(plans)
        if not all(isinstance(value, QueryPlan) for value in values):
            raise TypeError("plans must contain QueryPlan values")
        return tuple(self.check(value) for value in values)

    def clear_cache(self) -> None:
        self._cache.clear()

    def semantic_shortcut(self, axiom: owl.LogicalAxiom) -> bool | None:
        """Answer finite named-domain entailments from native coarse results."""

        if (
            isinstance(axiom, owl.SubClassOf)
            and isinstance(axiom.sub_class, owl.Class)
            and isinstance(axiom.super_class, owl.Class)
        ):
            return _hierarchy_shortcut(
                self._classes(),
                axiom.sub_class,
                axiom.super_class,
            )
        if isinstance(axiom, owl.EquivalentClasses) and all(
            isinstance(value, owl.Class) for value in axiom.expressions
        ):
            return _one_hierarchy_node(
                self._classes(),
                tuple(cast(owl.Class, value) for value in axiom.expressions),
            )
        if isinstance(axiom, owl.SubObjectPropertyOf) and isinstance(
            axiom.sub_property,
            (owl.ObjectProperty, owl.ObjectInverseOf),
        ):
            return _hierarchy_shortcut(
                self._object_properties(),
                axiom.sub_property,
                axiom.super_property,
            )
        if isinstance(axiom, owl.EquivalentObjectProperties):
            return _one_hierarchy_node(
                self._object_properties(),
                tuple(axiom.properties),
            )
        if isinstance(axiom, owl.InverseObjectProperties):
            return _one_hierarchy_node(
                self._object_properties(),
                (owl.inverse_property(axiom.first), axiom.second),
            )
        if isinstance(axiom, owl.SubDataPropertyOf):
            return _hierarchy_shortcut(
                self._data_properties(),
                axiom.sub_property,
                axiom.super_property,
            )
        if isinstance(axiom, owl.EquivalentDataProperties):
            return _one_hierarchy_node(
                self._data_properties(),
                tuple(axiom.properties),
            )
        if (
            isinstance(axiom, owl.ClassAssertion)
            and isinstance(axiom.class_expression, owl.Class)
            and isinstance(axiom.individual, owl.NamedIndividual)
        ):
            return self._has_named_type(
                axiom.individual,
                axiom.class_expression,
            )
        if (
            isinstance(axiom, owl.ObjectPropertyAssertion)
            and isinstance(axiom.source, owl.NamedIndividual)
            and isinstance(axiom.target, owl.NamedIndividual)
        ):
            return self._has_object_target(
                axiom.source,
                axiom.property,
                axiom.target,
            )
        if isinstance(axiom, owl.DataPropertyAssertion) and isinstance(
            axiom.source, owl.NamedIndividual
        ):
            if axiom.value not in self._context.source_literals:
                return None
            return self._has_data_target(
                axiom.source,
                axiom.property,
                axiom.value,
            )
        if isinstance(axiom, owl.SameIndividual) and all(
            isinstance(value, owl.NamedIndividual) for value in axiom.individuals
        ):
            if any(value not in self._context.source_signature for value in axiom.individuals):
                return None
            groups = self._realized().same_as
            return any(all(value in group for value in axiom.individuals) for group in groups)
        if isinstance(axiom, owl.DifferentIndividuals) and all(
            isinstance(value, owl.NamedIndividual) for value in axiom.individuals
        ):
            if any(value not in self._context.source_signature for value in axiom.individuals):
                return None
            group_by_member = self._group_by_member()
            individuals = tuple(cast(owl.NamedIndividual, value) for value in axiom.individuals)
            group_ids = tuple(group_by_member[value] for value in individuals)
            different = self._realized().different_from
            return all(
                tuple(sorted((left, right))) in different
                for index, left in enumerate(group_ids)
                for right in group_ids[index + 1 :]
            )
        return None

    def _classes(self) -> Hierarchy[owl.Class]:
        retained = self._class_hierarchy
        if retained is None:
            retained = self._mapper.class_hierarchy(self._session.classify_classes())
            self._class_hierarchy = retained
        return retained

    def _object_properties(self) -> Hierarchy[owl.ObjectPropertyExpression]:
        retained = self._object_hierarchy
        if retained is None:
            retained = self._mapper.object_property_hierarchy(
                self._session.classify_object_properties()
            )
            self._object_hierarchy = retained
        return retained

    def _data_properties(self) -> Hierarchy[owl.DataProperty]:
        retained = self._data_hierarchy
        if retained is None:
            retained = self._mapper.data_property_hierarchy(
                self._session.classify_data_properties()
            )
            self._data_hierarchy = retained
        return retained

    def _realized(self) -> MappedRealization:
        retained = self._realization
        if retained is None:
            retained = self._mapper.realization(
                self._session.realize(),
                self._classes(),
            )
            self._realization = retained
        return retained

    def _group_by_member(self) -> dict[owl.NamedIndividual, int]:
        return {
            member: group_id
            for group_id, group in enumerate(self._realized().same_as)
            for member in group
        }

    def _has_named_type(
        self,
        individual: owl.NamedIndividual,
        class_: owl.Class,
    ) -> bool | None:
        group_id = self._group_by_member().get(individual)
        class_node = _hierarchy_node(self._classes(), class_)
        if group_id is None or class_node is None:
            return None
        direct = dict(self._realized().direct_types).get(group_id, frozenset())
        return any(
            node == class_node or class_node in self._classes().ancestors(node) for node in direct
        )

    def _has_object_target(
        self,
        subject: owl.NamedIndividual,
        property_: owl.ObjectPropertyExpression,
        object_: owl.NamedIndividual,
    ) -> bool | None:
        groups = self._group_by_member()
        subject_group = groups.get(subject)
        object_group = groups.get(object_)
        if (
            subject_group is None
            or object_group is None
            or property_ not in self._mapper.object_property_ids.values()
        ):
            return None
        return any(
            group_id == subject_group
            and candidate_property == property_
            and object_group in targets
            for group_id, candidate_property, targets in self._realized().object_targets
        )

    def _has_data_target(
        self,
        subject: owl.NamedIndividual,
        property_: owl.DataProperty,
        value: owl.Literal,
    ) -> bool | None:
        subject_group = self._group_by_member().get(subject)
        if subject_group is None or property_ not in self._mapper.data_property_ids.values():
            return None
        return any(
            group_id == subject_group and candidate_property == property_ and value in targets
            for group_id, candidate_property, targets in self._realized().data_targets
        )


QueryExecutor = CompiledQueryExecutor | EncodedQueryExecutor


def _hierarchy_node(hierarchy: Hierarchy[_T], value: _T) -> int | None:
    return next(
        (node_id for node_id, members in enumerate(hierarchy.nodes) if value in members),
        None,
    )


def _hierarchy_shortcut(hierarchy: Hierarchy[_T], child: _T, parent: _T) -> bool | None:
    child_node = _hierarchy_node(hierarchy, child)
    parent_node = _hierarchy_node(hierarchy, parent)
    if child_node is None or parent_node is None:
        return None
    return child_node == parent_node or parent_node in hierarchy.ancestors(child_node)


def _one_hierarchy_node(hierarchy: Hierarchy[_T], values: tuple[_T, ...]) -> bool | None:
    nodes = tuple(_hierarchy_node(hierarchy, value) for value in values)
    if any(node is None for node in nodes):
        return None
    return len(set(nodes)) == 1


def _raise_if_cancelled(cancelled: Callable[[], bool] | None) -> None:
    if cancelled is not None and cancelled():
        from pyhermit.exceptions import ReasonerInterruptedError

        raise ReasonerInterruptedError("reasoning operation was interrupted")


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


__all__ = [
    "CompiledQueryExecutor",
    "EncodedQueryExecutor",
    "QueryExecutor",
    "QueryPlan",
    "TemporaryQueryChecker",
]
