"""Stable Python-native reasoner facade over immutable shared ontology views.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import threading
from collections.abc import Iterable, Iterator, Mapping
from contextlib import contextmanager, suppress
from dataclasses import dataclass
from enum import Enum
from typing import TypeVar, cast

import pyowl_core
import pyowl_core.model as owl
from pyowl_core import IRI, ImportResolver, LoadOptions, OntologyInput, OntologyView

from pyhermit.backends.dispatch import backend_info, select_backend_factory
from pyhermit.backends.native_mapping import CompiledResultMapper, MappedRealization
from pyhermit.backends.protocol import (
    BackendInfo,
    BackendSession,
    CheckResult,
    CompiledOntology,
    DeltaOutcome,
    Hierarchy,
)
from pyhermit.backends.protocol import (
    CompiledDelta as BackendCompiledDelta,
)
from pyhermit.clauses import (
    ClauseProgram,
    compile_captured_bundle,
    compile_delta_plan,
)
from pyhermit.config import ReasonerConfig
from pyhermit.core import capture_compatible_view
from pyhermit.events import CancellationSource
from pyhermit.exceptions import (
    ConcurrentMutationError,
    DisposedReasonerError,
)
from pyhermit.inputs import ValidatedOntology, capture_ontology
from pyhermit.normalize import NormalizedOntology
from pyhermit.services import (
    ClassificationService,
    CompiledQueryExecutor,
    EntailmentService,
)
from pyhermit.services.realization import IndividualResults, RealizationService

EntityT = TypeVar("EntityT", bound=owl.Entity)


class InferenceType(str, Enum):
    CLASS_HIERARCHY = "class_hierarchy"
    OBJECT_PROPERTY_HIERARCHY = "object_property_hierarchy"
    DATA_PROPERTY_HIERARCHY = "data_property_hierarchy"
    CLASS_ASSERTIONS = "class_assertions"
    OBJECT_PROPERTY_ASSERTIONS = "object_property_assertions"
    SAME_INDIVIDUAL = "same_individual"


@dataclass(slots=True)
class _Runtime:
    normalized: NormalizedOntology
    program: ClauseProgram
    compiled: CompiledOntology
    session: BackendSession
    executor: CompiledQueryExecutor
    entailment: EntailmentService
    classification: ClassificationService
    realization: RealizationService
    result_mapper: CompiledResultMapper | None


class Reasoner:
    """One serialized reasoning session over a retained pyowl-core view."""

    def __init__(
        self,
        ontology: OntologyInput,
        *,
        config: ReasonerConfig | None = None,
        document_iri: IRI | str | None = None,
        load_options: LoadOptions | None = None,
        resolver: ImportResolver | None = None,
    ) -> None:
        selected_config = ReasonerConfig() if config is None else config
        if not isinstance(selected_config, ReasonerConfig):
            raise TypeError("config must be ReasonerConfig or None")
        self._config = selected_config
        self._state_lock = threading.Lock()
        self._operation_lock = threading.Lock()
        self._active_thread: int | None = None
        self._disposed = False
        self._cancellation = CancellationSource()
        self._cancellation.begin_operation(
            timeout=selected_config.timeout,
            max_memory_bytes=selected_config.max_memory_bytes,
        )
        self._factory = select_backend_factory(selected_config)
        validated = capture_ontology(
            ontology,
            config=selected_config,
            document_iri=document_iri,
            load_options=load_options,
            resolver=resolver,
            cancelled=self._cancelled,
        )
        self._validated = validated
        self._runtime = self._compile_runtime(validated)
        self._pending_additions: set[owl.AxiomNode] = set()
        self._pending_removals: set[owl.AxiomNode] = set()
        self._precomputed: set[InferenceType] = set()

    @property
    def ontology(self) -> OntologyView:
        with self._state_lock:
            return self._validated.view

    @property
    def config(self) -> ReasonerConfig:
        return self._config

    @property
    def backend(self) -> BackendInfo:
        return self._factory.info

    def interrupt(self) -> None:
        with self._state_lock:
            self._require_open()
            if self._active_thread is None:
                return
            self._cancellation.interrupt("reasoner interrupted by caller")

    def dispose(self) -> None:
        thread_id = threading.get_ident()
        with self._state_lock:
            if self._disposed:
                return
            if self._active_thread == thread_id:
                raise ConcurrentMutationError(
                    "cannot dispose a reasoner reentrantly from its active operation"
                )
        self._operation_lock.acquire()
        try:
            with self._state_lock:
                if self._is_disposed():
                    return
                self._active_thread = thread_id
            self._runtime.session.close()
            with self._state_lock:
                self._disposed = True
        finally:
            with self._state_lock:
                self._active_thread = None
            self._operation_lock.release()

    def __enter__(self) -> Reasoner:
        with self._state_lock:
            self._require_open()
        return self

    def __exit__(self, *_args: object) -> None:
        self.dispose()

    def is_consistent(self) -> bool:
        with self._operation():
            return self._runtime.entailment.is_consistent()

    def is_satisfiable(self, expression: owl.ClassExpression) -> bool:
        with self._operation():
            return self._runtime.entailment.is_satisfiable(expression)

    def is_subclass(
        self,
        sub: owl.ClassExpression,
        sup: owl.ClassExpression,
    ) -> bool:
        with self._operation():
            return self._runtime.entailment.is_subclass(sub, sup)

    def entails(self, axiom: owl.LogicalAxiom) -> bool:
        with self._operation():
            return self._runtime.entailment.entails(axiom)

    def entails_all(self, axioms: Iterable[owl.LogicalAxiom]) -> bool:
        with self._operation():
            return self._runtime.entailment.entails_all(axioms)

    def supports_entailment(self, axiom_type: type[owl.AxiomNode]) -> bool:
        with self._operation():
            return self._runtime.entailment.supports_entailment(axiom_type)

    def is_defined(self, entity: owl.Entity) -> bool:
        with self._operation():
            return self._runtime.entailment.is_defined(entity)

    def precompute(self, *types: InferenceType) -> None:
        requested = tuple(types)
        if not all(isinstance(value, InferenceType) for value in requested):
            raise TypeError("precompute values must be InferenceType")
        with self._operation():
            completed: set[InferenceType] = set()
            for value in requested:
                if value in self._precomputed or value in completed:
                    continue
                self._precompute(value)
                completed.add(value)
            self._precomputed.update(completed)

    def is_precomputed(self, type: InferenceType) -> bool:
        if not isinstance(type, InferenceType):
            raise TypeError("type must be InferenceType")
        with self._operation():
            return type in self._precomputed

    def precomputable(self) -> frozenset[InferenceType]:
        with self._operation():
            return frozenset(InferenceType)

    def class_hierarchy(self) -> Hierarchy[owl.Class]:
        with self._operation():
            return self._runtime.classification.class_hierarchy()

    def equivalent_classes(
        self,
        expression: owl.ClassExpression,
    ) -> frozenset[owl.Class]:
        with self._operation():
            return self._runtime.classification.equivalent_classes(expression)

    def superclasses(
        self,
        expression: owl.ClassExpression,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.Class]]:
        with self._operation():
            return self._runtime.classification.superclasses(expression, direct=direct)

    def subclasses(
        self,
        expression: owl.ClassExpression,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.Class]]:
        with self._operation():
            return self._runtime.classification.subclasses(expression, direct=direct)

    def unsatisfiable_classes(self) -> frozenset[owl.Class]:
        with self._operation():
            return self._runtime.classification.unsatisfiable_classes()

    def disjoint_classes(
        self,
        expression: owl.ClassExpression,
    ) -> frozenset[frozenset[owl.Class]]:
        with self._operation():
            return self._runtime.classification.disjoint_classes(expression)

    def object_property_hierarchy(self) -> Hierarchy[owl.ObjectPropertyExpression]:
        with self._operation():
            return self._runtime.classification.object_property_hierarchy()

    def equivalent_object_properties(
        self,
        property_: owl.ObjectPropertyExpression,
    ) -> frozenset[owl.ObjectPropertyExpression]:
        with self._operation():
            return self._runtime.classification.equivalent_object_properties(property_)

    def super_object_properties(
        self,
        property_: owl.ObjectPropertyExpression,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.ObjectPropertyExpression]]:
        with self._operation():
            return self._runtime.classification.super_object_properties(property_, direct=direct)

    def sub_object_properties(
        self,
        property_: owl.ObjectPropertyExpression,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.ObjectPropertyExpression]]:
        with self._operation():
            return self._runtime.classification.sub_object_properties(property_, direct=direct)

    def inverse_object_properties(
        self,
        property_: owl.ObjectPropertyExpression,
    ) -> frozenset[owl.ObjectPropertyExpression]:
        with self._operation():
            return self._runtime.classification.inverse_object_properties(property_)

    def disjoint_object_properties(
        self,
        property_: owl.ObjectPropertyExpression,
    ) -> frozenset[frozenset[owl.ObjectPropertyExpression]]:
        with self._operation():
            return self._runtime.classification.disjoint_object_properties(property_)

    def object_property_domains(
        self,
        property_: owl.ObjectPropertyExpression,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.Class]]:
        with self._operation():
            return self._runtime.classification.object_property_domains(property_, direct=direct)

    def object_property_ranges(
        self,
        property_: owl.ObjectPropertyExpression,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.Class]]:
        with self._operation():
            return self._runtime.classification.object_property_ranges(property_, direct=direct)

    def data_property_hierarchy(self) -> Hierarchy[owl.DataProperty]:
        with self._operation():
            return self._runtime.classification.data_property_hierarchy()

    def equivalent_data_properties(
        self,
        property_: owl.DataProperty,
    ) -> frozenset[owl.DataProperty]:
        with self._operation():
            return self._runtime.classification.equivalent_data_properties(property_)

    def super_data_properties(
        self,
        property_: owl.DataProperty,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.DataProperty]]:
        with self._operation():
            return self._runtime.classification.super_data_properties(property_, direct=direct)

    def sub_data_properties(
        self,
        property_: owl.DataProperty,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.DataProperty]]:
        with self._operation():
            return self._runtime.classification.sub_data_properties(property_, direct=direct)

    def disjoint_data_properties(
        self,
        property_: owl.DataProperty,
    ) -> frozenset[frozenset[owl.DataProperty]]:
        with self._operation():
            return self._runtime.classification.disjoint_data_properties(property_)

    def data_property_domains(
        self,
        property_: owl.DataProperty,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.Class]]:
        with self._operation():
            return self._runtime.classification.data_property_domains(property_, direct=direct)

    def types(
        self,
        individual: owl.NamedIndividual,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.Class]]:
        with self._operation():
            return self._runtime.realization.types(individual, direct=direct)

    def has_type(
        self,
        individual: owl.NamedIndividual,
        expression: owl.ClassExpression,
        *,
        direct: bool = False,
    ) -> bool:
        with self._operation():
            return self._runtime.realization.has_type(individual, expression, direct=direct)

    def instances(
        self,
        expression: owl.ClassExpression,
        *,
        direct: bool = False,
    ) -> IndividualResults:
        with self._operation():
            return self._runtime.realization.instances(expression, direct=direct)

    def same_individuals(
        self,
        individual: owl.NamedIndividual,
    ) -> frozenset[owl.NamedIndividual]:
        with self._operation():
            return self._runtime.realization.same_individuals(individual)

    def different_individuals(
        self,
        individual: owl.NamedIndividual,
    ) -> IndividualResults:
        with self._operation():
            return self._runtime.realization.different_individuals(individual)

    def object_property_values(
        self,
        subject: owl.NamedIndividual,
        property_: owl.ObjectPropertyExpression,
    ) -> IndividualResults:
        with self._operation():
            return self._runtime.realization.object_property_values(subject, property_)

    def object_property_instances(
        self,
        property_: owl.ObjectPropertyExpression,
    ) -> Mapping[owl.NamedIndividual, frozenset[owl.NamedIndividual]]:
        with self._operation():
            return self._runtime.realization.object_property_instances(property_)

    def has_object_property_relationship(
        self,
        subject: owl.NamedIndividual,
        property_: owl.ObjectPropertyExpression,
        object: owl.NamedIndividual,
    ) -> bool:
        with self._operation():
            return self._runtime.realization.has_object_property_relationship(
                subject, property_, object
            )

    def data_property_values(
        self,
        subject: owl.NamedIndividual,
        property_: owl.DataProperty,
    ) -> frozenset[owl.Literal]:
        with self._operation():
            return self._runtime.realization.data_property_values(subject, property_)

    def has_data_property_relationship(
        self,
        subject: owl.NamedIndividual,
        property_: owl.DataProperty,
        value: owl.Literal,
    ) -> bool:
        with self._operation():
            return self._runtime.realization.has_data_property_relationship(
                subject, property_, value
            )

    def add_axioms(self, axioms: Iterable[owl.AxiomNode]) -> None:
        values = _materialize_axioms(axioms)
        with self._operation():
            view = self._validated.view
            for axiom in values:
                if axiom in self._pending_removals:
                    self._pending_removals.remove(axiom)
                elif not view.contains(axiom):
                    self._pending_additions.add(axiom)
            if not self._config.buffer_changes:
                self._flush_locked()

    def remove_axioms(self, axioms: Iterable[owl.AxiomNode]) -> None:
        values = _materialize_axioms(axioms)
        with self._operation():
            view = self._validated.view
            for axiom in values:
                if axiom in self._pending_additions:
                    self._pending_additions.remove(axiom)
                elif view.contains(axiom):
                    self._pending_removals.add(axiom)
            if not self._config.buffer_changes:
                self._flush_locked()

    def pending_additions(self) -> frozenset[owl.AxiomNode]:
        with self._operation():
            return frozenset(self._pending_additions)

    def pending_removals(self) -> frozenset[owl.AxiomNode]:
        with self._operation():
            return frozenset(self._pending_removals)

    def flush(self) -> None:
        with self._operation():
            self._flush_locked()

    def _compile_runtime(self, validated: ValidatedOntology) -> _Runtime:
        validate_encoded = getattr(self._factory, "_validate_encoded_handoff", None)
        if callable(validate_encoded):
            validate_encoded(validated.view)
        bundle = compile_captured_bundle(
            validated.captured,
            self._config,
            cancelled=self._cancelled,
        )
        session = self._factory.create_session(bundle[2], self._config, self._cancellation.token)
        try:
            return self._services(bundle, session)
        except BaseException:
            session.close()
            raise

    def _services(
        self,
        bundle: tuple[NormalizedOntology, ClauseProgram, CompiledOntology],
        session: BackendSession,
    ) -> _Runtime:
        normalized, program, compiled = bundle
        executor = CompiledQueryExecutor(
            normalized,
            program,
            session,
            temporary_check=self._temporary_check,
            cancelled=self._cancelled,
        )
        entailment = EntailmentService(
            executor,
            fresh_entities=self._config.fresh_entities,
        )
        classification = ClassificationService(
            entailment,
            config=self._config,
            cancelled=self._cancelled,
        )
        realization = RealizationService(
            entailment,
            classification,
            config=self._config,
            cancelled=self._cancelled,
        )
        result_mapper: CompiledResultMapper | None = None
        if self._factory.info.name == "native":
            mapper = CompiledResultMapper(
                program,
                signature=entailment.source_signature,
                source_literals=realization.source_literals,
            )
            result_mapper = mapper
            classification._install_coarse_hierarchy_providers(
                classes=lambda: mapper.class_hierarchy(session.classify_classes()),
                object_properties=lambda: mapper.object_property_hierarchy(
                    session.classify_object_properties()
                ),
                data_properties=lambda: mapper.data_property_hierarchy(
                    session.classify_data_properties()
                ),
            )

            def coarse_realization() -> MappedRealization:
                class_hierarchy = classification.class_hierarchy()
                return mapper.realization(session.realize(), class_hierarchy)

            realization._install_coarse_provider(coarse_realization)
        return _Runtime(
            normalized,
            program,
            compiled,
            session,
            executor,
            entailment,
            classification,
            realization,
            result_mapper,
        )

    def _temporary_check(self, axioms: tuple[owl.AxiomNode, ...]) -> CheckResult:
        overlay = pyowl_core.apply_delta(
            self._validated.view,
            pyowl_core.OntologyDelta(add_axioms=owl.CanonicalSet(axioms)),
        )
        captured = capture_compatible_view(overlay)
        bundle = compile_captured_bundle(
            captured,
            self._config,
            cancelled=self._cancelled,
        )
        session = self._factory.create_session(bundle[2], self._config, self._cancellation.token)
        try:
            return session.check()
        finally:
            session.close()

    def _flush_locked(self) -> None:
        if not self._pending_additions and not self._pending_removals:
            return
        additions = frozenset(self._pending_additions)
        removals = frozenset(self._pending_removals)
        proposed = pyowl_core.apply_delta(
            self._validated.view,
            pyowl_core.OntologyDelta(
                add_axioms=owl.CanonicalSet(additions),
                remove_axioms=owl.CanonicalSet(removals),
            ),
        )
        validated = capture_ontology(
            proposed,
            config=self._config,
            cancelled=self._cancelled,
        )
        bundle = compile_captured_bundle(
            validated.captured,
            self._config,
            cancelled=self._cancelled,
        )
        old = self._runtime
        delta = compile_delta_plan(
            old.program,
            bundle[1],
            additions=additions,
            removals=removals,
        )
        outcome = old.session.apply_delta(cast(BackendCompiledDelta, delta))
        if outcome is DeltaOutcome.APPLIED_INCREMENTALLY:
            runtime = self._services(bundle, old.session)
        else:
            session = self._factory.create_session(
                bundle[2], self._config, self._cancellation.token
            )
            try:
                runtime = self._services(bundle, session)
            except BaseException:
                session.close()
                raise
            try:
                old.session.close()
            except BaseException:
                session.close()
                raise
        self._validated = validated
        self._runtime = runtime
        self._pending_additions.clear()
        self._pending_removals.clear()
        self._precomputed.clear()

    def _precompute(self, type: InferenceType) -> None:
        runtime = self._runtime
        if type is InferenceType.CLASS_HIERARCHY:
            runtime.classification.class_hierarchy()
        elif type is InferenceType.OBJECT_PROPERTY_HIERARCHY:
            runtime.classification.object_property_hierarchy()
        elif type is InferenceType.DATA_PROPERTY_HIERARCHY:
            runtime.classification.data_property_hierarchy()
        elif type is InferenceType.CLASS_ASSERTIONS:
            runtime.classification.class_hierarchy()
            for individual in _entities(runtime, owl.NamedIndividual):
                runtime.realization.types(individual)
        elif type is InferenceType.OBJECT_PROPERTY_ASSERTIONS:
            for property_ in _entities(runtime, owl.ObjectProperty):
                runtime.realization.object_property_instances(property_)
        elif type is InferenceType.SAME_INDIVIDUAL:
            for individual in _entities(runtime, owl.NamedIndividual):
                runtime.realization.same_individuals(individual)

    @contextmanager
    def _operation(self) -> Iterator[None]:
        thread_id = threading.get_ident()
        with self._state_lock:
            self._require_open()
            if self._active_thread == thread_id:
                raise ConcurrentMutationError(
                    "reentrant calls into the same reasoner are not allowed"
                )
        self._operation_lock.acquire()
        active = False
        try:
            with self._state_lock:
                self._require_open()
                self._active_thread = thread_id
                active = True
            token = self._cancellation.begin_operation(
                timeout=self._config.timeout,
                max_memory_bytes=self._config.max_memory_bytes,
            )
            token.check()
            try:
                yield
                token.check()
            except BaseException:
                with suppress(Exception):
                    self._runtime.session.reset_query_state()
                raise
        finally:
            if active:
                with self._state_lock:
                    self._active_thread = None
            self._operation_lock.release()

    def _cancelled(self) -> bool:
        self._cancellation.token.check()
        return False

    def _require_open(self) -> None:
        if self._disposed:
            raise DisposedReasonerError("reasoner is disposed")

    def _is_disposed(self) -> bool:
        return self._disposed


def _materialize_axioms(axioms: Iterable[owl.AxiomNode]) -> tuple[owl.AxiomNode, ...]:
    values = tuple(axioms)
    if not all(isinstance(value, owl.AxiomNode) for value in values):
        raise TypeError("axioms must contain exact pyowl-core AxiomNode values")
    return values


def _entities(
    runtime: _Runtime,
    type_: type[EntityT],
) -> tuple[EntityT, ...]:
    return tuple(
        sorted(
            (value for value in runtime.entailment.source_signature if isinstance(value, type_)),
            key=lambda value: value.canonical_bytes(),
        )
    )


__all__ = ["InferenceType", "Reasoner", "backend_info"]
