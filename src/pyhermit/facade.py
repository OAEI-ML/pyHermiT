"""Stable Python-native reasoner facade over immutable shared ontology views.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import hashlib
import json
import threading
from collections.abc import Iterable, Iterator, Mapping
from contextlib import contextmanager, suppress
from dataclasses import dataclass
from enum import Enum
from time import perf_counter
from types import MappingProxyType
from typing import TypeVar, cast

import pyowl_core
import pyowl_core.model as owl
from pyowl_core import IRI, ImportResolver, LoadOptions, OntologyInput, OntologyView

from pyhermit.backends.dispatch import (
    NATIVE_ABI_VERSION,
    backend_info,
    select_backend_factory,
)
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
from pyhermit.core import (
    COMPILER_CACHE_SCHEMA_VERSION,
    CapturedOntology,
    capture_compatible_view,
)
from pyhermit.events import CancellationSource
from pyhermit.exceptions import (
    BackendVersionError,
    ConcurrentMutationError,
    DisposedReasonerError,
)
from pyhermit.inputs import ValidatedOntology, capture_ontology
from pyhermit.normalize import NormalizedOntology
from pyhermit.services import (
    ClassificationService,
    CompiledQueryExecutor,
    EncodedQueryExecutor,
    EntailmentService,
    QueryExecutor,
)
from pyhermit.services.realization import IndividualResults, RealizationService

EntityT = TypeVar("EntityT", bound=owl.Entity)

_ENCODED_DIAGNOSTIC_DEFAULTS: Mapping[str, bool | int] = MappingProxyType(
    {
        "encoded_buffer_bytes": 0,
        "encoded_buffer_count": 0,
        "encoded_compiler_gil_released": False,
        "encoded_detached_buffer_count": 0,
        "encoded_indexed_buffer_count": 0,
        "encoded_posting_bytes": 0,
        "encoded_private_ir_bytes": 0,
        "encoded_referenced_view_count": 0,
        "encoded_segment_count": 0,
        "encoded_staging_copy_bytes": 0,
        "encoded_zero_copy_buffers": 0,
    }
)


class InferenceType(str, Enum):
    CLASS_HIERARCHY = "class_hierarchy"
    OBJECT_PROPERTY_HIERARCHY = "object_property_hierarchy"
    DATA_PROPERTY_HIERARCHY = "data_property_hierarchy"
    CLASS_ASSERTIONS = "class_assertions"
    OBJECT_PROPERTY_ASSERTIONS = "object_property_assertions"
    SAME_INDIVIDUAL = "same_individual"


@dataclass(slots=True)
class _Runtime:
    normalized: NormalizedOntology | None
    program: ClauseProgram | None
    compiled: CompiledOntology | None
    compiler_digest: str
    session: BackendSession
    executor: QueryExecutor
    entailment: EntailmentService
    classification: ClassificationService
    realization: RealizationService
    result_mapper: CompiledResultMapper | None
    consumer_compile_seconds: float
    ingestion_diagnostics: Mapping[str, bool | int]


def _canonical_compiler_digest(compiled: CompiledOntology) -> str:
    """Hash the complete compiler manifest without the path-specific session key."""

    manifest = compiled.canonical_manifest()
    fingerprints = manifest.get("fingerprints")
    if not isinstance(fingerprints, dict) or "ontology" not in fingerprints:
        raise RuntimeError("compiled ontology manifest lost its fingerprint contract")
    canonical_fingerprints = dict(fingerprints)
    del canonical_fingerprints["ontology"]
    manifest["fingerprints"] = canonical_fingerprints
    encoded = json.dumps(
        manifest,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    return hashlib.sha256(b"pyhermit/compiler-digest/v1\0" + encoded).hexdigest()


def _encoded_session_diagnostics(session: BackendSession) -> Mapping[str, bool | int]:
    values = getattr(session, "ingestion_counters", None)
    if not isinstance(values, Mapping) or values.keys() != _ENCODED_DIAGNOSTIC_DEFAULTS.keys():
        raise BackendVersionError(
            "encoded native session has no complete ingestion ledger",
            context={"reason": "session_surface_invalid"},
        )
    canonical: dict[str, bool | int] = {}
    for key, expected in _ENCODED_DIAGNOSTIC_DEFAULTS.items():
        value = values[key]
        if type(value) is not type(expected) or (type(value) is int and value < 0):
            raise BackendVersionError(
                "encoded native session returned an invalid ingestion ledger",
                context={"reason": "session_surface_invalid"},
            )
        canonical[key] = value
    if canonical["encoded_buffer_count"] == 0:
        raise BackendVersionError(
            "encoded native session reported no structural buffers",
            context={"reason": "session_surface_invalid"},
        )
    return MappingProxyType(canonical)


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
        profile_validator = getattr(
            self._factory,
            "_validate_encoded_profile_handoff",
            None,
        )
        validated = capture_ontology(
            ontology,
            config=selected_config,
            document_iri=document_iri,
            load_options=load_options,
            resolver=resolver,
            cancelled=self._cancelled,
            _profile_validator=profile_validator if callable(profile_validator) else None,
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

    def diagnostics(self) -> Mapping[str, bool | int | float | str]:
        """Return immutable, path-safe compiler and ingestion diagnostics.

        The ``encoded_*`` values account only for structural-view compilation into
        the permanent session.  Scalar compatibility paths therefore report exact
        zero values even when the native adapter performs a validation-only encoded
        preflight before its private wire handoff.
        """

        with self._state_lock:
            compiler_digest = self._runtime.compiler_digest
            consumer_compile_seconds = self._runtime.consumer_compile_seconds
            ingestion_diagnostics = self._runtime.ingestion_diagnostics
            encoded_native = self._runtime.program is None
            backend = self._factory.info
        values: dict[str, bool | int | float | str] = {
            "compiler_cache_schema_version": COMPILER_CACHE_SCHEMA_VERSION,
            "compiler_digest": compiler_digest,
            "consumer_compile_seconds": consumer_compile_seconds,
            **_ENCODED_DIAGNOSTIC_DEFAULTS,
            **ingestion_diagnostics,
            "implementation_version": backend.implementation_version,
            "ingestion_path": (
                "encoded-native"
                if encoded_native
                else ("scalar-python" if backend.name == "python" else "scalar-wire")
            ),
            "ir_schema_version": backend.ir_schema_version,
        }
        if backend.name in {"native", "verify"}:
            values["native_abi_version"] = NATIVE_ABI_VERSION
        return MappingProxyType(dict(sorted(values.items())))

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
        compile_started = perf_counter()
        session = self._create_encoded_lifecycle_session(validated.captured)
        try:
            if session is not None:
                return self._encoded_services(
                    validated,
                    session,
                    compile_started=compile_started,
                )
            bundle = compile_captured_bundle(
                validated.captured,
                self._config,
                cancelled=self._cancelled,
            )
            session = self._create_backend_session(validated.view, bundle[2])
            return self._services(bundle, session, compile_started=compile_started)
        except BaseException:
            if session is not None:
                session.close()
            raise

    def _create_encoded_lifecycle_session(
        self,
        captured: CapturedOntology,
        *,
        validate_profile: bool = True,
    ) -> BackendSession | None:
        create_encoded = getattr(self._factory, "_create_encoded_lifecycle_handoff", None)
        if not callable(create_encoded):
            return None
        return cast(
            BackendSession | None,
            create_encoded(
                captured,
                self._config,
                self._cancellation.token,
                validate_profile=validate_profile,
            ),
        )

    def _create_backend_session(
        self,
        view: OntologyView,
        compiled: CompiledOntology,
    ) -> BackendSession:
        create_encoded = getattr(self._factory, "_create_encoded_session_handoff", None)
        session = (
            create_encoded(
                view,
                compiled,
                self._config,
                self._cancellation.token,
            )
            if callable(create_encoded)
            else None
        )
        if session is None:
            session = self._factory.create_session(
                compiled,
                self._config,
                self._cancellation.token,
            )
        return session

    def _encoded_services(
        self,
        validated: ValidatedOntology,
        session: BackendSession,
        *,
        compile_started: float,
    ) -> _Runtime:
        context_loader = getattr(session, "_encoded_service_context", None)
        if not callable(context_loader):
            raise BackendVersionError(
                "encoded native session has no service-context exporter",
                context={"reason": "session_surface_invalid"},
            )
        context = context_loader(validated.view.signature())
        executor = EncodedQueryExecutor(
            context,
            session,
            temporary_check=self._temporary_encoded_check,
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
        mapper = executor.result_mapper
        self._install_native_providers(
            session,
            classification,
            realization,
            mapper,
        )
        return _Runtime(
            None,
            None,
            None,
            context.compiler_digest,
            session,
            executor,
            entailment,
            classification,
            realization,
            mapper,
            perf_counter() - compile_started,
            _encoded_session_diagnostics(session),
        )

    def _services(
        self,
        bundle: tuple[NormalizedOntology, ClauseProgram, CompiledOntology],
        session: BackendSession,
        *,
        compile_started: float,
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
            self._install_native_providers(
                session,
                classification,
                realization,
                mapper,
            )

        return _Runtime(
            normalized,
            program,
            compiled,
            _canonical_compiler_digest(compiled),
            session,
            executor,
            entailment,
            classification,
            realization,
            result_mapper,
            perf_counter() - compile_started,
            _ENCODED_DIAGNOSTIC_DEFAULTS,
        )

    @staticmethod
    def _install_native_providers(
        session: BackendSession,
        classification: ClassificationService,
        realization: RealizationService,
        mapper: CompiledResultMapper,
    ) -> None:
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
        session = self._create_backend_session(overlay, bundle[2])
        try:
            return session.check()
        finally:
            session.close()

    def _temporary_encoded_check(
        self,
        axioms: tuple[owl.AxiomNode, ...],
    ) -> CheckResult:
        overlay = pyowl_core.apply_delta(
            self._validated.view,
            pyowl_core.OntologyDelta(add_axioms=owl.CanonicalSet(axioms)),
        )
        captured = capture_compatible_view(overlay)
        # Query-reduction overlays contain private witness axioms rather than a
        # replacement public ontology.  They are already derived from the
        # validated source and therefore bypass the ontology-profile gate while
        # retaining every structural/resource check in the native constructor.
        session = self._create_encoded_lifecycle_session(
            captured,
            validate_profile=False,
        )
        if session is None:
            raise BackendVersionError(
                "encoded query compilation lost its negotiated native capability",
                context={"reason": "encoded_session_capability_lost"},
            )
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
        profile_validator = getattr(
            self._factory,
            "_validate_encoded_profile_handoff",
            None,
        )
        validated = capture_ontology(
            proposed,
            config=self._config,
            cancelled=self._cancelled,
            _profile_validator=profile_validator if callable(profile_validator) else None,
        )
        compile_started = perf_counter()
        old = self._runtime
        if old.program is None:
            session = self._create_encoded_lifecycle_session(validated.captured)
            if session is None:
                raise BackendVersionError(
                    "encoded update compilation lost its negotiated native capability",
                    context={"reason": "encoded_session_capability_lost"},
                )
            try:
                runtime = self._encoded_services(
                    validated,
                    session,
                    compile_started=compile_started,
                )
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
            return

        bundle = compile_captured_bundle(
            validated.captured,
            self._config,
            cancelled=self._cancelled,
        )
        if old.program is None:
            raise RuntimeError("scalar update path lost its compiled program")
        delta = compile_delta_plan(
            old.program,
            bundle[1],
            additions=additions,
            removals=removals,
        )
        outcome = old.session.apply_delta(cast(BackendCompiledDelta, delta))
        if outcome is DeltaOutcome.APPLIED_INCREMENTALLY:
            runtime = self._services(bundle, old.session, compile_started=compile_started)
        else:
            session = self._create_backend_session(validated.view, bundle[2])
            try:
                runtime = self._services(bundle, session, compile_started=compile_started)
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
