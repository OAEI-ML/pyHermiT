"""Exact class, object-property, and data-property classification services.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import itertools
import time
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass
from enum import Enum
from typing import TypeVar, cast

import pyowl_core.model as owl

from pyhermit.backends.protocol import Hierarchy
from pyhermit.config import ReasonerConfig
from pyhermit.events import ProgressEvent
from pyhermit.exceptions import (
    BackendMismatchError,
    InconsistentOntologyError,
    ReasonerInterruptedError,
)
from pyhermit.hierarchy import (
    ClassificationMode,
    ClassificationResult,
    ClassificationStatistics,
    HierarchyIndex,
    IncrementalClassifier,
    SlowAllPairsClassifier,
    build_hierarchy,
    canonical_structural_key,
)
from pyhermit.normalize import NormalizedRecord

from .entailment import EntailmentService

T = TypeVar("T")


class ClassificationDomain(str, Enum):
    CLASSES = "classes"
    OBJECT_PROPERTIES = "object_properties"
    DATA_PROPERTIES = "data_properties"


@dataclass(frozen=True, slots=True)
class _Position:
    parents: frozenset[int]
    children: frozenset[int]
    equivalent: int | None


class ClassificationService:
    """Lazily classify one immutable ontology without publishing partial caches."""

    __slots__ = (
        "_cancelled",
        "_class_hierarchy_provider",
        "_class_position_cache",
        "_classes",
        "_config",
        "_data_properties",
        "_data_property_hierarchy_provider",
        "_object_position_cache",
        "_object_properties",
        "_object_property_hierarchy_provider",
        "_operation_sequence",
        "_service",
        "_statistics",
    )

    def __init__(
        self,
        service: EntailmentService,
        *,
        config: ReasonerConfig | None = None,
        cancelled: Callable[[], bool] | None = None,
    ) -> None:
        if not isinstance(service, EntailmentService):
            raise TypeError("service must be EntailmentService")
        selected_config = ReasonerConfig() if config is None else config
        if not isinstance(selected_config, ReasonerConfig):
            raise TypeError("config must be ReasonerConfig or None")
        if cancelled is not None and not callable(cancelled):
            raise TypeError("cancelled must be callable or None")
        self._service = service
        self._config = selected_config
        self._cancelled = cancelled
        self._class_hierarchy_provider: Callable[[], Hierarchy[owl.Class]] | None = None
        self._object_property_hierarchy_provider: (
            Callable[[], Hierarchy[owl.ObjectPropertyExpression]] | None
        ) = None
        self._data_property_hierarchy_provider: (
            Callable[[], Hierarchy[owl.DataProperty]] | None
        ) = None
        self._classes: HierarchyIndex[owl.Class] | None = None
        self._object_properties: HierarchyIndex[owl.ObjectPropertyExpression] | None = None
        self._data_properties: HierarchyIndex[owl.DataProperty] | None = None
        self._statistics: dict[ClassificationDomain, ClassificationStatistics] = {}
        self._class_position_cache: dict[bytes, _Position] = {}
        self._object_position_cache: dict[bytes, _Position] = {}
        self._operation_sequence = 0

    def _install_coarse_hierarchy_providers(
        self,
        *,
        classes: Callable[[], Hierarchy[owl.Class]],
        object_properties: Callable[[], Hierarchy[owl.ObjectPropertyExpression]],
        data_properties: Callable[[], Hierarchy[owl.DataProperty]],
    ) -> None:
        """Install one native coarse boundary before any taxonomy cache is published."""

        providers = (classes, object_properties, data_properties)
        if not all(callable(provider) for provider in providers):
            raise TypeError("coarse hierarchy providers must be callable")
        if any(
            value is not None
            for value in (self._classes, self._object_properties, self._data_properties)
        ):
            raise RuntimeError("coarse hierarchy providers cannot change after classification")
        self._class_hierarchy_provider = classes
        self._object_property_hierarchy_provider = object_properties
        self._data_property_hierarchy_provider = data_properties

    def class_hierarchy(self) -> Hierarchy[owl.Class]:
        return self._class_index().hierarchy

    def object_property_hierarchy(self) -> Hierarchy[owl.ObjectPropertyExpression]:
        return self._object_index().hierarchy

    def data_property_hierarchy(self) -> Hierarchy[owl.DataProperty]:
        return self._data_index().hierarchy

    def statistics(
        self,
        domain: ClassificationDomain | str,
    ) -> ClassificationStatistics | None:
        try:
            selected = (
                domain if isinstance(domain, ClassificationDomain) else ClassificationDomain(domain)
            )
        except (TypeError, ValueError) as error:
            raise ValueError("unknown classification domain") from error
        return self._statistics.get(selected)

    def clear_caches(self) -> None:
        self._classes = None
        self._object_properties = None
        self._data_properties = None
        self._statistics.clear()
        self._class_position_cache.clear()
        self._object_position_cache.clear()

    def equivalent_classes(
        self,
        expression: owl.ClassExpression,
    ) -> frozenset[owl.Class]:
        _require_class_expression(expression)
        index = self._class_index()
        if isinstance(expression, owl.Class) and expression in index.by_member:
            return index.node(expression)
        position = self._class_position(expression, index)
        return (
            frozenset()
            if position.equivalent is None
            else index.hierarchy.nodes[position.equivalent]
        )

    def superclasses(
        self,
        expression: owl.ClassExpression,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.Class]]:
        _require_class_expression(expression)
        _require_bool(direct, "direct")
        index = self._class_index()
        if isinstance(expression, owl.Class) and expression in index.by_member:
            node_id = index.node_id(expression)
            return index.groups(index.supernodes(node_id, direct=direct))
        position = self._class_position(expression, index)
        if position.equivalent is not None:
            return index.groups(index.supernodes(position.equivalent, direct=direct))
        nodes = set(position.parents)
        if not direct:
            nodes.update(
                ancestor
                for parent in position.parents
                for ancestor in index.hierarchy.ancestors(parent)
            )
        return index.groups(frozenset(nodes))

    def subclasses(
        self,
        expression: owl.ClassExpression,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.Class]]:
        _require_class_expression(expression)
        _require_bool(direct, "direct")
        index = self._class_index()
        if isinstance(expression, owl.Class) and expression in index.by_member:
            node_id = index.node_id(expression)
            return index.groups(index.subnodes(node_id, direct=direct))
        position = self._class_position(expression, index)
        if position.equivalent is not None:
            return index.groups(index.subnodes(position.equivalent, direct=direct))
        nodes = set(position.children)
        if not direct:
            nodes.update(
                descendant
                for child in position.children
                for descendant in index.hierarchy.descendants(child)
            )
        return index.groups(frozenset(nodes))

    def unsatisfiable_classes(self) -> frozenset[owl.Class]:
        return self._class_index().bottom

    def disjoint_classes(
        self,
        expression: owl.ClassExpression,
    ) -> frozenset[frozenset[owl.Class]]:
        _require_class_expression(expression)
        index = self._class_index()
        representatives = tuple(_representative(node) for node in index.hierarchy.nodes)
        selected: set[int] = set()
        if (
            isinstance(expression, owl.Class)
            and expression in index.by_member
            and index.node_id(expression) == index.hierarchy.bottom_node
        ) or (
            not isinstance(expression, owl.Class)
            and not self._service.is_satisfiable(expression)
        ):
            # OWL Nothing, and every expression equivalent to it, is disjoint
            # with itself.  A CanonicalSet cannot represent the duplicate pair,
            # so account for the bottom node without constructing a unary axiom.
            selected.add(index.hierarchy.bottom_node)
        outcomes = self._service._entails_each(
            tuple(
                owl.DisjointClasses(owl.CanonicalSet((expression, representative)))
                for representative in representatives
                if representative != expression
            )
        )
        candidate_ids = tuple(
            node_id
            for node_id, representative in enumerate(representatives)
            if representative != expression
        )
        selected.update(
            node_id
            for node_id, entailed in zip(candidate_ids, outcomes, strict=True)
            if entailed
        )
        return index.groups(frozenset(selected))

    def equivalent_object_properties(
        self,
        property_: owl.ObjectPropertyExpression,
    ) -> frozenset[owl.ObjectPropertyExpression]:
        _require_object_property(property_)
        index = self._object_index()
        if property_ in index.by_member:
            return index.node(property_)
        position = self._object_position(property_, index)
        return (
            frozenset()
            if position.equivalent is None
            else index.hierarchy.nodes[position.equivalent]
        )

    def super_object_properties(
        self,
        property_: owl.ObjectPropertyExpression,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.ObjectPropertyExpression]]:
        _require_object_property(property_)
        _require_bool(direct, "direct")
        return self._property_groups(property_, self._object_index(), upward=True, direct=direct)

    def sub_object_properties(
        self,
        property_: owl.ObjectPropertyExpression,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.ObjectPropertyExpression]]:
        _require_object_property(property_)
        _require_bool(direct, "direct")
        return self._property_groups(property_, self._object_index(), upward=False, direct=direct)

    def inverse_object_properties(
        self,
        property_: owl.ObjectPropertyExpression,
    ) -> frozenset[owl.ObjectPropertyExpression]:
        _require_object_property(property_)
        inverse = owl.inverse_property(property_)
        index = self._object_index()
        result: set[owl.ObjectPropertyExpression] = {inverse}
        if inverse in index.by_member:
            result.update(index.node(inverse))
        else:
            position = self._object_position(inverse, index)
            if position.equivalent is not None:
                result.update(index.hierarchy.nodes[position.equivalent])
        return frozenset(result)

    def disjoint_object_properties(
        self,
        property_: owl.ObjectPropertyExpression,
    ) -> frozenset[frozenset[owl.ObjectPropertyExpression]]:
        _require_object_property(property_)
        index = self._object_index()
        return cast(
            frozenset[frozenset[owl.ObjectPropertyExpression]],
            self._disjoint_property_groups(property_, index, object_properties=True),
        )

    def object_property_domains(
        self,
        property_: owl.ObjectPropertyExpression,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.Class]]:
        _require_object_property(property_)
        _require_bool(direct, "direct")
        return self._property_class_groups(property_, direct=direct, range_query=False)

    def object_property_ranges(
        self,
        property_: owl.ObjectPropertyExpression,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.Class]]:
        _require_object_property(property_)
        _require_bool(direct, "direct")
        return self._property_class_groups(property_, direct=direct, range_query=True)

    def equivalent_data_properties(
        self,
        property_: owl.DataProperty,
    ) -> frozenset[owl.DataProperty]:
        _require_data_property(property_)
        index = self._data_index()
        if property_ in index.by_member:
            return index.node(property_)
        position = self._data_position(property_, index)
        return (
            frozenset()
            if position.equivalent is None
            else index.hierarchy.nodes[position.equivalent]
        )

    def super_data_properties(
        self,
        property_: owl.DataProperty,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.DataProperty]]:
        _require_data_property(property_)
        _require_bool(direct, "direct")
        return self._data_property_groups(property_, upward=True, direct=direct)

    def sub_data_properties(
        self,
        property_: owl.DataProperty,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.DataProperty]]:
        _require_data_property(property_)
        _require_bool(direct, "direct")
        return self._data_property_groups(property_, upward=False, direct=direct)

    def disjoint_data_properties(
        self,
        property_: owl.DataProperty,
    ) -> frozenset[frozenset[owl.DataProperty]]:
        _require_data_property(property_)
        return cast(
            frozenset[frozenset[owl.DataProperty]],
            self._disjoint_property_groups(
                property_,
                self._data_index(),
                object_properties=False,
            ),
        )

    def data_property_domains(
        self,
        property_: owl.DataProperty,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.Class]]:
        _require_data_property(property_)
        _require_bool(direct, "direct")
        index = self._class_index()
        representatives = tuple(_representative(node) for node in index.hierarchy.nodes)
        outcomes = self._service._entails_each(
            tuple(owl.DataPropertyDomain(property_, value) for value in representatives)
        )
        selected = frozenset(
            node_id for node_id, entailed in enumerate(outcomes) if entailed
        )
        return index.groups(_minimal_nodes(index, selected) if direct else selected)

    def classify_slow(
        self,
        domain: ClassificationDomain,
    ) -> ClassificationResult[object]:
        """Run the deliberately quadratic tiny-domain differential oracle."""

        if not isinstance(domain, ClassificationDomain):
            raise TypeError("domain must be ClassificationDomain")
        self._require_consistent()
        if domain is ClassificationDomain.CLASSES:
            class_elements = tuple(self._class_elements())
            return cast(
                ClassificationResult[object],
                SlowAllPairsClassifier(
                    class_elements,
                    self._test_classes,
                    top=owl.OWL_THING,
                    bottom=owl.OWL_NOTHING,
                    key=canonical_structural_key,
                    cancelled=self._cancelled,
                ).classify(),
            )
        if domain is ClassificationDomain.OBJECT_PROPERTIES:
            object_elements = tuple(self._object_elements())
            return cast(
                ClassificationResult[object],
                SlowAllPairsClassifier(
                    object_elements,
                    self._test_object_properties,
                    top=owl.OWL_TOP_OBJECT_PROPERTY,
                    bottom=owl.OWL_BOTTOM_OBJECT_PROPERTY,
                    key=canonical_structural_key,
                    cancelled=self._cancelled,
                ).classify(),
            )
        data_elements = tuple(self._data_elements())
        return cast(
            ClassificationResult[object],
            SlowAllPairsClassifier(
                data_elements,
                self._test_data_properties,
                top=owl.OWL_TOP_DATA_PROPERTY,
                bottom=owl.OWL_BOTTOM_DATA_PROPERTY,
                key=canonical_structural_key,
                cancelled=self._cancelled,
            ).classify(),
        )

    def _class_index(self) -> HierarchyIndex[owl.Class]:
        retained = self._classes
        if retained is not None:
            return retained
        provider = self._class_hierarchy_provider
        if provider is not None:
            self._classes = self._coarse_index(
                ClassificationDomain.CLASSES,
                self._class_elements(),
                provider,
                top=owl.OWL_THING,
                bottom=owl.OWL_NOTHING,
            )
            return self._classes
        result = self._classify(
            ClassificationDomain.CLASSES,
            tuple(self._class_elements()),
            self._test_classes,
            top=owl.OWL_THING,
            bottom=owl.OWL_NOTHING,
            known=self._known_class_relations(),
            complete=_class_told_relation_is_complete(self._service.normalized.records),
        )
        self._classes = result.hierarchy
        self._statistics[ClassificationDomain.CLASSES] = result.statistics
        return self._classes

    def _object_index(self) -> HierarchyIndex[owl.ObjectPropertyExpression]:
        retained = self._object_properties
        if retained is not None:
            return retained
        provider = self._object_property_hierarchy_provider
        if provider is not None:
            self._object_properties = self._coarse_index(
                ClassificationDomain.OBJECT_PROPERTIES,
                self._object_elements(),
                provider,
                top=owl.OWL_TOP_OBJECT_PROPERTY,
                bottom=owl.OWL_BOTTOM_OBJECT_PROPERTY,
            )
            return self._object_properties
        result = self._classify(
            ClassificationDomain.OBJECT_PROPERTIES,
            tuple(self._object_elements()),
            self._test_object_properties,
            top=owl.OWL_TOP_OBJECT_PROPERTY,
            bottom=owl.OWL_BOTTOM_OBJECT_PROPERTY,
            known=self._known_object_relations(),
            complete=_object_told_relation_is_complete(self._service.normalized.records),
        )
        self._object_properties = result.hierarchy
        self._statistics[ClassificationDomain.OBJECT_PROPERTIES] = result.statistics
        return self._object_properties

    def _data_index(self) -> HierarchyIndex[owl.DataProperty]:
        retained = self._data_properties
        if retained is not None:
            return retained
        provider = self._data_property_hierarchy_provider
        if provider is not None:
            self._data_properties = self._coarse_index(
                ClassificationDomain.DATA_PROPERTIES,
                self._data_elements(),
                provider,
                top=owl.OWL_TOP_DATA_PROPERTY,
                bottom=owl.OWL_BOTTOM_DATA_PROPERTY,
            )
            return self._data_properties
        result = self._classify(
            ClassificationDomain.DATA_PROPERTIES,
            tuple(self._data_elements()),
            self._test_data_properties,
            top=owl.OWL_TOP_DATA_PROPERTY,
            bottom=owl.OWL_BOTTOM_DATA_PROPERTY,
            known=self._known_data_relations(),
            complete=_data_told_relation_is_complete(self._service.normalized.records),
        )
        self._data_properties = result.hierarchy
        self._statistics[ClassificationDomain.DATA_PROPERTIES] = result.statistics
        return self._data_properties

    def _coarse_index(
        self,
        domain: ClassificationDomain,
        elements: Iterable[T],
        provider: Callable[[], Hierarchy[T]],
        *,
        top: T,
        bottom: T,
    ) -> HierarchyIndex[T]:
        self._require_consistent()
        self._checkpoint()
        expected = frozenset(elements)
        self._operation_sequence += 1
        operation_id = f"classification-{domain.value}-{self._operation_sequence}"
        started = time.perf_counter()
        self._emit_progress(
            operation_id,
            "classification-started",
            0,
            len(expected),
            started,
        )
        hierarchy = provider()
        if not isinstance(hierarchy, Hierarchy):
            raise BackendMismatchError(
                "coarse classification provider returned an incompatible result",
                context={"reason": "coarse_hierarchy_type"},
            )
        by_member = {
            member: node_id
            for node_id, node in enumerate(hierarchy.nodes)
            for member in node
        }
        if frozenset(by_member) != expected:
            raise BackendMismatchError(
                "coarse classification hierarchy does not cover exactly its public domain",
                context={"domain": domain.value, "reason": "coarse_hierarchy_partition"},
            )
        if top not in hierarchy.nodes[hierarchy.top_node] or bottom not in hierarchy.nodes[
            hierarchy.bottom_node
        ]:
            raise BackendMismatchError(
                "coarse classification hierarchy has invalid top or bottom membership",
                context={"domain": domain.value, "reason": "coarse_hierarchy_boundary"},
            )
        result = HierarchyIndex(hierarchy, by_member)
        self._checkpoint()
        self._emit_progress(
            operation_id,
            "classification-completed",
            len(expected),
            len(expected),
            started,
        )
        return result

    def _classify(
        self,
        domain: ClassificationDomain,
        elements: Sequence[T],
        tester: Callable[[tuple[tuple[T, T], ...]], tuple[bool, ...]],
        *,
        top: T,
        bottom: T,
        known: Iterable[tuple[T, T]],
        complete: bool,
    ) -> ClassificationResult[T]:
        self._require_consistent()
        self._checkpoint()
        mode = (
            ClassificationMode.QUASI_ORDER
            if self._config.force_quasi_order_classification
            or not self._service.deterministic_program
            else ClassificationMode.DETERMINISTIC
        )
        self._operation_sequence += 1
        operation_id = f"classification-{domain.value}-{self._operation_sequence}"
        started = time.perf_counter()
        self._emit_progress(operation_id, "classification-started", 0, len(elements), started)
        element_set = frozenset(elements)
        known_values = tuple(
            (child, parent)
            for child, parent in known
            if child in element_set and parent in element_set
        )
        if complete:
            hierarchy = build_hierarchy(
                elements,
                known_values,
                top=top,
                bottom=bottom,
                key=canonical_structural_key,
            )
            statistics = ClassificationStatistics(
                mode=mode,
                elements=len(elements),
                semantic_tests=0,
                batches=0,
                cache_hits=0,
                known_subsumptions=len(known_values),
                possible_subsumptions=0,
            )
            result = ClassificationResult(hierarchy, statistics)
        else:
            result = IncrementalClassifier(
                elements,
                tester,
                top=top,
                bottom=bottom,
                key=canonical_structural_key,
                known=known_values,
                mode=mode,
                cancelled=self._cancelled,
            ).classify()
        self._checkpoint()
        self._emit_progress(
            operation_id,
            "classification-completed",
            len(elements),
            len(elements),
            started,
            statistics=result.statistics,
        )
        return result

    def _class_elements(self) -> frozenset[owl.Class]:
        return frozenset(
            {
                owl.OWL_THING,
                owl.OWL_NOTHING,
                *(
                    entity
                    for entity in self._service.source_signature
                    if isinstance(entity, owl.Class)
                ),
            }
        )

    def _object_elements(self) -> frozenset[owl.ObjectPropertyExpression]:
        named = {
            entity
            for entity in self._service.source_signature
            if isinstance(entity, owl.ObjectProperty)
        }
        named.update((owl.OWL_TOP_OBJECT_PROPERTY, owl.OWL_BOTTOM_OBJECT_PROPERTY))
        return frozenset(named | {owl.inverse_property(value) for value in named})

    def _data_elements(self) -> frozenset[owl.DataProperty]:
        return frozenset(
            {
                owl.OWL_TOP_DATA_PROPERTY,
                owl.OWL_BOTTOM_DATA_PROPERTY,
                *(
                    entity
                    for entity in self._service.source_signature
                    if isinstance(entity, owl.DataProperty)
                ),
            }
        )

    def _test_classes(
        self,
        pairs: tuple[tuple[owl.Class, owl.Class], ...],
    ) -> tuple[bool, ...]:
        return self._service._is_subclass_each(pairs)

    def _test_object_properties(
        self,
        pairs: tuple[
            tuple[owl.ObjectPropertyExpression, owl.ObjectPropertyExpression], ...
        ],
    ) -> tuple[bool, ...]:
        return self._service._entails_each(
            tuple(owl.SubObjectPropertyOf(sub, sup) for sub, sup in pairs)
        )

    def _test_data_properties(
        self,
        pairs: tuple[tuple[owl.DataProperty, owl.DataProperty], ...],
    ) -> tuple[bool, ...]:
        return self._service._entails_each(
            tuple(owl.SubDataPropertyOf(sub, sup) for sub, sup in pairs)
        )

    def _known_class_relations(self) -> frozenset[tuple[owl.Class, owl.Class]]:
        relations: set[tuple[owl.Class, owl.Class]] = set()
        for record in self._service.normalized.records:
            value = record.statement
            if isinstance(value, owl.SubClassOf) and isinstance(
                value.sub_class, owl.Class
            ) and isinstance(value.super_class, owl.Class):
                relations.add((value.sub_class, value.super_class))
            elif isinstance(value, owl.EquivalentClasses):
                classes = tuple(
                    expression
                    for expression in value.expressions
                    if isinstance(expression, owl.Class)
                )
                relations.update(itertools.permutations(classes, 2))
            elif isinstance(value, owl.DisjointUnion):
                relations.update(
                    (member, value.defined_class)
                    for member in value.expressions
                    if isinstance(member, owl.Class)
                )
        return frozenset(relations)

    def _known_object_relations(
        self,
    ) -> frozenset[tuple[owl.ObjectPropertyExpression, owl.ObjectPropertyExpression]]:
        relations: set[
            tuple[owl.ObjectPropertyExpression, owl.ObjectPropertyExpression]
        ] = set()

        def include(
            sub: owl.ObjectPropertyExpression,
            sup: owl.ObjectPropertyExpression,
        ) -> None:
            relations.add((sub, sup))
            relations.add((owl.inverse_property(sub), owl.inverse_property(sup)))

        for record in self._service.normalized.records:
            value = record.statement
            if isinstance(value, owl.SubObjectPropertyOf) and isinstance(
                value.sub_property, (owl.ObjectProperty, owl.ObjectInverseOf)
            ):
                include(value.sub_property, value.super_property)
            elif isinstance(value, owl.EquivalentObjectProperties):
                for left, right in itertools.permutations(value.properties, 2):
                    include(left, right)
            elif isinstance(value, owl.InverseObjectProperties):
                include(value.first, owl.inverse_property(value.second))
                include(value.second, owl.inverse_property(value.first))
        return frozenset(relations)

    def _known_data_relations(self) -> frozenset[tuple[owl.DataProperty, owl.DataProperty]]:
        relations: set[tuple[owl.DataProperty, owl.DataProperty]] = set()
        for record in self._service.normalized.records:
            value = record.statement
            if isinstance(value, owl.SubDataPropertyOf):
                relations.add((value.sub_property, value.super_property))
            elif isinstance(value, owl.EquivalentDataProperties):
                relations.update(itertools.permutations(value.properties, 2))
        return frozenset(relations)

    def _class_position(
        self,
        expression: owl.ClassExpression,
        index: HierarchyIndex[owl.Class],
    ) -> _Position:
        key = expression.canonical_bytes()
        retained = self._class_position_cache.get(key)
        if retained is not None:
            return retained
        position = _semantic_position(
            cast(HierarchyIndex[owl.ClassExpression], index),
            self._service._is_subclass_each,
            expression,
        )
        self._class_position_cache[key] = position
        return position

    def _object_position(
        self,
        property_: owl.ObjectPropertyExpression,
        index: HierarchyIndex[owl.ObjectPropertyExpression],
    ) -> _Position:
        key = property_.canonical_bytes()
        retained = self._object_position_cache.get(key)
        if retained is not None:
            return retained
        position = _semantic_position(
            index,
            lambda pairs: self._service._entails_each(
                tuple(owl.SubObjectPropertyOf(sub, sup) for sub, sup in pairs)
            ),
            property_,
        )
        self._object_position_cache[key] = position
        return position

    def _data_position(
        self,
        property_: owl.DataProperty,
        index: HierarchyIndex[owl.DataProperty],
    ) -> _Position:
        return _semantic_position(
            index,
            lambda pairs: self._service._entails_each(
                tuple(owl.SubDataPropertyOf(sub, sup) for sub, sup in pairs)
            ),
            property_,
        )

    def _property_groups(
        self,
        property_: owl.ObjectPropertyExpression,
        index: HierarchyIndex[owl.ObjectPropertyExpression],
        *,
        upward: bool,
        direct: bool,
    ) -> frozenset[frozenset[owl.ObjectPropertyExpression]]:
        if property_ in index.by_member:
            node = index.node_id(property_)
            selected = (
                index.supernodes(node, direct=direct)
                if upward
                else index.subnodes(node, direct=direct)
            )
        else:
            position = self._object_position(property_, index)
            selected = _position_nodes(index, position, upward=upward, direct=direct)
        return index.groups(selected)

    def _data_property_groups(
        self,
        property_: owl.DataProperty,
        *,
        upward: bool,
        direct: bool,
    ) -> frozenset[frozenset[owl.DataProperty]]:
        index = self._data_index()
        if property_ in index.by_member:
            node = index.node_id(property_)
            selected = (
                index.supernodes(node, direct=direct)
                if upward
                else index.subnodes(node, direct=direct)
            )
        else:
            selected = _position_nodes(
                index,
                self._data_position(property_, index),
                upward=upward,
                direct=direct,
            )
        return index.groups(selected)

    def _disjoint_property_groups(
        self,
        property_: owl.ObjectPropertyExpression | owl.DataProperty,
        index: HierarchyIndex[owl.ObjectPropertyExpression] | HierarchyIndex[owl.DataProperty],
        *,
        object_properties: bool,
    ) -> frozenset[frozenset[owl.ObjectPropertyExpression | owl.DataProperty]]:
        representatives = tuple(_representative(node) for node in index.hierarchy.nodes)
        axioms: tuple[owl.LogicalAxiom, ...]
        selected: set[int] = set()
        if object_properties:
            bottom_entailed = self._service.entails(
                owl.SubObjectPropertyOf(
                    cast(owl.ObjectPropertyExpression, property_),
                    owl.OWL_BOTTOM_OBJECT_PROPERTY,
                )
            )
            axioms = tuple(
                owl.DisjointObjectProperties(
                    owl.CanonicalSet(
                        (
                            cast(owl.ObjectPropertyExpression, property_),
                            cast(owl.ObjectPropertyExpression, representative),
                        )
                    )
                )
                for representative in representatives
                if representative != property_
            )
        else:
            bottom_entailed = self._service.entails(
                owl.SubDataPropertyOf(
                    cast(owl.DataProperty, property_),
                    owl.OWL_BOTTOM_DATA_PROPERTY,
                )
            )
            axioms = tuple(
                owl.DisjointDataProperties(
                    owl.CanonicalSet(
                        (
                            cast(owl.DataProperty, property_),
                            cast(owl.DataProperty, representative),
                        )
                    )
                )
                for representative in representatives
                if representative != property_
            )
        outcomes = self._service._entails_each(axioms)
        candidate_ids = tuple(
            node_id
            for node_id, representative in enumerate(representatives)
            if representative != property_
        )
        if bottom_entailed:
            selected.add(index.hierarchy.bottom_node)
        selected.update(
            node_id
            for node_id, entailed in zip(candidate_ids, outcomes, strict=True)
            if entailed
        )
        return index.groups(frozenset(selected))

    def _property_class_groups(
        self,
        property_: owl.ObjectPropertyExpression,
        *,
        direct: bool,
        range_query: bool,
    ) -> frozenset[frozenset[owl.Class]]:
        index = self._class_index()
        representatives = tuple(_representative(node) for node in index.hierarchy.nodes)
        axioms = tuple(
            (
                owl.ObjectPropertyRange(property_, value)
                if range_query
                else owl.ObjectPropertyDomain(property_, value)
            )
            for value in representatives
        )
        outcomes = self._service._entails_each(axioms)
        selected = frozenset(
            node_id for node_id, entailed in enumerate(outcomes) if entailed
        )
        return index.groups(_minimal_nodes(index, selected) if direct else selected)

    def _require_consistent(self) -> None:
        if not self._service.is_consistent():
            raise InconsistentOntologyError(
                "classification is undefined for an inconsistent ontology"
            )

    def _checkpoint(self) -> None:
        if self._cancelled is not None and self._cancelled():
            raise ReasonerInterruptedError("classification was interrupted")

    def _emit_progress(
        self,
        operation_id: str,
        kind: str,
        completed: int,
        total: int,
        started: float,
        *,
        statistics: ClassificationStatistics | None = None,
    ) -> None:
        callback = self._config.progress
        if callback is None:
            return
        details: dict[str, str | int | float | bool | None] = {}
        if statistics is not None:
            details.update(
                {
                    "batches": statistics.batches,
                    "mode": statistics.mode.value,
                    "semantic_tests": statistics.semantic_tests,
                }
            )
        callback(
            ProgressEvent(
                version=1,
                operation_id=operation_id,
                kind=kind,
                completed=completed,
                total=total,
                elapsed_seconds=time.perf_counter() - started,
                details=details,
            )
        )


def _semantic_position(
    index: HierarchyIndex[T],
    tester: Callable[[tuple[tuple[T, T], ...]], tuple[bool, ...]],
    element: T,
) -> _Position:
    parents = _semantic_boundary(index, tester, element, upward=False)
    children = _semantic_boundary(index, tester, element, upward=True)
    common = parents.intersection(children)
    if common and (parents != children or len(common) != 1):
        raise RuntimeError("semantic query violated hierarchy-position invariants")
    return _Position(
        frozenset(parents),
        frozenset(children),
        next(iter(common)) if common else None,
    )


def _semantic_boundary(
    index: HierarchyIndex[T],
    tester: Callable[[tuple[tuple[T, T], ...]], tuple[bool, ...]],
    element: T,
    *,
    upward: bool,
) -> set[int]:
    start = index.hierarchy.bottom_node if upward else index.hierarchy.top_node
    frontier = {start}
    visited: set[int] = set()
    proven_true = {start}
    boundary: set[int] = set()
    while frontier:
        successors = {
            node: (
                index.direct_supernodes(node) if upward else index.direct_subnodes(node)
            )
            for node in frontier
        }
        candidates = tuple(
            sorted(
                {
                    candidate
                    for values in successors.values()
                    for candidate in values
                    if candidate not in visited
                }
            )
        )
        pairs = tuple(
            (
                (_representative(index.hierarchy.nodes[candidate]), element)
                if upward
                else (element, _representative(index.hierarchy.nodes[candidate]))
            )
            for candidate in candidates
        )
        outcomes = tester(pairs)
        true_candidates = {
            candidate
            for candidate, outcome in zip(candidates, outcomes, strict=True)
            if outcome
        }
        proven_true.update(true_candidates)
        for node in frontier:
            if not successors[node].intersection(proven_true):
                boundary.add(node)
        visited.update(frontier)
        frontier = true_candidates - visited
    return boundary


def _position_nodes(
    index: HierarchyIndex[T],
    position: _Position,
    *,
    upward: bool,
    direct: bool,
) -> frozenset[int]:
    if position.equivalent is not None:
        return (
            index.supernodes(position.equivalent, direct=direct)
            if upward
            else index.subnodes(position.equivalent, direct=direct)
        )
    selected = set(position.parents if upward else position.children)
    if not direct:
        selected.update(
            related
            for node in tuple(selected)
            for related in (
                index.hierarchy.ancestors(node)
                if upward
                else index.hierarchy.descendants(node)
            )
        )
    return frozenset(selected)


def _minimal_nodes(index: HierarchyIndex[T], selected: frozenset[int]) -> frozenset[int]:
    return frozenset(
        node
        for node in selected
        if not index.hierarchy.descendants(node).intersection(selected)
    )


def _class_told_relation_is_complete(records: Sequence[NormalizedRecord]) -> bool:
    for record in records:
        statement = record.statement
        if not (
            isinstance(statement, owl.SubClassOf)
            and isinstance(statement.sub_class, owl.Class)
            and isinstance(statement.super_class, owl.Class)
        ):
            return False
    return True


def _object_told_relation_is_complete(records: Sequence[NormalizedRecord]) -> bool:
    for record in records:
        statement = record.statement
        if not (
            isinstance(statement, owl.SubObjectPropertyOf)
            and isinstance(
                statement.sub_property,
                (owl.ObjectProperty, owl.ObjectInverseOf),
            )
        ):
            return False
    return True


def _data_told_relation_is_complete(records: Sequence[NormalizedRecord]) -> bool:
    return all(isinstance(record.statement, owl.SubDataPropertyOf) for record in records)


def _representative(values: frozenset[T]) -> T:
    return min(values, key=canonical_structural_key)


def _require_class_expression(value: object) -> None:
    if not isinstance(value, owl.CLASS_EXPRESSION_TYPES):
        raise TypeError("expression must be an exact core ClassExpression")


def _require_object_property(value: object) -> None:
    if not isinstance(value, (owl.ObjectProperty, owl.ObjectInverseOf)):
        raise TypeError("property must be an exact core ObjectPropertyExpression")


def _require_data_property(value: object) -> None:
    if not isinstance(value, owl.DataProperty):
        raise TypeError("property must be an exact core DataProperty")


def _require_bool(value: object, name: str) -> None:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be bool")


__all__ = ["ClassificationDomain", "ClassificationService"]
