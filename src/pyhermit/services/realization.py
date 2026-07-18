"""Exact finite named-individual realization and property answer services.

SPDX-License-Identifier: LGPL-3.0-or-later
"""

from __future__ import annotations

import itertools
import time
from collections.abc import Callable, Iterable, Mapping, Sequence
from dataclasses import dataclass
from types import MappingProxyType
from typing import TypeAlias, TypeVar

import pyowl_core.model as owl

from pyhermit.backends.native_mapping import MappedRealization
from pyhermit.config import IndividualGrouping, ReasonerConfig
from pyhermit.events import ProgressEvent
from pyhermit.exceptions import (
    BackendMismatchError,
    InconsistentOntologyError,
    ReasonerInterruptedError,
)
from pyhermit.normalize import DataRangeInclusion

from .classification import ClassificationService
from .entailment import EntailmentService

IndividualResults: TypeAlias = (
    frozenset[owl.NamedIndividual]
    | frozenset[frozenset[owl.NamedIndividual]]
)
T = TypeVar("T", owl.NamedIndividual, owl.Class)


@dataclass(frozen=True, slots=True)
class RealizationStatistics:
    """Observable logical work performed by one realization service."""

    entailment_tests: int
    batches: int
    cache_hits: int

    def __post_init__(self) -> None:
        for name in ("entailment_tests", "batches", "cache_hits"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a nonnegative integer")


class RealizationService:
    """Lazily refine exact named answers over one immutable ontology session.

    Unknown candidate relations remain absent from the caches until an isolated
    entailment batch decides them.  Each operation publishes its result only after
    the complete batch and cancellation checkpoint succeed.
    """

    __slots__ = (
        "_batches",
        "_cache_hits",
        "_cancelled",
        "_classification",
        "_coarse_loaded",
        "_coarse_provider",
        "_config",
        "_data_values",
        "_different_groups",
        "_entailment_tests",
        "_group_by_member",
        "_instance_groups",
        "_named",
        "_object_targets",
        "_operation_sequence",
        "_same_groups",
        "_service",
        "_source_literals",
        "_type_nodes",
    )

    def __init__(
        self,
        service: EntailmentService,
        classification: ClassificationService,
        *,
        config: ReasonerConfig | None = None,
        cancelled: Callable[[], bool] | None = None,
    ) -> None:
        if not isinstance(service, EntailmentService):
            raise TypeError("service must be EntailmentService")
        if not isinstance(classification, ClassificationService):
            raise TypeError("classification must be ClassificationService")
        selected_config = ReasonerConfig() if config is None else config
        if not isinstance(selected_config, ReasonerConfig):
            raise TypeError("config must be ReasonerConfig or None")
        if cancelled is not None and not callable(cancelled):
            raise TypeError("cancelled must be callable or None")
        self._service = service
        self._classification = classification
        self._coarse_provider: Callable[[], MappedRealization] | None = None
        self._coarse_loaded = False
        self._config = selected_config
        self._cancelled = cancelled
        self._named = tuple(
            sorted(
                (
                    value
                    for value in service.source_signature
                    if isinstance(value, owl.NamedIndividual)
                ),
                key=lambda value: value.canonical_bytes(),
            )
        )
        self._source_literals = _source_literals(service)
        self._same_groups: tuple[frozenset[owl.NamedIndividual], ...] | None = None
        self._group_by_member: Mapping[owl.NamedIndividual, int] | None = None
        self._type_nodes: dict[bytes, frozenset[int]] = {}
        self._instance_groups: dict[bytes, frozenset[int]] = {}
        self._different_groups: dict[bytes, frozenset[int]] = {}
        self._object_targets: dict[
            tuple[bytes, bytes],
            tuple[frozenset[owl.NamedIndividual], ...],
        ] = {}
        self._data_values: dict[tuple[bytes, bytes], frozenset[owl.Literal]] = {}
        self._entailment_tests = 0
        self._batches = 0
        self._cache_hits = 0
        self._operation_sequence = 0

    def _install_coarse_provider(
        self,
        provider: Callable[[], MappedRealization],
    ) -> None:
        """Install the complete native realization boundary before publishing caches."""

        if not callable(provider):
            raise TypeError("coarse realization provider must be callable")
        if self._coarse_loaded or any(
            (
                self._same_groups is not None,
                bool(self._type_nodes),
                bool(self._instance_groups),
                bool(self._different_groups),
                bool(self._object_targets),
                bool(self._data_values),
            )
        ):
            raise RuntimeError("coarse realization provider cannot change after realization")
        self._coarse_provider = provider

    @property
    def named_individuals(self) -> frozenset[owl.NamedIndividual]:
        return frozenset(self._named)

    @property
    def source_literals(self) -> frozenset[owl.Literal]:
        return frozenset(self._source_literals)

    @property
    def statistics(self) -> RealizationStatistics:
        return RealizationStatistics(
            entailment_tests=self._entailment_tests,
            batches=self._batches,
            cache_hits=self._cache_hits,
        )

    def clear_caches(self) -> None:
        self._coarse_loaded = False
        self._same_groups = None
        self._group_by_member = None
        self._type_nodes.clear()
        self._instance_groups.clear()
        self._different_groups.clear()
        self._object_targets.clear()
        self._data_values.clear()

    def types(
        self,
        individual: owl.NamedIndividual,
        *,
        direct: bool = False,
    ) -> frozenset[frozenset[owl.Class]]:
        _require_named_individual(individual)
        _require_bool(direct, "direct")
        self._validate_individual(individual)
        selected = self._type_node_ids(individual)
        if direct:
            selected = self._minimal_type_nodes(selected)
        hierarchy = self._classification.class_hierarchy()
        return frozenset(hierarchy.nodes[node] for node in selected)

    def has_type(
        self,
        individual: owl.NamedIndividual,
        expression: owl.ClassExpression,
        *,
        direct: bool = False,
    ) -> bool:
        _require_named_individual(individual)
        _require_class_expression(expression)
        _require_bool(direct, "direct")
        entailed = self._evaluate((owl.ClassAssertion(expression, individual),))[0]
        if not entailed or not direct:
            return entailed
        return self._is_direct_instance(individual, expression)

    def instances(
        self,
        expression: owl.ClassExpression,
        *,
        direct: bool = False,
    ) -> IndividualResults:
        _require_class_expression(expression)
        _require_bool(direct, "direct")
        self._validate_class_expression(expression)
        groups = self._same_partition()
        key = expression.canonical_bytes()
        retained = self._instance_groups.get(key)
        if retained is None:
            operation_id, started = self._start("instances", len(groups))
            outcomes = self._evaluate(
                tuple(
                    owl.ClassAssertion(expression, _representative(group))
                    for group in groups
                )
            )
            selected = frozenset(
                index
                for index, entailed in enumerate(outcomes)
                if entailed
            )
            self._checkpoint()
            self._instance_groups[key] = selected
            retained = selected
            self._finish(operation_id, len(groups), started)
        else:
            self._cache_hits += 1
        if direct:
            retained = frozenset(
                index
                for index in retained
                if self._is_direct_instance(_representative(groups[index]), expression)
            )
        return self._format_groups(tuple(groups[index] for index in sorted(retained)))

    def same_individuals(
        self,
        individual: owl.NamedIndividual,
    ) -> frozenset[owl.NamedIndividual]:
        _require_named_individual(individual)
        self._validate_individual(individual)
        groups = self._same_partition()
        by_member = self._require_group_index()
        group_id = by_member.get(individual)
        return frozenset((individual,)) if group_id is None else groups[group_id]

    def different_individuals(
        self,
        individual: owl.NamedIndividual,
    ) -> IndividualResults:
        _require_named_individual(individual)
        self._validate_individual(individual)
        groups = self._same_partition()
        own = self._group_id(individual)
        canonical = self._canonical_individual(individual)
        key = canonical.canonical_bytes()
        retained = self._different_groups.get(key)
        if retained is None:
            candidates = tuple(
                index for index in range(len(groups)) if index != own
            )
            outcomes = self._evaluate(
                tuple(
                    owl.DifferentIndividuals(
                        owl.CanonicalSet((individual, _representative(groups[index])))
                    )
                    for index in candidates
                )
            )
            selected = frozenset(
                index
                for index, entailed in zip(candidates, outcomes, strict=True)
                if entailed
            )
            self._checkpoint()
            self._different_groups[key] = selected
            retained = selected
        else:
            self._cache_hits += 1
        return self._format_groups(tuple(groups[index] for index in sorted(retained)))

    def object_property_values(
        self,
        subject: owl.NamedIndividual,
        property_: owl.ObjectPropertyExpression,
    ) -> IndividualResults:
        _require_named_individual(subject)
        _require_object_property(property_)
        self._validate_individual(subject)
        self._validate_object_property(property_)
        return self._format_groups(self._object_target_groups(subject, property_))

    def object_property_instances(
        self,
        property_: owl.ObjectPropertyExpression,
    ) -> Mapping[owl.NamedIndividual, frozenset[owl.NamedIndividual]]:
        _require_object_property(property_)
        self._validate_object_property(property_)
        answers: dict[owl.NamedIndividual, frozenset[owl.NamedIndividual]] = {}
        for subject_group in self._same_partition():
            targets = self._object_target_groups(
                _representative(subject_group),
                property_,
            )
            names = frozenset(
                target for group in targets for target in group
            )
            if names:
                answers.update((subject, names) for subject in subject_group)
        return MappingProxyType(
            dict(sorted(answers.items(), key=lambda item: item[0].canonical_bytes()))
        )

    def has_object_property_relationship(
        self,
        subject: owl.NamedIndividual,
        property_: owl.ObjectPropertyExpression,
        object_: owl.NamedIndividual,
    ) -> bool:
        _require_named_individual(subject)
        _require_object_property(property_)
        _require_named_individual(object_)
        return self._evaluate(
            (owl.ObjectPropertyAssertion(property_, subject, object_),)
        )[0]

    def data_property_values(
        self,
        subject: owl.NamedIndividual,
        property_: owl.DataProperty,
    ) -> frozenset[owl.Literal]:
        _require_named_individual(subject)
        _require_data_property(property_)
        self._validate_individual(subject)
        self._validate_data_property(property_)
        self._ensure_coarse()
        canonical = self._canonical_individual(subject)
        key = (canonical.canonical_bytes(), property_.canonical_bytes())
        retained = self._data_values.get(key)
        if retained is not None:
            self._cache_hits += 1
            return retained
        outcomes = self._evaluate(
            tuple(
                owl.DataPropertyAssertion(property_, subject, literal)
                for literal in self._source_literals
            )
        )
        selected = frozenset(
            literal
            for literal, entailed in zip(self._source_literals, outcomes, strict=True)
            if entailed
        )
        self._checkpoint()
        self._data_values[key] = selected
        return selected

    def has_data_property_relationship(
        self,
        subject: owl.NamedIndividual,
        property_: owl.DataProperty,
        value: owl.Literal,
    ) -> bool:
        _require_named_individual(subject)
        _require_data_property(property_)
        if not isinstance(value, owl.Literal):
            raise TypeError("value must be an exact core Literal")
        return self._evaluate((owl.DataPropertyAssertion(property_, subject, value),))[0]

    def _type_node_ids(self, individual: owl.NamedIndividual) -> frozenset[int]:
        self._ensure_coarse()
        canonical = self._canonical_individual(individual)
        key = canonical.canonical_bytes()
        retained = self._type_nodes.get(key)
        if retained is not None:
            self._cache_hits += 1
            return retained
        hierarchy = self._classification.class_hierarchy()
        representatives = tuple(_representative(node) for node in hierarchy.nodes)
        outcomes = self._evaluate(
            tuple(
                owl.ClassAssertion(representative, individual)
                for representative in representatives
            )
        )
        selected = frozenset(
            node for node, entailed in enumerate(outcomes) if entailed
        )
        self._checkpoint()
        self._type_nodes[key] = selected
        return selected

    def _minimal_type_nodes(self, selected: frozenset[int]) -> frozenset[int]:
        hierarchy = self._classification.class_hierarchy()
        return frozenset(
            node
            for node in selected
            if not hierarchy.descendants(node).intersection(selected)
        )

    def _is_direct_instance(
        self,
        individual: owl.NamedIndividual,
        expression: owl.ClassExpression,
    ) -> bool:
        strict_subclasses = self._classification.subclasses(expression)
        if not strict_subclasses:
            return True
        hierarchy = self._classification.class_hierarchy()
        node_by_member = {
            member: node
            for node, members in enumerate(hierarchy.nodes)
            for member in members
        }
        strict_nodes = frozenset(
            node_by_member[_representative(group)] for group in strict_subclasses
        )
        return not self._type_node_ids(individual).intersection(strict_nodes)

    def _same_partition(self) -> tuple[frozenset[owl.NamedIndividual], ...]:
        self._ensure_coarse()
        retained = self._same_groups
        if retained is not None:
            self._cache_hits += 1
            return retained
        operation_id, started = self._start("same-as", len(self._named))
        self._evaluate(())
        parent = list(range(len(self._named)))
        source_index = {
            individual: index for index, individual in enumerate(self._named)
        }

        def root(value: int) -> int:
            while parent[value] != value:
                parent[value] = parent[parent[value]]
                value = parent[value]
            return value

        for record in self._service.normalized.records:
            statement = record.statement
            if not isinstance(statement, owl.SameIndividual):
                continue
            asserted = tuple(
                individual
                for individual in statement.individuals
                if isinstance(individual, owl.NamedIndividual)
                and individual in source_index
            )
            if len(asserted) < 2:
                continue
            first_root = root(source_index[asserted[0]])
            for individual in asserted[1:]:
                other_root = root(source_index[individual])
                if first_root != other_root:
                    parent[other_root] = first_root

        seed_groups: dict[int, set[owl.NamedIndividual]] = {}
        for index, individual in enumerate(self._named):
            seed_groups.setdefault(root(index), set()).add(individual)
        representatives = tuple(
            _representative(frozenset(group))
            for group in seed_groups.values()
        )
        pairs = (
            tuple(itertools.combinations(representatives, 2))
            if _semantic_equality_possible(self._service)
            else ()
        )
        outcomes = self._evaluate(
            tuple(
                owl.SameIndividual(owl.CanonicalSet(pair))
                for pair in pairs
            )
        )
        for (left, right), entailed in zip(pairs, outcomes, strict=True):
            if not entailed:
                continue
            left_root = root(source_index[left])
            right_root = root(source_index[right])
            if left_root != right_root:
                parent[right_root] = left_root
        mutable: dict[int, set[owl.NamedIndividual]] = {}
        for index, individual in enumerate(self._named):
            mutable.setdefault(root(index), set()).add(individual)
        groups = tuple(
            sorted(
                (frozenset(group) for group in mutable.values()),
                key=lambda group: tuple(
                    value.canonical_bytes()
                    for value in sorted(group, key=lambda item: item.canonical_bytes())
                ),
            )
        )
        by_member = MappingProxyType(
            {
                member: group_id
                for group_id, group in enumerate(groups)
                for member in group
            }
        )
        self._checkpoint()
        self._group_by_member = by_member
        self._same_groups = groups
        self._finish(operation_id, len(self._named), started)
        return groups

    def _object_target_groups(
        self,
        subject: owl.NamedIndividual,
        property_: owl.ObjectPropertyExpression,
    ) -> tuple[frozenset[owl.NamedIndividual], ...]:
        self._ensure_coarse()
        candidates = list(self._same_partition())
        canonical = self._canonical_individual(subject)
        key = (canonical.canonical_bytes(), property_.canonical_bytes())
        retained = self._object_targets.get(key)
        if retained is not None:
            self._cache_hits += 1
            return retained
        if self._group_id(subject) is None:
            candidates.append(frozenset((subject,)))
        outcomes = self._evaluate(
            tuple(
                owl.ObjectPropertyAssertion(
                    property_,
                    subject,
                    _representative(group),
                )
                for group in candidates
            )
        )
        selected = tuple(
            group
            for group, entailed in zip(candidates, outcomes, strict=True)
            if entailed
        )
        self._checkpoint()
        self._object_targets[key] = selected
        return selected

    def _ensure_coarse(self) -> None:
        provider = self._coarse_provider
        if provider is None or self._coarse_loaded:
            return
        operation_id, started = self._start("all", len(self._named))
        value = provider()
        if not isinstance(value, MappedRealization):
            raise BackendMismatchError(
                "coarse realization provider returned an incompatible result",
                context={"reason": "coarse_realization_type"},
            )
        groups = tuple(value.same_as)
        observed_names = frozenset(member for group in groups for member in group)
        if observed_names != frozenset(self._named):
            raise BackendMismatchError(
                "coarse realization does not partition exactly the named individuals",
                context={"reason": "coarse_realization_partition"},
            )
        by_member = MappingProxyType(
            {
                member: group_id
                for group_id, group in enumerate(groups)
                for member in group
            }
        )

        hierarchy = self._classification.class_hierarchy()
        direct_by_group = dict(value.direct_types)
        if frozenset(direct_by_group) != frozenset(range(len(groups))):
            raise BackendMismatchError(
                "coarse realization lacks direct class types for a same-as group",
                context={"reason": "coarse_realization_type_partition"},
            )
        expanded_by_group = {
            group_id: frozenset(
                node_id
                for direct in direct_by_group[group_id]
                for node_id in (direct, *hierarchy.ancestors(direct))
            )
            for group_id in range(len(groups))
        }
        type_nodes = {
            _representative(group).canonical_bytes(): expanded_by_group[group_id]
            for group_id, group in enumerate(groups)
        }
        instance_groups: dict[bytes, frozenset[int]] = {}
        for node_id, members in enumerate(hierarchy.nodes):
            selected = frozenset(
                group_id
                for group_id, type_ids in expanded_by_group.items()
                if node_id in type_ids
            )
            for member in members:
                instance_groups[member.canonical_bytes()] = selected

        different_mutable: dict[int, set[int]] = {
            group_id: set() for group_id in range(len(groups))
        }
        for left, right in value.different_from:
            different_mutable[left].add(right)
            different_mutable[right].add(left)
        different_groups = {
            _representative(group).canonical_bytes(): frozenset(
                different_mutable[group_id]
            )
            for group_id, group in enumerate(groups)
        }

        all_groups = tuple(groups)
        object_targets: dict[
            tuple[bytes, bytes],
            tuple[frozenset[owl.NamedIndividual], ...],
        ] = {}
        for group in groups:
            subject_key = _representative(group).canonical_bytes()
            for property_ in _object_property_candidates(self._service):
                targets = (
                    all_groups
                    if property_
                    in {
                        owl.OWL_TOP_OBJECT_PROPERTY,
                        owl.inverse_property(owl.OWL_TOP_OBJECT_PROPERTY),
                    }
                    else ()
                )
                object_targets[(subject_key, property_.canonical_bytes())] = targets
        for subject, property_, target_ids in value.object_targets:
            subject_key = _representative(groups[subject]).canonical_bytes()
            object_targets[(subject_key, property_.canonical_bytes())] = tuple(
                groups[target] for target in sorted(target_ids)
            )

        data_values: dict[tuple[bytes, bytes], frozenset[owl.Literal]] = {}
        all_literals = frozenset(self._source_literals)
        for group in groups:
            subject_key = _representative(group).canonical_bytes()
            for data_property in _data_property_candidates(self._service):
                data_values[(subject_key, data_property.canonical_bytes())] = (
                    all_literals
                    if data_property == owl.OWL_TOP_DATA_PROPERTY
                    else frozenset()
                )
        for subject, data_property, literals in value.data_targets:
            subject_key = _representative(groups[subject]).canonical_bytes()
            data_values[(subject_key, data_property.canonical_bytes())] = literals

        self._checkpoint()
        # A callback failure must not leave a result that its initiating call did not receive.
        self._finish(operation_id, len(self._named), started)
        self._group_by_member = by_member
        self._same_groups = groups
        self._type_nodes = type_nodes
        self._instance_groups = instance_groups
        self._different_groups = different_groups
        self._object_targets = object_targets
        self._data_values = data_values
        self._coarse_loaded = True

    def _format_groups(
        self,
        groups: Sequence[frozenset[owl.NamedIndividual]],
    ) -> IndividualResults:
        if self._config.individual_grouping is IndividualGrouping.BY_SAME_AS:
            return frozenset(groups)
        return frozenset(individual for group in groups for individual in group)

    def _canonical_individual(
        self,
        individual: owl.NamedIndividual,
    ) -> owl.NamedIndividual:
        if self._same_groups is None:
            return individual
        group_id = self._require_group_index().get(individual)
        return (
            individual
            if group_id is None
            else _representative(self._same_groups[group_id])
        )

    def _group_id(self, individual: owl.NamedIndividual) -> int | None:
        self._same_partition()
        return self._require_group_index().get(individual)

    def _require_group_index(self) -> Mapping[owl.NamedIndividual, int]:
        retained = self._group_by_member
        if retained is None:
            raise RuntimeError("same-as partition has no member index")
        return retained

    def _validate_individual(self, individual: owl.NamedIndividual) -> None:
        self._evaluate((owl.ClassAssertion(owl.OWL_THING, individual),))

    def _validate_class_expression(self, expression: owl.ClassExpression) -> None:
        self._evaluate((owl.SubClassOf(expression, owl.OWL_THING),))

    def _validate_object_property(
        self,
        property_: owl.ObjectPropertyExpression,
    ) -> None:
        self._evaluate((owl.SubObjectPropertyOf(property_, owl.OWL_TOP_OBJECT_PROPERTY),))

    def _validate_data_property(self, property_: owl.DataProperty) -> None:
        self._evaluate((owl.SubDataPropertyOf(property_, owl.OWL_TOP_DATA_PROPERTY),))

    def _evaluate(
        self,
        axioms: Sequence[owl.LogicalAxiom],
    ) -> tuple[bool, ...]:
        self._checkpoint()
        if not axioms:
            if not self._service.is_consistent():
                raise InconsistentOntologyError(
                    "realization is undefined for an inconsistent ontology"
                )
            return ()
        outcomes = self._service._entails_each(tuple(axioms))
        self._entailment_tests += len(axioms)
        self._batches += 1
        self._checkpoint()
        return outcomes

    def _checkpoint(self) -> None:
        if self._cancelled is not None and self._cancelled():
            raise ReasonerInterruptedError("realization was interrupted")

    def _start(self, label: str, total: int) -> tuple[str, float]:
        self._operation_sequence += 1
        operation_id = f"realization-{label}-{self._operation_sequence}"
        started = time.perf_counter()
        self._emit(operation_id, "realization-started", 0, total, started)
        return operation_id, started

    def _finish(self, operation_id: str, total: int, started: float) -> None:
        self._emit(operation_id, "realization-completed", total, total, started)

    def _emit(
        self,
        operation_id: str,
        kind: str,
        completed: int,
        total: int,
        started: float,
    ) -> None:
        callback = self._config.progress
        if callback is None:
            return
        callback(
            ProgressEvent(
                version=1,
                operation_id=operation_id,
                kind=kind,
                completed=completed,
                total=total,
                elapsed_seconds=time.perf_counter() - started,
                details={
                    "batches": self._batches,
                    "cache_hits": self._cache_hits,
                    "entailment_tests": self._entailment_tests,
                },
            )
        )


def _source_literals(service: EntailmentService) -> tuple[owl.Literal, ...]:
    values: dict[bytes, owl.Literal] = {}
    for record in service.normalized.records:
        statement = record.statement
        if isinstance(statement, DataRangeInclusion):
            nodes: Iterable[owl.StructuralNode] = itertools.chain(
                owl.walk(statement.sub_range),
                owl.walk(statement.super_range),
            )
        else:
            nodes = owl.walk(statement)
        for node in nodes:
            if isinstance(node, owl.Literal):
                values[node.canonical_bytes()] = node
    return tuple(values[key] for key in sorted(values))


def _object_property_candidates(
    service: EntailmentService,
) -> frozenset[owl.ObjectPropertyExpression]:
    named = {
        value
        for value in service.source_signature
        if isinstance(value, owl.ObjectProperty)
    }
    named.update((owl.OWL_TOP_OBJECT_PROPERTY, owl.OWL_BOTTOM_OBJECT_PROPERTY))
    return frozenset(named | {owl.inverse_property(value) for value in named})


def _data_property_candidates(service: EntailmentService) -> frozenset[owl.DataProperty]:
    return frozenset(
        {
            owl.OWL_TOP_DATA_PROPERTY,
            owl.OWL_BOTTOM_DATA_PROPERTY,
            *(
                value
                for value in service.source_signature
                if isinstance(value, owl.DataProperty)
            ),
        }
    )


def _semantic_equality_possible(service: EntailmentService) -> bool:
    equality_axioms = (
        owl.FunctionalObjectProperty,
        owl.InverseFunctionalObjectProperty,
        owl.HasKey,
    )
    equality_expressions = (
        owl.ObjectOneOf,
        owl.ObjectMaxCardinality,
        owl.ObjectExactCardinality,
    )
    for record in service.normalized.records:
        statement = record.statement
        if isinstance(statement, equality_axioms):
            return True
        if isinstance(statement, DataRangeInclusion):
            continue
        if any(isinstance(node, equality_expressions) for node in owl.walk(statement)):
            return True
    return any(
        isinstance(node, equality_expressions)
        for definition in service.normalized.definitions
        for node in owl.walk(definition.expression)
    )


def _representative(values: frozenset[T]) -> T:
    return min(values, key=lambda value: value.canonical_bytes())


def _require_named_individual(value: object) -> None:
    if not isinstance(value, owl.NamedIndividual):
        raise TypeError("individual must be an exact core NamedIndividual")


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


__all__ = [
    "IndividualResults",
    "RealizationService",
    "RealizationStatistics",
]
