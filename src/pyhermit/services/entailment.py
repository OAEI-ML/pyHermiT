"""Complete OWL 2 consistency, satisfiability, and entailment reductions."""

from __future__ import annotations

import hashlib
import itertools
from collections import defaultdict, deque
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass
from typing import TypeAlias, cast

import pyowl_core.model as owl

from pyhermit.config import FreshEntityPolicy
from pyhermit.exceptions import FreshEntityError, InconsistentOntologyError
from pyhermit.normalize import DataRangeInclusion, NormalizedOntology

from .checks import CompiledQueryExecutor, QueryPlan

_OBJECT_PROPERTIES = (owl.ObjectProperty, owl.ObjectInverseOf)
_INDIVIDUALS = (owl.NamedIndividual, owl.AnonymousIndividual)
_INTERNAL_IRI_PREFIX = "urn:pyhermit:query:v1:"

Reduction: TypeAlias = bool | tuple[QueryPlan, ...]

_REDUCTION_METHODS: dict[type[owl.AxiomNode], str] = {
    owl.SubClassOf: "_reduce_subclass",
    owl.EquivalentClasses: "_reduce_equivalent_classes",
    owl.DisjointClasses: "_reduce_disjoint_classes",
    owl.DisjointUnion: "_reduce_disjoint_union",
    owl.SubObjectPropertyOf: "_reduce_sub_object_property",
    owl.EquivalentObjectProperties: "_reduce_equivalent_object_properties",
    owl.DisjointObjectProperties: "_reduce_disjoint_object_properties",
    owl.InverseObjectProperties: "_reduce_inverse_object_properties",
    owl.ObjectPropertyDomain: "_reduce_object_property_domain",
    owl.ObjectPropertyRange: "_reduce_object_property_range",
    owl.FunctionalObjectProperty: "_reduce_functional_object_property",
    owl.InverseFunctionalObjectProperty: "_reduce_inverse_functional_object_property",
    owl.ReflexiveObjectProperty: "_reduce_reflexive_object_property",
    owl.IrreflexiveObjectProperty: "_reduce_irreflexive_object_property",
    owl.SymmetricObjectProperty: "_reduce_symmetric_object_property",
    owl.AsymmetricObjectProperty: "_reduce_asymmetric_object_property",
    owl.TransitiveObjectProperty: "_reduce_transitive_object_property",
    owl.SubDataPropertyOf: "_reduce_sub_data_property",
    owl.EquivalentDataProperties: "_reduce_equivalent_data_properties",
    owl.DisjointDataProperties: "_reduce_disjoint_data_properties",
    owl.DataPropertyDomain: "_reduce_data_property_domain",
    owl.DataPropertyRange: "_reduce_data_property_range",
    owl.FunctionalDataProperty: "_reduce_functional_data_property",
    owl.DatatypeDefinition: "_reduce_datatype_definition",
    owl.HasKey: "_reduce_has_key",
    owl.SameIndividual: "_reduce_same_individual",
    owl.DifferentIndividuals: "_reduce_different_individuals",
    owl.ClassAssertion: "_reduce_class_assertion",
    owl.ObjectPropertyAssertion: "_reduce_object_property_assertion",
    owl.NegativeObjectPropertyAssertion: "_reduce_negative_object_property_assertion",
    owl.DataPropertyAssertion: "_reduce_data_property_assertion",
    owl.NegativeDataPropertyAssertion: "_reduce_negative_data_property_assertion",
}
ENTAILMENT_REDUCTION_TYPES = frozenset(_REDUCTION_METHODS)
if frozenset(owl.LOGICAL_AXIOM_TYPES) != ENTAILMENT_REDUCTION_TYPES:
    raise RuntimeError("entailment reduction registry is not exhaustive for logical axioms")

_BUILTIN_ENTITIES = frozenset(
    {
        owl.OWL_THING,
        owl.OWL_NOTHING,
        owl.OWL_TOP_OBJECT_PROPERTY,
        owl.OWL_BOTTOM_OBJECT_PROPERTY,
        owl.OWL_TOP_DATA_PROPERTY,
        owl.OWL_BOTTOM_DATA_PROPERTY,
        owl.RDFS_LITERAL,
        owl.XSD_STRING,
        owl.RDF_PLAIN_LITERAL,
    }
)


class EntailmentService:
    """Logical services over one immutable permanent backend session.

    ``force_reductions`` disables asserted/built-in shortcuts and is intended for
    differential verification.  It never changes logical results.
    """

    __slots__ = (
        "_asserted",
        "_consistent",
        "_datatype_definitions",
        "_executor",
        "_force_reductions",
        "_fresh_policy",
        "_signature",
        "_signature_bytes",
    )

    def __init__(
        self,
        executor: CompiledQueryExecutor,
        *,
        fresh_entities: FreshEntityPolicy | str = FreshEntityPolicy.ALLOW,
        force_reductions: bool = False,
    ) -> None:
        if not isinstance(executor, CompiledQueryExecutor):
            raise TypeError("executor must be CompiledQueryExecutor")
        selected_fresh_entities: FreshEntityPolicy
        if isinstance(fresh_entities, FreshEntityPolicy):
            selected_fresh_entities = fresh_entities
        else:
            try:
                selected_fresh_entities = FreshEntityPolicy(fresh_entities)
            except (TypeError, ValueError) as error:
                raise TypeError("fresh_entities must be FreshEntityPolicy") from error
        if not isinstance(force_reductions, bool):
            raise TypeError("force_reductions must be bool")
        self._executor = executor
        self._fresh_policy = selected_fresh_entities
        self._force_reductions = force_reductions
        self._consistent: bool | None = None
        signature = _source_signature(executor.normalized) | _BUILTIN_ENTITIES
        self._signature = frozenset(signature)
        self._signature_bytes = frozenset(value.canonical_bytes() for value in signature)
        self._asserted = frozenset(
            value.statement.canonical_bytes()
            for value in executor.normalized.records
            if not value.generated and isinstance(value.statement, owl.LOGICAL_AXIOM_TYPES)
        )
        self._datatype_definitions = frozenset(
            value.statement.datatype.canonical_bytes()
            for value in executor.normalized.records
            if isinstance(value.statement, owl.DatatypeDefinition)
        )

    @property
    def normalized(self) -> NormalizedOntology:
        """The immutable normalized ontology captured by this service."""

        return self._executor.normalized

    @property
    def source_signature(self) -> frozenset[owl.Entity]:
        """Source-visible entities plus the required OWL/RDF built-ins."""

        return self._signature

    @property
    def deterministic_program(self) -> bool:
        """Whether the permanent clause program has no disjunctive choice points."""

        return not self._executor.program.expressivity.non_horn

    def is_consistent(self) -> bool:
        retained = self._consistent
        if retained is None:
            retained = self._executor.check_permanent().satisfiable
            self._consistent = retained
        return retained

    def is_satisfiable(self, expression: owl.ClassExpression) -> bool:
        _require_class_expression(expression)
        self._require_known(expression)
        self._require_consistent()
        if not self._force_reductions:
            if expression == owl.OWL_THING:
                return True
            if expression == owl.OWL_NOTHING:
                return False
        witnesses = self._witnesses(expression, "satisfiable")
        plan = QueryPlan(
            (owl.ClassAssertion(expression, witnesses.anonymous("root")),),
            ("class-expression-satisfiability",),
        )
        return self._executor.check(plan).satisfiable

    def is_subclass(
        self,
        sub: owl.ClassExpression,
        sup: owl.ClassExpression,
    ) -> bool:
        _require_class_expression(sub)
        _require_class_expression(sup)
        self._require_known(sub)
        self._require_known(sup)
        self._require_consistent()
        shortcut = None if self._force_reductions else _subclass_shortcut(sub, sup)
        if shortcut is not None:
            return shortcut
        witnesses = self._witnesses_pair(sub, sup, "subclass")
        return not self._executor.check(_subclass_plan(sub, sup, witnesses, "subclass")).satisfiable

    def entails(self, axiom: owl.LogicalAxiom) -> bool:
        return self.entails_all((axiom,))

    def entails_all(self, axioms: Iterable[owl.LogicalAxiom]) -> bool:
        """Return exact conjunction after fully snapshotting and validating the input."""

        values = tuple(axioms)
        if not all(isinstance(value, owl.LOGICAL_AXIOM_TYPES) for value in values):
            raise TypeError("axioms must contain exact core logical axiom values")
        if not values:
            return True
        for value in values:
            self._require_known(value)
        self._require_consistent()

        anonymous, ordinary = _partition_anonymous_assertions(values)
        plans: list[QueryPlan] = []
        for axiom in ordinary:
            reduction = self._reduce(axiom)
            if isinstance(reduction, bool):
                if not reduction:
                    return False
            else:
                plans.extend(reduction)
        if anonymous:
            plans.extend(_roll_up_anonymous_forest(anonymous, self._witnesses_for_axioms(values)))
        return all(not result.satisfiable for result in self._executor.check_many(tuple(plans)))

    def _entails_each(
        self,
        axioms: Sequence[owl.LogicalAxiom] | Iterable[owl.LogicalAxiom],
    ) -> tuple[bool, ...]:
        """Evaluate independent entailments through one isolated backend batch.

        Classification uses this private vector operation so a hierarchy-search
        frontier crosses the backend boundary once.  Anonymous individuals retain
        their per-axiom existential scope; ``entails_all`` remains the separate API
        for a jointly scoped conclusion ontology.
        """

        values = tuple(axioms)
        if not all(isinstance(value, owl.LOGICAL_AXIOM_TYPES) for value in values):
            raise TypeError("axioms must contain exact core logical axiom values")
        if not values:
            return ()
        for value in values:
            self._require_known(value)
        self._require_consistent()

        resolved: list[bool | None] = [None] * len(values)
        plans: list[QueryPlan] = []
        owners: list[int] = []
        for index, axiom in enumerate(values):
            anonymous, ordinary = _partition_anonymous_assertions((axiom,))
            if anonymous:
                reduction: Reduction = _roll_up_anonymous_forest(
                    anonymous,
                    self._witnesses_for_axioms((axiom,)),
                )
            else:
                reduction = self._reduce(ordinary[0])
            if isinstance(reduction, bool):
                resolved[index] = reduction
                continue
            if not reduction:
                resolved[index] = True
                continue
            plans.extend(reduction)
            owners.extend((index,) * len(reduction))

        if plans:
            for owner, result in zip(
                owners,
                self._executor.check_many(tuple(plans)),
                strict=True,
            ):
                entailed = not result.satisfiable
                previous = resolved[owner]
                resolved[owner] = entailed if previous is None else previous and entailed
        if any(value is None for value in resolved):
            raise RuntimeError("entailment batch left an unresolved result slot")
        return tuple(bool(value) for value in resolved)

    def _is_subclass_each(
        self,
        pairs: Sequence[tuple[owl.ClassExpression, owl.ClassExpression]],
    ) -> tuple[bool, ...]:
        return self._entails_each(tuple(owl.SubClassOf(sub, sup) for sub, sup in pairs))

    def supports_entailment(self, axiom_type: type[owl.AxiomNode]) -> bool:
        if not isinstance(axiom_type, type):
            raise TypeError("axiom_type must be a type")
        return axiom_type in ENTAILMENT_REDUCTION_TYPES

    def is_defined(self, entity: owl.Entity) -> bool:
        if not isinstance(entity, owl.Entity):
            raise TypeError("entity must be an exact core Entity")
        return entity in self._signature

    def clear_caches(self) -> None:
        self._consistent = None
        self._executor.clear_cache()

    def _reduce(self, axiom: owl.LogicalAxiom) -> Reduction:
        if not self._force_reductions:
            if axiom.canonical_bytes() in self._asserted:
                return True
            shortcut = _axiom_shortcut(axiom)
            if shortcut is not None:
                return shortcut
        method_name = _REDUCTION_METHODS[type(axiom)]
        method = cast(Callable[[owl.LogicalAxiom], Reduction], getattr(self, method_name))
        return method(axiom)

    def _reduce_subclass(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.SubClassOf, value)
        witnesses = self._witnesses(axiom, "subclass-axiom")
        return (_subclass_plan(axiom.sub_class, axiom.super_class, witnesses, "subclass"),)

    def _reduce_equivalent_classes(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.EquivalentClasses, value)
        expressions = tuple(axiom.expressions)
        first = expressions[0]
        witnesses = self._witnesses(axiom, "equivalent-classes")
        return tuple(
            _subclass_plan(left, right, witnesses, f"equivalent-classes:{index}:{direction}")
            for index, other in enumerate(expressions[1:], 1)
            for direction, left, right in (("forward", first, other), ("reverse", other, first))
        )

    def _reduce_disjoint_classes(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.DisjointClasses, value)
        witnesses = self._witnesses(axiom, "disjoint-classes")
        return tuple(
            _satisfiability_plan(
                _class_intersection((left, right)),
                witnesses,
                f"disjoint-classes:{index}",
            )
            for index, (left, right) in enumerate(itertools.combinations(axiom.expressions, 2))
        )

    def _reduce_disjoint_union(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.DisjointUnion, value)
        members = tuple(axiom.expressions)
        witnesses = self._witnesses(axiom, "disjoint-union")
        plans = [
            _subclass_plan(member, axiom.defined_class, witnesses, f"member:{index}")
            for index, member in enumerate(members)
        ]
        missing_member = _class_intersection(
            (axiom.defined_class, *(owl.ObjectComplementOf(member) for member in members))
        )
        plans.append(_satisfiability_plan(missing_member, witnesses, "defined-outside-union"))
        plans.extend(
            _satisfiability_plan(
                _class_intersection((left, right)),
                witnesses,
                f"disjoint-members:{index}",
            )
            for index, (left, right) in enumerate(itertools.combinations(members, 2))
        )
        return tuple(plans)

    def _reduce_sub_object_property(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.SubObjectPropertyOf, value)
        witnesses = self._witnesses(axiom, "sub-object-property")
        properties = (
            tuple(axiom.sub_property.properties)
            if isinstance(axiom.sub_property, owl.ObjectPropertyChain)
            else (axiom.sub_property,)
        )
        return (_object_inclusion_plan(properties, axiom.super_property, witnesses, "sub-role"),)

    def _reduce_equivalent_object_properties(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.EquivalentObjectProperties, value)
        properties = tuple(axiom.properties)
        first = properties[0]
        witnesses = self._witnesses(axiom, "equivalent-object-properties")
        return tuple(
            _object_inclusion_plan((left,), right, witnesses, f"equivalent-object:{i}:{name}")
            for i, other in enumerate(properties[1:], 1)
            for name, left, right in (("forward", first, other), ("reverse", other, first))
        )

    def _reduce_disjoint_object_properties(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.DisjointObjectProperties, value)
        witnesses = self._witnesses(axiom, "disjoint-object-properties")
        plans: list[QueryPlan] = []
        for index, (left, right) in enumerate(itertools.combinations(axiom.properties, 2)):
            source = witnesses.anonymous(f"source:{index}")
            target = witnesses.anonymous(f"target:{index}")
            plans.append(
                QueryPlan(
                    (
                        owl.ObjectPropertyAssertion(left, source, target),
                        owl.ObjectPropertyAssertion(right, source, target),
                    ),
                    (f"disjoint-object-properties:{index}",),
                )
            )
        return tuple(plans)

    def _reduce_inverse_object_properties(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.InverseObjectProperties, value)
        witnesses = self._witnesses(axiom, "inverse-object-properties")
        inverse_first = owl.inverse_property(axiom.first)
        return (
            _object_inclusion_plan((inverse_first,), axiom.second, witnesses, "inverse:forward"),
            _object_inclusion_plan((axiom.second,), inverse_first, witnesses, "inverse:reverse"),
        )

    def _reduce_object_property_domain(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.ObjectPropertyDomain, value)
        witnesses = self._witnesses(axiom, "object-domain")
        some = owl.ObjectSomeValuesFrom(axiom.property, owl.OWL_THING)
        return (_subclass_plan(some, axiom.domain, witnesses, "object-domain"),)

    def _reduce_object_property_range(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.ObjectPropertyRange, value)
        witnesses = self._witnesses(axiom, "object-range")
        universal = owl.ObjectAllValuesFrom(axiom.property, axiom.range)
        return (_subclass_plan(owl.OWL_THING, universal, witnesses, "object-range"),)

    def _reduce_functional_object_property(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.FunctionalObjectProperty, value)
        return (
            _object_functionality_plan(
                axiom.property,
                self._witnesses(axiom, "functional"),
                False,
            ),
        )

    def _reduce_inverse_functional_object_property(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.InverseFunctionalObjectProperty, value)
        return (
            _object_functionality_plan(
                axiom.property,
                self._witnesses(axiom, "inverse-functional"),
                True,
            ),
        )

    def _reduce_reflexive_object_property(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.ReflexiveObjectProperty, value)
        witnesses = self._witnesses(axiom, "reflexive")
        node = witnesses.anonymous("node")
        marker = witnesses.class_("marker")
        return (
            QueryPlan(
                (
                    owl.ClassAssertion(marker, node),
                    owl.ClassAssertion(
                        owl.ObjectAllValuesFrom(axiom.property, owl.ObjectComplementOf(marker)),
                        node,
                    ),
                ),
                ("reflexive-object-property",),
            ),
        )

    def _reduce_irreflexive_object_property(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.IrreflexiveObjectProperty, value)
        node = self._witnesses(axiom, "irreflexive").anonymous("node")
        return (
            QueryPlan(
                (owl.ObjectPropertyAssertion(axiom.property, node, node),),
                ("irreflexive-object-property",),
            ),
        )

    def _reduce_symmetric_object_property(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.SymmetricObjectProperty, value)
        witnesses = self._witnesses(axiom, "symmetric")
        source = witnesses.anonymous("source")
        target = witnesses.anonymous("target")
        marker = witnesses.class_("marker")
        return (
            QueryPlan(
                (
                    owl.ObjectPropertyAssertion(axiom.property, source, target),
                    owl.ClassAssertion(marker, source),
                    owl.ClassAssertion(
                        owl.ObjectAllValuesFrom(axiom.property, owl.ObjectComplementOf(marker)),
                        target,
                    ),
                ),
                ("symmetric-object-property",),
            ),
        )

    def _reduce_asymmetric_object_property(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.AsymmetricObjectProperty, value)
        witnesses = self._witnesses(axiom, "asymmetric")
        source = witnesses.anonymous("source")
        target = witnesses.anonymous("target")
        return (
            QueryPlan(
                (
                    owl.ObjectPropertyAssertion(axiom.property, source, target),
                    owl.ObjectPropertyAssertion(axiom.property, target, source),
                ),
                ("asymmetric-object-property",),
            ),
        )

    def _reduce_transitive_object_property(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.TransitiveObjectProperty, value)
        witnesses = self._witnesses(axiom, "transitive")
        return (
            _object_inclusion_plan(
                (axiom.property, axiom.property),
                axiom.property,
                witnesses,
                "transitive-object-property",
            ),
        )

    def _reduce_sub_data_property(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.SubDataPropertyOf, value)
        return (
            _data_inclusion_plan(
                axiom.sub_property,
                axiom.super_property,
                self._witnesses(axiom, "sub-data"),
            ),
        )

    def _reduce_equivalent_data_properties(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.EquivalentDataProperties, value)
        properties = tuple(axiom.properties)
        first = properties[0]
        witnesses = self._witnesses(axiom, "equivalent-data")
        return tuple(
            _data_inclusion_plan(left, right, witnesses, f"equivalent-data:{i}:{name}")
            for i, other in enumerate(properties[1:], 1)
            for name, left, right in (("forward", first, other), ("reverse", other, first))
        )

    def _reduce_disjoint_data_properties(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.DisjointDataProperties, value)
        witnesses = self._witnesses(axiom, "disjoint-data")
        plans: list[QueryPlan] = []
        for index, (left, right) in enumerate(itertools.combinations(axiom.properties, 2)):
            source = witnesses.anonymous(f"disjoint-data:{index}:source")
            constant = witnesses.literal(f"disjoint-data:{index}:value")
            plans.append(
                QueryPlan(
                    (
                        owl.DataPropertyAssertion(left, source, constant),
                        owl.DataPropertyAssertion(right, source, constant),
                    ),
                    (f"disjoint-data:{index}",),
                )
            )
        return tuple(plans)

    def _reduce_data_property_domain(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.DataPropertyDomain, value)
        witnesses = self._witnesses(axiom, "data-domain")
        some = owl.DataSomeValuesFrom((axiom.property,), owl.RDFS_LITERAL)
        return (_subclass_plan(some, axiom.domain, witnesses, "data-domain"),)

    def _reduce_data_property_range(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.DataPropertyRange, value)
        witnesses = self._witnesses(axiom, "data-range")
        universal = owl.DataAllValuesFrom((axiom.property,), axiom.range)
        return (_subclass_plan(owl.OWL_THING, universal, witnesses, "data-range"),)

    def _reduce_functional_data_property(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.FunctionalDataProperty, value)
        witnesses = self._witnesses(axiom, "functional-data")
        expression = owl.DataMinCardinality(2, axiom.property, owl.RDFS_LITERAL)
        return (_satisfiability_plan(expression, witnesses, "functional-data-property"),)

    def _reduce_datatype_definition(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.DatatypeDefinition, value)
        if axiom.datatype.canonical_bytes() not in self._datatype_definitions:
            # An unconstrained custom datatype can vary independently between models;
            # it cannot be entailed equal to a range until the permanent ontology
            # provides a definition for it.  This also avoids pretending opaque
            # datatype names have executable value-space semantics.
            return False
        witnesses = self._witnesses(axiom, "datatype-definition")
        probe = witnesses.data_property("probe")
        datatype_outside_range = _class_intersection(
            (
                owl.DataSomeValuesFrom((probe,), axiom.datatype),
                owl.DataAllValuesFrom((probe,), owl.DataComplementOf(axiom.data_range)),
            )
        )
        range_outside_datatype = _class_intersection(
            (
                owl.DataSomeValuesFrom((probe,), axiom.data_range),
                owl.DataAllValuesFrom((probe,), owl.DataComplementOf(axiom.datatype)),
            )
        )
        return (
            _satisfiability_plan(
                datatype_outside_range,
                witnesses,
                "datatype-definition:forward",
            ),
            _satisfiability_plan(
                range_outside_datatype,
                witnesses,
                "datatype-definition:reverse",
            ),
        )

    def _reduce_has_key(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.HasKey, value)
        witnesses = self._witnesses(axiom, "has-key")
        first = witnesses.named("key-subject-a")
        second = witnesses.named("key-subject-b")
        axioms: list[owl.AxiomNode] = [
            owl.ClassAssertion(axiom.class_expression, first),
            owl.ClassAssertion(axiom.class_expression, second),
        ]
        for index, object_property in enumerate(axiom.object_properties):
            shared = witnesses.named(f"object-key-value:{index}")
            axioms.extend(
                (
                    owl.ObjectPropertyAssertion(object_property, first, shared),
                    owl.ObjectPropertyAssertion(object_property, second, shared),
                )
            )
        for index, data_property in enumerate(axiom.data_properties):
            shared_literal = witnesses.literal(f"key-value-{index}")
            axioms.extend(
                (
                    owl.DataPropertyAssertion(data_property, first, shared_literal),
                    owl.DataPropertyAssertion(data_property, second, shared_literal),
                )
            )
        axioms.append(owl.DifferentIndividuals(owl.CanonicalSet((first, second))))
        return (QueryPlan(tuple(axioms), ("has-key-named-guard",)),)

    def _reduce_same_individual(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.SameIndividual, value)
        individuals = tuple(axiom.individuals)
        first = individuals[0]
        return tuple(
            QueryPlan(
                (owl.DifferentIndividuals(owl.CanonicalSet((first, other))),),
                (f"same-individual:{index}",),
            )
            for index, other in enumerate(individuals[1:], 1)
        )

    def _reduce_different_individuals(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.DifferentIndividuals, value)
        return tuple(
            QueryPlan(
                (owl.SameIndividual(owl.CanonicalSet((left, right))),),
                (f"different-individuals:{index}",),
            )
            for index, (left, right) in enumerate(itertools.combinations(axiom.individuals, 2))
        )

    def _reduce_class_assertion(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.ClassAssertion, value)
        return (
            QueryPlan(
                (
                    owl.ClassAssertion(
                        owl.ObjectComplementOf(axiom.class_expression),
                        axiom.individual,
                    ),
                ),
                ("class-assertion",),
            ),
        )

    def _reduce_object_property_assertion(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.ObjectPropertyAssertion, value)
        witnesses = self._witnesses(axiom, "object-assertion")
        marker = witnesses.class_("target-marker")
        return (
            QueryPlan(
                (
                    owl.ClassAssertion(marker, axiom.target),
                    owl.ClassAssertion(
                        owl.ObjectAllValuesFrom(axiom.property, owl.ObjectComplementOf(marker)),
                        axiom.source,
                    ),
                ),
                ("object-property-assertion",),
            ),
        )

    def _reduce_negative_object_property_assertion(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.NegativeObjectPropertyAssertion, value)
        return (
            QueryPlan(
                (owl.ObjectPropertyAssertion(axiom.property, axiom.source, axiom.target),),
                ("negative-object-property-assertion",),
            ),
        )

    def _reduce_data_property_assertion(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.DataPropertyAssertion, value)
        return (
            QueryPlan(
                (owl.NegativeDataPropertyAssertion(axiom.property, axiom.source, axiom.value),),
                ("data-property-assertion",),
            ),
        )

    def _reduce_negative_data_property_assertion(self, value: owl.LogicalAxiom) -> Reduction:
        axiom = cast(owl.NegativeDataPropertyAssertion, value)
        return (
            QueryPlan(
                (owl.DataPropertyAssertion(axiom.property, axiom.source, axiom.value),),
                ("negative-data-property-assertion",),
            ),
        )

    def _require_consistent(self) -> None:
        if not self.is_consistent():
            raise InconsistentOntologyError(
                "semantic query is undefined for an inconsistent ontology",
            )

    def _require_known(self, value: owl.StructuralNode) -> None:
        if self._fresh_policy is FreshEntityPolicy.ALLOW:
            return
        fresh = next(
            (
                node
                for node in owl.walk(value)
                if isinstance(node, owl.Entity) and node not in self._signature
            ),
            None,
        )
        if fresh is not None:
            raise FreshEntityError(
                f"query contains fresh {fresh.kind.value}: {fresh.iri.value}",
                context={"iri": fresh.iri.value, "kind": fresh.kind.value},
            )

    def _witnesses(self, value: owl.StructuralNode, purpose: str) -> _WitnessFactory:
        return _WitnessFactory(
            self._executor.normalized.digest,
            value.canonical_bytes(),
            purpose,
            self._signature_bytes,
        )

    def _witnesses_pair(
        self,
        first: owl.StructuralNode,
        second: owl.StructuralNode,
        purpose: str,
    ) -> _WitnessFactory:
        payload = first.canonical_bytes() + b"\x00" + second.canonical_bytes()
        return _WitnessFactory(
            self._executor.normalized.digest,
            payload,
            purpose,
            self._signature_bytes,
        )

    def _witnesses_for_axioms(
        self,
        values: Sequence[owl.LogicalAxiom],
    ) -> _WitnessFactory:
        payload = b"".join(
            len(value.canonical_bytes()).to_bytes(8, "big") + value.canonical_bytes()
            for value in values
        )
        return _WitnessFactory(
            self._executor.normalized.digest,
            payload,
            "anonymous-forest",
            self._signature_bytes,
        )


@dataclass(slots=True)
class _WitnessFactory:
    permanent_digest: str
    source: bytes
    purpose: str
    reserved: frozenset[bytes]

    def __post_init__(self) -> None:
        digest = hashlib.sha256(b"pyhermit:entailment-witness:v1\x00")
        digest.update(bytes.fromhex(self.permanent_digest))
        digest.update(len(self.source).to_bytes(8, "big"))
        digest.update(self.source)
        digest.update(self.purpose.encode("utf-8"))
        self.permanent_digest = digest.hexdigest()

    def anonymous(self, name: str) -> owl.AnonymousIndividual:
        scope = bytes.fromhex(self.permanent_digest)
        suffix = 0
        while True:
            key = f"{self.purpose}:{name}:{suffix}".encode()
            candidate = owl.AnonymousIndividual(scope, key)
            if candidate.canonical_bytes() not in self.reserved:
                return candidate
            suffix += 1

    def class_(self, name: str) -> owl.Class:
        return cast(owl.Class, self._entity(owl.Class, "class", name))

    def named(self, name: str) -> owl.NamedIndividual:
        return cast(owl.NamedIndividual, self._entity(owl.NamedIndividual, "individual", name))

    def data_property(self, name: str) -> owl.DataProperty:
        return cast(owl.DataProperty, self._entity(owl.DataProperty, "data-property", name))

    def datatype(self, name: str) -> owl.Datatype:
        return cast(owl.Datatype, self._entity(owl.Datatype, "datatype", name))

    def literal(self, name: str) -> owl.Literal:
        return owl.Literal(
            f"pyhermit-query-{self.permanent_digest}-{self.purpose}-{name}",
            owl.XSD_STRING,
        )

    def _entity(
        self,
        constructor: Callable[[owl.IRI], owl.Entity],
        kind: str,
        name: str,
    ) -> owl.Entity:
        suffix = 0
        while True:
            iri = owl.IRI(f"{_INTERNAL_IRI_PREFIX}{self.permanent_digest}:{kind}:{name}:{suffix}")
            candidate = constructor(iri)
            if candidate.canonical_bytes() not in self.reserved:
                return candidate
            suffix += 1


def _subclass_plan(
    sub: owl.ClassExpression,
    sup: owl.ClassExpression,
    witnesses: _WitnessFactory,
    label: str,
) -> QueryPlan:
    counterexample = _class_intersection((sub, owl.ObjectComplementOf(sup)))
    return _satisfiability_plan(counterexample, witnesses, label)


def _satisfiability_plan(
    expression: owl.ClassExpression,
    witnesses: _WitnessFactory,
    label: str,
) -> QueryPlan:
    return QueryPlan(
        (owl.ClassAssertion(expression, witnesses.anonymous(f"root:{label}")),),
        (label,),
    )


def _object_inclusion_plan(
    sub_properties: Sequence[owl.ObjectPropertyExpression],
    super_property: owl.ObjectPropertyExpression,
    witnesses: _WitnessFactory,
    label: str,
) -> QueryPlan:
    nodes = tuple(
        witnesses.anonymous(f"{label}:node:{index}") for index in range(len(sub_properties) + 1)
    )
    marker = witnesses.class_(f"{label}:target-marker")
    axioms: list[owl.AxiomNode] = [
        owl.ObjectPropertyAssertion(property_, nodes[index], nodes[index + 1])
        for index, property_ in enumerate(sub_properties)
    ]
    axioms.extend(
        (
            owl.ClassAssertion(marker, nodes[-1]),
            owl.ClassAssertion(
                owl.ObjectAllValuesFrom(super_property, owl.ObjectComplementOf(marker)),
                nodes[0],
            ),
        )
    )
    return QueryPlan(tuple(axioms), (label,))


def _object_functionality_plan(
    property_: owl.ObjectPropertyExpression,
    witnesses: _WitnessFactory,
    inverse: bool,
) -> QueryPlan:
    common = witnesses.anonymous("common")
    first = witnesses.anonymous("first")
    second = witnesses.anonymous("second")
    marker = witnesses.class_("different-marker")
    if inverse:
        edges = (
            owl.ObjectPropertyAssertion(property_, first, common),
            owl.ObjectPropertyAssertion(property_, second, common),
        )
        label = "inverse-functional-object-property"
    else:
        edges = (
            owl.ObjectPropertyAssertion(property_, common, first),
            owl.ObjectPropertyAssertion(property_, common, second),
        )
        label = "functional-object-property"
    return QueryPlan(
        (
            *edges,
            owl.ClassAssertion(marker, first),
            owl.ClassAssertion(owl.ObjectComplementOf(marker), second),
        ),
        (label,),
    )


def _data_inclusion_plan(
    sub_property: owl.DataProperty,
    super_property: owl.DataProperty,
    witnesses: _WitnessFactory,
    label: str = "sub-data-property",
) -> QueryPlan:
    source = witnesses.anonymous(f"{label}:source")
    constant = witnesses.literal(f"{label}:value")
    negated_super = witnesses.data_property(f"{label}:negated-super")
    return QueryPlan(
        (
            owl.DataPropertyAssertion(sub_property, source, constant),
            owl.DataPropertyAssertion(negated_super, source, constant),
            owl.DisjointDataProperties(owl.CanonicalSet((super_property, negated_super))),
        ),
        (label,),
    )


def _class_intersection(values: Iterable[owl.ClassExpression]) -> owl.ClassExpression:
    operands = tuple(owl.CanonicalSet(values))
    if not operands:
        return owl.OWL_THING
    if len(operands) == 1:
        return operands[0]
    return owl.ObjectIntersectionOf(owl.CanonicalSet(operands))


def _subclass_shortcut(
    sub: owl.ClassExpression,
    sup: owl.ClassExpression,
) -> bool | None:
    if sub == sup or sub == owl.OWL_NOTHING or sup == owl.OWL_THING:
        return True
    return None


def _axiom_shortcut(axiom: owl.LogicalAxiom) -> bool | None:
    if isinstance(axiom, owl.SubClassOf):
        return _subclass_shortcut(axiom.sub_class, axiom.super_class)
    if isinstance(axiom, owl.SubObjectPropertyOf):
        sub = axiom.sub_property
        if sub == axiom.super_property or axiom.super_property == owl.OWL_TOP_OBJECT_PROPERTY:
            return True
        if sub == owl.OWL_BOTTOM_OBJECT_PROPERTY:
            return True
        if (
            isinstance(sub, owl.ObjectPropertyChain)
            and owl.OWL_BOTTOM_OBJECT_PROPERTY in sub.properties
        ):
            return True
    if isinstance(axiom, owl.SubDataPropertyOf) and (
        axiom.sub_property == axiom.super_property
        or axiom.sub_property == owl.OWL_BOTTOM_DATA_PROPERTY
        or axiom.super_property == owl.OWL_TOP_DATA_PROPERTY
    ):
        return True
    if (
        isinstance(
            axiom,
            (owl.FunctionalObjectProperty, owl.InverseFunctionalObjectProperty),
        )
        and axiom.property == owl.OWL_BOTTOM_OBJECT_PROPERTY
    ):
        return True
    if (
        isinstance(axiom, owl.FunctionalDataProperty)
        and axiom.property == owl.OWL_BOTTOM_DATA_PROPERTY
    ):
        return True
    if isinstance(axiom, owl.ReflexiveObjectProperty):
        if axiom.property == owl.OWL_TOP_OBJECT_PROPERTY:
            return True
        if axiom.property == owl.OWL_BOTTOM_OBJECT_PROPERTY:
            return False
    if isinstance(axiom, owl.IrreflexiveObjectProperty):
        if axiom.property == owl.OWL_BOTTOM_OBJECT_PROPERTY:
            return True
        if axiom.property == owl.OWL_TOP_OBJECT_PROPERTY:
            return False
    if isinstance(axiom, (owl.SymmetricObjectProperty, owl.TransitiveObjectProperty)) and (
        axiom.property in (owl.OWL_TOP_OBJECT_PROPERTY, owl.OWL_BOTTOM_OBJECT_PROPERTY)
    ):
        return True
    if isinstance(axiom, owl.AsymmetricObjectProperty):
        if axiom.property == owl.OWL_BOTTOM_OBJECT_PROPERTY:
            return True
        if axiom.property == owl.OWL_TOP_OBJECT_PROPERTY:
            return False
    if isinstance(axiom, owl.ClassAssertion):
        if axiom.class_expression == owl.OWL_THING:
            return True
        if axiom.class_expression == owl.OWL_NOTHING:
            return False
    if isinstance(axiom, owl.ObjectPropertyAssertion):
        if axiom.property == owl.OWL_TOP_OBJECT_PROPERTY:
            return True
        if axiom.property == owl.OWL_BOTTOM_OBJECT_PROPERTY:
            return False
    if isinstance(axiom, owl.NegativeObjectPropertyAssertion):
        if axiom.property == owl.OWL_BOTTOM_OBJECT_PROPERTY:
            return True
        if axiom.property == owl.OWL_TOP_OBJECT_PROPERTY:
            return False
    if isinstance(axiom, owl.DataPropertyAssertion):
        if axiom.property == owl.OWL_TOP_DATA_PROPERTY:
            return True
        if axiom.property == owl.OWL_BOTTOM_DATA_PROPERTY:
            return False
    if isinstance(axiom, owl.NegativeDataPropertyAssertion):
        if axiom.property == owl.OWL_BOTTOM_DATA_PROPERTY:
            return True
        if axiom.property == owl.OWL_TOP_DATA_PROPERTY:
            return False
    return None


def _source_signature(normalized: NormalizedOntology) -> set[owl.Entity]:
    generated = {value.symbol.canonical_bytes() for value in normalized.definitions}
    result = set(normalized.declared_entities)
    for record in normalized.records:
        statement = record.statement
        if isinstance(statement, DataRangeInclusion):
            nodes: Iterable[owl.StructuralNode] = itertools.chain(
                owl.walk(statement.sub_range),
                owl.walk(statement.super_range),
            )
        else:
            nodes = owl.walk(statement)
        result.update(
            node
            for node in nodes
            if isinstance(node, owl.Entity) and node.canonical_bytes() not in generated
        )
    return result


def _require_class_expression(value: object) -> None:
    if not isinstance(value, owl.CLASS_EXPRESSION_TYPES):
        raise TypeError("expression must be an exact core ClassExpression")


def _partition_anonymous_assertions(
    axioms: Sequence[owl.LogicalAxiom],
) -> tuple[tuple[owl.LogicalAxiom, ...], tuple[owl.LogicalAxiom, ...]]:
    anonymous: list[owl.LogicalAxiom] = []
    ordinary: list[owl.LogicalAxiom] = []
    for axiom in axioms:
        if (
            (
                isinstance(axiom, owl.ClassAssertion)
                and isinstance(axiom.individual, owl.AnonymousIndividual)
            )
            or (
                isinstance(axiom, owl.ObjectPropertyAssertion)
                and (
                    isinstance(axiom.source, owl.AnonymousIndividual)
                    or isinstance(axiom.target, owl.AnonymousIndividual)
                )
            )
            or (
                isinstance(axiom, owl.DataPropertyAssertion)
                and isinstance(axiom.source, owl.AnonymousIndividual)
            )
        ):
            anonymous.append(axiom)
        else:
            if isinstance(
                axiom,
                (
                    owl.SameIndividual,
                    owl.DifferentIndividuals,
                    owl.NegativeObjectPropertyAssertion,
                    owl.NegativeDataPropertyAssertion,
                ),
            ) and any(isinstance(node, owl.AnonymousIndividual) for node in owl.walk(axiom)):
                raise ValueError(
                    f"{type(axiom).__name__} cannot contain anonymous individuals in OWL 2 DL"
                )
            ordinary.append(axiom)
    return tuple(anonymous), tuple(ordinary)


def _roll_up_anonymous_forest(
    axioms: Sequence[owl.LogicalAxiom],
    witnesses: _WitnessFactory,
) -> tuple[QueryPlan, ...]:
    labels: dict[owl.AnonymousIndividual, list[owl.ClassExpression]] = defaultdict(list)
    adjacency: dict[owl.AnonymousIndividual, set[owl.AnonymousIndividual]] = defaultdict(set)
    edges: dict[
        frozenset[owl.AnonymousIndividual],
        tuple[owl.AnonymousIndividual, owl.AnonymousIndividual, owl.ObjectPropertyExpression],
    ] = {}
    named_links: dict[
        owl.AnonymousIndividual,
        list[tuple[owl.NamedIndividual, owl.ObjectPropertyExpression]],
    ] = defaultdict(list)
    nodes: set[owl.AnonymousIndividual] = set()

    for axiom in axioms:
        if isinstance(axiom, owl.ClassAssertion):
            individual = cast(owl.AnonymousIndividual, axiom.individual)
            nodes.add(individual)
            if axiom.class_expression != owl.OWL_THING:
                labels[individual].append(axiom.class_expression)
        elif isinstance(axiom, owl.DataPropertyAssertion):
            individual = cast(owl.AnonymousIndividual, axiom.source)
            nodes.add(individual)
            labels[individual].append(owl.DataHasValue(axiom.property, axiom.value))
        elif isinstance(axiom, owl.ObjectPropertyAssertion):
            source = axiom.source
            target = axiom.target
            if isinstance(source, owl.AnonymousIndividual) and isinstance(
                target, owl.AnonymousIndividual
            ):
                nodes.update((source, target))
                key = frozenset((source, target))
                if source == target or key in edges:
                    raise ValueError(
                        "anonymous-individual conclusion must be a forest with one edge per pair"
                    )
                edges[key] = (source, target, axiom.property)
                adjacency[source].add(target)
                adjacency[target].add(source)
            elif isinstance(source, owl.AnonymousIndividual):
                nodes.add(source)
                named_links[source].append((cast(owl.NamedIndividual, target), axiom.property))
            else:
                anonymous_target = cast(owl.AnonymousIndividual, target)
                nodes.add(anonymous_target)
                named_links[anonymous_target].append((source, owl.inverse_property(axiom.property)))

    components = _anonymous_components(nodes, adjacency)
    plans: list[QueryPlan] = []
    for component_index, component in enumerate(components):
        links = [
            (node, named, property_)
            for node in component
            for named, property_ in named_links.get(node, ())
        ]
        if len(links) > 1:
            raise ValueError(
                "anonymous-individual forest component has more than one named-individual edge"
            )
        root = links[0][0] if links else min(component, key=lambda value: value.canonical_bytes())
        expression = _roll_expression(root, None, labels, adjacency, edges, set())
        if links:
            _node, named, from_root = links[0]
            required = owl.ObjectSomeValuesFrom(owl.inverse_property(from_root), expression)
            counterexample: owl.AxiomNode = owl.ClassAssertion(
                owl.ObjectComplementOf(required),
                named,
            )
            label = f"anonymous-forest:named:{component_index}"
            plans.append(QueryPlan((counterexample,), (label,)))
        else:
            # Entailment of an existential component: every model must contain a root
            # satisfying the roll-up.  Its exact counterexample forces that class empty.
            counterexample = owl.SubClassOf(
                owl.OWL_THING,
                owl.ObjectComplementOf(expression),
            )
            label = f"anonymous-forest:existential:{component_index}"
            plans.append(QueryPlan((counterexample,), (label,)))
    return tuple(plans)


def _anonymous_components(
    nodes: set[owl.AnonymousIndividual],
    adjacency: dict[owl.AnonymousIndividual, set[owl.AnonymousIndividual]],
) -> tuple[frozenset[owl.AnonymousIndividual], ...]:
    remaining = set(nodes)
    components: list[frozenset[owl.AnonymousIndividual]] = []
    while remaining:
        start = min(remaining, key=lambda value: value.canonical_bytes())
        queue = deque((start,))
        component: set[owl.AnonymousIndividual] = set()
        while queue:
            node = queue.popleft()
            if node in component:
                continue
            component.add(node)
            queue.extend(adjacency.get(node, ()))
        remaining.difference_update(component)
        components.append(frozenset(component))
    return tuple(
        sorted(
            components,
            key=lambda value: min(item.canonical_bytes() for item in value),
        )
    )


def _roll_expression(
    node: owl.AnonymousIndividual,
    parent: owl.AnonymousIndividual | None,
    labels: dict[owl.AnonymousIndividual, list[owl.ClassExpression]],
    adjacency: dict[owl.AnonymousIndividual, set[owl.AnonymousIndividual]],
    edges: dict[
        frozenset[owl.AnonymousIndividual],
        tuple[owl.AnonymousIndividual, owl.AnonymousIndividual, owl.ObjectPropertyExpression],
    ],
    path: set[owl.AnonymousIndividual],
) -> owl.ClassExpression:
    if node in path:
        raise ValueError("anonymous-individual conclusion graph contains a cycle")
    path.add(node)
    expressions = list(labels.get(node, ()))
    for child in sorted(adjacency.get(node, ()), key=lambda value: value.canonical_bytes()):
        if child == parent:
            continue
        source, target, property_ = edges[frozenset((node, child))]
        outward = (
            property_ if source == node and target == child else owl.inverse_property(property_)
        )
        expressions.append(
            owl.ObjectSomeValuesFrom(
                outward,
                _roll_expression(child, node, labels, adjacency, edges, path),
            )
        )
    path.remove(node)
    return _class_intersection(expressions)


__all__ = ["ENTAILMENT_REDUCTION_TYPES", "EntailmentService"]
