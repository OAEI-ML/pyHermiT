# Stable API reference

The `pyhermit.Reasoner` facade is the supported reasoning boundary. It accepts any
`pyowl_core.OntologyInput`, retains a supplied compatible view by identity, serializes
operations, and implements the context-manager protocol. Keyword-only `direct=False`
selects the transitive answer; `direct=True` selects immediate quotient-graph neighbors.

## Lifetime and diagnostics

| Member | Contract |
|---|---|
| `Reasoner.ontology` | Retained immutable `OntologyView`; a compatible supplied view is returned by identity. |
| `Reasoner.config` | Frozen `ReasonerConfig` used to create the session. |
| `Reasoner.backend` | Selected immutable `BackendInfo`, including name, version, capabilities, and acceleration state. |
| `Reasoner.interrupt` | Requests cooperative cancellation of the active operation; it is a no-op when idle. |
| `Reasoner.dispose` | Idempotently closes private state; later semantic or update operations fail. |

## Logical checks and precomputation

| Member | Result |
|---|---|
| `Reasoner.is_consistent` | Logical consistency as `bool`. |
| `Reasoner.is_satisfiable` | Satisfiability of one `ClassExpression` as `bool`. |
| `Reasoner.is_subclass` | Whether one class expression is subsumed by another. |
| `Reasoner.entails` | Entailment of one supported logical axiom. |
| `Reasoner.entails_all` | Conjunctive entailment of a materialized iterable of logical axioms. |
| `Reasoner.supports_entailment` | Whether an axiom node type is supported by `entails`. |
| `Reasoner.is_defined` | Whether an entity occurs in the retained ontology signature. |
| `Reasoner.precompute` | Computes one or more requested `InferenceType` values atomically. |
| `Reasoner.is_precomputed` | Whether the requested inference type completed for the current state. |
| `Reasoner.precomputable` | All supported `InferenceType` values. |

## Class taxonomy

| Member | Result |
|---|---|
| `Reasoner.class_hierarchy` | Full class `Hierarchy`, retaining equivalence nodes and quotient edges. |
| `Reasoner.equivalent_classes` | Named classes equivalent to a class expression. |
| `Reasoner.superclasses` | Grouped named superclasses, direct or transitive. |
| `Reasoner.subclasses` | Grouped named subclasses, direct or transitive. |
| `Reasoner.unsatisfiable_classes` | Named classes equivalent to bottom. |
| `Reasoner.disjoint_classes` | Grouped named classes disjoint with an expression. |

## Object-property taxonomy

| Member | Result |
|---|---|
| `Reasoner.object_property_hierarchy` | Full object-property-expression `Hierarchy`. |
| `Reasoner.equivalent_object_properties` | Equivalent object-property expressions. |
| `Reasoner.super_object_properties` | Grouped super-properties, direct or transitive. |
| `Reasoner.sub_object_properties` | Grouped sub-properties, direct or transitive. |
| `Reasoner.inverse_object_properties` | Inverse property expressions. |
| `Reasoner.disjoint_object_properties` | Grouped disjoint property expressions. |
| `Reasoner.object_property_domains` | Grouped named domain classes, direct or transitive. |
| `Reasoner.object_property_ranges` | Grouped named range classes, direct or transitive. |

## Data-property taxonomy

| Member | Result |
|---|---|
| `Reasoner.data_property_hierarchy` | Full data-property `Hierarchy`. |
| `Reasoner.equivalent_data_properties` | Equivalent named data properties. |
| `Reasoner.super_data_properties` | Grouped super-properties, direct or transitive. |
| `Reasoner.sub_data_properties` | Grouped sub-properties, direct or transitive. |
| `Reasoner.disjoint_data_properties` | Grouped disjoint data properties. |
| `Reasoner.data_property_domains` | Grouped named domain classes, direct or transitive. |

## Realization and values

`IndividualResults` is either a frozen set of named individuals or a frozen set of
same-as groups according to `ReasonerConfig.individual_grouping`.

| Member | Result |
|---|---|
| `Reasoner.types` | Grouped named types of an individual, direct or transitive. |
| `Reasoner.has_type` | Whether an individual has a class-expression type, direct or transitive. |
| `Reasoner.instances` | Named instances or same-as groups, direct or transitive. |
| `Reasoner.same_individuals` | The named same-as equivalence group containing an individual. |
| `Reasoner.different_individuals` | Individuals known different from the argument. |
| `Reasoner.object_property_values` | Object values for a subject/property pair. |
| `Reasoner.object_property_instances` | Subject-to-object mapping for a property expression. |
| `Reasoner.has_object_property_relationship` | Whether one object-property assertion is entailed. |
| `Reasoner.data_property_values` | Source-preserving literals for a subject/data-property pair. |
| `Reasoner.has_data_property_relationship` | Whether one data-property assertion is entailed. |

## Buffered updates

| Member | Contract |
|---|---|
| `Reasoner.add_axioms` | Adds materialized axioms to the pending set, or flushes immediately when unbuffered. |
| `Reasoner.remove_axioms` | Removes materialized axioms through the same buffering policy. |
| `Reasoner.pending_additions` | Immutable snapshot of pending additions. |
| `Reasoner.pending_removals` | Immutable snapshot of pending removals. |
| `Reasoner.flush` | Publishes one new overlay-backed ontology state and rebuilds affected private state. |

`Hierarchy`, `ReasonerConfig`, `BackendName`, `BackendInfo`, `InferenceType`, and the
exception hierarchy are also public. A `Hierarchy` stores equivalence groups directly as
`nodes: tuple[frozenset[T], ...]`; `edges`, `top_node`, and `bottom_node` reference those
groups by integer index. See the
[user guide](user-guide.md) for backend selection, grouping, errors, cancellation,
shared views, and performance diagnostics. Public exports and signatures remain typed in
`pyhermit/__init__.py` and `pyhermit/facade.py`; changes to the facade member set must
update both this reference and the executable [coverage matrix](../reports/coverage-matrix.json).
