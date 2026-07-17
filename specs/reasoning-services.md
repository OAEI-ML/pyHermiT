# Reasoning services and public API

The API is Python-native but covers the observable core services of pinned HermiT
[`Reasoner.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/Reasoner.java)
and
[`EntailmentChecker.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/EntailmentChecker.java).

## 1. Public values

```python
T = TypeVar("T", bound=Entity)

@dataclass(frozen=True, slots=True)
class HierarchyNode(Generic[T]):
    members: frozenset[T]

@dataclass(frozen=True, slots=True)
class Hierarchy(Generic[T]):
    nodes: frozenset[HierarchyNode[T]]
    direct_edges: frozenset[tuple[HierarchyNode[T], HierarchyNode[T]]]
    top: HierarchyNode[T]
    bottom: HierarchyNode[T]

class InferenceType(StrEnum):
    CLASS_HIERARCHY = "class_hierarchy"
    OBJECT_PROPERTY_HIERARCHY = "object_property_hierarchy"
    DATA_PROPERTY_HIERARCHY = "data_property_hierarchy"
    CLASS_ASSERTIONS = "class_assertions"
    OBJECT_PROPERTY_ASSERTIONS = "object_property_assertions"
    SAME_INDIVIDUAL = "same_individual"
```

`HierarchyNode` equality is member-set equality. Each `direct_edges` pair is
`(subordinate, immediate_superior)`; reversing that orientation is an API error.
Public methods returning several equivalence/same-as groups use
`frozenset[frozenset[T]]`; methods returning flattened entities use `frozenset[T]`.
No empty node/group is returned.

## 2. Construction and lifecycle

```python
class Reasoner:
    def __init__(self, ontology: OntologyInput, *,
                 config: ReasonerConfig | None = None,
                 load_options: LoadOptions | None = None,
                 resolver: ImportResolver | None = None) -> None: ...
    @property
    def ontology(self) -> OntologyView: ...
    @property
    def config(self) -> ReasonerConfig: ...
    @property
    def backend(self) -> BackendInfo: ...
    def interrupt(self) -> None: ...
    def dispose(self) -> None: ...
    def __enter__(self) -> Reasoner: ...
    def __exit__(self, ...) -> None: ...
```

Construction calls `pyowl_core.coerce_snapshot` once, requires an already proven or newly
loaded strict import closure, validates, compiles private HermiT IR, and selects a backend.
Compatible core views are captured by identity; a provider is called once and never
reparsed. Construction MAY defer tableau allocation and classification. `dispose` is idempotent,
releases native memory/caches, and makes subsequent semantic/update calls raise
`DisposedReasonerError`; immutable `config`, `backend`, and diagnostic metadata remain
readable. It never closes/invalidates the shared core view.

`interrupt` may be called safely from another thread. It targets the currently active
operation(s), is not a permanent disposed state, and does not carry over to a later
operation after cleanup.

## 3. Basic satisfiability and entailment

```python
def is_consistent(self) -> bool: ...
def is_satisfiable(self, expression: ClassExpression) -> bool: ...
def is_subclass(self, sub: ClassExpression, sup: ClassExpression) -> bool: ...
def entails(self, axiom: LogicalAxiom) -> bool: ...
def entails_all(self, axioms: Iterable[LogicalAxiom]) -> bool: ...
def supports_entailment(self, axiom_type: type[LogicalAxiom]) -> bool: ...
def is_defined(self, entity: Entity) -> bool: ...
```

`entails_all` is true iff every axiom in the materialized input iterable is entailed;
the empty set is true. It snapshots the iterable before work and performs no partial
mutation if iteration raises. All in-scope logical axiom classes are supported for
1.0, so `supports_entailment` is false only for nonlogical/out-of-scope model classes.

### 3.1 Reductions

- Consistency is permanent ontology satisfiability.
- Class-expression satisfiability adds an operation-local anonymous `ROOT` witness
  asserted to the expression and checks consistency. It is explicitly not an OWL named
  individual and cannot activate a `HasKey` named guard.
- Subsumption `C ⊑ D` is tested by unsatisfiability of `C ⊓ ¬D` when no classified
  cache gives the answer.
- Entailment is reduced to inconsistency with the exact negation/counterexample of the
  axiom, or to a sound specialized/cache lookup.

Every axiom family has an explicit reduction tested against Direct Semantics.
Multientity axioms (equivalence, disjointness, same/different individuals) check all
required pairwise/directional conditions. Keys retain their named-individual semantics.
Negative assertions are not checked as absence of a positive fact; open-world
semantics requires an inconsistency reduction.

Query compilation cannot make permanent generated symbols visible or change later
answers.

## 4. Precomputation and cache status

```python
def precompute(self, *types: InferenceType) -> None: ...
def is_precomputed(self, type: InferenceType) -> bool: ...
def precomputable(self) -> frozenset[InferenceType]: ...
```

Unsupported enum values are errors; known but currently redundant requests may be
ignored only if the exact answers are already derivable from another completed cache.
Precompute is atomic per inference type: timeout/cancellation does not mark an
incomplete cache ready. A later call resumes only from a validated checkpoint or starts
again.

## 5. Class reasoning

```python
def class_hierarchy(self) -> Hierarchy[Class]: ...
def equivalent_classes(self, expression: ClassExpression) -> frozenset[Class]: ...
def superclasses(self, expression: ClassExpression, *, direct: bool = False) -> frozenset[frozenset[Class]]: ...
def subclasses(self, expression: ClassExpression, *, direct: bool = False) -> frozenset[frozenset[Class]]: ...
def unsatisfiable_classes(self) -> frozenset[Class]: ...
def disjoint_classes(self, expression: ClassExpression) -> frozenset[frozenset[Class]]: ...
```

Declared classes are included even when absent from logical axioms. `owl:Thing` and
`owl:Nothing` are always present. Unsatisfiable named classes share the bottom node.
For a complex query expression not already in the hierarchy, equivalence/super/sub/
disjoint results use satisfiability/subsumption reductions against named class nodes;
the query expression is not permanently inserted.

`direct=True` returns only cover relations after collapsing equivalence. The result
does not include the query's own equivalence node. Top/bottom edge cases follow the
mathematical hierarchy and pinned HermiT fixtures; no empty placeholder groups.

### 5.1 Classification algorithm

Use HermiT's optimized approach rather than testing every class pair blindly:

- deterministic ontologies use deterministic classification when safe;
- nondeterministic ontologies and forced mode use quasi-order classification;
- told subsumptions, obvious top/bottom/equivalence, model labels, and possible
  subsumer sets seed/prune tests; and
- every omitted relation must be justified by a sound bound.

References:
[`hierarchy/DeterministicClassification.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/hierarchy/DeterministicClassification.java),
[`hierarchy/QuasiOrderClassification.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/hierarchy/QuasiOrderClassification.java),
and
[`hierarchy/Hierarchy.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/hierarchy/Hierarchy.java).

A slow all-pairs classifier for tiny ontologies is retained in tests as an oracle.

## 6. Object-property reasoning

```python
def object_property_hierarchy(self) -> Hierarchy[ObjectPropertyExpression]: ...
def equivalent_object_properties(self, p: ObjectPropertyExpression) -> frozenset[ObjectPropertyExpression]: ...
def super_object_properties(self, p: ObjectPropertyExpression, *, direct: bool = False) -> frozenset[frozenset[ObjectPropertyExpression]]: ...
def sub_object_properties(self, p: ObjectPropertyExpression, *, direct: bool = False) -> frozenset[frozenset[ObjectPropertyExpression]]: ...
def inverse_object_properties(self, p: ObjectPropertyExpression) -> frozenset[ObjectPropertyExpression]: ...
def disjoint_object_properties(self, p: ObjectPropertyExpression) -> frozenset[frozenset[ObjectPropertyExpression]]: ...
def object_property_domains(self, p: ObjectPropertyExpression, *, direct: bool = False) -> frozenset[frozenset[Class]]: ...
def object_property_ranges(self, p: ObjectPropertyExpression, *, direct: bool = False) -> frozenset[frozenset[Class]]: ...
```

Named properties and their inverse expressions are handled consistently. Equivalent
inverses may share hierarchy nodes as in HermiT. Top/bottom properties are always
present. Property-chain inclusion is available through `entails`; a chain is not a
hierarchy element.

Domain/range answers are entailed named classes, classified into equivalence groups.
`direct=True` removes redundant strict superclasses in the class hierarchy. Range of
an inverse corresponds to domain of the forward role and vice versa.

Property classification may use the HermiT reduction of roles to fresh concepts and a
quasi-order traversal, but internal concept names cannot leak. Disjointness and
characteristics are semantic entailments, not merely asserted-axiom lookup.

## 7. Data-property reasoning

```python
def data_property_hierarchy(self) -> Hierarchy[DataProperty]: ...
def equivalent_data_properties(self, p: DataProperty) -> frozenset[DataProperty]: ...
def super_data_properties(self, p: DataProperty, *, direct: bool = False) -> frozenset[frozenset[DataProperty]]: ...
def sub_data_properties(self, p: DataProperty, *, direct: bool = False) -> frozenset[frozenset[DataProperty]]: ...
def disjoint_data_properties(self, p: DataProperty) -> frozenset[frozenset[DataProperty]]: ...
def data_property_domains(self, p: DataProperty, *, direct: bool = False) -> frozenset[frozenset[Class]]: ...
```

Top/bottom data properties and declared unused properties are included. Data ranges are
queried through entailment of `DataPropertyRange`; no named-class hierarchy is invented
for ranges in the 1.0 public API.

## 8. Realization and individuals

```python
def types(self, individual: NamedIndividual, *, direct: bool = False) -> frozenset[frozenset[Class]]: ...
def has_type(self, individual: NamedIndividual, expression: ClassExpression, *, direct: bool = False) -> bool: ...
def instances(self, expression: ClassExpression, *, direct: bool = False) -> frozenset[frozenset[NamedIndividual]] | frozenset[NamedIndividual]: ...
def same_individuals(self, individual: NamedIndividual) -> frozenset[NamedIndividual]: ...
def different_individuals(self, individual: NamedIndividual) -> frozenset[frozenset[NamedIndividual]] | frozenset[NamedIndividual]: ...
def object_property_values(self, subject: NamedIndividual, p: ObjectPropertyExpression) -> frozenset[frozenset[NamedIndividual]] | frozenset[NamedIndividual]: ...
def object_property_instances(self, p: ObjectPropertyExpression) -> Mapping[NamedIndividual, frozenset[NamedIndividual]]: ...
def has_object_property_relationship(self, subject: NamedIndividual, p: ObjectPropertyExpression, object: NamedIndividual) -> bool: ...
def data_property_values(self, subject: NamedIndividual, p: DataProperty) -> frozenset[Literal]: ...
def has_data_property_relationship(self, subject: NamedIndividual, p: DataProperty, value: Literal) -> bool: ...
```

The return form controlled by `IndividualGrouping` is:

- `BY_SAME_AS`: sets of same-as groups; and
- `BY_NAME` (HermiT default): flattened individual names where the operation permits.

`same_individuals` always returns the complete group including the queried name.
Anonymous source individuals affect reasoning but are not returned by named-individual
methods. Internal witnesses are never returned.

### 8.1 Semantics

- `types(..., direct=False)` returns all entailed named types, grouped by class
  equivalence; direct types are minimal non-bottom nodes.
- `instances(..., direct=False)` returns all named individuals entailed to satisfy the
  expression; direct instances are those whose direct type node is the expression's
  named equivalence node. For a complex expression, direct semantics follow the pinned
  HermiT behavior and dedicated fixtures rather than an ad hoc definition.
- same/different answers are entailments; lack of same-as is not different-from.
- object values include subproperties, inverses, equality of subjects/objects, and
  entailed assertions after merging.
- data values include subproperties and same subjects and preserve the literal/value
  policy in `datatypes.md`.
- top/bottom property queries obey Direct Semantics and do not enumerate anonymous
  domain elements as named answers.

Use a port of the behavior/optimizations in HermiT's instance manager, with a naive
per-query entailment implementation retained for tiny differential tests.

## 9. Fresh entities and inconsistent ontologies

With `FreshEntityPolicy.ALLOW` (default), a previously unseen named class/property/
individual receives the consequences fixed by OWL Direct Semantics and built-ins; it
is not inserted into the permanent declared hierarchy. With `DISALLOW`, any fresh
entity in a query raises `FreshEntityError` before backend work.

If the ontology is inconsistent, `is_consistent()` returns `False`. Other semantic
queries raise `InconsistentOntologyError` by default because classical explosion makes
ordinary result sets unhelpful, matching pinned HermiT's default. This behavior is
consistent across cached and uncached paths.

## 10. Updates and flushing

```python
def add_axioms(self, axioms: Iterable[Axiom]) -> None: ...
def remove_axioms(self, axioms: Iterable[Axiom]) -> None: ...
def pending_additions(self) -> frozenset[Axiom]: ...
def pending_removals(self) -> frozenset[Axiom]: ...
def flush(self) -> None: ...
```

`Axiom` above is the exact core class. Pending batches are canonicalized using core
structural identity. Commit constructs `OntologyDelta` and calls
`pyowl_core.apply_delta(current_view, delta)`; pyHermiT does not create a private ontology
revision/model.

In buffered mode, changes are canonicalized into two sets. Adding then removing the
same not-yet-present axiom cancels appropriately; exact set/revision semantics are
tested. Queries before `flush` see the last committed revision. In immediate mode,
each change batch commits before return.

`flush` builds/validates the proposed core overlay and strict import closure before modifying the
active session. On error the old revision remains usable and pending changes remain
inspectable. Assertion-only deltas may use a proven incremental backend path; all other
changes rebuild. Every committed change invalidates precisely or conservatively all
affected consistency, hierarchy, realization, role, datatype, and signature caches.

No update is visible to a concurrent query halfway through; it observes either the old
core view or the new immutable overlay. Core owns explicit overlay compaction;
pyHermiT never eagerly copies the unchanged base. Backend incremental application remains a
private optimization and must equal a fresh compilation from the effective overlay.

## 11. Timeouts, reuse, and thread behavior

Timeout applies separately to each public operation using monotonic time. Batched
precompute/check operations report timeout rather than returning a prefix. A reasoner
that can restore its operation-root checkpoint remains usable; otherwise it rebuilds
transparently before the next query or raises `BackendPoisonedError` if rebuilding also
fails.

One reasoner serializes semantic operations by default. Independent reasoners can run
concurrently. `interrupt`, immutable property reads, and pending-change inspection are
thread-safe. Callback reentrancy into the same reasoner is rejected with
`ConcurrentMutationError` rather than deadlocking.

## 12. Acceptance requirements

1. Every listed API has black-box tests on empty, consistent, and inconsistent
   ontologies, built-ins, fresh entities, equivalence, and direct/transitive edges.
2. Every logical axiom class has positive entailment and non-entailment reductions.
3. Class/property hierarchies compare exactly with HermiT after canonical grouping.
4. A naive tiny classifier/realizer agrees with optimized algorithms on generated
   ontologies.
5. Updates and every cache are tested against constructing a fresh reasoner for the
   resulting revision.
6. Forced Python/native/verify modes return identical immutable values and exceptions.
7. Repeated, concurrent-independent, timeout, interrupt, dispose, and callback-error
   tests leave no stale answer or memory leak.
