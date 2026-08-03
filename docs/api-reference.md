# Stable API reference

The `pyhermit.Reasoner` facade is the supported reasoning boundary. Everything in
this document is importable from the top-level `pyhermit` package unless noted
otherwise. Public exports and signatures remain typed in `pyhermit/__init__.py` and
`pyhermit/facade.py`.

Reading the tables:

- `ontology`, `config`, and `backend` are read-only properties; every other facade
  member is a method.
- Entity, expression, axiom, and literal arguments are exact `pyowl_core.model`
  values (`Class`, `ClassExpression`, `ObjectPropertyExpression`, `DataProperty`,
  `NamedIndividual`, `LogicalAxiom`, `Literal`, ...). Results reuse the same types.
- Keyword-only `direct=False` selects the transitive answer; `direct=True` selects
  only immediate quotient-graph neighbors.
- Grouped results of type `frozenset[frozenset[...]]` preserve equivalence classes:
  each inner frozenset is one group of mutually equivalent entities, never a
  flattened union.

## Constructing a reasoner

```python
Reasoner(
    ontology: pyowl_core.OntologyInput,
    *,
    config: ReasonerConfig | None = None,
    document_iri: pyowl_core.IRI | str | None = None,
    load_options: pyowl_core.LoadOptions | None = None,
    resolver: pyowl_core.ImportResolver | None = None,
)
```

| Parameter | Meaning |
|---|---|
| `ontology` | A path, bytes, caller-owned stream, `OntologyDocument`, an existing core view (`OntologySnapshot`, `OntologyOverlay`, `OntologyComposite`), or a provider exposing `owl_snapshot()`. A compatible supplied view is retained by identity, never reparsed. |
| `config` | Frozen `ReasonerConfig`; `None` uses the defaults. |
| `document_iri` | Optional document IRI for raw sources. |
| `load_options` | Optional `pyowl_core.LoadOptions` applied when the input must be loaded. |
| `resolver` | Optional `pyowl_core.ImportResolver` for offline or custom import resolution. |

Construction validates the input (identity, import closure, OWL 2 DL profile),
selects the backend once, and compiles the private session. Input, profile, and
backend failures raise before the reasoner exists; see the
[error reference](errors.md).

`Reasoner` implements the context-manager protocol; `with Reasoner(view) as r:`
disposes the session on exit. All operations on one reasoner are serialized.

## Lifetime and diagnostics

| Member | Contract |
|---|---|
| `Reasoner.ontology` | Property. Retained immutable `OntologyView`; a compatible supplied view is returned by identity. |
| `Reasoner.config` | Property. Frozen `ReasonerConfig` used to create the session. |
| `Reasoner.backend` | Property. Selected immutable `BackendInfo`, including name, versions, capabilities, and acceleration state. |
| `Reasoner.diagnostics` | `()` — immutable sorted scalar mapping describing compiler identity, `consumer_compile_seconds`, ingestion path, and bounded encoded-ingestion counters. See the [user guide](user-guide.md#version-and-performance-diagnostics). |
| `Reasoner.interrupt` | `()` — requests cooperative cancellation of the active operation from another thread; a no-op when idle. The interrupted operation raises `ReasonerInterruptedError`. |
| `Reasoner.dispose` | `()` — idempotently closes private state. Later semantic, update, precompute, or interrupt operations raise `DisposedReasonerError`; the three properties above remain readable. |

## Logical checks and precomputation

| Member | Result |
|---|---|
| `Reasoner.is_consistent` | `()` — logical consistency as `bool`. Returns `False` for an inconsistent ontology instead of raising. |
| `Reasoner.is_satisfiable` | `(expression)` — satisfiability of one `ClassExpression` as `bool`. |
| `Reasoner.is_subclass` | `(sub, sup)` — whether one class expression is subsumed by another. |
| `Reasoner.entails` | `(axiom)` — entailment of one supported `LogicalAxiom`. |
| `Reasoner.entails_all` | `(axioms)` — conjunctive entailment of a materialized iterable of logical axioms. |
| `Reasoner.supports_entailment` | `(axiom_type)` — whether an axiom node type is supported by `entails`. |
| `Reasoner.is_defined` | `(entity)` — whether an entity occurs in the retained ontology signature. |
| `Reasoner.precompute` | `(*types)` — computes one or more requested `InferenceType` values atomically. |
| `Reasoner.is_precomputed` | `(type)` — whether the requested inference type completed for the current ontology state. |
| `Reasoner.precomputable` | `()` — all supported `InferenceType` values as a `frozenset`. |

`InferenceType` values: `CLASS_HIERARCHY`, `OBJECT_PROPERTY_HIERARCHY`,
`DATA_PROPERTY_HIERARCHY`, `CLASS_ASSERTIONS`, `OBJECT_PROPERTY_ASSERTIONS`, and
`SAME_INDIVIDUAL`. Precomputation is an optional warm-up: every service computes
what it needs on demand, and `flush()` invalidates completed precomputations.

## Class taxonomy

| Member | Result |
|---|---|
| `Reasoner.class_hierarchy` | `()` — full class `Hierarchy`, retaining equivalence nodes and quotient edges. |
| `Reasoner.equivalent_classes` | `(expression)` — named classes equivalent to a class expression, as `frozenset[Class]`. |
| `Reasoner.superclasses` | `(expression, *, direct=False)` — grouped named superclasses. |
| `Reasoner.subclasses` | `(expression, *, direct=False)` — grouped named subclasses. |
| `Reasoner.unsatisfiable_classes` | `()` — named classes equivalent to `owl:Nothing`. |
| `Reasoner.disjoint_classes` | `(expression)` — grouped named classes disjoint with an expression. |

## Object-property taxonomy

| Member | Result |
|---|---|
| `Reasoner.object_property_hierarchy` | `()` — full object-property-expression `Hierarchy`. |
| `Reasoner.equivalent_object_properties` | `(property_)` — equivalent object-property expressions. |
| `Reasoner.super_object_properties` | `(property_, *, direct=False)` — grouped super-properties. |
| `Reasoner.sub_object_properties` | `(property_, *, direct=False)` — grouped sub-properties. |
| `Reasoner.inverse_object_properties` | `(property_)` — inverse property expressions. |
| `Reasoner.disjoint_object_properties` | `(property_)` — grouped disjoint property expressions. |
| `Reasoner.object_property_domains` | `(property_, *, direct=False)` — grouped named domain classes. |
| `Reasoner.object_property_ranges` | `(property_, *, direct=False)` — grouped named range classes. |

## Data-property taxonomy

| Member | Result |
|---|---|
| `Reasoner.data_property_hierarchy` | `()` — full data-property `Hierarchy`. |
| `Reasoner.equivalent_data_properties` | `(property_)` — equivalent named data properties. |
| `Reasoner.super_data_properties` | `(property_, *, direct=False)` — grouped super-properties. |
| `Reasoner.sub_data_properties` | `(property_, *, direct=False)` — grouped sub-properties. |
| `Reasoner.disjoint_data_properties` | `(property_)` — grouped disjoint data properties. |
| `Reasoner.data_property_domains` | `(property_, *, direct=False)` — grouped named domain classes. |

## Realization and values

`IndividualResults` is either `frozenset[NamedIndividual]` or
`frozenset[frozenset[NamedIndividual]]` according to
`ReasonerConfig.individual_grouping`: `BY_NAME` (default) returns named
individuals, `BY_SAME_AS` retains same-as groups.

| Member | Result |
|---|---|
| `Reasoner.types` | `(individual, *, direct=False)` — grouped named types of an individual. |
| `Reasoner.has_type` | `(individual, expression, *, direct=False)` — whether an individual has a class-expression type. |
| `Reasoner.instances` | `(expression, *, direct=False)` — instances as `IndividualResults`. |
| `Reasoner.same_individuals` | `(individual)` — the named same-as equivalence group containing an individual. |
| `Reasoner.different_individuals` | `(individual)` — individuals known different from the argument, as `IndividualResults`. |
| `Reasoner.object_property_values` | `(subject, property_)` — object values for a subject/property pair, as `IndividualResults`. |
| `Reasoner.object_property_instances` | `(property_)` — mapping from each subject to its `frozenset` of objects. |
| `Reasoner.has_object_property_relationship` | `(subject, property_, object)` — whether one object-property assertion is entailed. |
| `Reasoner.data_property_values` | `(subject, property_)` — literals as `frozenset[Literal]`, preserving observable lexical and datatype identity. |
| `Reasoner.has_data_property_relationship` | `(subject, property_, value)` — whether one data-property assertion is entailed. |

## Buffered updates

| Member | Contract |
|---|---|
| `Reasoner.add_axioms` | `(axioms)` — adds materialized axioms to the pending set, or flushes immediately when `buffer_changes=False`. An axiom pending removal is simply un-removed. |
| `Reasoner.remove_axioms` | `(axioms)` — removes materialized axioms through the same buffering policy. |
| `Reasoner.pending_additions` | `()` — immutable snapshot of pending additions. |
| `Reasoner.pending_removals` | `()` — immutable snapshot of pending removals. |
| `Reasoner.flush` | `()` — publishes one new overlay-backed ontology state, rebuilds affected private state, and clears precomputation markers. The caller's original core view is never mutated. |

## ReasonerConfig

`ReasonerConfig` is a frozen dataclass captured at construction; changing a setting
requires a new reasoner. String values are accepted anywhere an enum is expected
(`backend="python"`). Defaults preserve pinned-HermiT-compatible semantics; strategy
options change time and witness construction, never logical answers.

| Field | Default | Meaning |
|---|---|---|
| `backend` | `BackendName.AUTO` | Backend selection; see below. |
| `timeout` | `None` | Per-public-operation wall-clock limit in seconds; finite and positive, or `None` for unbounded. |
| `buffer_changes` | `True` | Buffer `add_axioms`/`remove_axioms` until `flush()`; `False` flushes on every call. |
| `fresh_entities` | `FreshEntityPolicy.ALLOW` | `ALLOW` gives query-only entities their OWL Direct Semantics consequences; `DISALLOW` raises `FreshEntityError` before backend work. |
| `individual_grouping` | `IndividualGrouping.BY_NAME` | Shape of `IndividualResults`: named individuals or same-as groups. |
| `unsupported_datatypes` | `UnsupportedDatatypePolicy.ERROR` | `ERROR` raises `UnsupportedDatatypeError`; `IGNORE_WITH_WARNING` continues and emits a warning event. |
| `blocking` | `BlockingMode.AUTO` | Tableau blocking strategy: `AUTO` follows pinned HermiT's per-ontology choice; `ANYWHERE`, `VALIDATED_ANYWHERE`, and `ANCESTOR` force one strategy for testing and diagnostics. All legal strategies return identical answers. |
| `existentials` | `ExistentialMode.AUTO` | Existential-expansion strategy: `AUTO`/`CREATION_ORDER` expand in stable creation order; `INDIVIDUAL_REUSE` enables the optional sound witness-reuse optimization. |
| `disjunction_learning` | `True` | Dependency-directed disjunct learning. |
| `force_quasi_order_classification` | `False` | Forces the quasi-order classification path regardless of heuristics. |
| `workers` | `0` | `0` is backend-safe automatic sizing; a positive value is an exact native worker cap. The Python backend may remain single-threaded without changing answers. |
| `max_memory_bytes` | `None` | Per-operation memory budget; exceeding it raises `ResourceLimitError`. |
| `deterministic` | `True` | `False` may permit experimental scheduling but never different logical answers; excluded from reproducible baselines. |
| `progress` | `None` | `Callable[[ProgressEvent], None]`, invoked synchronously on the initiating thread. |
| `warnings` | `None` | `Callable[[WarningEvent], None]`, same delivery contract. |

`ReasonerConfig.as_dict()` returns the stable scalar mapping of semantic options
(callbacks excluded) suitable for logging alongside results. The event dataclasses
`ProgressEvent` and `WarningEvent` live in `pyhermit.events`.

### Backend names

| `BackendName` | Behavior |
|---|---|
| `AUTO` | Selects once at construction: native when a compatible extension passes its handshake, otherwise Python. The `PYHERMIT_BACKEND` environment variable can override `AUTO`; an explicit `config.backend` always wins. |
| `PYTHON` | The complete pure-Python engine; always available. |
| `NATIVE` | The Rust engine; fail-closed — raises `NativeBackendUnavailableError` instead of silently falling back. |
| `VERIFY` | Runs native and an independent Python shadow, comparing every observable answer; any difference raises `BackendMismatchError`. Intended for focused verification, not routine throughput. |

## Result and status types

### Hierarchy

`Hierarchy[T]` is the frozen quotient graph returned by the three
`*_hierarchy()` methods:

- `nodes: tuple[frozenset[T], ...]` — each node is one equivalence group of
  entities; the groups partition all named entities of the kind.
- `edges: frozenset[tuple[int, int]]` — direct edges as `(child, parent)` pairs of
  node indexes, pointing from the more specific to the more general group.
- `top_node: int` / `bottom_node: int` — indexes of the top group (for classes:
  `owl:Thing`) and bottom group (`owl:Nothing`).
- `ancestors(node)` / `descendants(node)` — transitive reachability from a node
  index, as `frozenset[int]` of node indexes.

### Backend information

- `backend_info()` — module-level function reporting availability without creating
  a session. Returns a `BackendStatus` with the raw `PYHERMIT_BACKEND` request, the
  default selection, one `BackendAvailability` record per backend (including an
  unavailability `reason` such as `"not_installed"` or `"import_failed"`), and the
  detected core package/API versions.
- `BackendInfo` — the selected backend of a live reasoner (`Reasoner.backend`):
  name (`"python"`, `"native"`, or `"verify"`), package and implementation
  versions, core contract versions, `complete_features`, and whether it is
  `accelerated`.

### Constants

| Constant | Purpose |
|---|---|
| `COMPILER_CACHE_SCHEMA_VERSION` | Version of the private compiler-cache record layout. |
| `COMPILED_IR_SCHEMA_VERSION` | Version of the compiled private-IR schema shared with the native backend. |
| `NATIVE_ABI_VERSION` | Version of the Python/Rust extension ABI. |
| `__version__` | The pyHermiT package version. |

All three schema constants are import-light and intended for cache partitioning and
provenance records; see the [user guide](user-guide.md#version-and-performance-diagnostics).

## Exceptions

The full taxonomy, stable error codes, and handling guidance are in the
[error reference](errors.md). `InferenceType`, the configuration enums, and the
exception classes are all exported from the top-level `pyhermit` package;
convenience re-exports of the core loading surface (`load_snapshot`,
`apply_delta`, `compose_views`, `LoadOptions`, `OntologyDelta`, the view types,
`IRI`, and `ImportResolver`) are also available there.

Changes to the facade member set must update both this reference and the
executable [coverage matrix](../reports/coverage-matrix.json).
