# Shared contracts

This document defines values that cross module or backend boundaries. Concrete Python
tableau objects and Rust structs are private and are not part of this contract.

Public OWL structural values and ontology documents/views (snapshot/overlay/composite) are not defined here:
they are the exact `pyowl_core` 0.2 classes. The contracts below begin at pyHermiT's
configuration, compiled-reasoner, backend, and result boundaries.

Upstream reference points:

- [`Configuration.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/Configuration.java)
- [`Reasoner.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/Reasoner.java)
- [`model/`](https://github.com/phillord/hermit-reasoner/tree/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/model)
- [`tableau/ReasoningTaskDescription.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/ReasoningTaskDescription.java)

## 1. General value rules

All public and backend-neutral contract values MUST be:

- immutable after construction;
- structurally comparable and hashable where their fields are hashable;
- free of backend pointers, Java values, ambient global configuration, and mutable
  default arguments;
- serializable to a versioned canonical JSON representation for fixture diagnostics;
- type annotated without `Any` at a public boundary; and
- validated on construction so malformed IR cannot reach either tableau.

No pyHermiT public contract may duplicate, wrap, monkey-patch, or attach reasoner state to a
core OWL value. Public result entities/literals retain exact core class identity.

Collections with set semantics are stored as sorted tuples in serialized forms. Python
APIs may expose `frozenset` when ordering is immaterial. A caller must never infer
semantic meaning from iteration order.

## 2. Identity and deterministic IDs

### 2.1 Public identity

Named entities are identified by `(EntityKind, absolute_iri)`. Punning therefore
creates distinct values with the same IRI. Built-ins use their normative OWL/RDF/RDFS/
XSD IRIs and are never replaced by spelling aliases.

Anonymous-individual scoping, alpha-canonical keys, named entity identity, literal structural
identity, and standards-canonical language handling are pyowl-core contracts consumed
unchanged. Blank-node labels from two core documents never collide after imports are
combined.

Private compilation preserves a core source-literal reference while deriving a
language-neutral data-domain identity token and datatype-family comparison record.
Source-literal structural identity, OWL data-value identity, and facet comparison/equality
are three distinct relations as specified in `datatypes.md`; only the first is public/core.
No API or wire field named merely `value_id` may blur them.

### 2.2 Compiled IDs

The compiler assigns dense unsigned IDs independently in these domains:

- entities by kind;
- class expressions and data ranges;
- object-property expressions/roles;
- individuals;
- source literals and data-domain identity values (separate ID domains);
- predicates; and
- normalized clauses/atoms.

IDs are assigned from canonical sort keys, never hash-table iteration or parse order.
ID `0` in each domain is either a documented built-in/sentinel or a valid first item;
there are no implicit negative sentinels across the Python/Rust boundary. Width is
`u32` while the count fits; compilation raises `ResourceLimitError` before overflow.
Rust may widen internal counters to `usize`, but serialized IDs remain `u32` in schema
version 1.

Generated names use an IRI namespace derived from the captured core `logical_fingerprint`, the
canonical source expression, and its polarity class, not the combined ontology
fingerprint or an incrementing parse-order counter. Query-local names also include the
query hash. A generated symbol map is retained in diagnostic IR but generated IRIs
never appear as answers.

## 3. Canonical compiled IR

The facade first retains a small capture record; it is metadata plus one reference, not a
second ontology:

```python
@dataclass(frozen=True, slots=True)
class CapturedOntology:
    view: OntologyView
    structural_fingerprint: Fingerprint
    logical_fingerprint: Fingerprint
    signature_fingerprint: Fingerprint
    core_package_version: str
    core_api_version: tuple[int, int]
    core_model_schema_version: int
    core_wire_format_version: tuple[int, int]
    core_adapter_protocol_version: int
```

`view` is retained by identity and may be a snapshot, overlay, or composite. Its effective
closure is compiled into private HermiT IR without flattening/copying the public model.

`CompiledOntology` is the immutable handoff to a backend. It contains only primitives,
sorted tuples, and versioned records:

```python
@dataclass(frozen=True, slots=True)
class CompiledOntology:
    schema_version: int
    ontology_fingerprint: str
    source_structural_fingerprint: Fingerprint
    source_logical_fingerprint: Fingerprint
    source_signature_fingerprint: Fingerprint
    core_package_version: str
    core_api_version: tuple[int, int]
    core_model_schema_version: int
    core_wire_format_version: tuple[int, int]
    core_adapter_protocol_version: int
    symbols: SymbolTable
    clauses: tuple[DLClause, ...]
    positive_facts: tuple[GroundAtom, ...]
    negative_facts: tuple[GroundAtom, ...]
    ground_disjunctions: tuple[GroundDisjunctionIR, ...]
    role_model: RoleModel
    datatype_model: DatatypeModel
    expressivity: Expressivity
    declared_entities: tuple[EntityRef, ...]
    named_individuals: tuple[int, ...]
    provenance: ProvenanceTable
```

The exact atom and clause grammar is in `normalization-clausification.md`. The record
MUST validate all references, arities, sort constraints, role simplicity constraints,
and deterministic ordering. `schema_version` changes whenever an existing reader could
misinterpret bytes or values; Python and native versions must match exactly.

`CompiledQuery` contains additional clauses/facts and a result interpretation for one
consistency reduction. Its generated IDs live in a query-local range and cannot mutate
the permanent IR. Reusing a backend session after a query MUST leave the permanent
ontology byte-for-byte logically unchanged.

`ontology_fingerprint` is pyHermiT's domain-separated compiler/session key over core
logical/signature fingerprints and schema/wire/adapter versions, pyHermiT compiler
schema/configuration, and the pinned compatibility identifier. The stored structural
fingerprint is provenance/profile metadata, not necessarily a semantic IR cache partition.
This is not a reimplementation of a core fingerprint and is never derived by serializing
Functional Syntax or RDF. `CompiledOntology` remains private HermiT IR; it MUST NOT be passed
to pyELK/Exact-OM/projectors as an ontology snapshot.

## 4. Configuration

```python
class BackendName(StrEnum):
    AUTO = "auto"
    PYTHON = "python"
    NATIVE = "native"
    VERIFY = "verify"

class FreshEntityPolicy(StrEnum):
    DISALLOW = "disallow"
    ALLOW = "allow"

class IndividualGrouping(StrEnum):
    BY_SAME_AS = "by_same_as"
    BY_NAME = "by_name"

class UnsupportedDatatypePolicy(StrEnum):
    ERROR = "error"
    IGNORE_WITH_WARNING = "ignore_with_warning"

class BlockingMode(StrEnum):
    AUTO = "auto"
    ANYWHERE = "anywhere"
    VALIDATED_ANYWHERE = "validated_anywhere"
    ANCESTOR = "ancestor"             # diagnostics/reference comparisons

class ExistentialMode(StrEnum):
    AUTO = "auto"
    CREATION_ORDER = "creation_order"
    INDIVIDUAL_REUSE = "individual_reuse"

@dataclass(frozen=True, slots=True)
class ReasonerConfig:
    backend: BackendName = BackendName.AUTO
    timeout: float | None = None
    buffer_changes: bool = True
    fresh_entities: FreshEntityPolicy = FreshEntityPolicy.ALLOW
    individual_grouping: IndividualGrouping = IndividualGrouping.BY_NAME
    unsupported_datatypes: UnsupportedDatatypePolicy = UnsupportedDatatypePolicy.ERROR
    blocking: BlockingMode = BlockingMode.AUTO
    existentials: ExistentialMode = ExistentialMode.AUTO
    disjunction_learning: bool = True
    force_quasi_order_classification: bool = False
    workers: int = 0                 # 0 = backend-safe automatic sizing
    max_memory_bytes: int | None = None
    deterministic: bool = True
    progress: ProgressCallback | None = field(default=None, compare=False, repr=False)
    warnings: WarningCallback | None = field(default=None, compare=False, repr=False)
```

Validation rules:

- `timeout` is `None` or finite and strictly positive.
- `workers` is nonnegative; positive values are an exact native worker cap. The pure
  Python backend may remain single-threaded without changing answers.
- resource limits are `None` or positive integers.
- callbacks are callable and invoked synchronously on the initiating Python thread;
  native work queues events while the GIL is released and drains them at safe points.
- `deterministic=False` MAY permit experimental scheduling but never different logical
  answers; it is excluded from reproducible benchmark baselines.
- public defaults preserve HermiT-compatible semantics. Strategies can change time and
  witness construction, never answers.

Unknown configuration keys are errors. Config is captured at reasoner construction;
mutating the original object is impossible and changing a setting requires a new
reasoner.

## 5. Backend protocol

Only `backends.protocol` defines this interface. The protocol is synchronous; an
application can place calls in its own worker threads. Implementations MAY cache and
batch internally.

```python
@dataclass(frozen=True, slots=True)
class BackendInfo:
    name: Literal["python", "native", "verify"]
    package_version: str
    ir_schema_version: int
    implementation_version: str
    core_package_version: str
    core_api_version: tuple[int, int]
    core_model_schema_version: int
    core_wire_format_version: tuple[int, int]
    core_adapter_protocol_version: int
    complete_features: frozenset[str]
    accelerated: bool

@dataclass(frozen=True, slots=True)
class BackendAvailability:
    name: Literal["python", "native"]
    available: bool
    implementation_version: str | None
    ir_schema_version: int | None
    reason: str | None    # native only: "not_installed", "unsupported_runtime",
                          # "abi_mismatch", "self_test_failed", ...

@dataclass(frozen=True, slots=True)
class BackendStatus:
    environment_request: str | None      # raw PYHERMIT_BACKEND value, if set
    default_selection: Literal["python", "native"]
    python: BackendAvailability
    native: BackendAvailability
    core_package_version: str
    core_api_version: tuple[int, int]

def backend_info() -> BackendStatus: ...

class BackendFactory(Protocol):
    @property
    def info(self) -> BackendInfo: ...

    def create_session(
        self,
        ontology: CompiledOntology,
        config: ReasonerConfig,
        cancellation: CancellationToken,
    ) -> BackendSession: ...

class BackendSession(Protocol):
    @property
    def ontology_fingerprint(self) -> str: ...
    def check(self, query: CompiledQuery | None = None) -> CheckResult: ...
    def check_many(self, queries: Sequence[CompiledQuery]) -> tuple[CheckResult, ...]: ...
    def classify_classes(self) -> HierarchyIds: ...
    def classify_object_properties(self) -> HierarchyIds: ...
    def classify_data_properties(self) -> HierarchyIds: ...
    def realize(self) -> RealizationIds: ...
    def apply_delta(self, delta: CompiledDelta) -> DeltaOutcome: ...
    def reset_query_state(self) -> None: ...
    def close(self) -> None: ...
```

`check(None)` checks permanent-ontology consistency. A query is a satisfiability
reduction; `CheckResult.satisfiable` is the only semantic truth returned. Optional
statistics and traces are explicitly nonsemantic. `check_many` is equivalent to
ordered independent calls and MUST isolate rollback/cancellation between items.

Native classification/realization methods are first-class so repeated tests do not
cross the FFI for each entity. The Python backend may implement them through shared
hierarchy algorithms and `check_many`. `apply_delta` returns `APPLIED_INCREMENTALLY`
or `REBUILD_REQUIRED`; it must never claim incremental success after a conservative
fallback. The public reasoner performs the rebuild when required.

`backend_info()` is the module-level diagnostic exported by the facade
(`SPEC.md` §5.1, `native-backend.md` §11). It is side-effect-light: it may import
and self-test `_native` to answer availability, but it creates no session,
performs no I/O beyond the import, and emits no warning for ordinary absence
(`reason="not_installed"` is a normal answer). A present extension that fails
`self_test()` or mismatches the IR schema is reported unavailable with the hard
error reason, matching dispatch behavior. `BackendInfo` remains the per-session
record returned by `Reasoner.backend`; `BackendStatus` never claims a session
exists.

After `close`, every operation raises `DisposedReasonerError`. `close` is idempotent.

The backend session holds or is dominated by the facade's strong reference to the captured
core view for the complete native-borrow lifetime. Backends never own, close, or
mutate it. Native transfer is coarse and bounded as specified in `native-backend.md`.

## 6. Result contracts

### 6.1 Checks

```python
@dataclass(frozen=True, slots=True)
class CheckResult:
    satisfiable: bool
    statistics: ReasoningStatistics
```

Statistics do not participate in equality. No partial model or anonymous witness is a
stable API in 1.0. Debug traces, if enabled in a later version, use a separate unstable
namespace and cannot affect rule scheduling.

### 6.2 Hierarchies

`Hierarchy[T]` is a finite DAG whose nodes are nonempty equivalence sets. It includes a
distinguished top and bottom node. Edges are the transitive reduction and are always
oriented `(subordinate, immediate_superior)` (for example, subclass to superclass or
subproperty to superproperty). Invariants:

1. every declared in-domain entity occurs in exactly one node;
2. bottom contains all and only unsatisfiable elements for a class hierarchy;
3. top/bottom built-ins are always present;
4. no edge is reflexive and no alternate path connects the endpoints of a direct edge;
5. `ancestors`/`descendants` are derived from edges and do not store contradictory
   caches; and
6. canonical serialization sorts members by full IRI and nodes by their member tuple.

`HierarchyIds` uses compiled IDs at the backend boundary. The facade validates it and
maps IDs to `Hierarchy[Entity]`.

### 6.3 Realization

`RealizationIds` contains:

- same-as equivalence classes for every named individual;
- direct class-node types per same-as node;
- direct object-property targets indexed by subject and property, with same-as groups;
- finite entailed data-property answers as source-literal IDs, each resolving through
  the symbol table to its lexical triple, data-identity token, and comparison record;
  multiple explicit lexical/datatype aliases are retained; and
- different-from relationships when entailed.

Transitive/all types and instances are derived from the classified hierarchy. Property
queries must account for property hierarchy, inverses, equality merging, and bottom/top
semantics. Data-value enumeration is over the finite source-literal candidate universe
defined in `reasoning-services.md`; it never pretends to enumerate the infinite data
domain. The facade validates that every referenced ID exists, each literal ID has a
valid identity/comparison record, and same-as groups partition the named individuals.

## 7. Exception taxonomy

Parsing, import acquisition, resolver, core wire, and core load-limit failures retain the
corresponding `pyowl_core` exception classes and diagnostics; pyHermiT may re-export them by
identity but does not wrap/rewrite them. Its hierarchy covers validation and reasoning:

All public exceptions inherit `PyHermiTError`:

```text
PyHermiTError
├── OntologyInputError
│   ├── IncompleteImportClosureError
│   ├── OntologyProfileError
│   ├── InvalidLiteralError
│   └── UnsupportedDatatypeError
├── ReasonerStateError
│   ├── DisposedReasonerError
│   ├── InconsistentOntologyError
│   ├── FreshEntityError
│   └── ConcurrentMutationError
├── ReasoningAbortedError
│   ├── ReasonerTimeoutError
│   ├── ReasonerInterruptedError
│   └── ResourceLimitError
├── BackendError
│   ├── NativeBackendUnavailableError
│   ├── BackendVersionError
│   ├── BackendMismatchError
│   └── BackendPoisonedError
├── FeatureNotImplementedError
└── InternalInvariantError
```

Each exception has a stable machine-readable `code`, a human message, and optional
structured context. Python and Rust map the same condition to the same public class and
code. Source locations and Rust panic strings may appear only as chained diagnostic
causes, not as the stable message contract.

## 8. Cancellation and events

`CancellationToken` combines an atomic interrupted flag, optional monotonic deadline,
and optional resource counters. Checks occur at least at clause-batch, expansion,
branch, merge, datatype-check, and classification-test boundaries. A configurable
internal polling stride may be optimized but the default worst-case cancellation
latency must meet `performance.md`.

Progress events have a version, operation ID, kind, completed/total when known, and
monotonic elapsed time. They never contain backend-owned mutable objects. Callback
exceptions request cancellation and are re-raised on the initiating thread after the
backend reaches a safe point.

## 9. Contract tests

Every contract type needs:

- construction and rejection tests;
- stable canonical JSON round trips;
- deterministic output under randomized insertion/parse order;
- equality/hash laws;
- Python/Rust schema round trips for native-visible types;
- unknown-version and corrupt-reference rejection; and
- property tests at size boundaries (`0`, `1`, maximum `u32` metadata without
  allocation, and overflow).
