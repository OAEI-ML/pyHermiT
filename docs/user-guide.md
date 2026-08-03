# User guide

This guide walks through installing pyHermiT, choosing a backend, loading
ontologies, running every service family, applying updates, and handling limits and
errors. Exact member signatures live in the [API reference](api-reference.md);
exception semantics live in the [error reference](errors.md).

## Install and select a backend

pyHermiT supports CPython 3.10+ (wheels are built and release-tested on 3.10 and
3.12) and requires `pyowl-core>=0.2,<0.3`. A compatible native wheel contains one
`abi3` Rust extension; the universal wheel is the compiler-free Python fallback.
Neither artifact contains or starts Java.

Install a published release in a fresh virtual environment:

```shell
python -m pip install --upgrade pip
python -m pip install pyHermiT
```

For a coordinated checkout, install the matching core and force a compiler-free
editable build:

```shell
python -m pip install /path/to/pyOWLCore
PYHERMIT_BUILD_NATIVE=0 python -m pip install --no-deps -e /path/to/pyHermiT
```

`--no-deps` is intentional only for coordinated development checkouts where the
compatible `pyowl-core 0.2.x` checkout is already installed.

Source builds use `PYHERMIT_BUILD_NATIVE=auto|0|1`: `auto` tries Rust and otherwise
builds a truthful pure wheel, `0` always builds the fallback, and `1` fails if the
native extension cannot be built.

### Runtime backend selection

Which engine answers queries is chosen per reasoner, independently of how the
package was built:

```python
from pyhermit import BackendName, ReasonerConfig, backend_info

print(backend_info())  # availability report; creates no session
python_config = ReasonerConfig(backend=BackendName.PYTHON)
native_config = ReasonerConfig(backend=BackendName.NATIVE)
```

- `AUTO` (default) selects once when a reasoner is created: native when a
  compatible extension passes its capability handshake, otherwise Python.
- `PYTHON` is the complete pure-Python engine and is always available.
- `NATIVE` is fail-closed: it raises `NativeBackendUnavailableError` when the
  extension or capability handshake is unavailable rather than silently falling
  back.
- `VERIFY` runs native and an independent Python shadow and raises
  `BackendMismatchError` on any observable mismatch; it roughly doubles the work
  and is intended for focused verification, not routine throughput.

The `PYHERMIT_BACKEND` environment variable (`auto`, `python`, `native`, or
`verify`) overrides the `AUTO` default — useful for CI lanes and diagnostics — but
an explicit `ReasonerConfig(backend=...)` always wins. `backend_info()` reports
both backends' availability, the raw environment request, and an unavailability
`reason` (for example `"not_installed"` or `"import_failed"`) without creating a
session.

Every backend must produce identical logical answers and error classes; they may
differ only in speed. Semantic parity is enforced by the release test suite.

## Load once or reuse a shared view

A path, bytes, caller-owned stream, `OntologyDocument`, or core view can be supplied to
`Reasoner`. For standalone use, load explicitly when more than one consumer needs the
ontology:

```python
from pyowl_core import BackendPreference, ImportPolicy, LoadOptions, load_snapshot
from pyhermit import BackendName, Reasoner, ReasonerConfig

options = LoadOptions(
    imports=ImportPolicy.RESOLVE_STRICT,
    backend=BackendPreference.PYTHON,
)
source = (
    b"Prefix(:=<urn:guide#>) Ontology(<urn:guide> "
    b"Declaration(Class(:A)) Declaration(Class(:B)) SubClassOf(:A :B))"
)
snapshot = load_snapshot(source, options=options)

with Reasoner(
    snapshot,
    config=ReasonerConfig(backend=BackendName.PYTHON),
) as reasoner:
    assert reasoner.ontology is snapshot
    assert reasoner.is_consistent()
```

Reasoning requires a complete import closure and an OWL 2 DL-conforming view. Pass an
explicit core resolver for offline imports; ignored or unresolved required imports are
rejected before reasoning with `IncompleteImportClosureError`, and profile
violations raise `OntologyProfileError`.

Exact-OM and other orchestrators can share overlays and composites without reparsing or
concatenating their public models. This continuation of the preceding example is
executable as written:

```python
from pyowl_core import CanonicalSet, Class, IRI, OntologyDelta, SubClassOf
from pyowl_core import apply_delta, compose_views, load_snapshot
from pyhermit import Reasoner

target = load_snapshot(
    b"Prefix(:=<urn:target#>) Ontology(<urn:target> Declaration(Class(:C)))",
    options=options,
)
bridge_axiom = SubClassOf(Class(IRI("urn:guide#A")), Class(IRI("urn:target#C")))
candidate_source = apply_delta(
    snapshot,
    OntologyDelta(add_axioms=CanonicalSet((bridge_axiom,))),
)
combined = compose_views(candidate_source, target, roles=("source", "target"))

with Reasoner(combined) as reasoner:
    assert reasoner.ontology is combined
    unsatisfiable = reasoner.unsatisfiable_classes()
```

A provider may expose `owl_snapshot()` instead. It is called exactly once and must
return a compatible `OntologyView`; the returned object is retained by identity.

## Query services and result shape

The facade provides:

- consistency, class-expression satisfiability, subclass and axiom entailment;
- class, object-property, and data-property classification;
- equivalence, disjointness, domain, range, inverse, superclass, and subclass queries;
- realization: types, instances, same/different individuals, and object/data values;
- precomputation diagnostics; and
- buffered axiom addition/removal followed by `flush()`.

The [API reference](api-reference.md) lists every stable facade member and its result
shape. A few worked examples, continuing from the snapshot loaded above:

```python
from pyowl_core import Class, IRI, SubClassOf

a = Class(IRI("urn:guide#A"))
b = Class(IRI("urn:guide#B"))

with Reasoner(snapshot) as reasoner:
    # Boolean checks.
    assert reasoner.is_subclass(a, b)
    assert reasoner.entails(SubClassOf(a, b))

    # Navigation: each result group is one equivalence class of named classes.
    direct_supers = reasoner.superclasses(a, direct=True)   # {frozenset({b})}
    all_supers = reasoner.superclasses(a)                   # includes owl:Thing

    # Whole taxonomy as a quotient graph.
    taxonomy = reasoner.class_hierarchy()
    top_group = taxonomy.nodes[taxonomy.top_node]           # owl:Thing's group
    below_top = taxonomy.descendants(taxonomy.top_node)     # node indexes
```

### Reading grouped results

Hierarchy answers preserve equivalence nodes. Methods returning
`frozenset[frozenset[...]]` therefore return groups, not flattened names: if `:A`
and `:B` are equivalent superclasses of `:C`, `superclasses(:C)` contains one
group `{A, B}`, not two separate entries. Flatten explicitly when group structure
does not matter:

```python
named_superclasses = {cls for group in reasoner.superclasses(a) for cls in group}
```

For navigation queries, `direct=True` selects only immediate quotient-graph
neighbors; the default returns the transitive answer. Individual results follow
`ReasonerConfig.individual_grouping`: `BY_NAME` (default) returns named
individuals, while `BY_SAME_AS` retains same-as groups. Returned literals preserve
observable lexical and datatype identity even when data-domain comparison says two
values are equal.

An inconsistent ontology raises `InconsistentOntologyError` for services whose answer
is undefined; it is never converted to an empty set. `is_consistent()` itself
returns `False`. `supports_entailment()` reports whether an axiom type is accepted
before a query is attempted.

By default, entities that appear in a query but not in the ontology signature are
answered under OWL Direct Semantics (`fresh_entities=ALLOW`); set
`FreshEntityPolicy.DISALLOW` to make such queries raise `FreshEntityError`
instead. `is_defined()` checks signature membership explicitly.

## Updates and lifetime

With the default `buffer_changes=True`, `add_axioms()` and `remove_axioms()` update the
pending sets and `flush()` publishes one new immutable overlay-backed view. With
`buffer_changes=False`, each call flushes immediately. Current delta handling may
rebuild private compiled state; it does not mutate the caller's core view.

```python
from pyowl_core import Class, IRI, SubClassOf

new_axiom = SubClassOf(Class(IRI("urn:guide#B")), Class(IRI("urn:guide#A")))
reasoner.add_axioms([new_axiom])
assert new_axiom in reasoner.pending_additions()
reasoner.flush()                      # publishes a new overlay-backed view
assert reasoner.ontology.contains(new_axiom)
```

Use a context manager or call `dispose()`. Later semantic, update, precompute, or interrupt
operations raise `DisposedReasonerError`; the immutable `ontology`, `config`, and `backend`
diagnostic properties remain readable. A reasoner serializes its operations. A second thread may call
`interrupt()`; queries and mutations from different threads wait for the active operation
and then run serially. Same-thread reentrant calls and reentrant disposal raise
`ConcurrentMutationError` rather than exposing partial state.

## Time, memory, cancellation, and errors

`ReasonerConfig(timeout=seconds, max_memory_bytes=bytes)` applies per public operation.
Timeout and interrupt paths roll back operation-local state before another query is
allowed, so the reasoner remains usable after an aborted operation. They raise
`ReasonerTimeoutError`, `ReasonerInterruptedError`, or another
`ReasoningAbortedError` subclass; they are not logical `False` answers.

```python
from pyhermit import Reasoner, ReasonerConfig, ReasoningAbortedError

config = ReasonerConfig(timeout=30.0, max_memory_bytes=2_000_000_000)
with Reasoner(snapshot, config=config) as reasoner:
    try:
        taxonomy = reasoner.class_hierarchy()
    except ReasoningAbortedError as error:
        print("aborted:", error.code, dict(error.context))
```

Configure limits for untrusted or large inputs: OWL 2 DL reasoning is worst-case
intractable, and a hostile ontology can otherwise consume unbounded time or memory.

Failures produced after the pyowl-core input boundary derive from `PyHermiTError` and
carry a stable code/context mapping through `as_dict()`. Python argument-contract errors
remain `TypeError`/`ValueError`, and pyowl-core acquisition, parsing, import, and resolver
errors propagate unchanged. The [error reference](errors.md) documents the full
taxonomy; the most common configuration/input failures are
`IncompleteImportClosureError`, `OntologyProfileError`, `UnsupportedDatatypeError`,
`NativeBackendUnavailableError`, `BackendVersionError`, and `ResourceLimitError`.
Messages are diagnostic and are not a compatibility key; match on the class or
`code`.

### Progress and warning callbacks

Long operations can report progress without polling:

```python
from pyhermit import ReasonerConfig

def on_progress(event):   # pyhermit.events.ProgressEvent
    print(event.kind, event.completed, event.total, event.elapsed_seconds)

def on_warning(event):    # pyhermit.events.WarningEvent
    print(event.code, event.message)

config = ReasonerConfig(progress=on_progress, warnings=on_warning)
```

Callbacks are invoked synchronously on the initiating Python thread; native work
queues events while the GIL is released and drains them at safe points. They are
observability hooks only — they never change results and intentionally do not
partition caches.

## Version and performance diagnostics

Record `pyhermit.__version__`, `backend_info()`, `reasoner.backend`,
`reasoner.diagnostics()`, the core structural, logical, and signature fingerprints, and
`ReasonerConfig.as_dict()` with a result. The immutable diagnostics mapping uses the shared
`scalar-python`, `scalar-wire`, and `encoded-native` ingestion-path vocabulary. Its lowercase
SHA-256 `compiler_digest` covers the canonical compiler manifest and is independent of the
selected backend/ingestion path. The path-specific private session-cache key is deliberately not
exposed as that digest. `consumer_compile_seconds` is the monotonic wall duration of the latest
successful private compilation and permanent-session preparation from an already validated core
view; input acquisition, parsing, and profile validation are outside that interval. The public
`COMPILER_CACHE_SCHEMA_VERSION`, `COMPILED_IR_SCHEMA_VERSION`, and `NATIVE_ABI_VERSION`
constants support import-light cache partitioning.

When a compatible native extension and pyowl-core encoded structural-view schema 2 are
available, `ingestion_path` is `encoded-native` and the eleven `encoded_*` fields report
the measured permanent-session compiler boundary. Scalar Python and scalar native-wire
compatibility paths report exact zero/false values; a validation-only encoded preflight is
deliberately excluded from those counters. Do not compare a warm shared view to a cold file
load as if they were the same workload.
General parser, core-wire, scalar-materialization, and public-model-copy deltas are not inferred
from an input shape and are omitted until their owning boundary exposes an authoritative counter.
The required methodology separates load, validation, compilation, first/repeated
reasoning, classification, realization, updates, and peak RSS; see
[the performance specification](../specs/performance.md).

## Troubleshooting

- **`backend_info()` says native is unavailable.** The `reason` field explains why:
  `"not_installed"` means the universal (pure-Python) wheel is installed — check
  that your platform is one of the published native targets; `"import_failed"`
  means the extension exists but could not load; a handshake reason means the
  extension and the Python package disagree on ABI, IR schema, or core versions —
  reinstall matching versions. The Python backend is complete, so everything still
  works, only slower.
- **`IncompleteImportClosureError` on load.** The ontology imports documents that
  were not resolved. Pass `LoadOptions(imports=ImportPolicy.RESOLVE_STRICT)` with a
  reachable source, or supply an explicit `ImportResolver` for offline resolution.
- **`InconsistentOntologyError` from a query.** The ontology is inconsistent;
  call `is_consistent()` first and repair the ontology (the axiom set returned by
  `unsatisfiable_classes()` on a consistent-but-incoherent ontology is often the
  faster diagnostic).
- **Persisted 0.1 data fails to load.** pyHermiT 0.2.0 rejects the pyowl-core 0.1
  API/model contract fail-closed. Persisted pyowl-core 0.1 snapshot bytes, encoded
  descriptors, and consumer cache keys must be regenerated with pyowl-core 0.2
  before use; see the [0.2 migration guide](migration-0.2.md).

Local wheels and semantic suites are verified. The historical `0.1.1`
[release report](../reports/release-report-local.json) records the prior universal
publication, while the `0.2.0` workflow requires the complete hosted wheel set. The owner
accepted only the remaining external WP17 runs as post-release follow-up.
