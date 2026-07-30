# User guide

## Install and select a backend

pyHermiT supports CPython 3.10 and 3.12 and requires `pyowl-core>=0.1,<0.2`.
A compatible native wheel contains one `abi3` Rust extension; the universal wheel is
the compiler-free Python fallback. Neither artifact contains or starts Java.

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
compatible `pyowl-core 0.1.0` checkout is already installed.

Source builds use `PYHERMIT_BUILD_NATIVE=auto|0|1`: `auto` tries Rust and otherwise
builds a truthful pure wheel, `0` always builds the fallback, and `1` fails if the
native extension cannot be built. Runtime selection is separate:

```python
from pyhermit import BackendName, ReasonerConfig, backend_info

print(backend_info())
python_config = ReasonerConfig(backend=BackendName.PYTHON)
native_config = ReasonerConfig(backend=BackendName.NATIVE)
```

`AUTO` selects once when a reasoner is created. `NATIVE` is fail-closed when the
extension or capability handshake is unavailable. `VERIFY` runs native and an
independent Python shadow and raises `BackendMismatchError` on any observable mismatch;
it is intended for focused verification, not routine throughput.

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
rejected before reasoning.

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
shape.

Hierarchy answers preserve equivalence nodes. Methods returning
`frozenset[frozenset[...]]` therefore return groups, not flattened names. For navigation
queries, `direct=True` selects only immediate quotient-graph neighbors; the default
returns the transitive answer. Individual results follow
`ReasonerConfig.individual_grouping`: `BY_NAME` returns named individuals, while
`BY_SAME_AS` retains same-as groups. Returned literals preserve observable lexical and
datatype identity even when data-domain comparison says two values are equal.

An inconsistent ontology raises `InconsistentOntologyError` for services whose answer
is undefined; it is never converted to an empty set. `supports_entailment()` reports
whether an axiom type is accepted before a query is attempted.

## Updates and lifetime

With the default `buffer_changes=True`, `add_axioms()` and `remove_axioms()` update the
pending sets and `flush()` publishes one new immutable overlay-backed view. With
`buffer_changes=False`, each call flushes immediately. Current delta handling may
rebuild private compiled state; it does not mutate the caller's core view.

Use a context manager or call `dispose()`. Later semantic, update, precompute, or interrupt
operations raise `DisposedReasonerError`; the immutable `ontology`, `config`, and `backend`
diagnostic properties remain readable. A reasoner serializes its operations. A second thread may call
`interrupt()`; queries and mutations from different threads wait for the active operation
and then run serially. Same-thread reentrant calls and reentrant disposal raise
`ConcurrentMutationError` rather than exposing partial state.

## Time, memory, cancellation, and errors

`ReasonerConfig(timeout=seconds, max_memory_bytes=bytes)` applies per public operation.
Timeout and interrupt paths roll back operation-local state before another query is
allowed. They raise `ReasonerTimeoutError`, `ReasonerInterruptedError`, or another
`ReasoningAbortedError` subclass; they are not logical `False` answers.

Failures produced after the pyowl-core input boundary derive from `PyHermiTError` and
carry a stable code/context mapping through `as_dict()`. Python argument-contract errors
remain `TypeError`/`ValueError`, and pyowl-core acquisition, parsing, import, and resolver
errors propagate unchanged. Important pyHermiT configuration/input failures include
`IncompleteImportClosureError`, `OntologyProfileError`, `UnsupportedDatatypeError`,
`NativeBackendUnavailableError`, `BackendVersionError`, and `ResourceLimitError`.
Messages are diagnostic and are not a compatibility key.

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

Until the encoded-native session path is enabled, the eleven `encoded_*` fields are exact
zero/false accounting for the permanent-session compiler boundary. They are not estimates or
unimplemented placeholders: a native validation-only encoded preflight is deliberately excluded,
and the selected session still consumes the scalar private wire. Do
not compare a warm shared view to a cold file load as if they were the same workload.
General parser, core-wire, scalar-materialization, and public-model-copy deltas are not inferred
from an input shape and are omitted until their owning boundary exposes an authoritative counter.
The required methodology separates load, validation, compilation, first/repeated
reasoning, classification, realization, updates, and peak RSS; see
[the performance specification](../specs/performance.md).

Local wheels and semantic suites are verified. The machine-readable
[release report](../reports/release-report-local.json) records the owner's acceptance of
the remaining external WP17 runs as post-release follow-up for `0.1.1`.
