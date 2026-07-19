# pyHermiT — master specification

## 1. Product definition

pyHermiT is a Python package implementing a complete OWL 2 DL reasoner based on the
HermiT hypertableau approach. It has two interchangeable engines:

- a complete, readable pure-Python engine that works on every supported Python
  installation without a C or Rust compiler; and
- an optimized Rust engine distributed in platform wheels and selected automatically
  when available.

The package MUST have no Java process, JVM, JAR, JNI/JPype bridge, OWLAPI dependency, or
Java installation requirement while building any release artifact, installing, importing,
or running. A separately invoked development oracle MAY use the pinned upstream
Java implementation to generate and compare fixtures. Oracle tools and upstream Java
artifacts MUST NOT be included in wheels or imported by production code.

The canonical public OWL structural/parsing/communication layer is the separate distribution
`pyowl-core` / import `pyowl_core`. pyHermiT 0.1.x requires `pyowl-core>=0.1,<0.2`, re-exports
its OWL types by identity, accepts its ontology views/providers without reparsing, and
keeps all normalized clauses/tableau state private.

The behavioral reference is the head of HermiT's `master` branch selected by the
project owner, pinned here to immutable commit
[`37ec30aced32ac81ebecc5e33fad255ddefcb4c3`](https://github.com/phillord/hermit-reasoner/commit/37ec30aced32ac81ebecc5e33fad255ddefcb4c3)
(upstream Maven version `1.4.0.0-SNAPSHOT`). The pin may change only in a dedicated
reference-update pull request that regenerates fixtures, reruns the complete parity
matrix, and documents every changed result.

## 2. Meaning of compatibility

### 2.1 Required observable behavior

For every valid OWL 2 DL ontology in the supported input model, pyHermiT MUST agree
with the compatibility oracle on all logically observable core results:

- ontology consistency;
- satisfiability of arbitrary class expressions;
- entailment and non-entailment of every logical OWL 2 axiom type;
- the complete class hierarchy, equivalence sets, direct and transitive parents and
  children, unsatisfiable classes, and disjoint classes;
- the complete object-property and data-property hierarchies, equivalence sets,
  inverses, disjointness, domains, and ranges;
- realization: all and direct types, all and direct instances, same and different
  individuals, and entailed object- and data-property values;
- handling of fresh entities, inconsistency, timeout, interruption, disposal, imports,
  declarations, annotations, and invalid/unsupported inputs as defined in the domain
  specs; and
- results after supported ontology updates and cache invalidation.

Set-valued results are compared as canonical mathematical sets, not Java iteration
order. Equivalence classes are compared as sets of sets. Anonymous internal witnesses,
node IDs, generated symbol spelling, hash-table order, proof order, and the particular
model found are not public behavior.

### 2.2 Correctness precedence and bug fixes

The desired result is HermiT-compatible **and** standards-correct. When those differ,
the following precedence applies:

1. the W3C OWL 2 Structural Specification, Direct Semantics, published errata, and an
   applicable approved conformance test;
2. an accepted entry in [`deviations.md`](deviations.md);
3. the pinned HermiT result for behavior not fixed by the standard;
4. pure-Python and Rust exact parity.

Thus a confirmed HermiT bug MUST be fixed rather than reproduced, but never silently.
Every intentional mismatch needs a minimal reproducer, normative evidence, expected
results for both backends, and a permanent regression test. Performance changes and
different data structures do not require deviation records when results are unchanged.

### 2.3 Full behavior and staged development

Work may land in dependency-ordered stages, but the product MUST NOT claim general
OWL 2 DL or HermiT compatibility until every mandatory release gate passes. During
development, unsupported mandatory constructs MUST fail explicitly with
`FeatureNotImplementedError(feature_id=...)`; they MUST NOT be ignored, approximated,
or assigned a guessed result. No mandatory construct may remain in that state for a
1.0 release.

The pure-Python backend and Rust backend have the same semantic scope. It is forbidden
to make a construct native-only. The Rust engine MAY temporarily lag on a development
branch, in which case `auto` dispatches the entire reasoning session to Python before
work starts; it MUST NOT switch engines halfway through a tableau or silently answer a
query in Python after a native semantic failure.

## 3. Scope

### 3.1 Included core

The following are mandatory:

1. The complete OWL 2 DL structural language and Direct Semantics, including SROIQ
   object reasoning, nominals, inverses, qualified number restrictions, complex role
   inclusions, keys, negative assertions, punning, and required datatypes.
2. Validation of the OWL 2 DL typing and global restrictions before reasoning.
3. Strict resolved import-closure semantics supplied by pyowl-core, with an explicit,
   deterministic resolver/load policy.
4. Exact public pyowl-core ontology/expression/axiom values, immutable `OntologyView`
   snapshots/deltas/overlays/composites, and the `SnapshotProvider` communication contract.
5. Standalone path/bytes/stream loading through pyowl-core and zero-reparse consumption of
   an existing document/view/provider. Syntax parsing, RDF mapping, and canonical
   OWL writing are core responsibilities, not pyHermiT implementations.
6. HermiT's core hypertableau family: normalization and clausification, role
   preprocessing, hyperresolution, anywhere blocking, dependency-directed
   backtracking, equality merging, existential expansion, the nominal-introduction
   rule, cardinalities, datatype constraints, clash detection, and termination.
7. Optimized class, object-property, and data-property classification plus individual
   realization and property-instance retrieval.
8. Buffered and immediate update modes for additions/removals that preserve semantic
   correctness. An implementation MAY rebuild instead of incrementally updating for a
   change class not covered by a proven incremental path.
9. Synchronous Python APIs, cooperative timeout/interruption, deterministic result
   canonicalization, thread-safe independent reasoners, and documented resource
   ownership.
10. CPython wheels with the Rust accelerator and a compiler-free pure-Python path.

All input syntaxes produce the same structural model. Parser differences are never an
excuse for reasoning-result differences.

### 3.2 Explicitly excluded extras

Do not implement or ship:

- DL-safe SWRL rules or the standalone datalog engine;
- HermiT description graphs;
- SPARQL/conjunctive-query answering;
- the Protege/OSGi plugin, OWLLink server, Java OWLReasoner compatibility facade, JNI,
  or Java command-line interface;
- the interactive debugger, derivation-history UI, Swing components, or upstream
  monitor implementations;
- ontology explanation/minimal-justification generation;
- pretty-print/dump utilities whose only purpose is reproducing Java CLI output; or
- RDF-Based Semantics or OWL Full reasoning.

A small Python CLI MAY be added after 1.0 as a separate work package, but it is not a
core completion requirement. Structured progress events and metrics are allowed as
Python-native observability, not as ports of the Java monitor hierarchy.

### 3.3 Boundary cases

- Annotation axioms and annotations are accepted and retained by I/O when requested,
  but ignored by Direct Semantics. They never enter the reasoning kernel.
- Declarations affect parsing/type validation but not entailments.
- OWL 2 profiles (EL, QL, RL) are subsets of the mandatory language, not separate
  approximate engines.
- Invalid OWL 2 DL ontologies are rejected by profile validation. The reasoner does
  not apply OWL Full semantics.
- Unsupported nonstandard datatypes are errors by default. An explicit compatibility
  configuration may reproduce HermiT's `ignoreUnsupportedDatatypes` policy, with a
  warning event and tests.
- Network retrieval is never implicit. The default resolver accepts caller-provided
  documents and local files; HTTP resolution requires an explicit resolver supplied
  by the caller.

## 4. Architecture

### 4.1 Intended repository tree

```text
pyHermiT/
├── pyproject.toml
├── Cargo.toml                    # Rust workspace; absent from pure wheel payload
├── README.md
├── LICENSE
├── NOTICE.md
├── specs/
├── src/pyhermit/
│   ├── __init__.py               # stable public facade only
│   ├── api.py                    # Reasoner and top-level helpers
│   ├── config.py                 # frozen ReasonerConfig
│   ├── exceptions.py
│   ├── events.py                 # optional structured progress/warning events
│   ├── core.py                   # pyowl-core versions/types/re-export guard
│   ├── inputs.py                 # coerce_snapshot/provider capture only
│   ├── model/__init__.py         # optional exact core re-exports; no model classes
│   ├── profile/                  # OWL 2 DL typing/global-restriction validator
│   ├── normalize/                # normalization and fresh-symbol allocator
│   ├── clauses/                  # backend-neutral normalized ontology/DL-clause IR
│   ├── roles/                    # role hierarchy, regularity, automata
│   ├── datatypes/                # lexical/value model and Python constraint solver
│   ├── hierarchy/                # backend-neutral hierarchy/result algorithms
│   ├── backends/
│   │   ├── protocol.py           # narrow complete-session backend protocol
│   │   ├── dispatch.py           # auto/python/native/verify selection
│   │   └── python/               # complete pure-Python hypertableau
│   └── _native.pyi               # typed surface of optional compiled module
├── native/                       # PyO3 Rust crate; never imported by Python backend
│   ├── Cargo.toml
│   └── src/
├── tests/
│   ├── unit/
│   ├── conformance/
│   ├── parity/
│   ├── differential/
│   ├── property/
│   ├── packaging/
│   └── data/
├── tools/reference/              # opt-in Java oracle fetch/run/normalize tools
├── benchmarks/
└── .github/workflows/
```

Names may change only through a spec amendment before dependent work begins. Source
files MUST use the lower-case import package `pyhermit`; the distribution name is
`pyHermiT` if available on the target index.

### 4.2 Dependency direction

```text
pyowl_core ← core/re-exports ← inputs, profile
pyowl_core ← normalize ← roles
pyowl_core + normalize + roles ← clauses
contracts/config/events/core/clauses ← backends.protocol
backends.protocol ← backends.python
backends.protocol ← optional _native
all of the above ← hierarchy/reasoning services ← api
```

More concretely:

- `core`/re-exports, `config`, `exceptions`, and immutable result contracts are leaves and MUST
  NOT import a backend.
- `inputs` and profile validation MUST NOT import a tableau backend.
- normalization, role processing, and clause IR MUST NOT import a concrete backend.
- the Python backend MUST NOT import `_native`, PyO3, or Rust-specific values.
- the native extension MUST consume owned or borrowed primitive buffers of pyHermiT's
  private compiled IR at a coarse boundary; it MUST NOT callback into Python during saturation
  or mistake that IR for a pyowl-core view.
- hierarchy/services may call only `BackendSession`, never concrete tableau classes.
- only `backends.dispatch` may conditionally import `_native`.
- import-linter (or an equivalent AST check) enforces these rules in CI.

### 4.3 Reasoning pipeline

Every backend executes the same logical pipeline:

```text
path/stream or shared core document/view/provider
→ pyowl_core.coerce_snapshot (identity-preserving for compatible shared inputs)
→ require a strict resolved immutable import closure
→ validate OWL 2 DL structure and global restrictions
→ canonicalize expressions, entities, axioms, literals, and deterministic fresh names
→ normalize axioms
→ compute role hierarchy, simplicity/regularity, and role automata
→ clausify to an immutable normalized-ontology IR
→ initialize ABox facts and tableau indexes
→ saturate with hypertableau rules, blocking, datatype checks, and backtracking
→ reduce the satisfiability result to the requested reasoning service
→ canonicalize the public result
```

Core loading is cacheable by core fingerprints; backend-neutral HermiT transformations are
cacheable by core fingerprints plus core/compiler schema versions.
Backends MUST receive the same frozen IR. A future optimization MAY move an exactly
equivalent transformation into Rust, but parity against the shared transformation is
then mandatory and the public cache key must remain stable.

### 4.4 Stable boundary: whole sessions, not tiny kernels

The native boundary is deliberately coarse. Creating a native session transfers the
normalized ontology once. A session exposes satisfiability/entailment primitives and
batched classification/realization operations. Nodes, extension rows, dependency sets,
and rule matches remain inside one backend. Per-tuple or per-rule Python/Rust calls are
forbidden in production because they would dominate execution time and complicate
rollback ownership.

The two engines may use different internal representations, but both MUST implement
the invariants in `tableau-state.md` and rule semantics in `hypertableau.md`.

## 5. Public product contract

### 5.1 Main values and entry points

The stable facade exposes:

```python
from pyhermit import (
    OntologySnapshot,
    OntologyOverlay,
    OntologyComposite,
    OntologyView,
    Reasoner,
    ReasonerConfig,
    load_snapshot,
    backend_info,
)
```

`Reasoner(ontology_input, config=..., document_iri=..., load_options=..., resolver=...)`
coerces exactly once,
requires a strict core import closure, and captures the core view by identity plus its
fingerprints. Query methods and exact return shapes are specified in
`reasoning-services.md`. OWL expressions are exact immutable core values; updates create a
core `OntologyOverlay` through `OntologyDelta` or enter an explicit reasoner change buffer.

No public value exposes a backend-specific pointer or numeric ID. Public entities use
full IRIs. Results that distinguish direct from transitive answers accept a keyword-only
`direct: bool = False`. All collections returned by public APIs are immutable.

### 5.2 Configuration

`ReasonerConfig` is a frozen, slot-based dataclass. At minimum it owns:

- `backend: Literal["auto", "python", "native", "verify"] = "auto"`;
- `timeout: float | None = None` in monotonic seconds per public operation;
- `buffer_changes: bool = True`;
- fresh-entity and individual-node-set policies;
- unsupported-datatype policy;
- deterministic seed/order policy (default fixed and reproducible);
- safe public choices for blocking and existential strategy, with `"auto"` defaults;
- resource limits that fail explicitly rather than corrupting state; and
- optional warning/progress callbacks invoked outside native locks.

Environment variable `PYHERMIT_BACKEND` may override `auto` for diagnostics, but an
explicit constructor value wins. All effective configuration is available from
`reasoner.config` and included in diagnostic manifests.

### 5.3 Errors and cancellation

The public exception taxonomy is backend-independent. It includes parse, import,
profile, unsupported datatype/feature, inconsistency, fresh entity, timeout,
interruption, disposed reasoner, resource exhaustion, native availability, and
internal invariant errors. The native layer translates Rust errors and panics at the
boundary; no Rust panic may unwind into CPython.

`Reasoner.interrupt()` is thread-safe and cooperative. Timeout and interrupt checks
occur at bounded work intervals in both engines. A cancelled query never returns a
partial logical result. A backend session may be reused only if rollback to its last
committed checkpoint is proven; otherwise it is marked poisoned and rebuilt before the
next query.

### 5.4 Determinism and concurrency

- Identical ontology, configuration, backend version, and query MUST yield identical
  canonical public results across processes and supported platforms.
- Hash randomization and thread scheduling MUST NOT affect fresh names, branch order
  recorded in fixtures, or public ordering.
- Separate `Reasoner` instances are safe to use concurrently.
- One instance permits concurrent read-only queries only if its backend advertises and
  tests snapshot safety. Otherwise calls serialize with a per-instance lock.
- Mutation/flush/dispose are exclusive operations.
- The Rust backend releases the GIL during long computation and uses internal threads
  only where determinism, cancellation, and memory limits remain enforceable.

## 6. Backends and packaging

### 6.1 Dispatch behavior

`auto` selects native only when the extension imports successfully, its ABI/schema
version exactly matches the Python package, and it declares the complete feature set
required by the frozen ontology. Otherwise selection happens before session creation
and Python is used. Import absence is normal and MUST NOT emit a warning.

An extension that imports but fails an invariant/self-test is an installation error,
not a reason for silent fallback. Native semantic errors, crashes, or result mismatches
are never swallowed. `verify` runs both complete engines on the same IR in development,
compares canonical outputs, and raises `BackendMismatchError`; it is not intended for
untrusted production workloads.

### 6.2 Distribution behavior

Official CPython wheels include a PyO3 extension built with the oldest practical
stable CPython ABI supported by the project. A universal pure-Python wheel and sdist
remain installable on unsupported platforms and interpreters. Building the optional
extension from an sdist MUST be best-effort: absence of `rustc`/Cargo produces a valid
pure-Python installation. Build control is `PYHERMIT_BUILD_NATIVE=auto|0|1`: `auto`
tries an optional extension, `0` builds pure only, and `1` requires native or fails.

Packaging tests cover:

- each supported native wheel and a forced-native smoke/conformance subset;
- the universal wheel with native artifacts proven absent;
- an isolated sdist build with Rust deliberately unavailable;
- forced Python operation even when native is installed;
- import and reasoning without a network, Java, a compiler, or writable source tree;
- packaged type information, licenses/notices, and pyowl-core compatibility metadata; no
  duplicate parser resources.

Every artifact declares `pyowl-core>=0.1,<0.2`. No artifact contains or depends on a JAR,
class file, JVM launcher, JNI/JPype bridge, Java package, or downloaded Java resource.

The final matrix and build mechanism are normative in `native-backend.md`.

## 7. Verification contract

Correctness has four independent oracles:

1. W3C OWL 2 approved Direct Semantics tests;
2. upstream HermiT regression and black-box behavior at the pinned commit;
3. hand-derived unit tests for calculus rules and state invariants; and
4. exact Python-versus-Rust differential tests.

The Java oracle is never queried only once and trusted blindly. Oracle records contain
the source commit, Java/OWLAPI versions, input hash, operation, normalized output,
exception category, configuration, and generator version. Committed fixtures are
reviewable text or content-addressed compressed records. See `verification.md`.

Every mandatory construct has positive, negative, inconsistent, interacting-feature,
and rollback tests. Random generators preserve OWL 2 DL global restrictions unless a
test is explicitly about invalid input. Metamorphic tests exercise axiom reordering,
equivalent syntax, alpha-renamed anonymous individuals, redundant entailed axioms,
imports flattening, and backend/session reuse.

## 8. Performance contract

Correctness always gates optimization. The pure-Python implementation is the readable
fallback and correctness baseline; it is not required to match Java speed. It must,
however, avoid accidental superlinear behavior where the specified algorithm provides
a better bound and must complete the designated small conformance suite under its
budget.

The native engine is the production performance target. It MUST:

- beat the pure-Python backend materially on each designated medium/large workload;
- introduce no greater than the allowed regression against the pinned benchmark
  baseline on any workload class;
- meet the Java comparison targets in `performance.md` on the controlled reference
  machine;
- report peak resident memory as well as time;
- keep Python/Rust boundary time separately measurable; and
- retain exact output parity when an optimization is enabled or disabled.

When the captured core advertises a compatible `EncodedStructuralView`, the optimized path also
MUST satisfy `native-structural-ingestion.md`: profile validation, normalization, clausification,
and permanent-session construction occur as one transactional Rust compilation without scalar
Python ontology expansion or a serialized private ontology IR. Scalar Python and scalar-wire
native paths remain complete compatibility paths.

No work package may claim a speedup using a smaller semantic workload, warmed cache on
only one side, omitted answers, relaxed timeout, or different ontology revision.

## 9. Global definition of done

A 1.0 release is permitted only when all of the following are true:

1. Every in-scope OWL 2 DL construct and reasoning service has an owning implementation
   and tests in both backends.
2. All applicable approved W3C Direct Semantics tests pass; every exclusion is tied to
   an invalid/out-of-scope test category, never a convenience skip.
3. The upstream quick, heavy, structural, tableau, and relevant OWL WG behaviors have
   been mapped; all in-scope fixtures pass or have accepted deviations.
4. Generated differential campaigns reach the published case/seed targets with zero
   unexplained semantic mismatch.
5. Forced-Python and forced-native runs pass the same public semantic suite with exact
   canonical results.
6. Sanitizers, Miri-compatible focused checks where feasible, property tests, leak
   checks, type checking, linting, documentation builds, and import-boundary checks are
   green.
7. Compiler-free installation and the complete wheel matrix pass in clean containers.
8. Performance and memory gates pass on the controlled runner with stored raw results.
9. No production code, package metadata, wheel, or sdist contains or invokes Java.
10. `reference-scope.md`, the deviation ledger, licenses, notices, API docs, and
    benchmark manifests match the shipped source.
11. CPython 3.10 and 3.12 pass standalone and already-parsed core view/provider workflows;
    compatible views are identity-preserved with zero reparse/public-model copy and bounded
    overlay/composite/native transfer behavior.
12. `deviations.md` LIC-001 is closed by an owner/legal-reviewed licensing/provenance/source
    strategy; while it is open, release is prohibited regardless of other gates.
13. The successor encoded-native compiler, when advertised, passes exact compiler-manifest and
    reasoning parity plus the no-materialization, copy, RSS, end-to-end, and consumer gates in
    `native-structural-ingestion.md`; capability presence alone is not a performance claim.

Passing only a profile subset, only deterministic ontologies, only TBox reasoning, or
only one backend is not completion.

## 10. Development rules for parallel agents

- Contracts and normalized IR land before components that exchange them.
- Rule-family agents implement handlers against the state protocols; they do not all
  edit one central saturation loop.
- Each work package owns narrowly listed paths. Shared facade/manifest edits are made
  by the integration owner or coordinated explicitly.
- Native work begins only after the corresponding Python contract tests and golden
  state transitions are stable, but can then proceed in parallel with higher-level
  Python services.
- Tests may use temporary adapters for an unmerged dependency only when the adapter is
  test-local and validates the exact published protocol. Production stubs are banned.
- A pull request must state the upstream classes/methods examined, semantic choices,
  tests run in both backend modes, performance impact, and any deviation proposal.
- Work-package completion does not permit marking skipped dependencies as complete.
