# Native structural ingestion, validation, and clausification

Status: normative successor optimization for the implemented native reasoner. It preserves the
OWL 2 DL acceptance boundary, HermiT compatibility, public API, and complete scalar pure-Python
path while replacing ontology-sized Python preparation on the optimized path.

## 1. Objective

A native pyHermiT session SHOULD begin from the exact retained
`pyowl_core.OntologyView` already owned by the caller and compile that ontology through public
`EncodedStructuralView` buffers. The optimized path MUST NOT materialize every OWL axiom as a
Python object, construct a complete Python `NormalizedOntology`/`ClauseProgram`/
`CompiledOntology`, or serialize that private IR merely for Rust to decode it again.

Rust owns, as one fail-closed compilation transaction:

1. structural/profile scanning and OWL 2 DL global-restriction validation;
2. normalization and deterministic fresh-definition allocation;
3. role preprocessing, regularity/simplicity checks, and automata;
4. clausification, symbol tables, facts, disjunctions, datatype/nominal records, and indexes; and
5. publication of the permanent reasoning session only after all validation succeeds.

These remain pyHermiT-private semantics. Nothing reasoner-specific enters pyowl-core, and no Rust
ontology object becomes public.

## 2. Negotiation and compatibility paths

After identity-preserving core coercion, pyHermiT inspects
`CoreCapabilities.encoded_view_schemas` and requests the documented
`pyowl_core.EncodedStructuralView` through `view.view(...)`. It validates the schema/version,
model schema, scope, descriptor digest, structural fingerprint, little-endian fields, offsets,
counts, tags, segment graph, and owner lifetime before native compilation.

Three paths remain explicit:

- `scalar-python`: existing scalar profile validation, normalization, clausification, and Python
  reasoning;
- `scalar-wire`: existing Python compilation and validated native input wire, retained as
  a compatibility path; and
- `encoded-native`: public core columns/segments directly into the Rust compiler and permanent
  Rust session.

A scalar-only compatible provider continues to support every public service and backend.
`backend="native"` does not by itself require encoded ingestion. Diagnostics and provenance
report the compilation path, core encoded schema, pyHermiT compiler schema, and whether any bulk
column was copied. A malformed advertised encoded view fails before session publication and never
falls back after partial consumption.

The stable public `Reasoner.diagnostics()` path vocabulary is `scalar-python`, `scalar-wire`, and
`encoded-native`; `scalar-native` is reserved for a future semantically distinct path. The mapping
also exposes `compiler_digest`, `compiler_cache_schema_version`, `ir_schema_version`,
`implementation_version`, optional `native_abi_version`, and the shared pyELK/Exact/OAEI
`encoded_*` counter ledger. Those counters account only for structural-view compilation into the
permanent session. On current scalar paths they are contractual zero/false measurements even when
the native adapter performs a validation-only encoded preflight; they are not placeholders.

No path imports `pyowl_core._native`, relies on core arena layout, persists encoded dense IDs, or
performs per-axiom Python/Rust calls. Native compilation retains the encoded owner for the complete
borrow lifetime and may allocate the transformed HermiT IR exactly once.

## 3. Segment-aware compilation

Direct snapshots, decoded snapshots, mmap-backed snapshots, overlays, and composites are required
inputs. Overlay/composite segment manifests are traversed without concatenating base axioms or
copying the source/target closure. Canonical duplicate handling, origin roles, document-scoped
anonymous individuals, import completeness, and all fingerprints must match scalar traversal.

A compiled-session cache key includes:

```text
(core logical and structural fingerprints,
 core model schema and import/segment manifest,
 encoded-view schema and descriptor digest,
 HermiT compatibility/configuration,
 pyHermiT normalization/compiler/native schema and package versions)
```

Schema-local IDs are invalid outside their owner and cannot independently identify cache entries.
Queries and small update deltas may retain their existing typed compiler/wire path when profiling
shows ontology compilation dominates, but they cannot trigger ontology re-expansion. A later
native query compiler requires its own parity fixtures and schema decision.

## 4. Exact compiler parity

The scalar and encoded compilers expose test-only canonical manifests/digests for:

- profile-validation result and ordered stable diagnostic rule IDs;
- normalized axioms, definitions, fresh-symbol assignments, and provenance;
- role graph, simplicity/regularity classification, automata, and transition order;
- symbol tables, DL clauses, facts, ground disjunctions, datatype and nominal records;
- declared entities, taxonomy domains, source-literal round-tripping, and ontology fingerprint;
  and
- accepted limits, cancellation checkpoints, and failure category/context.

Exact digest/count equality is required before comparing reasoning results. Every current Python,
forced-native, verify, W3C, HermiT golden, generated/metamorphic, incoherent hierarchy, datatype,
nominal, role, overlay, and composite fixture runs through both compilers. The previously reported
multi-level-superclass/bottom incoherence shape remains an explicit forced-native regression.

`verify` mode compiles independently through scalar and encoded paths, compares compiler
manifests, then compares public operations. Its extra cost is intentional development evidence;
production native mode does not build a Python shadow IR.

## 5. Failure, lifetime, and resource safety

Compilation is transactional: invalid profile input, resource exhaustion, cancellation, panic,
bad buffers, or semantic compiler mismatch publishes no partial session or cache. Count-derived
allocation is checked before growth. Rust releases the GIL only while holding no Python callback;
progress events use the existing bounded event mechanism.

Direct-buffer borrowing has documented aliasing/lifetime/thread/fork/close invariants and focused
Miri-compatible, sanitizer, fuzz, interpreter-shutdown, and hostile-descriptor tests. A copied
column is permitted only when Rust ownership or alignment requires it, and its byte count is
reported. The normal retained-native/mmap path has zero ontology-sized staging copy and no Python
private-IR serialization.

## 6. Performance and memory gates

The benchmark boundary begins with an already captured core view and records separately:

1. encoded-view acquisition/validation;
2. OWL 2 DL profile validation;
3. normalization, role preprocessing, and clausification;
4. native session publication;
5. consistency, classification, realization, and representative queries; and
6. scalar materializations, parser/wire calls, copied bytes, FFI calls, allocations, RSS, and
   worker scaling.

Equivalent cold/warm states, options, timeouts, workers, input bytes/snapshot identity, semantic
digests, and result volumes are mandatory. Microbenchmarks never replace complete view-to-result
evidence.

In addition to `performance.md`, encoded-native acceptance requires:

- zero parser/resolver/core-wire/scalar-axiom/base-flattening calls for an existing compatible
  view;
- no Python `NormalizedOntology`, `ClauseProgram`, complete `CompiledOntology`, or native input
  ontology wire on the encoded-native production path;
- encoded-view validation and Python/Rust boundary time below 5% of native
  compile-plus-classification time on each designated medium/large workload;
- encoded-native view-to-session time at least 2x faster than scalar-wire by geometric
  mean, with no nontrivial workload more than 10% slower outside the noise floor;
- no more than 10% peak/incremental-RSS regression without an accepted measured time/scale
  tradeoff; and
- the existing native >=3x pure-Python medium/large target and calibrated Java-relative gates.

The optimization objective remains faster end-to-end execution than pinned Java HermiT. Until the
controlled corpus and same-machine comparison pass, documentation describes encoded compilation
as experimental and reports limitations rather than extrapolating from small fixtures.

## 7. Versions, artifacts, and consumers

The implementation records the minimum core package/API/adapter and exact encoded schema range.
It increments only pyHermiT compiler/native schemas whose meaning changes; core model or wire
versions are not changed merely because the in-process view is new. Incompatible caches rebuild
or fail explicitly.

Pure wheels and compiler-free sdists remain semantically complete on Python 3.10+. Native wheels
retain the established ABI, sanitizer, reproducibility, license, and no-Java gates. Exact-OM and
OAEI pass their existing snapshot/composite identities unchanged; they do not depend on this
private compiler or import pyHermiT internals.

## 8. Completion

Completion requires exact scalar/encoded compiler and reasoning parity, complete direct/mmap/
overlay/composite and hostile-input coverage, labelled release-scale time/RSS/copy evidence,
updated provenance/cache/docs/version ranges, and consumer conformance over the exact released
core and pyHermiT revisions. The existence of an encoded-view entry point alone is not
optimization evidence.
