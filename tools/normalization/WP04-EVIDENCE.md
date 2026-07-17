# WP04 deterministic normalization evidence

## Implemented contract

- `AXIOM_HANDLER_TABLE` is an import-time exact match for pyowl-core's closed set of
  37 OWL axiom constructors. Unknown future constructors and non-OWL extensions fail
  loudly before structural serialization.
- Class-expression and data-range normalization implements NNF duals, double-complement
  elimination, safe built-in simplification, exact/minimum/maximum cardinality rewrites,
  and the zero-cardinality edge cases without unsigned underflow.
- Complex class/data roots are atomized with deterministic, polarity-aware definitions.
  Generated symbols are keyed by the authoritative logical fingerprint, canonical
  expression bytes, and polarity. A final collision check prevents those symbols from
  entering the declared signature.
- Immutable normalized records cover class, object-property, data-property, datatype,
  key, and ABox families. Source provenance is aggregated without affecting semantic
  identity or rule truth. The compact provenance keys are structural-axiom hashes;
  occurrence/document/span provenance remains authoritative in the retained core
  `OntologyView.origin_index` and can be joined lazily by compilation/diagnostics instead
  of being copied into every private record.
- Query normalization has a separate content-addressed namespace, can reuse permanent
  definitions, reports rebuild-requiring role/schema changes, and cannot mutate permanent
  records or symbols. Query sources are collected with a one-item lookahead, so a configured
  source limit cannot accidentally consume an unbounded iterator before failing.
- Snapshot, overlay, composite, and materialized views are consumed through the core view
  protocol directly. No parser, RDF graph, Java, tableau backend, or native backend is
  imported by the normalization package.
- Full diagnostic snapshots retain provenance and counters. Semantic snapshots/digests
  exclude provenance, declarations, and processing counters so annotation-only or
  diagnostic changes cannot fragment compilation/query caches.
- Definition expansion uses an iterative work queue. Deep legal expressions therefore do
  not leak Python `RecursionError`; configured depth limits fail with the public resource
  error, the recursive expression core is capped at its tested safe depth of 512, and
  provenance discovered after a shared nested definition is propagated to its complete
  definition dependency chain.
- Definition symbols are self-authenticating: immutable snapshots rederive their ontology or
  query namespace, kind, polarity, and expression digest, then require exactly one directional
  generated record with matching provenance. Arbitrary, missing, duplicate, orphaned, or
  cross-snapshot private definitions are rejected at construction time.
- N-ary disjoint classes use one shared normalized record rather than eagerly materializing
  every pair. Duplicate normalized operands, `owl:Thing`, and `owl:Nothing` retain their
  exact empty-class consequences; WP06 owns the linear shared/prefix clause encoding.

The behavior review is pinned to HermiT commit
`37ec30aced32ac81ebecc5e33fad255ddefcb4c3`, especially
`structural/OWLNormalization.java` and `structural/ExpressionManager.java`. The formal
semantic reference is [OWL 2 Direct Semantics](https://www.w3.org/TR/owl2-direct-semantics/).
These sources are development references only; Java is neither invoked by ordinary tests
nor imported or packaged at runtime.

## Correctness evidence

The focused suite covers:

- exact constructor-table closure and execution of all 37 handlers;
- positive/negative class and data NNF, nested complements, cardinality duals, and
  top/bottom simplification;
- annotation-free normalized logical statements with provenance retained separately;
- content-addressed definition reuse, opposite-polarity separation, collision rejection,
  query-local names, annotation-insensitive query identity, permanent-query isolation, and
  a closed safe-overlay/rebuild classification for every handler and expression constructor;
- every permutation of representative axiom collections;
- exact handler execution for all 37 axiom constructors, exact identity/provenance checks
  for 27 semantics-preserving handlers, and transformation-direction checks for complex
  class, property-domain/range, key, assertion, and datatype cases;
- linear n-ary disjointness at 100/1,000/5,000 operands, including duplicate/top/bottom
  edge cases;
- 400 nested definitions under the configured limit, a 520-deep public depth-limit error,
  and permutation-stable late provenance propagation through shared definition chains;
- snapshot/overlay/composite/materialized view equivalence;
- canonical JSON round trips and rejection of noncanonical decoded order;
- an independent exhaustive propositional finite-model oracle plus deterministic generated
  cases, extended over two-object object/data relations to cover inverse roles, nominals,
  self restrictions, object and data quantifiers/cardinalities, complex assertions, and keys;
  each case checks source satisfiability iff some interpretation of generated symbols satisfies
  the normalized output;
- configured source/record/definition/depth limits and cooperative cancellation;
- a frozen nontrivial normalization trace with 9 records, 5 definitions, and 16 expression
  steps (`818ae79befd1a7879380dd1cf9db76bebd144405a31fc45ac0f182f506f6fd64`);
  and
- a fresh-process static import gate proving no tableau, JNI/native, or JPype side effect.

The quarantined development oracle now also exposes HermiT's private `OWLAxioms`
structural-normalization holders as a typed, schema-validated JSON graph. Its committed broad
fixture populates all 13 holder families, including five concept inclusions, four data-range
inclusions, seven fact kinds, simple/complex roles, disjointness, keys, and defined datatypes.
Whole-graph canonicalization alpha-renames HermiT's parse-order-dependent `internal:` class and
datatype symbols and is tested against reordered inputs and different raw private names.

An independent atomic fixture is parsed by pyowl-core and normalized by this Python work
package; its complete projected holder graph matches the pinned-Java committed golden exactly.
For the all-13-family broad fixture, the test removes each implementation's private definition
encoding and expands its symbols into a common holder-level semantic projection. Both the
pinned-Java golden and Python output then equal the source projection. This proves coverage
without falsely requiring byte equality between HermiT's parse-order private names and this
specification's deterministic polarity-aware names. The independent finite-model oracle covers
the deliberate structural differences as a second check; observable end-to-end parity remains
a compiler/reasoner gate. Java is invoked only to explicitly regenerate development goldens;
ordinary tests read committed factual output and import no Java bridge.

## Performance evidence

The first direct implementation normalized 50,000 preconstructed, distinct atomic
`SubClassOf` axioms in **11.644 s** (4,294 axioms/s) on CPython 3.12. Profiling showed six
core canonical serializations per simple source axiom. Caching normalized record bytes,
reusing the source bytes for unchanged annotation-free axioms, and removing repeated sort-key
serialization reduced that path to one source serialization per axiom.

The final uninstrumented probe used three fresh normalization runs on the same machine and
produced exactly 50,000 records per run. The table reports the median:

| Runtime | Elapsed | Throughput |
|---|---:|---:|
| CPython 3.10.11 | 3.453 s | 14,479 axioms/s |
| CPython 3.12.3 | 2.963 s | 16,873 axioms/s |

The CPython 3.12 result is about **3.9x** the initial throughput. First computation of the
bounded incremental semantic digest for that 50,000-record result took 0.093 s on 3.10 and
0.067 s on 3.12; subsequent reads used the immutable cached 64-character digest and took
approximately one microsecond. This is a structural
normalization microbenchmark, not an end-to-end reasoning or Java-relative performance
claim. Large-ontology behavior remains bounded by explicit limits and direct one-pass input
iteration; downstream role/clause/tableau scale is measured by their owning work packages.

The disjoint-class probe produced one record and no definitions in 0.0066 s (100 operands),
0.0563 s (1,000), and 0.2284 s (5,000). This verifies the work package does not construct
the previous 4,950/499,500/12,497,500 pairwise records on this path.

## Validation matrix

The counts below are refreshed by the final clean gate before commit. Ruff covers source
and tests, strict MyPy covers the configured runtime/development source set, and
import-linter checks both architecture contracts.

| Gate | Result |
|---|---:|
| focused normalization tests, CPython 3.10.11 | 68 passed |
| focused normalization tests, CPython 3.12.3 | 68 passed |
| repository suite, CPython 3.10.11 | 259 passed + 4 subtests |
| repository suite, CPython 3.12.3 | 259 passed + 4 subtests |
| Ruff | clean |
| strict MyPy | 59 source files; clean |
| import-linter | 2 contracts kept; 0 broken |
