# Verification and conformance

pyHermiT uses exact semantic gates. Approximate precision/recall, Jaccard similarity,
or “close enough” hierarchy results are never valid for a reasoner.

Primary sources:

- [OWL 2 Conformance](https://www.w3.org/TR/owl2-conformance/)
- [OWL 2 Structural Specification](https://www.w3.org/TR/owl2-syntax/)
- [OWL 2 Direct Semantics](https://www.w3.org/TR/owl2-direct-semantics/)
- [OWL 2 RDF Mapping](https://www.w3.org/TR/owl2-mapping-to-rdf/)
- [Pinned HermiT tests](https://github.com/phillord/hermit-reasoner/tree/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/test)
- [Pinned known failures](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/known-test-failures.txt)

## 1. Test layers

| Layer | Purpose | Java needed? | Release blocking? |
|---|---|---:|---:|
| Unit/invariant | Core identity/input adapters, each rewrite, rule, state transition, datatype, hierarchy operation | No | Yes |
| W3C conformance | Normative OWL 2 DL document/semantic results | No after licensed corpus is acquired | Yes |
| Committed HermiT goldens | Exact observable pinned-reference behavior | No | Yes |
| Live Java differential | Detect golden generator/reference drift | Development/scheduled only | Yes before a reference update/release |
| Python/native parity | Same IR, API, answer, exception, and lifecycle | No | Yes |
| Generative/metamorphic | Broad interactions and invariant preservation | No, except sampled live differentials | Yes |
| Packaging | Wheels, sdist, compiler-free fallback, artifact contents | No | Yes |
| Performance/safety | Time, memory, cancellation, sanitizers, leaks | Java only for comparison lane | Yes |

Every test has a stable case ID, owning feature(s), source/provenance, expected outcome,
and backend applicability. A machine-generated coverage matrix fails CI when a
mandatory constructor, axiom family, reasoning operation, or high-risk interaction has
no positive and negative case.

## 2. Pinned corpus inventory

At reference commit `37ec30aced32ac81ebecc5e33fad255ddefcb4c3`:

- `src/test/resources/org/semanticweb/HermiT/owl_wg_tests/ontologies/all.rdf`
  contains 266 Approved + Direct + DL test-case resources;
- those resources expand to 350 separately executable semantic checks:
  169 consistency, 97 inconsistency, 75 positive entailment, and 9 negative
  entailment checks;
- the pinned `all.rdf` SHA-256 is
  `a703d36b774f55f14c0758cf20f2bdd635677045f7ba55053199660c10d6fefc`;
- `src/test` contains 186 tracked files and 598 statically declared Java test methods
  before expanding parameterized W3C cases.

These numbers are an inventory of the pinned export, not a claim about a mutable
current online W3C repository. A fixture acquisition script verifies counts and hashes.
The release report records both test-case resources and expanded semantic checks. The
350 Approved Direct-DL checks are the immutable normative minimum, not a ceiling:
every other in-scope upstream regression or non-rejected OWL WG case is inventoried and
run as compatibility evidence with its original status recorded. A newer mutable W3C
corpus changes the release gate only through a reviewed reference/spec update.

### 2.1 Upstream family treatment

| Upstream family | Treatment |
|---|---|
| `reasoner` semantic/API/datatype/classification tests | Port observable intent and/or generate black-box goldens |
| `structural` normalization/clausification | Port semantic intent and IR invariants; canonicalize generated names |
| `tableau` tuple/dependency/merge/NI/blocking tests | Re-express as backend-neutral state/rule tests |
| `owl_wg_tests` | Reimplement manifest execution; do not copy AGPL harness code |
| `RulesTest`, `DatalogEngineTest`, description-graph tests | Inventory as excluded extensions |
| `OWLLinkTest` | Extract its core import/update/classification/realization cases; exclude only OWLLink transport/integration behavior |
| Protege/CLI/debugger tests | Inventory as excluded integrations |

The upstream structural suite was disabled in its quick suite because parse order could
change generated concept names. pyHermiT fixes deterministic names and compares
canonical semantics/IR, not raw Java clause strings. Public parsing/canonical OWL identity
is tested in pyowl-core; this suite tests the core-view-to-HermiT compiler boundary.

### 2.2 Known failures

Historical HermiT timeouts, OOMs, and failing blocking-validation tests are stored as
reference observations. They are not expected passes, expected logical answers, or
permission to skip. `TIMEOUT`, `RESOURCE_LIMIT`, `ERROR`, `SAT`, and `UNSAT` remain
distinct. GA requires the agreed W3C release lane to produce a logical answer for all
350 applicable checks within its documented budget.

## 3. Development-only Java oracle

`tools/reference/` contains an opt-in, reproducible runner. It fetches/verifies the
pinned source or image, builds outside the package tree, and accepts a versioned request:

```json
{
  "schema": 1,
  "ontology_sha256": "...",
  "ontology_format": "functional",
  "imports": {"iri": {"sha256": "...", "bytes_ref": "..."}},
  "operation": "class_hierarchy",
  "arguments": {},
  "configuration": {},
  "timeout_seconds": 300,
  "memory_bytes": 2147483648
}
```

It emits JSONL with request/input hashes, HermiT commit/Maven version, OWLAPI/JVM
versions, exact configuration, raw outcome, normalized outcome, duration, peak RSS,
stdout/stderr hashes, and generator version. Java exception text is diagnostic only.

The runner executes in a network-disabled, memory/CPU/time-limited process after inputs
are staged. It never resolves arbitrary imports from the network. Ordinary CI consumes
reviewed goldens and cannot require Java. Wheels/sdists exclude the runner, source,
JARs, JVM artifacts, and goldens not needed for normal tests.

Golden regeneration is an explicit command and never happens during a test. Changes
produce a semantic diff for review. A reference-update PR must run old and new oracle
versions over the complete corpus.

The `normalization` operation is a component oracle: after loading the staged import closure it
runs pinned `OWLNormalization` into `OWLAxioms`, without constructing `Reasoner` or invoking
clausification. Its typed value contains concept/data disjunction arrays, ordered simple and
complex property inclusions, disjoint/characteristic property families, facts, keys, and defined
datatypes. SWRL rules are rejected as excluded scope. A broad project-authored golden covers all
families; a second atomic golden has no generated definitions and supports exact WP04 overlap.

## 4. Normalized comparison

Normalize representation only where it has no semantic/public meaning:

- booleans compare exactly; timeout/error/unknown are never coerced to `False`;
- IRIs retain exact Unicode code points and are sorted only for set comparison;
- a hierarchy is the unordered set of nonempty equivalence nodes plus direct quotient
  DAG edges, with each node an unordered set of typed full IRIs;
- all hierarchy results compare transitive closures when `direct=False` and exact
  transitive-reduction neighbors when `direct=True`;
- inverse properties use `(named_property_iri, inverse: bool)`;
- individual results compare same-as groups or flattened names according to the
  configured node policy;
- blank nodes are alpha-canonicalized within each document and standardized apart
  across imports;
- HermiT `internal:` entities in structural-normalization output are graph-alpha-canonicalized
  within their entity sort; canonicalization preserves distinct symbols and fails at a bounded
  ambiguity limit rather than using Java allocation names;
- literals compare their observable source token `(lexical, datatype IRI, normalized
  language component)`, their data-domain identity token, and—where a facet/range
  operation is under test—the separate comparison/order result; returned lexical
  aliases are not collapsed and comparison-equal nonidentical values are not merged;
- mappings/sets are order independent; and
- errors compare stable public categories/codes, not messages or stack traces.

Important HermiT compatibility: data-property values may include distinct source
literals such as integer lexical aliases or a value typed as different numeric
datatypes even when their data values compare equal. The facade must preserve those
observable literals while equality/cardinality uses data-value identity and facet
reasoning uses the distinct comparison relation.

Generated internal symbols, anonymous witnesses, node IDs, branch order, timings, and
models are excluded from cross-backend parity. Focused component tests compare
canonical logical snapshots and rule consequences at prescribed abstract checkpoints;
they may test one backend's private schedule internally, but may not require Python and
Rust to share IDs, allocation order, checkpoints, or an identical transition schedule.

## 5. Exact backend matrix

Every deterministic semantic test is parameterized over:

```text
PYHERMIT_BACKEND=python
PYHERMIT_BACKEND=native   # on native-capable lanes; absence is a failure here
PYHERMIT_BACKEND=auto
PYHERMIT_BACKEND=verify   # focused/nightly due to cost
```

Release blocking requirements:

1. identical normalized answers and public immutable return types;
2. identical equivalence/same-as grouping and `direct` behavior;
3. identical observable literal lexical forms;
4. identical public exception class/code for invalid/state/abort conditions;
5. no internal IDs or backend-specific ordering exposed;
6. forced Python remains fully functional with native installed;
7. `auto` selects once before a session and reports the selected backend;
8. no native semantic failure silently falls back; and
9. cancellation/resource errors do not corrupt a later query or reasoner.

Run native parity on Linux x86-64/aarch64, macOS arm64/x86-64 while supported by CI,
and Windows x86-64/arm64. Unsupported platforms, subinterpreters, and unaudited
free-threaded CPython run the complete Python suite and packaging fallback tests.

## 6. Constructor and operation coverage

The generated matrix enumerates every item in `ontology-model.md`, every datatype and
facet, every normalized predicate/rule handler, and every public operation in
`reasoning-services.md`. Each semantic construct has:

- a positive/satisfiable/entailed case;
- a negative/nonentailed case;
- an inconsistent or clash case where meaningful;
- a case combined with at least one high-risk interacting feature;
- parse cases in every required syntax; and
- Python/native/HermiT or W3C oracle status.

Mandatory interaction rows include open-world/no-UNA behavior, equality/inequality,
keys and named guards, top/bottom entities, vacuous universals, inverse/transitive/role
chains, nominals plus cardinality/blocking, negative property assertions, multiple
unsatisfiable classes, legal punning, anonymous imports, cyclic imports, fresh entities,
inconsistent queries, direct/all results, updates, interruption, and timeout.

## 7. Generative tests

### 7.1 Grammar generator

The generator produces both valid OWL 2 DL ontologies and deliberately invalid
ontologies. Valid generation tracks entity typing, reserved terms, role simplicity,
chain regularity, datatype-definition acyclicity, legal facets, and anonymous-individual
forest/placement restrictions. Invalid generation records the exact rule deliberately
violated and avoids accidental unrelated violations when possible.

Cases have reproducible seeds and shrink structurally while preserving validity or the
target violation. Every unexplained mismatch is minimized and committed as a permanent
regression case before fixing it.

### 7.2 Metamorphic relations

Required relations include:

- bijective renaming of nonreserved IRIs renames answers correspondingly;
- axiom/import-list permutation and structural duplicate removal preserve answers;
- annotation add/remove preserves logical answers;
- equivalent RDF/XML, Functional Syntax, and OWL/XML agree;
- imports flattening preserves semantics while standardizing blank nodes apart;
- passing a loaded snapshot/provider/no-op overlay instead of its source path preserves
  semantics and invokes no parser;
- `compose_views(source, target, bridge)` equals the logical union for reasoning while
  retaining component provenance and without concatenating component collections;
- adding fresh declarations/annotations conservatively extends only the signature;
- adding logical axioms is monotonic for entailment and cannot turn inconsistency into
  consistency;
- adding an already entailed axiom changes no semantic answer;
- reciprocal subclass axioms equal class equivalence;
- n-ary disjointness equals pairwise disjointness;
- disjoint union equals equivalence-to-union plus pairwise disjointness;
- exact cardinality equals minimum plus maximum;
- has-value equals some-values-from a singleton nominal;
- double class/data complement elimination;
- transitivity equals the valid corresponding self-chain inclusion;
- inverse-property reversal preserves relationship answers;
- types, instances, and assertion entailment agree;
- type/instance results respect subclass closure;
- forward and inverse object-value queries agree;
- same-as is an equivalence relation and supports substitution;
- lexical aliases agree in datatype constraints while preserving returned literals;
  and
- top/bottom identities hold.

### 7.3 Volume gates

- Pull request: at least 1,000 valid and 1,000 invalid generated cases per available
  backend, with bounded sizes suitable for fast shrinking.
- Nightly: at least 50,000 backend/metamorphic cases and 5,000 small live-Java
  differential cases.
- Release campaign: at least 1,000,000 accumulated backend/metamorphic cases, 10,000
  live-Java differentials, and a 24-hour native sanitizer/fuzz campaign.

Seed ranges, generator version, size distribution, exclusions, and hardware are stored
in the report. Zero unexplained mismatch, crash, hang, or invariant failure is allowed.

## 8. State, lifecycle, and hostile-input testing

- Model-based state machines cover add/remove/flush/query/precompute/interrupt/dispose.
- A fresh reasoner over every committed effective core overlay is the oracle for an
  incrementally updated private backend session.
- Fault injection cancels after every mutation category and forces allocation/resource
  failures at bounded points.
- Consume the compatible pyowl-core parser/wire fuzz and conformance report as a dependency
  gate rather than duplicating its parser implementation. pyHermiT adapter/profile and FFI
  fuzzers cover malformed/incompatible providers/views, huge lengths/IDs, strict-import
  manifests, invalid profile/literal interactions, corrupt private IR, and hostile callbacks.
- Native runs under ASan/UBSan where supported, leak/reference-count checks, thread
  sanitizer on focused components, and Miri-compatible unit tests for unsafe-free core
  structures where practical.
- Rust `unsafe` is denied by default; any exception has an owning proof/test/audit.

No leak, use-after-free, overflow, double free, panic across FFI, uninitialized read,
reference-count leak, deadlock, or stale result is acceptable.

## 9. Packaging tests

Clean isolated environments verify:

- native wheels import with `native` forced and expose the matching ABI/schema;
- the pure wheel contains no extension and reasons with no compiler/Java/network;
- sdist installation succeeds with `rustc`/Cargo deliberately hidden;
- explicit require-native build fails clearly when native compilation is impossible;
- installed files contain no `.java`, `.class`, `.jar`, JNI launcher, upstream checkout,
  JVM/JPype dependency, or runtime downloader;
- metadata requires Python `>=3.10` and `pyowl-core>=0.2,<0.3`; CPython 3.10 and 3.12 test
  standalone and snapshot/overlay/composite/provider inputs with compatible core pure/native
  variants where wheels exist;
- package data, type marker/stubs, licenses, notices, and resource hashes are present;
- read-only installation/source directories work; and
- installation/uninstallation leaves no compiled artifact in source/cache paths owned
  by another environment.

## 10. Licensing and corpus provenance gate

Every non-original test/ontology has a record with origin URL, immutable revision,
SHA-256, license, required notice, local path, and modifications. HermiT is
LGPL-3.0-or-later, but its historical bundled OWL test export does not itself establish
that every upstream W3C/third-party ontology may be redistributed under that license.
W3C's current dual test-suite licensing policy does not automatically relicense an old
snapshot without the stated notice.

Therefore:

- do not copy the AGPL `owlwg-test` harness; implement the public manifest format;
- acquire W3C tests from a source with an applicable W3C Test Suite/BSD notice or keep
  a hash-verifying fetch step outside distributed artifacts until permission is clear;
- do not vendor Pizza, Wine, GALEN, DOLCE, ORE, or other ontologies until each license
  is recorded; and
- describe modified subsets as internal regression suites, not an unqualified official
  W3C conformance suite.

In addition, `deviations.md` LIC-001 is a hard release gate. The recorded decision
(owner, 2026-07-17) adopts `LGPL-3.0-or-later` under the source-guided mode and the
`LICENSE`/`COPYING`/`NOTICE.md` files now reflect it, but no publication occurs until the
remaining LIC-001 items — exact SPDX metadata, file headers, provenance inventory, and
source obligations — are executed, audited, and reviewer-signed.

## 11. Release gates

GA has zero:

- wrong or unknown outcomes on the 350 pinned applicable W3C checks;
- unexplained pinned-HermiT semantic/API mismatches;
- Python/native/auto/verify parity mismatches;
- untested mandatory constructor/operation matrix rows;
- nondeterministic canonical results across supported platforms/hash seeds;
- unresolved sanitizer, leak, panic, crash, deadlock, or post-cancellation corruption;
- packaging failures in the compiler-free/native matrices;
- missing provenance/license records;
- an open LIC-001 compliance/review gate; and
- any shared-view reparse/public-model copy, provider multi-call, eager overlay base copy, or
  composite component concatenation found by the release instrumentation.

Timeouts are allowed only in separately labeled stress/benchmark lanes. The conformance
release budget and machine are fixed before the release candidate and all 350 checks
must finish within it.
