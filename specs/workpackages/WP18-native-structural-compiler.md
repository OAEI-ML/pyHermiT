# WP18 — Native structural compiler and zero-materialization handoff

**Goal:** compile a retained pyowl-core encoded structural view directly into the complete Rust
HermiT session, eliminating ontology-sized Python validation/normalization/clausification and the
private input-wire round trip on the optimized path.

**Status:** specified, not implemented. **Depends on:** WP17, WPR4, and a frozen candidate from
pyowl-core WP17. The pyELK and projector successor packages may run in parallel because each owns
its private consumer IR.

## Read first

| What | Where |
|---|---|
| Successor contract | `native-structural-ingestion.md` complete |
| Input/profile semantics | `ontology-model.md` complete |
| Normalization and clauses | `normalization-clausification.md` complete |
| Native session and safety | `native-backend.md` complete |
| Performance/verification | `performance.md`; `verification.md` |
| Shared bulk schema | pyowl-core `native-ontology-redesign.md`, `indexes-views.md`, WP17 ledger/handoff |

## Owned paths

- the new public-core encoded-view adapter and compilation dispatch under `src/pyhermit/`;
- native structural decoding, profile validation, normalization, roles, clausification, and direct
  session-construction modules;
- the native binding/stub and ingestion diagnostics needed for the coarse buffer call;
- test-only compiler manifests/comparators and focused scalar/encoded differential suites;
- encoded ingestion, hostile descriptor, owner-lifetime, overlay/composite, and consumer tests;
- successor performance/evidence reports and directly affected architecture/API/provenance docs;
  and
- coordinated core range, compiler/native schema, cache, build, and release metadata changes.

The existing scalar compiler remains the Python semantic fallback. This WP does not change public
reasoning semantics, overwrite frozen oracle fixtures, or place reasoner records in pyowl-core.

## Deliverables

1. Freeze and validate the supported encoded schema/descriptor/segment contract and owner
   lifetime.
2. Implement transactional Rust OWL 2 DL validation, normalization, role preprocessing,
   clausification, symbol/provenance construction, and direct permanent-session publication.
3. Preserve `scalar-python` and `scalar-wire-native` paths and add explicit, versioned compilation
   diagnostics without semantic backend leakage.
4. Add canonical compiler manifests and exact scalar/encoded comparisons for every constructor,
   validation rule, normalized/role/clause section, failure type, limit, and cancellation point.
5. Run the entire forced-native and verify suites, including the deep satisfiable-superclass-chain
   above an unsatisfiable class, generated permutations, direct/mmap/overlay/composite cases, and
   malformed/hostile encoded inputs.
6. Prove buffer lifetime, close/fork/thread/interpreter/panic safety and run Rust fuzz,
   sanitizer, clippy, formatting, and Miri-compatible focused checks.
7. Extend benchmarks to view-to-session and view-to-result time, phase profiles, copy/object/FFI/
   parser/wire counters, RSS, result hashes, medium/large biomedical corpora, and same-machine Java.
8. Update version ranges, compiler/cache/provenance schemas, changelog/migration/API docs,
   artifacts, SBOM/license inventories, and the Exact/OAEI compatibility matrix.

## Acceptance criteria

1. Scalar and encoded compiler manifests and every public result/error are exact for the complete
   conformance, differential, generated, and consumer matrices.
2. Existing compatible core views reach an encoded-native session with zero parser, resolver,
   core-wire, scalar-axiom, Python normalized/clause/compiled ontology, private ontology-wire,
   per-axiom FFI, or base-flattening counter delta.
3. Direct/mmap input creates no ontology-sized staging copy. Reported exceptional copies are
   bounded, justified, and included in RSS/time gates.
4. Invalid encoded data, invalid OWL 2 DL input, cancellation, limits, and panic publish no session
   or cache and preserve the scalar path's public error contract.
5. All gates in `../native-structural-ingestion.md` and `../performance.md` pass on the controlled
   runner. Tiny local or smoke measurements are explicitly insufficient.
6. Pure installations remain complete on Python 3.10+, and native artifacts pass the existing
   ABI/wheel/reproducibility/security/license/no-Java gates.
7. Exact-OM and OAEI observe their original view/composite identities, identical coherence/
   hierarchy results, and the selected compilation path without importing pyHermiT internals.

## Handoff

Publish exact core package/API/adapter/encoded-schema support, pyHermiT compiler/native schemas,
canonical compiler/result digests, benchmark raw data, known limitations, and the consumer
revisions tested. Older compatible scalar-only core providers continue to work through the
documented fallback path.
