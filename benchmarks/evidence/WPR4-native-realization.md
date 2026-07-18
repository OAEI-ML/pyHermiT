# WPR4 native realization evidence

Date: 2026-07-18

Scope: Python-independent construction and operation-local caching of canonical
`RealizationIds` from one read-only, completed, consistent tableau model. This tranche is a
result service kernel; it does not claim the remaining completed-model adapter, composite native
tableau, PyO3 session method, or `full_reasoner` handshake.

## Contract implemented

- `CompletedModelAccess` borrows named/equality records, compiled answer domains, and entailed
  direct-type, object, data, and different-from facts without a Python callback or a second
  ontology parse.
- Named individuals are partitioned by completed-model equality keys. Group members and groups
  are sorted canonically, every name occurs exactly once, and facts stated through any equal alias
  are collapsed into the same answer rows.
- Direct-type rows contain sorted unique class-node IDs. `object_targets` rows are explicitly
  `(subject_same_as_group_id, property_id, target_same_as_group_ids)`: target values are group IDs,
  not individual symbol IDs. Data targets retain every entailed finite source-literal ID, including
  distinct lexical aliases of one data value. Different-from pairs are canonical group-ID pairs.
- Anonymous source individuals and internal tableau witnesses may affect the completed model but
  are excluded from every public answer. A purported named reference absent from the compiled
  named domain fails closed rather than being treated as anonymous.
- Class-node, object/data-property, source-literal, equality-partition, and cross-row references
  are validated. Same-and-different contradictions and duplicate domain records fail as native
  invariants.
- Input order and duplicate entailed facts do not affect output. Ordered maps/sets provide stable
  rows and targets without hash-iteration dependence.
- Named/domain/fact/result-row/result-value/memory bounds use checked counters. Long scans poll
  `OperationControl`; cancellation, timeout, or resource failure returns no result.
- `RealizationCache` uses model fingerprint plus revision, owner-stamped operation tokens, and a
  private staged entry. Lookups expose only committed data; promotion is one assignment after the
  builder's final cancellation/resource checkpoint; rollback preserves the previous committed
  result.
- `RealizationIds` fields are private after validation. Borrowed access is immutable through an
  `Arc`. Consuming `into_wire_result()` moves the already canonical vectors directly into
  `result_wire::RealizationWireResult`; the borrowed helper performs only structural cloning and
  no semantic remapping.

## Verification

Focused command:

```text
cargo test --locked --no-default-features --lib services::realization_tests
```

Result: 9/9 passed. Coverage includes exact equality grouping and propagation, group-ID object
targets, retained source literals, anonymous/internal exclusion, hostile references and domains,
deterministic input permutations, cancellation and resource limits, cache hit/promotion/rollback,
foreign/stale ownership, failed and cancelled replacement isolation, and result-wire encoding.
The consuming wire-conversion test also proves that a same-as vector retains its allocation.

The large-ABox test builds 40,000 named singleton groups, 40,000 direct-type facts, and 39,999
object facts. It completed in 0.52 seconds in the focused debug run on the development host and
asserts work accounting exactly equals the exposed fact count; it creates no pairwise equality
candidate matrix.

Strict lint command:

```text
cargo clippy --locked --no-default-features --all-targets -- -D warnings
```

Result: passed.

Unified native command:

```text
cargo test --locked --no-default-features
```

Result: 189 unit tests plus 6 operation-control integration tests passed; 0 failed; doc tests
passed.

## Required integration

The composite tableau adapter must expose a view only after saturation, datatype checking, clash
resolution, and blocking validation have reached a consistent model-found boundary. Its facts must
already include property hierarchy, inverses, equality substitution, and the direct-type policy;
the builder intentionally does not infer missing entailments or directness. It must map internal
nodes to `Anonymous`/`Internal`, expose the finite source-literal candidate domain, and advance the
cache revision whenever permanent semantics change.

The native session can then call `realize_cached`, convert the result to the existing compact wire
record, and let the Python adapter map validated compiled IDs. Until that adapter and the rest of
WPR4 pass complete Python/native differential tests, `full_reasoner` and automatic native
selection must remain disabled.
