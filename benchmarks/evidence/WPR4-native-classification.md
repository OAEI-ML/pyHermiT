# WPR4 native classification evidence

Date: 2026-07-17

Scope: Python-independent deterministic/quasi-order hierarchy construction over canonical
compiled IDs. This tranche is a service kernel and does not claim the unfinished native tableau,
wire adapter, or `full_reasoner` handshake.

## Contract implemented

- Batched semantic subsumption checks with exact result-cardinality validation.
- Canonical equivalence partitions, subordinate-to-immediate-superior edges, and stable top/bottom
  node IDs matching `backends.protocol.HierarchyIds`.
- Memoized known/possible relations and deterministic statistics.
- A separate syntactically-complete fast path matching Python `build_hierarchy`: iterative
  Kosaraju SCC collapse, quotient construction, and exact transitive reduction with no tableau
  callback.
- Canonical-input, cancellation, semantic-work, seed-count, and memory limits fail before a
  partial result can be published.
- All graph traversals are iterative; compiled numeric ID order is the native equivalent of the
  compiler's canonical structural order.

## Targeted checks

Command:

```text
cargo test --no-default-features --lib services::tests
```

Result: 7/7 passed. Coverage includes deterministic/quasi-order parity, SCC equivalence collapse,
redundant-edge removal, malformed semantic batches, cancellation, memory/work bounds, non-extreme
top/bottom IDs, and a 10,000-node deep complete taxonomy. The deep taxonomy uses zero semantic
callbacks and the seven focused debug tests completed in 0.23 seconds on the development host.

Strict lint command:

```text
cargo clippy --no-default-features --all-targets -- -D warnings
```

Result: passed.

Unified native command:

```text
cargo test --no-default-features
```

Result: 169 unit tests + 6 operation-control integration tests passed; 0 failed; doc tests passed.

## Remaining WPR4 integration

The composite tableau must supply the batched `(child, parent)` satisfiability reductions, and the
native session/PyO3 adapter must serialize the returned IDs. Classification caches must be promoted
only after a complete operation. Until those pieces and realization are complete, the native
feature handshake must not advertise `full_reasoner` and automatic selection must remain disabled.
