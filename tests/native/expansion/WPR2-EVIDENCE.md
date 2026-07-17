# WPR2 evidence — native merging, existentials, NI, and blocking

Date: 2026-07-17

## Implemented native boundary

- Merge/copy/prune implements dependency-exact orientation, inequality clashes,
  incident-row rewrite and redispatch, child pruning, pending-existential
  transfer, fixed-data equality handling, cancellation, and exact rollback
  (`4f0abf01bae04074153c199e765819f59bbca840`).
- Annotated equalities remain queued semantic actions. Nominal introduction
  implements formal forgetting/target selection, root keys and canonical reuse,
  cardinality branches, last-choice dependency removal, advance/exhaustion,
  cancellation/resource recovery, and deterministic traces
  (`370b141eee7848650ef07398c2f922744b997938`).
- Single/pairwise and ancestor/anywhere/validated blocking implement generation-
  safe projections, stable signatures, bounded cache promotion, direct/indirect
  assignments, invalidation, validation/repair, SAT gating, and a full-recompute
  oracle (`b21d7c850f615840a800e5c25db2616756ec96ab`,
  `d2996e29d3e8a0863718ceeae493876d7a836f46`).
- Creation-order and individual-reuse expansion implement canonical object,
  unary-data, and n-ary-data satisfaction; bounded exact pairwise distinctness;
  top/bottom roles; TREE/CONCRETE/NI witnesses; role/filler/inequality
  consequences; stable deferral; reuse branching; and rollback
  (`6633b1d7c93574120139790b5156f13e224f7cd3`).
- The real runtime adapter keeps reuse maps in tableau snapshots, forwards coarse
  fact/node/branch/rule operations, preserves handle generations across rollback,
  and combines a live blocker with manager-owned cache blocking
  (`6458bc48a41e13e485a9a3a76f3257cb81027398`).

All operations remain inside Rust once entered. There is no per-fact PyO3 call,
unsafe Rust, Java, JNI, JPype, or ROBOT runtime path.

## Differential and generated evidence

| Gate | Result |
|---|---:|
| Python WP10/WP11 expansion, nominal, and blocking oracle slice on CPython 3.10 | 74 passed in 12.54 s |
| Same oracle slice on CPython 3.12 | 74 passed in 11.18 s |
| Complete native unit/generated suite | 89 passed |
| Generated distinctness graphs | 512 matched exhaustive reference |
| Generated object-satisfaction states | 192 matched reference enumeration |
| Random blocking mutation/rollback sequences | incremental and full snapshots identical |
| Real creation-order adapter | exact TREE/role/filler/inequality consequences |
| Real reuse adapter | NI rollback, fresh fallback, and exhaustion exact |
| Cache-only blocking adapter | blocked with live tableau `blocker=None` |

The native nominal suite additionally freezes forgetting, target order,
canonical owner/root reuse, pruned work, branch choice/exhaustion, and limit/
cancellation rollback. The blocking suite freezes the Python pairwise signature
trace, strategy selection, validation repair, cache safety, 5,000-node bounded
candidate work, and randomized full-oracle equality.

## Verification

```text
cargo fmt --manifest-path native/Cargo.toml --all -- --check
cargo check --locked --offline --no-default-features --all-targets \
  --manifest-path native/Cargo.toml
cargo test --locked --offline --no-default-features \
  --manifest-path native/Cargo.toml
cargo clippy --locked --offline --no-default-features --all-targets \
  --manifest-path native/Cargo.toml -- -D warnings
```

All gates pass on Rust 1.97.1. The crate declares Rust 1.83 and its locked
dependency set was previously verified on that MSRV in WPR0; a local 1.83
toolchain was not installed for this follow-up. Timed sanitizer/Miri/fuzz and
leak campaigns remain release-CI gates; the crate and Cargo lint configuration
both forbid unsafe code.

## Performance evidence

- Merge copying of 512 rows: 3.725 ms after removing a redundant nested state
  snapshot (about 8.5% below the first local sample).
- Nominal cardinality-4 first choice: 85.1 µs.
- Blocking projection/signature/cache/validation and 5,000-node cyclic-anywhere
  measurements are recorded in `WPR2-BLOCKING-EVIDENCE.md`.
- Real creation-order 1/8/64-witness measurements are recorded in
  `WPR2-EXISTENTIAL-EVIDENCE.md`.
- Genuine suffix recomputation plus removal of the production full oracle is
  committed in `040807155818ee534bfbcbfbeae8c74d4637187f`: the local quick dirty
  point estimate fell from 28.124 ms to 14.042 ms, and was 16.0% below the
  corresponding forced-full point estimate. Exact full parity remains an
  explicit invariant/property gate.

These are reproducible local baselines, not portable latency promises. The
evidence files retain intervals, fixture work scope, and statistical caveats.

## WPR2 acceptance audit

1. Merge, cardinality, existential, NI dependencies and rollback are covered by
   deterministic real-state tests plus generated/reference cases.
2. Every blocking strategy/cache mode is compared with full recomputation,
   including inverse-context, nominal eligibility, cardinality work, cyclic
   roles, validation, and rollback.
3. Validated-anywhere cannot report SAT before the current projection digest is
   accepted; rejection promotes core facts and reschedules each exposed pending
   node once.
4. Generation-safe handles, exact indexes, compound cancellation, randomized
   rollback, strict lint, bounded resource, and invariant lanes pass.
5. Ordered maps/sets and canonical snapshots prevent hash or strategy iteration
   order from changing public results.
6. Coarse runtime adapters contain no Python callback. Stored Criterion probes
   cover merge copying, NI, witnesses, signatures, cache, validation, and
   incremental versus full blocking.

The WPR3 `NativeDatatypeExpansion` seam is explicit: asserted range/inequality
rows are already exact, while nonmaterialized datatype range satisfaction and
fixed-value comparison join through the no-callback WPR3 solver. WPR2 does not
claim that later concrete-domain solver as part of this workpackage.
