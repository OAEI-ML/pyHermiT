# WPR2 native existential/cardinality evidence

This report records the first bounded runtime-adapter and Criterion evidence for
native existential expansion. It is a development-machine profile, not a
portable latency guarantee or a Java/Python comparison.

## Run identity

- UTC date: `2026-07-17`
- Base revision: `0408071c` plus the then-uncommitted existential adapter
- Host: x86_64 Darwin, macOS 26.5.2; crate MSRV `1.83`
- Toolchain: `rustc 1.97.1 (8bab26f4f 2026-07-14)`
- Criterion 0.5.1, release profile, `--quick`; fixture construction is outside
  the timed section

Reproduction:

```text
PYO3_PYTHON=/usr/local/bin/python3.12 cargo bench \
  --manifest-path native/Cargo.toml --bench rule_kernel \
  --locked --offline --no-default-features -- wpr2_existential --quick
```

The native crate links to the selected CPython for its extension boundary, but
the measured expansion, tableau, rule dispatch, and rollback operations contain
no Python or Java calls.

## Semantic gates

- All 89 native unit/generated tests pass. The existential subset covers 15
  standalone algorithm cases, 512 generated distinctness graphs, 192 generated
  object-satisfaction states, and three real-`TableauKernel` adapter cases.
- The real creation-order case creates two TREE witnesses and the exact role,
  filler, and pairwise-inequality facts, then consumes the pending obligation.
- The real individual-reuse case creates an NI candidate, advances its branch on
  clash, rolls the NI/reuse map back, creates a fresh TREE witness, then propagates
  exhaustion with exact branch support.
- A cache-derived block with `blocker=None` in `TableauKernel` is still observed
  by existential scheduling through `BlockingManager::is_blocked`.
- Strict all-target Clippy, rustfmt, state invariants, cancellation/resource
  rollback, and full blocking recomputation parity pass.

## Quick-run measurements

| Creation-order probe | Criterion interval | Middle estimate |
|---|---:|---:|
| One object witness | 29.592–30.974 µs | 29.868 µs |
| Eight object witnesses | 170.53–177.95 µs | 176.47 µs |
| Sixty-four object witnesses | 7.1003–7.1969 ms | 7.1197 ms |

The 64-witness case deliberately materializes all 2,016 pairwise inequality
consequences, so its work is quadratic in the required cardinality by semantics,
not merely in bookkeeping. These values establish local baselines only. A pinned
release machine should rerun non-quick samples and store Criterion output before
enforcing a numeric regression budget.

## Remaining boundary

`NativeDatatypeExpansion` is the WPR3 no-callback seam for semantic datatype
range satisfaction and fixed-value difference. Until WPR3 joins, the runtime
adapter uses `AssertedOnlyDatatypes`: explicit data-range and inequality rows are
fully honored, while no additional datatype consequence is invented. The
standalone WPR2 algorithm already covers unary/n-ary data witness behavior and
generated datatype-oracle cases without a Python callback.
