# WPR1 evidence — Rust hyperresolution and branching

Date: 2026-07-17

## Implemented native boundary

- Validated Rust rule/predicate/term records cover every compiled predicate kind,
  exact object/data sorts, canonical atom bytes, reciprocal opposites, range
  restriction, and stable clause/join ordering.
- Join plans implement the same deterministic semi-naive OLD/TOTAL partition as
  WP09. Predicate/position indexes avoid full extension scans; the independent
  exhaustive Rust evaluator remains available for bounded differential testing.
- The coarse `RuleEngine` initializes reflexive equalities and unconditional rules,
  advances complete immutable delta generations, deduplicates dependency-distinct
  substitutions, dispatches every ground-head family, and saturates without any
  per-fact or per-rule PyO3 call.
- Ground disjunctions are canonical and support satisfied, duplicate, unit, empty,
  and nondeterministic cases. Branch checkpoints implement learning on/off,
  alternative advance, exhaustion, and dependency-directed nonchronological
  backjumping.
- Join, match, cancellation, and branch failures reset the complete tableau to its
  operation root. Predicate and argument-position indexes are rebuilt exactly by
  checkpoint restoration and node merges.

The implementation contains no unsafe code and has no Java, JNI, JPype, or ROBOT
runtime path. Pinned Java HermiT behavior remains a development-only reference.

## Differential evidence

`tools/hyperresolution/run_wpr1_differential.py` verifies the registered SHA-256
of the shared `trace-v1.json` contract, executes the Python WP09 trace consumer,
executes the Rust semi-naive and branch transition cases, and then runs 32 generated
Rust indexed-versus-naive states. It is intentionally offline and selects the Python
interpreter used by PyO3 explicitly.
The differential gate passed unchanged with the CPython 3.10 and 3.12 reference
interpreters.

```text
python tools/hyperresolution/run_wpr1_differential.py \
  --python .reference/venv312/bin/python
```

The native unit suite also covers constants, repeated variables, equality with
unbound domains, symmetric inequality, ordering guards, exact dependency-bit order,
all predicate signatures, unconditional rules, reflexive equality, concrete-role
inequality consequences, partial match rollback, disjunction support strengthening,
cancellation after a branch mutation, and stale-handle/index invariants.

## Verification and performance probes

```text
cargo fmt --manifest-path native/Cargo.toml --all --check
cargo test --locked --offline --no-default-features --all-targets \
  --manifest-path native/Cargo.toml
cargo clippy --locked --offline --no-default-features --all-targets \
  --manifest-path native/Cargo.toml -- -D warnings
cargo bench --locked --offline --no-default-features \
  --manifest-path native/Cargo.toml --bench rule_kernel
```

The all-target test gate runs 38 unit/property tests, doc tests, and five benchmark
harness probes. Criterion targets measure dependency union, indexed 512-row delta
throughput, and branch advance/rollback; the existing state-kernel targets retain
index construction and checkpoint rollback baselines. Performance claims remain
local and reproducible rather than being inferred from debug-test timings.

The complete available repository suite passed on CPython 3.10 and 3.12 with
675 tests plus 4 subtests on each interpreter. The one excluded module is the
pre-existing Hypothesis trail test whose declared optional dependency is absent
from both offline reference environments.

Rust 1.97.1 release-profile Criterion quick samples on the development host:

- `wpr1_dependency_union_8`: 247.66–257.62 ns
- `wpr1_indexed_delta_512`: 8.8764–8.9508 ms
- `wpr1_branch_advance_rollback`: 22.189–22.635 µs
