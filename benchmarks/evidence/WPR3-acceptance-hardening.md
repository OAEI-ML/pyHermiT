# WPR3 acceptance hardening: criteria 3, 4, and 6

This tranche audits the remaining acceptance surface without changing the solver,
scheduler, tableau, session, rules, Python adapter, or public native exports.  The
measurements below were captured on 2026-07-18 on Darwin x86-64 with rustc/cargo 1.97.1
and Python 3.12.3.

## Acceptance audit

| Criterion | Audited result |
|---|---|
| 3. Bounded role languages and consequences match Python | The existing shared fixture already exhausts all words of length 0–2 and samples longer words over a generated legal hierarchy.  Its 7,980 per-automaton outcomes remain sufficient for NFA-language parity.  The missing aggregate propagation path is now covered by 665 additional consequence vectors produced by `RoleAxiomGraph.accepts`, including top/bottom hooks. |
| 4. Hostile lengths/integers/regex/XML/date inputs are bounded and cancellable | Existing value, primitive-range, XSD-regex, and range-wire tests cover canonical decoding, arbitrary-precision inputs, payload/text/binary ceilings, regex parser/DFA/state/transition/memory limits, date-time partial-order isolation, XML canonical identities, and cancellation.  This tranche adds overlong/dangling role-word execution plus public mixed-range DNF-growth and cancellation checks.  The crate continues to forbid `unsafe`; these paths use no locale or network API. |
| 6. Sanitizer/fuzz/leak/audit and stored performance gates pass | Dependency/advisory audit evidence and stored role, regex, component-solver, and now mixed-range Criterion baselines are present.  The full sanitizer, fuzz, Miri-suitable, and leak/reference campaigns are release-CI gates and were not available or executed in this local tranche.  Criterion 6 therefore remains open; unit tests and a short host-local benchmark are not a substitute for those campaigns or for a portable regression threshold. |

## Deterministic differential scope

The role fixture generator stores seed `0x57505233`.  It builds 12 NFAs from the
production Python role graph, evaluates 665 deterministic words per automaton (all 157
words of length 0–2 plus the unique results of 512 seeded length 3–6 draws), and stores:

- 7,980 authoritative Python NFA outcomes; and
- 665 authoritative `RoleAxiomGraph.accepts` component-consequence vectors.

The latter exercises the native `accepted_components` scan directly and includes all
191 corpus words containing the bottom role, for which production Python returns every
component without materializing bottom transitions.

The mixed-range algebra test stores seed `0xA17EBA5E20260718` and uses the existing
production-Python range-wire oracle.  A fixed 64-bit LCG chooses 512 expressions from
eight intersection/complement shapes over the 17 supported mixed ranges.  Rust compares
each result against Boolean combinations of Python's 35 literal-membership outcomes:
17,920 generated differential checks.  It additionally checks every base range against
its exact complement, double-complement cardinality, and all 595 double-complement
membership points.  A separate hostile case proves that a two-atom complement stops at
`max_dnf_clauses` and that public algebra cancellation is observed.

Reproduction and artifact checks:

```text
PYTHONPATH=src:../pyOWLCore/src python3 \
  tools/roles/build_native_fixture.py --check
PYTHONPATH=src:../pyOWLCore/src python3 \
  native/src/datatypes/range_wire_oracle.py --check

tests/data/roles/wpr3-role-automata-v1.json
  SHA-256 1714c76a42d1857e88801b4bc15eaa3c081e42efdce909888dbd885112da13cc
native/src/datatypes/range_wire_oracle_v1.json
  SHA-256 ecfe33c93efac2bd7264996359d400af0ab4ae031ab8717b4edd36e2226bd94e
```

## Mixed-range component baseline

`datatype_kernel` now measures the full 18-root canonical model decode and range 12,
the named five-value numeric/string union.  Membership probes the string arm; exact
cardinality crosses both arms; witness generation excludes numeric identities 0–3 to
force the remaining mixed-family member.

Command:

```text
cargo bench --manifest-path native/Cargo.toml --no-default-features \
  --bench datatype_kernel -- datatype_mixed_range \
  --warm-up-time 1 --measurement-time 2 --sample-size 10
```

| Workload | Optimized time interval |
|---|---:|
| decode canonical model, 18 roots | 725.95–777.63 µs |
| compile named numeric/string range | 12.754–13.772 µs |
| contains mixed string member | 72.537–77.335 ns |
| exact mixed finite cardinality | 24.718–26.219 µs |
| witness after four numeric exclusions | 37.983–42.024 µs |

These are reproducible host-local characterization numbers, not cross-machine release
thresholds.  They establish the missing stored baseline and name stable Criterion paths
for a later controlled regression gate.

## Verification

```text
cargo fmt --manifest-path native/Cargo.toml -- --check
cargo test --manifest-path native/Cargo.toml --lib --no-default-features
cargo clippy --manifest-path native/Cargo.toml --all-targets \
  --no-default-features -- -D warnings
cargo bench --manifest-path native/Cargo.toml --no-default-features \
  --bench datatype_kernel --no-run
python3 -m py_compile \
  tools/roles/build_native_fixture.py \
  native/src/datatypes/range_wire_oracle.py
PYTHONPATH=.:src:../pyOWLCore/src .reference/venv312/bin/pytest -q \
  tests/unit/roles/test_native_fixture.py
```

All commands passed in the final worktree.  The full native library suite reported 158
passed tests, including nine range-wire tests and eight role-runtime tests; the Python
fixture-reproducibility test reported one pass.
