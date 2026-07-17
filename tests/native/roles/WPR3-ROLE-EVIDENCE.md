# WPR3 role-automaton evidence

This is the independently committable role-language half of WPR3. Datatype values,
ranges, and component solving remain separate WPR3 work and are not claimed here.

## Runtime boundary

- `native/src/roles` owns validated, stable epsilon NFAs and never imports PyO3.
- Construction retains Python's state numbers, removes only duplicate transitions/final
  states, rejects dangling states/roles and non-accepting graphs, and never determinizes.
- Streaming bit-set cursors perform epsilon closure and labelled steps without rebuilding
  an automaton per role edge.
- `RoleRuntime` validates the complete inverse involution, implements source-order reversal
  for inverse chains, and represents top/bottom semantics as hooks rather than materialized
  relations.
- Aggregate state, transition, word-length, memory, and automaton bounds are checked before
  unsafe growth. Long validation/closure/scan paths poll a Python-independent control trait;
  the production cancellation handle implements that trait without callbacks.
- The crate continues to forbid `unsafe`.

## Python/Rust differential

`tools/roles/build_native_fixture.py` builds a fixed legal hierarchy covering simple
subroles, inverse-generated languages, transitivity, left recursion, right recursion,
and overlapping prefixes. The authoritative Python NFA evaluates 665 deterministic words
per automaton (all length 0–2 words plus 512 seeded length 3–6 words).

The committed fixture contains 12 roles, 12 automata, and 7,980 component/word outcomes.
Python 3.10 and 3.12 regenerate it byte-for-byte. Rust decodes the same JSON and matches
every result.

Observed gates on 2026-07-17:

- Python 3.10: `test_native_fixture.py` + `test_automata.py`: 24 passed in 46.28 s.
- Python 3.12: the same slice: 24 passed in 36.89 s.
- Rust focused role tests: 8 passed, including all 7,980 shared outcomes and
  cross-automaton cursor rejection; the full native crate is 97/97.
- `cargo check --all-targets --no-default-features`: pass.
- `cargo clippy --all-targets --no-default-features -- -D warnings`: pass.

## Quick component profile

Criterion release quick mode, native-safe implementation:

| Probe | Time interval | Throughput interval |
|---|---:|---:|
| transitive word, 1 edge | 589.79–603.98 ns | 1.656–1.696 M edges/s |
| transitive word, 8 edges | 2.648–2.739 µs | 2.921–3.021 M edges/s |
| transitive word, 64 edges | 22.053–22.129 µs | 2.892–2.902 M edges/s |
| transitive word, 512 edges | 164.64–167.63 µs | 3.054–3.110 M edges/s |
| epsilon fan-out, 8 branches | 0.984–1.040 µs | 7.695–8.132 M branches/s |
| epsilon fan-out, 64 branches | 2.872–2.918 µs | 21.933–22.284 M branches/s |
| epsilon fan-out, 512 branches | 13.051–13.520 µs | 37.871–39.231 M branches/s |

These figures are local quick-mode characterization, not cross-machine release thresholds.
They establish linear word scaling and bounded epsilon-fan-out behavior for later WPR3
profiles.
