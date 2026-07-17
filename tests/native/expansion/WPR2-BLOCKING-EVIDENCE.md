# WPR2 native blocking performance evidence

This report records the first bounded Criterion evidence for the Rust blocking
kernel. It is a reproducible development-machine profile, not a portable latency
guarantee or a comparison with Python/Java reasoners.

## Run identity

- UTC timestamp: `2026-07-17T21:05:27Z`
- Runtime base revision: `c617132552145097dd4cdd943533f859e5f6c171`
- Host: macOS 26.5.2 (`25F84`), x86_64 Darwin; CPU brand access was denied by
  the sandbox and is intentionally not inferred
- Toolchain: `rustc 1.97.1 (8bab26f4f 2026-07-14)`, crate MSRV `1.83`
- Python selected for PyO3 linking: Homebrew CPython 3.12.3
- Criterion: 0.5.1, release profile, `--quick`; setup cloning and fixture
  construction occur outside timed sections

Reproduction command:

```text
PYO3_PYTHON=/usr/local/bin/python3 cargo bench --bench blocking_kernel --no-default-features --offline -- --quick
```

`--no-default-features` makes the local benchmark executable link to the selected
Python runtime; the measured blocking code and fake state contain no Python or
Java calls.

## Semantic gates

The harness checks these conditions before Criterion begins measurement. The run
would abort instead of publishing timings if any gate failed.

| Area | Gate exercised | Result |
|---|---|---|
| Projection/signature | 512 pairwise-eligible tree nodes produce 512 signatures from a generation-safe projection containing a cyclic peer-role graph | Pass |
| Cache lookup | All 512 unique, preloaded canonical signatures are hits | Pass |
| Cache promotion | A completed satisfiable model with no nominal/additional/query-local hazard inserts and retains all 512 unique signatures | Pass |
| Incremental parity | Dirty incremental and forced-full managers produce identical canonical snapshots and state digests | Pass |
| Invalidation frontier | A relevant mutation on the final 1,024-node fixture child reports creation ID `1025` as the earliest recomputation frontier | Pass |
| Validated acceptance | At least one provisional block is checked, the pass succeeds, and `ready_for_sat` becomes true | Pass |
| Validated repair | The first invalid block is the only invalidated block; its requested fact becomes core and its pending node is rescheduled through the transactional mutation API | Pass |
| 5k anywhere/cyclic | The projection visits exactly 5,002 records (root, parent, and 5,000 children), uses no more than 5,000 candidate checks, and agrees with the full-recompute invariant oracle | Pass |

The 5k fixture uses pairwise anywhere blocking, inverse parent edges, 64 repeating
concept buckets, and a role edge from every child to the next child with the final
edge returning to the first. “Cyclic” therefore describes the ontology role graph;
the tableau parent relation remains a valid tree.

## Quick-run measurements

The interval and middle estimate below are Criterion's reported quick-run values.
Throughput counts the named fixture elements, not every fact or allocation.

| Probe | Reported time interval | Middle estimate | Middle throughput |
|---|---:|---:|---:|
| Projection, 512 | 4.0975–4.9176 ms | 4.2616 ms | 120.14 Kelem/s |
| Pairwise signatures, 512 | 1.3867–1.6998 ms | 1.6372 ms | 312.73 Kelem/s |
| Cache lookup hits, 512 | 591.35–601.84 µs | 593.45 µs | 862.76 Kelem/s |
| Sound cache promotion, 512 | 1.5813–1.7195 ms | 1.6089 ms | 318.22 Kelem/s |
| Clean incremental compute, 1,024 | 8.4090–8.6487 ms | 8.6008 ms | 119.06 Kelem/s |
| Dirty incremental compute, 1,024 | 24.501–29.029 ms | 28.124 ms | 36.411 Kelem/s |
| Dirty forced-full compute, 1,024 | 22.187–22.451 ms | 22.399 ms | 45.717 Kelem/s |
| Validated accept pass, 256 | 4.1063–4.5773 ms | 4.2005 ms | 60.945 Kelem/s |
| First-block validation repair, 256 | 4.1043–4.5047 ms | 4.4246 ms | 57.858 Kelem/s |
| Pairwise anywhere cyclic, 5,000 | 124.77–134.32 ms | 132.41 ms | 37.761 Kelem/s |

## Incremental optimization follow-up

A second `--quick` slice at `2026-07-17T21:24:19Z`, based on
`6633b1d7c93574120139790b5156f13e224f7cd3` plus the then-uncommitted blocking
optimization, measured the same 1,024-element fixture after the manager began
retaining its blocker index and reusing the unchanged prefix. Exhaustive
full-recompute comparison remains available through `check_invariants` and the
randomized parity lane, but it no longer executes inside the production hot
path.

| Probe | Reported time interval | Middle estimate | Point-estimate comparison |
|---|---:|---:|---:|
| Clean incremental compute, 1,024 | 6.5604–6.7858 ms | 6.7407 ms | 21.6% below the initial 8.6008 ms |
| Dirty incremental compute, 1,024 | 13.909–14.572 ms | 14.042 ms | 50.1% below the initial 28.124 ms |
| Dirty forced-full compute, 1,024 | 16.547–17.392 ms | 16.716 ms | dirty incremental 16.0% lower |

Criterion's quick comparison reported `p = 0.10` for the dirty incremental/full
changes, so these point estimates establish a promising local follow-up rather
than a statistically stable release threshold. A focused regression test also
asserts that invalidating the last of 128 children visits one recomputed node,
while the forced oracle visits all 129 projected nodes, with identical canonical
assignments.

## Interpretation and open performance work

- Projection and canonical signature construction now have isolated baselines,
  as do cache hit and sound-promotion operations.
- The clean incremental lane is a same-digest fast path. It still rebuilds the
  read-only projection before comparing the digest, so it is not a constant-time
  no-op.
- The initial dirty lane was about 25.6% slower than forced full recomputation
  because it recorded a frontier but recomputed every assignment and invoked a
  second full oracle in the hot path. The follow-up implements genuine suffix
  recomputation and records a 16.0% lower point estimate than forced full, while
  retaining exact semantic parity. The quick sample is not a release claim.
- The 5k cyclic/anywhere run demonstrates bounded, effectively linear candidate
  selection for this repeated-signature fixture, but its 132.41 ms middle value
  is only an initial local baseline. It is not evidence for all large-ontology
  shapes.
- No prior stored blocking baseline or numeric regression budget existed in the
  repository. These values establish evidence for a future stable-machine lane;
  they do not by themselves satisfy a cross-revision performance threshold.

For a release gate, rerun without `--quick` on pinned hardware, retain Criterion's
machine-readable baseline, and compare at least the dirty incremental and 5k
probes across revisions.
