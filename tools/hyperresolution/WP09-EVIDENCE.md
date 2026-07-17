# WP09 evidence — Python hyperresolution, clashes, and branching

Date: 2026-07-17

## Implemented calculus boundary

- Every compiled clause has one stable semi-naive plan per extension-backed delta
  body atom. Plans use the clause join metadata, bound-position indexes, canonical
  active nodes, exact object/data sorts, constants, repeated variables, negative
  predicates, symmetric inequality, equality, and strict ordering guards.
- The indexed executor partitions earlier body positions into `OLD` and later
  positions into `TOTAL`, so each match with one or more current-generation rows is
  emitted once. A deliberately exhaustive substitution evaluator is retained as an
  independent small-state oracle.
- Ground heads dispatch assertions, roles, equality/inequality, object/data minimum
  cardinality obligations, annotated equality, disjunctions, and empty heads. The
  dispatcher canonicalizes merged nodes while retaining merge-path dependencies and
  implements HermiT's positive/negative data-role value-inequality consequence.
- Ground disjunctions are canonical, duplicate-free, stably ordered, immediately
  reduced when satisfied/refuted/unit/empty, and deduplicated across derivations.
- Branch transitions retain exact dependency bitsets, learn failed-choice supports,
  backjump nonchronologically, propagate exhausted choices, and provide a
  chronological learning-disabled oracle. Cancellation and resource-limit failures
  recover to the operation root.

The implementation is pure Python and imports or invokes no Java/JNI/JPype code.
Pinned HermiT `HyperresolutionManager`, `DLClauseEvaluator`, `GroundDisjunction`, and
`ClashManager` were used only as development behavior references at commit
`37ec30aced32ac81ebecc5e33fad255ddefcb4c3`.

## Differential and transition evidence

The focused suite contains 24 tests covering:

- generated indexed-versus-naive equality across 16 seeded ontologies and across
  multiple delta generations;
- shared variables, constants, named guards, strict ordering, object and data keys,
  functional roles, inactive rows, and wrong sorts;
- every supported head family, immediate positive/negative clashes, concrete
  data-role inequalities, and canonicalization dependency retention;
- duplicate, satisfied, unit, empty, and annotated-equality disjunction behavior;
- learning on/off SAT and UNSAT agreement, chronological search, a backjump over two
  irrelevant levels, and exhausted-choice propagation; and
- cancellation after both join and branch mutations plus match resource rollback.

`tests/data/hyperresolution/trace-v1.json` is the canonical language-neutral WP09/WPR1
fixture. It exercises a semi-naive chain and exact branch advance/exhaustion state
transitions. Its SHA-256 is
`e1b31962360bbafa8a134ca67d70d7653dfc98e07192f7b95223b4e05a51aea5` and it is
registered in `tests/data/PROVENANCE.toml` as project-authored LGPL-3.0-or-later data.

## Verification

| Gate | CPython 3.10.11 | CPython 3.12.3 |
|---|---:|---:|
| WP09 focused suite | 24 passed | 24 passed |
| repository suite available locally | 577 passed + 4 subtests | 577 passed + 4 subtests |
| Ruff Python 3.10 target | clean | same source tree |
| strict MyPy, six WP09 runtime modules | clean | same source tree |

The repository runs exclude only
`tests/unit/tableau_state/test_dependencies_trail.py`, whose declared Hypothesis
development dependency is absent from both pre-existing offline reference
environments. No WP09 test is skipped.

## Reproducible throughput probe

Command (run independently with each reference interpreter):

```text
PYTHONPATH=.:src:../pyOWLCore/src <python> \
  benchmarks/bench_wp09_hyperresolution.py \
  --facts 1000 --depth 4 --samples 3 --cancellation-timeout-ms 1.0
```

The script SHA-256 is
`689ba07a5dbd467fd606d9a1d6499bfb7f277a661e2ed7e744e698fd61b6b455`.
It compiles one two-premise indexed join followed by a four-rule unary chain, then
creates 1,000 named roots with both premises. Compilation is outside the timed
region; every sample creates fresh state, initializes, saturates, checks invariants,
and hashes the complete active extension state.

| Measurement | CPython 3.10.11 | CPython 3.12.3 |
|---|---:|---:|
| saturated state | 10,000 rows; 7 generations | same |
| state SHA-256 | `0956c34c...81057` | identical |
| median initialization | 0.2955 s | 0.2548 s |
| median saturation | 1.1628 s | 0.8735 s |
| saturated rows/second | 8,599.8 | 11,447.7 |
| traced peak Python allocation | 15,656,548 bytes | 15,811,460 bytes |

These measurements establish a deterministic pure-Python fallback baseline, not a
Java-relative speed claim. WPR1 owns the coarse-grained Rust implementation of the
same trace and semantics for large-ontology production throughput.
