# Performance and optimization

Optimization is required, but cannot weaken logical work or output. This document
defines reproducible measurements and a ratcheting policy rather than rewarding one
unrepresentative headline benchmark.

## 1. Benchmark phases

Measure separately and end-to-end:

1. pyowl-core standalone load/parse/import closure, and separately zero-reparse capture of
   an existing snapshot, overlay, composite, or provider;
2. OWL 2 DL validation;
3. canonicalization, role preprocessing, normalization, and clausification;
4. first and repeated consistency/satisfiability checks;
5. batches of varied class-expression/axiom queries;
6. class classification;
7. object- and data-property classification;
8. realization;
9. type/instance/object-value/data-value query throughput; and
10. assertion-only update/flush versus full rebuild.

Standalone end-to-end reports include core loading; shared-workflow reports begin with the
same already-loaded `OntologyView`; kernel reports begin with the same private serialized
`CompiledOntology`. Never compare Java from parsed input to pyHermiT from a warm view/IR or
vice versa without labeling both numbers. Report shared-input savings explicitly.

## 2. Workload matrix

Use licensed, hash-pinned real ontologies plus generated families. The initial suite
must span:

- empty, tiny W3C, and small regression ontologies;
- deterministic/Horn and highly nondeterministic TBoxes;
- large taxonomies and deep/wide class hierarchies;
- ABox-heavy realization/property workloads;
- cyclic existential structures requiring blocking;
- inverse roles, role chains/transitivity, and large automata;
- nominals with min/max/exact cardinalities and equality merging;
- broad ground disjunctions and backjumping;
- numeric, string-regex, temporal, finite enumeration, and mixed datatype constraints;
- keys, negative assertions, and many same-as individuals; and
- broad/deep/cyclic import closures.
- Exact-OM-style source/target/bridge `OntologyComposite` views and shallow/deep repair
  overlays with controlled delta size.

Generated families parameterize axiom count, signature size, ABox size, hierarchy
shape, chain length, automaton states, maximum cardinality, nominal count, disjunction
width, datatype restrictions, anonymous depth, and import count. Each family has at
least small/medium/large points and a fixed seed.

No third-party ontology enters the repository or automated download set until its
license/provenance record passes `verification.md`.

## 3. Metrics

Record:

- wall and CPU time;
- peak RSS and native/Python allocation count/bytes where measurable;
- cold/warm cache state and cache bytes;
- throughput and timeout rate;
- Python/Rust boundary calls, transfer bytes, and boundary time;
- core parser/provider call counts, public-model bytes copied, overlay/composite component
  bytes retained, and view-capture time;
- normalized/clause/fact counts;
- created/peak active tableau nodes and extension rows;
- rule matches, existential expansions, merges, prunes, clashes, branches/backjumps;
- blocking checks/hits/cache hits/invalidations;
- datatype components/checks and automaton work; and
- result cardinality/hash proving both sides did identical logical work.

Instrumentation uses counters compiled/configured off for production hot paths. A
benchmark result without ontology/query/config/result hashes is invalid.

## 4. Methodology

- Run on a pinned dedicated machine/VM image with recorded CPU, cores, RAM, OS, Python,
  Rust, JVM, and governor/power settings.
- Pin process affinity where supported and prevent unrelated CI load.
- Build release artifacts with the exact published flags; Java uses the pinned HermiT,
  OWLAPI, JVM flags, heap cap, and warmed JVM policy in the manifest.
- Report cold process runs separately from repeated warm-session runs.
- Use at least 3 process samples for very long workloads and 10 measured samples for
  normal workloads after a declared warmup. Store every raw sample.
- Compare medians, dispersion/confidence intervals, geometric means across workload
  groups, and peak memory. Do not select the best sample.
- Validate exact normalized result hashes before accepting timing.
- Timeouts/resource failures are results, not omitted samples.

Microbenchmarks guide profiling but never substitute for end-to-end gates.

## 5. Baselines and gates

WP-PERF first measures pinned Java and the complete Python engine on the controlled
runner and commits `benchmarks/baselines/<machine>.json`. The release owner then freezes
the Java-relative hard thresholds in `benchmarks/targets.toml`; changing a target needs
a reviewed rationale and cannot occur in the same PR as a regression.

Minimum gates before that calibration are:

- no statistically credible median regression above 10% on a `must_not_regress`
  workload versus the previous accepted native baseline;
- geometric-mean regression no worse than 5% within each workload group;
- native no more than 5% slower than pure Python on any nontrivial core workload unless
  the absolute difference is below the benchmark noise floor;
- native at least 2× faster than pure Python by geometric mean at the first native
  milestone and at least 3× for the 1.0 medium/large core suite;
- no more than 10% peak-RSS regression without a measured time/scale tradeoff accepted
  in the benchmark manifest; and
- p95 cooperative interrupt latency below 250 ms during CPU-bound benchmark phases on
  the reference machine.
- zero core parser calls and zero public structural-model copies for compatible views;
  provider called once, overlay shared memory O(delta), and no component concatenation for
  composites; and
- at most one contiguous private-IR copy at native session creation, with no per-axiom FFI.

Provisional 1.0 Java target, to be confirmed by the calibration PR:

- native end-to-end geometric-mean wall time no worse than 1.25× pinned HermiT across
  the core suite;
- no required workload worse than 2× Java unless Java itself fails/times out and the
  exception is documented as a workload-specific release decision; and
- native peak-RSS geometric mean no worse than 1.25× Java.

The optimization objective after meeting the minimum is native geometric-mean time
below Java, not merely inside the gate. Faster new baselines ratchet forward.

The pure-Python backend has no Java-speed requirement. Its designated small W3C/unit
suite must stay within a documented CI budget, and algorithmic regressions visible in
size-scaling slopes are blocking even when small absolute times pass.

## 6. Optimization order

Profile before changing architecture. Preferred order:

1. eliminate repeated parsing/canonicalization/IR conversion and Python/Rust crossings;
2. improve clause join plans and predicate/argument indexes;
3. compact extension rows, dependency sets, queues, and arena locality;
4. reduce unnecessary rule matches, witnesses, merging, and datatype rechecks;
5. improve blocking signatures/invalidation/cache hit rate;
6. batch classification/realization tests and reuse safe models/caches;
7. specialize deterministic/Horn/common datatype paths while retaining the general
   path as an exact differential oracle; and
8. introduce deterministic parallelism only after single-thread profiles and parity
   are stable.

An optimization has an on/off test mode whenever practical. Both modes must return
identical results over targeted and generated cases. New unsafe Rust is a last resort
and requires a written invariant proof, safety tests, sanitizer/Miri coverage, and
measured benefit that cannot reasonably be obtained safely.

## 7. Parallelism

Parallelism is most naturally applied across independent classification/entailment
checks or independent reasoner instances. Parallel work inside one nondeterministic
tableau is allowed only if:

- dependency/trail/branch semantics remain race-free and deterministic at the public
  boundary;
- cancellation and memory accounting cover all workers;
- no Python callback occurs while native worker locks are held;
- single-thread mode remains available for debugging and constrained hosts; and
- scaling is measured at 1, 2, 4, and available physical-core counts, including memory.

Do not oversubscribe when callers run several reasoners. Thread count is a resource
configuration with a conservative auto policy.

## 8. Regression workflow

CI runs a stable smoke subset and compares stored distributions. Nightly/release runs
the full suite. A detected regression produces phase/counter/profile diffs and is not
silenced by increasing noise tolerances. Accepted tradeoffs record:

- affected workload and exact before/after raw data;
- correctness/safety/scale benefit;
- memory/time impact;
- owner and review date; and
- a follow-up target if temporary.

Benchmark fixtures, harness, pyowl-core package/model/wire/adapter versions, consumer
compiler schemas, fingerprints, and result canonicalizer are versioned.
A harness change establishes a new side-by-side baseline rather than comparing
incompatible measurements.
