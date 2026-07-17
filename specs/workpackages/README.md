# Agent work packages

Each work package is sized for one focused branch/PR and has one primary owner. The
machine-readable dependency/ownership source of truth is
[`manifest.toml`](manifest.toml); CI must eventually validate these briefs against it.

## Working rules

1. Claim one ready package. Do not begin while a listed dependency is incomplete.
2. Name branches `wp/<lowercase-id>-<short-title>` and mention the work-package ID in
   commits/PRs.
3. Read all listed normative sections and pinned upstream classes before editing.
4. Modify only owned paths. Changes to a shared path require explicit coordination with
   its current/integration owner and must be called out in the PR.
5. Do not merge placeholder implementations, hard-coded oracle answers, unconditional
   skips, fake benchmarks, or fallbacks that ignore a mandatory construct.
6. Tests must assert semantics/invariants, not only execution or snapshot churn.
7. A native package starts only from stable Python contract/transition fixtures and may
   not callback to Python for missing semantic behavior.
8. Finish with focused tests, all dependency tests, type/lint/import-boundary checks,
   and the acceptance evidence listed in the brief.

## Global definition of done for a package

- All deliverables and acceptance criteria in its brief are complete.
- Public/internal interfaces match the normative specs and carry type/doc contracts.
- Public OWL/document/view values are exact pyowl-core types; no work package creates a
  consumer-local structural model/parser.
- Error, cancellation, deterministic ordering, limits, and malformed-input paths have
  tests where relevant.
- New external material has provenance/license records.
- No existing passing test is weakened, skipped, or converted to an approximate
  comparison.
- Python/native work includes exact parity fixtures for the component.
- Performance-sensitive work records a before/after benchmark or explains why the
  package establishes semantics only.
- The PR lists pinned HermiT paths/methods examined and any proposed deviation.

Package completion is not product completion; [`../verification.md`](../verification.md)
and the master 1.0 gates still apply.

## Dependency graph

```text
WP00
├── WP01 ─┬─ WP02
│         ├─ WP04 ─┐
│         ├─ WP05 ─┼─ WP06 ─┐
│         ├─ WP07  │        │
│         └─ WP08 ─┼─ WP11  ├─ WP09 ─ WP10 ─┐
│                  └─ WPR0 ─┼─ WPR1 ────────┼─ WPR2
│                           └─ WPR3          │
└── WP03                                    │
                                            ├─ WP12 ─ WP13 ─ WP14 ─ WP15 ─ WP16
                                            │            └──────────────┐
                                            └───────────────────────────┼─ WPR4
                                                                         │
                                                WP16 + WPR4 ─ WPP0 ─ WP17
```

For exact edges, use the manifest; the diagram compresses multi-parent dependencies.

## Parallel waves

| Wave | Ready packages after prior waves |
|---:|---|
| 0 | WP00 scaffold/reference/build spike |
| 1 | WP01 pyowl-core/contracts boundary; WP03 oracle/conformance inventory |
| 2 | WP04 normalization; WP05 roles; WP07 datatypes; WP08 Python state |
| 3 | WP02 snapshot input/profile; WP06 clausification; WP11 blocking; WPR0 Rust wire/state |
| 4 | WP09 Python hyperresolution/branching; WPR3 Rust roles/datatypes |
| 5 | WP10 Python merge/existentials/NI; WPR1 Rust hyperresolution/branching |
| 6 | WP12 Python tableau integration; WPR2 Rust merge/existentials/blocking |
| 7 | WP13 consistency/satisfiability/entailment services |
| 8 | WP14 classification |
| 9 | WP15 realization |
| 10 | WP16 facade/lifecycle/updates; WPR4 Rust full-session/services integration |
| 11 | WPP0 wheel/sdist release matrix |
| 12 | WP17 final conformance, performance, documentation, and release audit |

An agent can pick any ready package in a wave. Multiple packages in one wave should not
share owned production paths.

## Package index

| ID | Brief | Outcome |
|---|---|---|
| WP00 | [`WP00-scaffold-reference.md`](WP00-scaffold-reference.md) | Reproducible project skeleton, source pin, CI, packaging proof |
| WP01 | [`WP01-contracts-model.md`](WP01-contracts-model.md) | pyowl-core adoption/re-exports plus private reasoner contracts/IDs/results/errors |
| WP02 | [`WP02-input-profile.md`](WP02-input-profile.md) | Snapshot/provider ingestion, strict imports, OWL 2 DL validation |
| WP03 | [`WP03-oracle-conformance.md`](WP03-oracle-conformance.md) | Java oracle/goldens and licensed W3C/upstream inventory |
| WP04 | [`WP04-normalization.md`](WP04-normalization.md) | Deterministic NNF/axiom normalization and definitions |
| WP05 | [`WP05-roles.md`](WP05-roles.md) | Role hierarchy, simplicity/regularity, NFAs, built-ins |
| WP06 | [`WP06-clausification.md`](WP06-clausification.md) | Complete compiled ontology/query/delta IR |
| WP07 | [`WP07-datatypes.md`](WP07-datatypes.md) | Complete pure-Python OWL 2 datatype subsystem |
| WP08 | [`WP08-python-state.md`](WP08-python-state.md) | Python nodes, extension stores, indexes, trail, dependencies |
| WP09 | [`WP09-python-hyperresolution.md`](WP09-python-hyperresolution.md) | Python joins, deltas, disjunctions, clashes, backjumping |
| WP10 | [`WP10-python-existentials-ni.md`](WP10-python-existentials-ni.md) | Python merging, cardinalities, witnesses, NI rule |
| WP11 | [`WP11-blocking.md`](WP11-blocking.md) | Python single/pairwise/anywhere/validated blocking |
| WP12 | [`WP12-python-tableau.md`](WP12-python-tableau.md) | Complete Python satisfiability session and scheduler |
| WP13 | [`WP13-entailment-services.md`](WP13-entailment-services.md) | Consistency, satisfiability, subsumption, all axiom entailment |
| WP14 | [`WP14-classification.md`](WP14-classification.md) | Class/object/data-property classification |
| WP15 | [`WP15-realization.md`](WP15-realization.md) | Types, instances, same-as, object/data property answers |
| WP16 | [`WP16-api-updates.md`](WP16-api-updates.md) | Stable facade, dispatch, lifecycle, precompute, buffered updates |
| WPR0 | [`WPR0-rust-wire-state.md`](WPR0-rust-wire-state.md) | PyO3 handshake/wire plus safe Rust state kernel |
| WPR1 | [`WPR1-rust-hyperresolution.md`](WPR1-rust-hyperresolution.md) | Native joins, deltas, branching, rollback |
| WPR2 | [`WPR2-rust-existentials-blocking.md`](WPR2-rust-existentials-blocking.md) | Native merge, cardinality, NI, existential, blocking semantics |
| WPR3 | [`WPR3-rust-roles-datatypes.md`](WPR3-rust-roles-datatypes.md) | Native role automata and datatype constraints |
| WPR4 | [`WPR4-rust-services.md`](WPR4-rust-services.md) | Complete native session, classification, realization, adapter |
| WPP0 | [`WPP0-packaging.md`](WPP0-packaging.md) | Same-version native/pure wheels and compiler-free sdist matrix |
| WP17 | [`WP17-release-integration.md`](WP17-release-integration.md) | Exact full-system gates, benchmark targets, docs, release audit |

## Shared-path ownership

`pyproject.toml`, `setup.py`, `Cargo.toml`, top-level README, public `__init__.py`, backend
dispatcher, work-package manifest, and release workflows are shared. WP00 creates their
initial forms, WP16 owns the final public facade/dispatcher, WPP0 owns final build and
release changes, and WP17 may make only reviewed integration corrections. Other agents
must coordinate changes rather than opportunistically editing them.
