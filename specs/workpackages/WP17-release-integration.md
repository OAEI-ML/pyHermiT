# WP17 — Final conformance, performance, documentation, and release audit

**Goal**: prove the assembled package meets the full, exact product contract and leave
reproducible user/developer evidence for a 1.0 decision.

## Read first

| What | Where |
|---|---|
| Global 1.0 definition | `SPEC.md` §§2–3, 7–10 |
| Exact release gates | `verification.md` complete |
| Benchmarks/targets | `performance.md` complete |
| Provenance/deviations/licenses | `deviations.md`; `reference-scope.md` |
| All completed briefs | this index and implementation PR evidence |

## Deliverables

- Complete constructor/operation/interaction coverage matrix and exact forced
  Python/native/auto/verify release reports.
- Licensed W3C 350-check lane, all in-scope upstream/golden cases, generated/metamorphic
  release volumes, Java differential sample, sanitizer/fuzz/leak/determinism campaigns.
- Licensed/hash-pinned real and generated benchmark corpus, dedicated-runner Java/
  Python/native baselines, frozen `targets.toml`, raw statistical/memory/counter data,
  profiles and accepted-tradeoff records.
- User docs: install/fallback/backend diagnostics, pyowl-core standalone loading and
  Exact-OM/shared snapshot/overlay/composite/provider use, every public service,
  semantics/directness/grouping, updates, timeouts/concurrency, errors, scope/exclusions,
  version diagnostics, and performance methodology.
- Developer architecture/IR/calculus/native/testing/provenance docs, README and NOTICE,
  changelog/deviation report, artifact no-Java/license audit.
- Final integration fixes coordinated with owning agents; no gate weakening.

## Depends on

WP16, WPR4, and WPP0, plus the transitive completion of every package.

## Acceptance criteria

1. All master `SPEC.md` global definition-of-done items pass with linked raw
   evidence; no mandatory feature or backend is marked partial/skipped/unknown.
2. All applicable 350 W3C checks finish with correct logical answers; zero unexplained
   HermiT/backend/generated/metamorphic mismatch or determinism failure remains.
3. Release fuzz/sanitizer/leak/concurrency/cancellation and complete wheel/compiler-free
   matrices pass; built artifacts contain no Java or reference runner.
4. Dedicated performance gates and frozen Java-relative targets pass with identical
   result hashes; regressions/tradeoffs are explicit and approved.
5. Every external artifact/dependency has provenance/license/notice and every intentional
   HermiT mismatch has an accepted deviation; otherwise release is blocked.
6. A new user can install pure/native paths and reproduce documented core examples;
   a new agent can trace every subsystem to its spec/upstream/tests without oral lore.
7. Counting parser/provider, identity/lifetime, allocation/RSS, overlay, composite, and FFI
   tests prove zero reparse/public-model copies and the bounded native copy budget.
8. LIC-001 is owner/legal-review closed with audited SPDX/headers/notices/provenance/source
   obligations, or release remains blocked without exception.
