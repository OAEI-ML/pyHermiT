# WP03 — Reference oracle and conformance inventory

**Goal**: create reviewable exact behavioral evidence while keeping Java entirely out
of the installed product and ordinary test run.

## Read first

| What | Where |
|---|---|
| Complete test/oracle policy | `verification.md` complete |
| Deviations and licensing | `deviations.md` complete |
| Observable result scope | `SPEC.md` §2; `reasoning-services.md` |
| Upstream suites | pinned `src/test`, `known-test-failures.txt`, checked-in test report |
| PyLogMap precedent | its `specs/verification.md` and work-package index (structure only; do not copy approximate gates) |

## Deliverables

- Hash-pinned reference manifest and an opt-in, sandboxable Java HermiT request/JSONL
  runner under `tools/reference`; no runtime imports or automatic downloads.
- Versioned request/result schema and canonicalizers for booleans, errors, typed IRIs,
  hierarchies, same-as nodes, inverse properties, literals, and blank nodes.
- Machine inventory of all 186 pinned test files/598 static methods, in-scope/excluded
  fate, and the 266-case/350-check W3C export with verified SHA-256/counts.
- Provenance/license manifest and an acquisition decision for each external corpus; no
  fixture is copied while redistribution rights are unresolved.
- W3C manifest executor independent of AGPL Java harness code.
- Initial reviewed goldens for empty/built-in/error/API shapes and scripts that semantic-
  diff regeneration rather than overwrite.

## Depends on

WP00. Integration with WP01/WP02 values happens later through WP13; this package's JSON
schema must remain language-neutral.

## Acceptance criteria

1. Oracle output records full reference/JVM/OWLAPI/config/input/generator identity and
   distinguishes logical answers, timeout, resource failure, and errors.
2. Repeating an oracle request yields identical normalized output despite Java set
   order/generated internal names.
3. Ordinary tests pass with Java absent and network disabled; wheel/sdist inclusion
   tests exclude reference code/artifacts.
4. Counts and `all.rdf` hash match `verification.md`; known failures are observations,
   not passing expectations.
5. Core cases hidden in `OWLLinkTest` are retained while transport behavior is excluded;
   Rules/Datalog/description-graph extras are inventoried, not ported.
6. Every vendored/fetch-only/generated artifact has an explicit provenance decision.

