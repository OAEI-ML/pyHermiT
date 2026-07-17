# WP13 — Consistency, satisfiability, and entailment services

**Goal**: expose complete backend-neutral logical reductions for consistency,
class-expression satisfiability/subsumption, and every OWL 2 logical axiom.

## Read first

| What | Where |
|---|---|
| Public basic services/reductions/errors | `reasoning-services.md` §§2–4, 9 |
| Observable compatibility | `SPEC.md` §2 |
| Exact oracle normalization/corpus | `verification.md` §§2–6 |
| Java behavior | pinned `EntailmentChecker.java`; `Reasoner.isConsistent/isSatisfiable/isEntailed/getTableau` |
| Direct Semantics | axiom satisfaction and inference-problem tables |

## Deliverables

- Service layer for consistency, satisfiability, subclass, defined/fresh entity, single
  axiom and materialized-set entailment using compiled isolated queries/batches.
- Exhaustive axiom-type reduction registry including n-ary class/property axioms,
  characteristics/chains, datatype definitions, keys, anonymous-individual rolling-up,
  positive/negative assertions, same/different individuals.
- Sound built-in/cache shortcuts with forced slow-reduction differential mode.
- Inconsistent ontology, fresh entity, timeout/interruption, and unsupported nonlogical
  behavior matching stable exception policy.
- Exact Python-vs-Java goldens and applicable 350-check W3C execution integration.
- Tests over standalone sources and identical existing snapshot/overlay/composite/provider
  views, proving zero reparse and unchanged exact core result values.

## Depends on

WP02, WP03, WP06, and WP12.

## Acceptance criteria

1. Every in-scope logical axiom class has positive, negative, open-world, built-in, and
   high-risk interaction tests; registry exhaustiveness is checked by type inventory.
2. `entails_all` is exact conjunction, snapshots one-shot iterables, treats empty as
   true, and never returns a partial result.
3. Anonymous individuals, keys' named guard, negative assertions, datatype definitions,
   property chains, and n-ary pairwise conditions match Direct Semantics/HermiT.
4. Fast/cache and forced reduction paths agree on generated cases; query IR never
   mutates permanent state or exposes internal names.
5. All applicable pinned W3C checks produce correct logical outcomes in Python mode;
   no timeout/error is recoded as false.
6. Exception category and result canonicalization match committed oracle records.
7. Query operands/results are exact core values and no query mutates/materializes the
   captured public ontology view.
