# WP14 — Class and property classification

**Goal**: compute exact transitively reduced class, object-property, and data-property
hierarchies with HermiT's optimized deterministic/quasi-order approach.

## Read first

| What | Where |
|---|---|
| Hierarchy/API semantics | `contracts.md` §6.2; `reasoning-services.md` §§5–7 |
| Performance/verification | `performance.md` §§1–3, 6; `verification.md` §§4–7 |
| Java behavior | pinned `hierarchy/DeterministicClassification`, `QuasiOrderClassification*`, `Hierarchy*`, `RoleElementManager` |
| Algorithm paper | HermiT “A Novel Approach to Ontology Classification” |

## Deliverables

- Immutable hierarchy builder, SCC/equivalence collapse, top/bottom, transitive
  reduction, direct/all navigation, declared-unused/fresh/complex-query handling.
- Deterministic classifier using one safe premodel/model read per element as applicable.
- Quasi-order known/possible subsumption graphs, model pruning, targeted checks, and
  force-quasi-order configuration.
- Object/data-property reduction/classification including inverses, equivalence,
  top/bottom, nonasserted semantic relations, domains/ranges/disjointness queries.
- Slow all-pairs tiny classifier and exact Java/Python/generated differential suite.

## Depends on

WP13.

## Acceptance criteria

1. Every declared entity occurs exactly once; class bottom equals all unsatisfiable
   classes; direct edges are the exact quotient-DAG transitive reduction.
2. Deterministic, quasi-order, and slow all-pairs modes produce identical canonical
   hierarchies on their common generated domain.
3. Multiple unsatisfiable classes, SCCs, isolated declarations, top/bottom, complex
   query expressions, inverse/equivalent roles, and nontrivial property classification
   match HermiT goldens.
4. No property hierarchy is merely asserted closure when semantic tests imply more.
5. Timeout/cancellation does not publish/mark a partial hierarchy; repeat/precompute
   cache use is exact and measurable.
6. Classification counters/benchmarks establish baselines for WPR4 without weakening
   semantic tests.

