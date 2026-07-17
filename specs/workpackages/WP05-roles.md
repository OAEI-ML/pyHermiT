# WP05 — Role hierarchy, regularity, and automata

**Goal**: implement the single private compiled object/data property model used by profile
validation, clausification, and both backends.

## Read first

| What | Where |
|---|---|
| Role processing contract | `normalization-clausification.md` §3 |
| OWL global role restrictions | `ontology-model.md` §5.2 and W3C Structural §11 |
| Java behavior | pinned `ObjectPropertyInclusionManager.java`, `BuiltInPropertyManager.java`, `graph/Graph.java` |
| Classification needs | `reasoning-services.md` §§6–7 |

## Deliverables

- Forward/inverse canonical object roles, data-property hierarchy, SCC/equivalence,
  subrole closure, and deterministic graph algorithms.
- Simple/non-simple propagation and detailed regularity violation reports reusable by
  WP02 without duplicating the algorithm.
- Role NFA construction for regular chains/transitivity/inverses with stable state IDs,
  no unsafe determinization blowup, reachability cleanup, and provenance.
- Exact top/bottom object/data property representation and nonmaterializing built-in
  hooks consumed by WP06/backends.
- Slow bounded word-language oracle and randomized hierarchy/automata tests.

## Depends on

WP01. Coordinate the narrow validation hook with WP02; WP05 owns the algorithm.

## Acceptance criteria

1. Legal regular role hierarchies and all global-restriction counterexamples match W3C
   and pinned HermiT behavior.
2. Inverse/equivalent/SCC/simple-role results are deterministic and internally
   consistent for every source insertion order.
3. For generated bounded alphabets/words, each NFA accepts exactly the chains implying
   its target role according to the slow closure oracle.
4. Transitivity, overlapping chain prefixes, inverse chains, cycles, top/bottom roles,
   and empty hierarchies have focused tests.
5. No NFA determinization/minimization is introduced without measured need and exact
   language parity tests.
6. `roles` imports only core structural types and private contracts/graph primitives, never
   tableau/backends; it does not duplicate a public ontology/property model.
