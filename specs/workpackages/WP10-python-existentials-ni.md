# WP10 — Python merging, cardinalities, existentials, and nominal introduction

**Goal**: implement the node-creating/equality rules that complete OWL 2 DL model
construction and its termination-critical nominal interaction.

## Read first

| What | Where |
|---|---|
| Existential/max-cardinality/NI rules | `hypertableau.md` §§6–8 |
| Merge/prune/rollback invariants | `tableau-state.md` §§2, 5–6 |
| Java behavior | pinned `MergingManager`, `ExistentialExpansionManager`, `NominalIntroductionManager`, `existentials/*` |
| Formal NI rule | Hypertableau paper nominal-introduction sections |

## Deliverables

- Deterministic merge orientation, assertion/support copying, inequality/negative clash
  checks, descendant pruning, rescheduling, and exact unmerge rollback.
- Satisfaction/counting of canonical pairwise-distinct successors and qualified
  min/max/exact cardinality consequences.
- Creation-order expansion default plus optional individual-reuse strategy behind the
  same interface and on/off parity tests.
- Object/data witness creation, role direction/filler/core/inequality facts, and
  processed-obligation trail state.
- Full annotated-equality buffer and NI root/key/level/create/reuse/merge algorithm.
- Ports of upstream `MergeTest`, `NIRuleTest`, reuse/core cases, plus generated traces.

## Depends on

WP09.

## Acceptance criteria

1. Merges of named/tree/NI nodes, ancestors/siblings, incoming/outgoing/self edges, and
   explicit inequalities preserve all facts/dependencies and roll back exactly.
2. Cardinality counts use canonical distinct representatives, re-evaluate after merge,
   and handle roles/inverses/qualifiers/data nodes correctly.
3. Cyclic existential, reuse on/off, bottom/top filler/role, and pairwise inequality
   tests yield exact semantic results without duplicate unbounded work.
4. Every formal NI side condition and upstream NI shape, including pre/post merge and
   rollback, has a focused test; annotated equality is never treated as eager ordinary
   equality.
5. Strategy alternatives alter only performance/witnesses, never public results.
6. State-transition traces are deterministic and replayable by WPR2.

