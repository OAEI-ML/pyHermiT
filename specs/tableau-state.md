# Tableau state and rollback

This document owns mutable reasoning state. Logical rules are in `hypertableau.md` and
blocking-specific state is in `blocking.md`.

Pinned upstream references:

- [`tableau/Tableau.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/Tableau.java)
- [`tableau/Node.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/Node.java)
- [`tableau/ExtensionManager.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/ExtensionManager.java)
- [`tableau/ExtensionTable.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/ExtensionTable.java)
- [`tableau/TupleIndex.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/TupleIndex.java)
- [`tableau/DependencySetFactory.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/DependencySetFactory.java)
- [`tableau/MergingManager.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/MergingManager.java)

## 1. State ownership

A `TableauSession` owns all mutable state for one compiled ontology and one active
query. Nothing mutable is shared between sessions. Permanent compiled IR is borrowed
immutably. Python uses explicit objects/arrays; Rust uses arenas and integer handles.
Both expose rule handlers through equivalent internal state interfaces and enforce the
same invariants.

Every state mutation is either permanent for the query root or recorded on the current
trail so it can be undone exactly. Caches are state: if a cache entry can become stale
after merge, prune, fact addition, or backtrack, its insertion/invalidation must also be
trailed or generation-keyed.

## 2. Nodes

Logical node kinds are:

- `ROOT`: object root for a source named individual, a source anonymous individual, or
  an operation-local anonymous satisfiability witness;
- `TREE`: anonymous object witness created by an existential/min-cardinality rule;
- `NI`: root object witness used by nominal introduction; and
- `CONCRETE`: data-value variable/constant node.

Description-graph nodes are excluded. Each handle refers to an arena slot plus a
generation in debug/safe APIs so a recycled slot cannot be mistaken for an old node.

Required fields, whether stored directly or derivable in O(1):

- stable creation ID and node kind/sort;
- `is_owl_named_individual`, true only for a source/query `NamedIndividual` and never
  inferred from `ROOT`; plus the source individual ID when one exists;
- lifecycle `ACTIVE`, `MERGED`, `PRUNED`, or `RETIRED`;
- parent and tree depth for tree nodes;
- canonical merge representative and dependency set for the merge path;
- creation checkpoint;
- blocking status/blocker and blocking generation;
- unprocessed existential cursor/set; and
- nominal/cardinality metadata required by the NI rule.

`ROOT` and NI nodes are roots. Source blank nodes and query-local anonymous roots have
`is_owl_named_individual=False`. Only a true flag receives HermiT's internal named
guard and can satisfy the Direct Semantics named-individual side condition of
`HasKey`; node kind alone MUST NOT be used for keys. Concrete nodes never participate
in object-role blocking.
Following canonical representatives performs path compression only if compression is
rollback-safe; otherwise use bounded union-chain traversal.

## 3. Extension store

### 3.1 Fact rows

The store represents unique assertions:

```text
(predicate, node)                 unary concept/data-range
(predicate, node, node)           binary object/data role
(equality-or-inequality, node,node)
```

Each row carries:

- active/inactive state;
- `core` flag used by blocking/expansion;
- the minimal known dependency set (or equivalent alternatives if needed for sound
  dependency-directed backtracking);
- derivation generation/checkpoint; and
- optional diagnostic provenance excluded from hot equality/index keys.

Adding an existing row combines support safely. A later deterministic derivation may
replace a larger dependency set with a subset; it must never lose the only support that
survives a backtrack. The exact support-retention design is property-tested against a
slow multiderivation reference store.

### 3.2 Delta views

Semi-naive evaluation maintains `TOTAL`, `DELTA_OLD`, and `DELTA_NEW` logical views.
Propagation atomically advances new facts to the next generation. A clause match must
include the designated delta atom so the same all-old match is not re-evaluated forever.
Rows derived while consuming a delta are placed in the next delta, not the range
currently being iterated.

Merge/prune activity is respected by every view. Stale rows may remain physically for
rollback efficiency but no logical retrieval may return an inactive tuple or a tuple
whose arguments have invalid lifecycle without canonicalization prescribed by merge.

### 3.3 Indexes

Each predicate/argument access pattern selected by the clause compiler has an index.
Indexes map primitive keys to compact row IDs; scans over all facts in the hot loop are
forbidden unless an explicit cost model chose them for a tiny relation.

Index insertion, deactivation, canonical-node changes, and rollback are atomic with the
row store. Debug mode reconstructs indexes from active rows and compares exact content
after every randomized operation sequence.

## 4. Dependency sets

A dependency set is an immutable sorted set/bitset of branching levels supporting a
fact, equality, disjunction, or clash. The empty set is deterministic. Required
operations are union, add level, maximum level, subset, permanent/interned conversion,
and release/garbage collection if reference counted.

Invariants:

- no level exceeds the current highest created branching level when installed;
- the clash dependency set contains every nondeterministic choice necessary for that
  clash and no fabricated future level;
- a deterministic clash has an empty set and terminates without trying to backtrack;
- merging combines the equality dependency with each copied fact's support; and
- dependency interning cannot retain unbounded dead sets across independent queries.

The Python implementation starts with `frozenset[int]` or a small immutable bitset for
clarity. Rust uses a small-inline representation with a shared bitmap fallback only
after parity tests stabilize.

## 5. Branches, trail, and checkpoints

A branching point records:

- its level and choice kind;
- a checkpoint into every append-only arena/trail/queue;
- remaining ordered alternatives;
- source disjunction/merge choice and its base dependency set; and
- learned dependencies needed when advancing choices.

The single logical trail covers node creation/lifecycle, facts/support changes,
ground-disjunction queues, merges, existential marks, datatype constraints, blocking
state/cache generations, and derived caches. Component-local trails are permitted only
if one `Checkpoint` captures all of their lengths consistently.

`backtrack_to(level)`:

1. clears the clash;
2. reverses every mutation after the target checkpoint in strict reverse order;
3. truncates created nodes/disjunctions/queues and restores inactive rows/supports;
4. restores merge representatives, pruned subtrees, existential and datatype state;
5. invalidates/reverts blocking and query caches;
6. drops higher branching points and dependency-set intern entries no longer used; and
7. passes a full invariant check before the next alternative in debug/test mode.

Cancellation uses a separate operation-root checkpoint. It never masquerades as a
logical clash or chooses another branch.

## 6. Equality, merging, and pruning

Equality addition first canonicalizes both nodes. Equal identical representatives is
a no-op with combined support. Equality between object and concrete nodes is an
invariant error. Equality contradicting active inequality derives a clash with the
union of dependencies.

Merge direction is deterministic and preserves sound tree structure. It considers
node kind (named/NI roots before anonymous tree nodes), ancestry, nominal level,
creation ID, and cardinality requirements in the order fixed by code-level tests.
Different internal direction is allowed only if all of these hold:

- the hypertableau/NI invariants remain valid;
- active unary and incoming/outgoing binary assertions are copied to the representative
  with equality dependencies;
- affected descendants are pruned exactly when no longer valid;
- pending rule, existential, datatype, and blocking work is rescheduled;
- inequalities and negative assertions are rechecked; and
- rollback reconstructs the exact pre-merge logical state.

No public individual name is lost: same-as groups are read from canonical
representatives plus the permanent name map, not from whichever node survived.

## 7. Ground disjunctions and clashes

A ground disjunction has immutable disjuncts, base dependency set, deterministic
disjunct order, lifecycle/processed marker, and creation checkpoint. It is satisfied if
any disjunct is active after canonicalization. Pruned disjunctions are skipped but
remain rollback-safe.

There is at most one current clash record:

```python
Clash(kind, dependency_set, participants, provenance_id)
```

Clash kinds include bottom/empty head, positive-negative atom, equality-inequality,
irreflexivity/asymmetry/disjoint role consequences, impossible cardinality, and
datatype unsatisfiability. Participants are diagnostic and cannot affect backjumping.
Combining two detected clashes may retain either only when its dependency set is no
worse for completeness; deterministic tie behavior is tested.

## 8. Queues and scheduler state

Queues exist for new deltas, annotated equalities, existential candidates, unprocessed
ground disjunctions, datatype components, and blocking invalidations. Membership flags
prevent duplicate unbounded enqueues. Work order is deterministic by rule phase and
stable IDs, except where an explicitly tested HermiT-compatible heuristic orders
disjuncts.

Queue entries always validate lifecycle/generation when popped. A stale entry is
discarded safely, never dereferenced after arena reuse.

## 9. Invariant checker

Both engines implement an expensive debug checker covering at least:

1. arena/free-list/generation consistency;
2. parent depth, active tree, representative, merge, and prune relationships;
3. extension uniqueness and exact index reconstruction;
4. no active row references a retired node and canonical retrieval is consistent;
5. delta partitions and queue membership;
6. dependency levels and branching-point/checkpoint order;
7. ground-disjunction list/queue reachability;
8. existential processed marks versus current labels;
9. blocking validity/cache ownership; and
10. datatype component membership and constant assignments.

It runs after every operation in small state-machine property tests, after every
backtrack in debug tests, and optionally through an environment flag in production
diagnostics.

## 10. Acceptance tests

- Port the intent of upstream tuple-index, tuple-table, dependency-set, NI, and merge
  tests.
- Generate random sequences of add fact, branch, node create, merge, prune, clash,
  backtrack, and cancel; compare with a deliberately slow persistent-state model.
- Snapshot canonical logical state before a branch and require exact equality after
  backtracking from every later mutation point.
- Force node-slot reuse to detect stale handles.
- Test multiple supports where only one branch is undone.
- Test merge of ancestors, siblings, named/tree/NI nodes, self-roles, incoming/outgoing
  edges, and concrete-node rejection.
- Run the same serialized operation trace in Python and Rust and compare every debug
  snapshot exactly.
