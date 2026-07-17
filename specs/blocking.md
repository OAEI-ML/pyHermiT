# Blocking

Blocking guarantees termination without losing completeness. It is a semantic
correctness component, not merely a speed optimization.

Pinned upstream references:

- [`blocking/`](https://github.com/phillord/hermit-reasoner/tree/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/blocking)
- [`blocking/AnywhereBlocking.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/blocking/AnywhereBlocking.java)
- [`blocking/AnywhereValidatedBlocking.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/blocking/AnywhereValidatedBlocking.java)
- [`blocking/BlockingValidator.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/blocking/BlockingValidator.java)
- [`blocking/BlockingSignatureCache.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/blocking/BlockingSignatureCache.java)

## 1. Strategy selection

With `blocking="auto"`:

- use single direct blocking when the compiled ontology has no inverse roles;
- use pairwise direct blocking when inverse roles require parent/edge context;
- use anywhere blocking as the normal global strategy;
- use the validated direct checker/validated-anywhere strategy when a selected core
  blocking optimization requires validation; and
- enable signature caching only when its soundness conditions hold, including the
  absence of nominals for the upstream-compatible cache path.

This follows the strategy construction in pinned `Reasoner.createTableau`. Explicit
ancestor/validated modes exist for testing and diagnostics. Every legal strategy must
return identical logical results.

## 2. Eligibility and terminology

A direct blocker/blockee is an active object `TREE` node. Named, NI, concrete, merged,
pruned, and retired nodes cannot be directly blocked. A node is indirectly blocked if
an ancestor is blocked or pruned in the manner defined by the expansion strategy.

A potential blocker must precede the blockee in the stable creation order, must not be
the blockee or one of its descendants, and must itself be active and not indirectly
blocked. Anywhere blocking searches all eligible earlier nodes, not only ancestors.
Candidate order is deterministic so traces and cache behavior reproduce across runs.

## 3. Direct signatures

The implementation defines immutable signatures from active, relevant assertions:

- **single** signature: the required positive/negative/core concept label of the node;
- **pairwise** signature: node label, parent label, and the relevant forward and inverse
  edge labels between node and parent; and
- **validated/core** signature: the core-label projection required by the chosen
  checker plus enough context for `BlockingValidator` to prove omitted constraints.

The exact included predicate categories and core semantics are ported from the pinned
direct checkers and captured as table-driven tests. Internal order is irrelevant;
signature equality is mathematical set equality. Data-node assertions, generated
ordering guards, inactive tuples, and facts on noncanonical merged nodes cannot pollute
an object blocking signature.

Hash equality is never accepted without full signature equality. Python and Rust use
the same canonical debug serialization even if their hash functions differ.

## 4. Anywhere maintenance

The manager maintains an index from signature hash/key to eligible blocker candidates.
It incrementally recomputes from the earliest changed node after:

- a relevant assertion or core-flag change;
- node creation/destruction/prune/reactivation;
- equality merge/unmerge;
- parent/edge label change;
- nominal/NI processing;
- existential expansion that changes relevant labels; or
- backtracking.

If precise invalidation is uncertain, recompute the affected suffix or all blocking;
stale positive blocks are unsound. A stale cache may at worst lose performance, never
skip a required expansion.

Direct blocking chooses the earliest valid candidate under the stable order. When a
node changes blocker, its descendants are invalidated/rescheduled as required.

## 5. Indirect blocking and expansion

An indirectly blocked node and its appropriate descendants receive no existential
expansion. Existing facts remain queryable for hyperresolution/signature validation.
Unblocking queues every still-unsatisfied existential exactly once. A node whose parent
was merged/pruned is not treated as an ordinary blocked node; pruning/rollback rules
own its lifecycle.

## 6. Signature cache

After a satisfiable model is found under allowed expressivity, reusable blocking
signatures may be stored in a session/ontology cache. A cached signature can block a
matching node without retaining the old model only when the pinned soundness conditions
hold.

The cache key includes compiled ontology fingerprint, direct-checker kind, core mode,
and complete signature. It is never shared across ontology revisions/configurations.
Entries derived from query-local axioms are not promoted to the permanent cache.
Nominals or incompatible additional/query ontology features disable it.

Cache insertion occurs only after a completed satisfiable run, never after timeout,
interrupt, resource error, poisoned session, or unsatisfiable branch. Memory is bounded
and eviction affects only speed.

## 7. Validated/core blocking

Provisional core blocking may ignore noncore labels and therefore needs a validation
phase. At apparent saturation:

1. enumerate direct blocks in stable order;
2. validate each block against all relevant DL clauses, role/parent context, and
   existential conditions following pinned `BlockingValidator`;
3. invalidate a failing block and any dependents;
4. make the necessary assertions core/reschedule exposed work according to simple or
   complex core mode; and
5. resume normal saturation until a fixed point, then validate again.

SAT cannot be returned while an invalid or unchecked provisional block remains.
Validation state and core promotions are rollback-safe.

## 8. Backtracking and cancellation

Blocker assignments, index membership, cached signature candidates, validation marks,
and earliest-changed cursors are trailed or generation-keyed. Rolling back yields the
same blocking state as recomputation from the restored logical facts. Tests compare
incremental state with full recomputation after every randomized rollback.

Cancellation during validation leaves no signature promoted and makes the session
rebuild/reset before reuse unless the operation-root rollback completes.

## 9. Acceptance tests

- Port the intent of upstream direct-checker, anywhere, validation, and known
  `BlockingValidatorTest` cases, including upstream known failures as explicit
  expected-reference observations rather than hidden skips.
- Cyclic TBoxes that require blocking terminate with the correct SAT/UNSAT result.
- Single/pairwise cases differ exactly where parent/edge context matters.
- Anywhere finds a nonancestor blocker that ancestor mode cannot use.
- Every relevant label/edge/core mutation invalidates a formerly valid block.
- Merge/unmerge and prune/backtrack restore full-recompute-equivalent state.
- Nominal, inverse-role, cardinality, role-chain, and NI interactions are covered.
- Cache on/off and every strategy mode have identical semantic results.
- Python/Rust signature serialization and chosen blocker IDs match on deterministic
  fixtures; differing private hash values are allowed.

