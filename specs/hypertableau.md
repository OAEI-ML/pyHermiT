# Hypertableau calculus and scheduler

The calculus is based on Motik, Shearer, and Horrocks,
[Hypertableau Reasoning for Description Logics](https://arxiv.org/abs/1401.3485), and
the pinned HermiT implementation. This specification fixes the implementation-level
behavior needed for complete OWL 2 DL reasoning while allowing different data
structures and safe optimizations.

Primary upstream references:

- [`tableau/Tableau.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/Tableau.java)
- [`tableau/HyperresolutionManager.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/HyperresolutionManager.java)
- [`tableau/DLClauseEvaluator.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/DLClauseEvaluator.java)
- [`tableau/ExistentialExpansionManager.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/ExistentialExpansionManager.java)
- [`tableau/NominalIntroductionManager.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/NominalIntroductionManager.java)
- [`tableau/MergingManager.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/tableau/MergingManager.java)
- [`existentials/`](https://github.com/phillord/hermit-reasoner/tree/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/existentials)

## 1. Correctness obligations

For every accepted compiled ontology/query, saturation MUST:

- terminate;
- return satisfiable iff the normalized ontology/query has a model under Direct
  Semantics;
- preserve completeness through nondeterministic choices and dependency-directed
  backtracking;
- never expand a blocked node unless validation invalidates the block;
- treat object and data domains as disjoint; and
- leave a reusable session at a defined checkpoint after success, clash, timeout,
  interruption, or error.

Rule order is an optimization except where state visibility, semi-naive deltas,
blocking validation, or HermiT-compatible branch dependencies make it part of these
obligations.

## 2. Initialization

Each `check` starts at a clean query-root checkpoint:

1. create nodes for required permanent/query individuals and data constants;
2. install positive and negative facts with their deterministic/query dependency
   class;
3. install initial ground disjunctions and clashes;
4. ensure at least one object node exists even for an empty ontology;
5. initialize strategy, blocking, datatype, and role-automaton state; and
6. enqueue all initial rows in `DELTA_NEW`.

Named-individual-to-node maps survive only as immutable input/result mappings. A
previous query's anonymous witnesses, branches, facts, and caches cannot leak into the
next query.

## 3. Main saturation schedule

The default scheduler mirrors the semantic phase order in HermiT's `runCalculus` and
`doIteration`:

```text
repeat
  if no clash:
    process pending annotated equalities (NI)
    while a DELTA_NEW generation exists and no clash:
      advance the delta generation
      apply permanent and query hyperresolution plans
      apply unknown-datatype compatibility semantics when configured
      check affected datatype components
      process newly pending annotated equalities (NI)
    if any delta was processed: continue outer loop

  if no clash and expand one deterministic batch of eligible existentials:
    continue outer loop

  if no clash and an unsatisfied unprocessed ground disjunction exists:
    choose/create a branch and add its first disjunct
    continue outer loop

  if clash:
    compute highest supported branching level
    if no legal level exists: return UNSAT
    rollback directly to that level and start its next choice
    continue outer loop

  if the chosen blocking strategy needs final validation and invalidates blocks:
    reschedule the exposed existentials and continue

  return SAT
```

Cancellation/resource checks occur inside long joins and datatype work as well as at
every shown phase boundary. A performance optimization may process a safe batch rather
than one item, but it must yield the same fixed point and valid dependency supports.

## 4. Hyperresolution (`Hyp` rule)

Each DL clause is compiled into join plans keyed by a selected delta body atom and
indexed access patterns for all remaining atoms. A substitution matches only active
facts after node canonicalization and respects:

- object/data sorts;
- positive and negative predicates;
- equality/inequality and internal ordering guards;
- repeated variables;
- active node/row lifecycle; and
- core flags where the specialized predicate requires them.

Dependencies of all matched premises are unioned. After substituting the head:

- zero disjuncts derive a clash;
- one disjunct applies deterministically;
- multiple disjuncts create one canonical ground disjunction unless already present;
- an already satisfied head produces no work; and
- duplicate substituted disjuncts are removed before deciding whether branching is
  required.

Head application dispatches by predicate: concept/data assertion, role assertion,
equality merge request, inequality, at-least obligation, annotated equality, or clash.
An internal predicate without a handler is an invariant error, never ignored.

Join compilation may reorder body atoms using relation cardinality/selectivity, but a
stable tie break is mandatory. Property tests compare compiled joins to naive complete
substitution enumeration on small states.

## 5. Ground disjunctions and branching

An unsatisfied disjunction with one remaining distinct disjunct is deterministic. For
larger disjunctions:

1. order disjuncts using the configured HermiT-compatible strategy with a stable
   predicate/argument tie break;
2. push a branching point at the next level;
3. add that level to the disjunction's base dependencies;
4. apply the first disjunct; and
5. retain remaining choices in the branching point.

On clash, backjump to the maximum level in the clash dependency set, skipping
irrelevant newer choices. Advancing a choice combines the prior clash information as
required for sound disjunction learning. When all choices at a level fail, propagate a
clash whose dependencies remove that exhausted choice level and continue backjumping.

Learning may reduce work but cannot discard a potentially satisfiable choice. Tests
force learning on/off and require identical answers, plus targeted cases where a
nonchronological backjump skips several levels.

## 6. Existential and minimum-cardinality expansion

`AtLeast(n, R, C)(x)` is satisfied only when there are at least `n` pairwise-different
canonical `R` successors of `x` satisfying `C` (or data values satisfying a data range).
For an active, unblocked node with an unsatisfied obligation:

- create/reuse exactly enough witnesses according to the selected sound strategy;
- add the role and filler assertions with the obligation dependency set;
- add pairwise inequalities between distinct newly required witnesses;
- mark created assertions `core` exactly as required for blocking; and
- trail the processed/reuse decision.

`n=0` is already satisfied. Existential quantification is the `n=1` case. Inverse
roles attach the edge in the correct direction. Bottom roles/fillers cause a clash via
normal consequences; top roles use their specialized semantics without quadratic
materialization.

### 6.1 Creation-order strategy

This is the default compatible strategy. It expands eligible obligations in stable
node/obligation creation order and cooperates with the configured blocking strategy.
No witness is reused unless equality or an explicit calculus rule establishes it.

### 6.2 Individual reuse

Individual reuse is an optional HermiT optimization. Reuse candidates and exclusions
must follow the upstream strategy's soundness conditions. A reused root receives all
required assertions/dependencies, and a later conflict backtracks the reuse choice as
needed. Reuse-on/off results must match exactly; performance alone never justifies an
unproved reuse.

## 7. Maximum cardinality and equality

Clausification expresses at-most restrictions as equality-producing disjunctions (and
qualified guards) over excessive pairwise-distinct successors. When such an equality
head is selected, merging follows `tableau-state.md`.

The implementation must correctly cover:

- qualified/unqualified object and data maximum/exact cardinalities;
- already merged successors and multiple names for a successor;
- inverse roles and role hierarchy consequences;
- explicit inequalities preventing a merge and causing another disjunct/clash;
- dependency union from the cardinality assertion, role/filler facts, and chosen
  equality; and
- re-evaluation after any merge changes canonical successor counts.

Counting raw rows or pre-merge node IDs is unsound and forbidden.

## 8. Nominal introduction (`NI` rule)

The NI rule handles the termination-critical interaction of nominals, inverse roles,
and number restrictions. Annotated equalities are not ordinary equality facts. The
nominal manager:

1. canonicalizes the root/target and annotation;
2. computes the deterministic root/annotation/cardinality key and required NI target;
3. creates or reuses the correct root NI node/level;
4. derives the equality with the full annotated-equality dependencies;
5. schedules all merge, blocking, existential, and datatype consequences; and
6. trails key maps, level counters, created nodes, and processed markers.

The implementation MUST follow the formal NI-rule side conditions in the hypertableau
paper and the pinned `NominalIntroductionManager`, including repeated annotations,
merges before/after processing, and rollback. Replacing annotated equality with eager
ordinary merging is not an acceptable approximation.

Focused parity fixtures cover every upstream `NIRuleTest` shape plus randomized
nominal/inverse/number interactions.

## 9. Clash rules

Clashes are derived for at least:

- empty clause head or explicit bottom concept/property;
- `A(x)` with its normalized negation;
- positive and negative role assertion on the same canonical tuple;
- equality and inequality of the same canonical nodes;
- irreflexive/asymmetric/disjoint property violations after hierarchy/inverse closure;
- insufficient distinct values/successors forced by incompatible cardinalities;
- impossible datatype components; and
- any specialized built-in contradiction.

The dependency set is the union of all premises establishing the contradiction.
Diagnostics cannot omit a premise from backtracking support merely to produce a small
explanation.

## 10. Blocking integration and termination

Before expanding an object tree node, the expansion strategy asks the blocking manager
to recompute/invalidate as needed. Blocked nodes do not receive existential expansion;
logical consequences already derivable by hyperresolution still maintain the labels
needed to validate blocks. Indirectly blocked descendants are likewise not expanded.

For validated/core blocking strategies whose provisional blocks are not necessarily
exact, reaching an apparent fixed point triggers a full validation pass. Invalid blocks
are cleared and their exposed obligations are rescheduled before SAT may be returned.
See `blocking.md`.

Termination tests include cyclic existentials, inverse roles, cardinalities, nominals,
role chains, and all combinations used by the formal calculus.

## 11. Datatype integration

New/removed data-range assertions, data-role edges, constants, equalities, and
inequalities mark an affected datatype component dirty. The datatype manager checks
only dirty components but a debug mode recomputes all and compares. It either records a
consistent assignment/existence certificate internally or derives a clash with exact
dependencies. It never chooses a floating approximation for an exact value. See
`datatypes.md`.

## 12. Required tests

1. One isolated state-transition test for every rule and predicate handler.
2. Naive-versus-indexed hyperresolution property tests.
3. Full branch trees with chronological and nonchronological backtracking, learning
   on/off, duplicate/satisfied disjunctions, and deterministic clashes.
4. Min/max/exact cardinality with merges, inequalities, role hierarchy, inverses,
   nominals, and data values.
5. NI regression and rollback tests.
6. Existential strategy and blocking strategy cross-product parity.
7. Cancellation injected after every mutation kind, followed by invariant validation
   and a successful reuse/rebuild query.
8. Exact Python/Rust result and debug transition-trace parity on bounded cases.
9. Pinned HermiT tableau and relevant black-box fixtures.

No test may assert only that the engine terminates; it must assert the semantic result
and, for state tests, the resulting invariants/dependencies.

