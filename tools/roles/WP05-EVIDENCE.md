# WP05 role preprocessing evidence

## Implemented contract

- Canonical forward/inverse object-property expressions and separate data-property
  hierarchy handling use only `pyowl_core` structural values.
- Deterministic SCCs, component DAGs, adaptive sparse/dense transitive closure, inverse
  closure, and stable IDs are independent of source axiom insertion order.
- OWL 2 composite/non-simple propagation and regularity diagnostics are computed once in
  `RoleAxiomGraph` for later validation and clausification consumers.
- Regular complex inclusions compile to epsilon NFAs.  No determinization or minimization
  is performed.  State traversal removes unreachable/dead states and assigns stable IDs.
- Top and bottom object/data properties are explicit.  Their universal/empty behavior is
  exposed through nonmaterializing hooks; effective word acceptance handles an empty-role
  chain without expanding every NFA by the whole role alphabet.
- Configurable role, chain, aggregate-state, and aggregate-transition limits fail closed.

The behavior review used OWL 2 Structural Specification section 11, especially the
definition of composite properties and the five legal regularity forms:
<https://www.w3.org/TR/owl2-syntax/#Global_Restrictions_on_Axioms_in_OWL_2_DL>.
The source-guided comparison is pinned to HermiT commit
`37ec30aced32ac81ebecc5e33fad255ddefcb4c3`, specifically
`ObjectPropertyInclusionManager.java`, `BuiltInPropertyManager.java`, and
`org/semanticweb/HermiT/graph/Graph.java`.  Java is reference material only and is not
imported, invoked, or packaged.

## Correctness evidence

The focused suite covers:

- empty and built-in-only models;
- simple closure, equivalence/SCCs, inverse and symmetric relationships;
- data-property closure independent of object roles;
- simple/non-simple propagation, transitivity, top, and bottom;
- legal left/right/transitive recursion and irregular internal/inverse/dependency cycles;
- mirrored inverse-chain languages, overlapping prefixes, and reachability cleanup;
- every input permutation of a representative model;
- 20 deterministic generated regular hierarchies, exhaustively checking all words through
  length three over five roles against an independent bounded grammar oracle;
- stable frozen model/NFA trace; and
- sparse/dense closure representation parity and configured resource limits.

Validation on macOS 26.5.2 x86_64:

| Gate | CPython 3.10.11 | CPython 3.12.3 |
|---|---:|---:|
| focused role tests | 40 passed | 40 passed |
| repository suite | 186 passed + 4 subtests | 186 passed + 4 subtests |
| Ruff | clean | clean |
| strict MyPy (`src/pyhermit/roles`) | clean | clean |

## Scale measurement

The synthetic sparse-signature probe constructs 5,000 declaration axioms, producing 10,002
forward/inverse/built-in roles and 10,002 components.  On the machine above, the final
untraced run completed role preprocessing in **1.015 seconds**, built only the two required
built-in automata, and retained **0.534 MiB** for the reachability tuple plus its adaptive
values (measured with `sys.getsizeof`).

This probe exposed and removed two scaling hazards before commit:

1. deterministic topological sorting was changed from repeated global scans to a heap plus
   dependency adjacency; and
2. dense integer singleton bitsets were replaced with adaptive sorted tuples/bitsets, so an
   edgeless high-ID signature is linear rather than quadratic in retained closure bytes.

`tracemalloc` instrumentation changes timing materially and is therefore reported separately:
the pre-adaptive 5,000-declaration probe retained 10.352 MiB and peaked at 24.835 MiB of traced
Python allocations while completing in 3.202 seconds.  The uninstrumented number is the timing
baseline; the traced number is only an allocation diagnostic.  This is a preprocessing
microbenchmark, not an end-to-end reasoner or Java-relative claim.

## Remaining integration boundary

WP05 supplies private role IR and effective built-in hooks.  WP02 must consume the regularity
report, and WP06/tableau backends must consume the same model rather than rebuild role closure.
End-to-end HermiT oracle parity remains gated on those downstream compiler/reasoner work
packages.
