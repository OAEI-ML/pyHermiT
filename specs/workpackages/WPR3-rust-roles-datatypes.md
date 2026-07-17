# WPR3 — Rust role automata and datatype constraints

**Goal**: accelerate role-language propagation and concrete-domain reasoning while
preserving the exact Python value/range/constraint semantics.

## Read first

| What | Where |
|---|---|
| Datatype semantics | `datatypes.md` complete |
| Role automata semantics | `normalization-clausification.md` §3 |
| Native wire/safety | `native-backend.md` §§3, 5–8 |
| Python semantic oracles | WP05 and WP07 implementations/tests |
| Java behavior | pinned `datatypes/*`, `DatatypeManager`, `ObjectPropertyInclusionManager` |

## Deliverables

- Rust decoding/representation and execution of stable role NFAs, inverses,
  transitivity, top/bottom hooks, with bounded-word language differentials.
- Exact tagged arbitrary-precision numeric/rational/IEEE, string/plain/XML, boolean,
  binary, URI, date-time values and ranges needed by the native solver.
- Facet/range algebra, XSD regex automata, component equality/inequality/distinctness
  constraint checking, dirty-component scheduling, sound clash dependencies.
- Shared golden semantic-value wire fixtures and Python/Rust exhaustive small-domain,
  boundary, hostile-input, fuzz, locale/timezone/platform differentials.
- Fallible resource accounting/cancellation and component benchmarks/profiles.

## Depends on

WP05, WP07, and WPR0.

## Acceptance criteria

1. Every required datatype/facet/value-equality/range case matches Python exactly,
   including lexical aliases, signed zero/NaN/INF, timezone partial order, regex, and
   finite cardinalities.
2. Generated constraint components match Python/exhaustive SAT/UNSAT and clash
   dependency results through rollback.
3. Native NFAs accept exactly the same bounded words and propagate the same role
   consequences as Python for generated legal hierarchies.
4. Hostile lengths/integers/regex/XML/date inputs respect limits/cancellation without
   panic, overflow, locale/network dependence, or unsafe code.
5. Returned literal IDs preserve source lexical forms; native never collapses public
   values more aggressively than Python.
6. Sanitizer/fuzz/leak/audit and stored component performance gates pass.

