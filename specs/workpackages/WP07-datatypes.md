# WP07 — Pure-Python datatype subsystem

**Goal**: implement the complete pinned OWL 2 datatype map, exact value semantics, data
ranges, and a readable constraint solver.

## Read first

| What | Where |
|---|---|
| Complete datatype contract | `datatypes.md` |
| Literal identity/return behavior | `contracts.md` §2.1; `verification.md` §4 |
| Java behavior | pinned `datatypes/` and reasoner datatype test classes |
| Normative definitions | W3C datatype map and Direct Semantics data-range tables |

## Deliverables

- Lexical parsers and immutable values for every required numeric, float/double,
  string/plain/XML, boolean, binary, URI, and date-time datatype.
- Exact cross-datatype value equality/disjointness, core source-literal preservation,
  standards-canonical language comparison, signed zero/NaN/INF, timezone partial ordering,
  and finite cardinalities. Any pinned quirk is a private compatibility key.
- Legal facet validation; symbolic range intersection/union/complement/emptiness/
  containment and XSD regex automata (not host-regex approximations).
- Acyclic custom datatype definitions and unsupported-datatype compatibility policy.
- Pure-Python component constraint solver for range constraints, constants,
  equality/inequality, and required distinct values with dependency provenance.
- Full datatype/facet boundary matrix, pinned HermiT/W3C cases, exhaustive small-domain
  oracle properties, locale/timezone independence, hostile/resource tests.

## Depends on

WP01.

## Acceptance criteria

1. Every datatype/facet named in `datatypes.md` has valid/invalid lexical, boundary,
   range algebra, ontology SAT/UNSAT, and serialization tests.
2. Arbitrary-precision numeric and date-time/string semantics never pass through lossy
   host coercion; results are platform/locale/timezone independent.
3. Semantic equal literals constrain as equal while distinct source lexical triples
   remain available for HermiT-compatible data-value returns.
4. Generated finite components agree with exhaustive assignment and report sound clash
   dependencies through branch rollback scenarios.
5. XML processing is entity/network safe; regex/large-number/range work is bounded and
   cancellable.
6. No Java/native dependency or tableau state import exists in the datatype library.
7. Public returned literals are the original exact core objects; compiler data identities
   never change/rebuild their equality or source spelling.
