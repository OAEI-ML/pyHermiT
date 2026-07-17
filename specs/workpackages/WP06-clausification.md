# WP06 — Complete clausification and compiled IR

**Goal**: translate normalized OWL plus role/data metadata into the validated immutable
private HermiT IR shared byte-for-byte by Python and Rust sessions, never as a replacement
for the pyowl-core ontology view.

## Read first

| What | Where |
|---|---|
| Clause/fact/query/delta contract | `normalization-clausification.md` §§4–8 |
| Compiled IR and deterministic IDs | `contracts.md` §§2–3 |
| Java behavior | pinned `OWLClausification.java`, `ReducedABoxOnlyClausification.java`, `model/DLClause.java`, `DLOntology.java` |
| Rule consumers | `hypertableau.md` §§3–9 |

## Deliverables

- Typed terms, predicate registry, atoms, DL clauses, facts, ground disjunctions,
  provenance, expressivity, `CompiledOntology`, `CompiledQuery`, and `CompiledDelta`.
- Exhaustive clausifier for every normalized class/property/datatype/key/assertion form,
  role automaton propagation, built-ins, negative facts, annotated equality, at-least,
  equality/inequality, and internal ordering guards.
- Canonical variable renaming, atom/clauses/fact sorting, safe tautology/deduplication,
  join-pattern metadata, deterministic dense IDs, and full IR validator.
- Query compilation/rebuild compatibility classification and assertion-only delta
  classification; no permanent symbol/state mutation.
- Canonical JSON/debug form plus the schema input used by WPR0's binary codec.
- Construct/interaction goldens, structural semantic-intent ports, fuzz/property tests.
- Compilation key binds core structural/logical/signature fingerprints and model/adapter
  versions; source OWL is never serialized to derive it.

## Depends on

WP04 and WP05.

## Acceptance criteria

1. Every in-scope normalized constructor has an explicit handler; no ignored default.
2. The IR validator rejects dangling IDs, wrong sorts/arities, unsafe variables,
   malformed equality/ordering predicates, and strategy-inconsistent expressivity.
3. Input/permutation/hash order yields byte-identical canonical debug IR; generated
   names compare modulo the documented canonical scheme with Java.
4. Dedicated goldens cover universals through role NFAs, qualified cardinalities,
   nominals/NI, keys' named guards, negative assertions, top/bottom roles, custom data
   ranges, punning, and complex ABox assertions.
5. Query compilation leaves a serialized permanent IR unchanged; unsafe deltas request
   rebuild rather than claiming incremental support.
6. Both naive semantic reductions and pinned black-box vectors agree on bounded cases.
7. Core view capture is zero-copy; compiler allocates only necessary private IR/bounded work
   tables and does not flatten overlay/composite bases into a public-model copy.
