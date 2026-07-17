# WP04 — Deterministic OWL normalization

**Goal**: normalize every in-scope core OWL axiom/expression into a deterministic,
equisatisfiable intermediate form with no parser-order artifacts.

## Read first

| What | Where |
|---|---|
| Normal-form stages and invariants | `normalization-clausification.md` §§1–2, 5–8 |
| Model/canonical names | `ontology-model.md` §6; `contracts.md` §§2–3 |
| Java behavior | pinned `structural/OWLNormalization.java`, `ExpressionManager.java`, `OWLAxioms.java`; WP03 `normalization` JSONL operation and atomic/broad goldens |
| Formal semantics | OWL 2 Direct Semantics expression/axiom tables |

## Deliverables

- Exhaustive visitor/dispatcher for every logical pyowl-core constructor, with no wrapper
  model or copied effective axiom collection.
- Correct class/data NNF duals, built-in simplification, arity/cardinality edge cases,
  and normalized ABox complex assertions.
- Polarity-aware deterministic definition introduction/reuse and provenance mapping.
- Normalized axiom records for class, property, assertion, key, and datatype families;
  role-specific output may be consumed by WP05/WP06.
- Query-local normalization with namespaced symbols and permanent-state isolation.
- Table-driven construct/polarity tests, upstream semantic-intent ports, permutation
  tests, and small finite-model/metamorphic checks.

## Depends on

WP01.

## Acceptance criteria

1. The constructor handler table is exhaustive and unknown variants fail loudly.
2. Normalization is deterministic across parse/axiom/import/hash order and idempotent
   modulo provenance aggregation.
3. Fresh definitions are stable by expression/polarity key and never enter the declared
   signature or public result values.
4. Every axiom has positive, negative-polarity, top/bottom, and nested interaction
   tests where meaningful.
5. Generated small cases are equisatisfiable with their source via an independent
   bounded oracle; pinned Java comparisons ignore only alpha-renamed internal symbols.
6. No tableau/backend/native import exists in `normalize`.
7. Snapshot/overlay/composite iteration is direct and deterministic; equivalent core
   fingerprints produce identical private output without parser/text/RDF intermediates.
