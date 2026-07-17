# WP15 — Realization and individual/property answers

**Goal**: implement complete class realization, same/different individuals, and
entailed object/data property query services.

## Read first

| What | Where |
|---|---|
| Realization result/API semantics | `contracts.md` §6.3; `reasoning-services.md` §8 |
| Literal observable policy | `datatypes.md` §2; `verification.md` §4 |
| Java behavior | pinned `hierarchy/InstanceManager.java`; relevant `Reasoner` individual/property methods |
| Updates/cache constraints | `reasoning-services.md` §§10–11 |

## Deliverables

- Known/possible class-instance and role-pair structures initialized from a consistency
  premodel and lazily/refinably checked without losing completeness.
- Direct/all types and instances, same-as partition, different individuals, by-name and
  by-same-as node policies.
- Object property values/instances/relationship checks across hierarchy, inverses, and
  equality; data values/relationship checks across subproperties/same subjects with
  preserved lexical literals.
- Top/bottom, fresh/unknown, anonymous/internal witness, inconsistent ontology, and
  complex-expression behavior.
- Naive entailment-per-answer oracle for tiny generated signatures plus upstream/API
  goldens and cache invalidation hooks.

## Depends on

WP13 and WP14.

## Acceptance criteria

1. `has_type`, types, instances, and assertion entailment agree; all results respect
   class closure and direct-node minimality.
2. Same-as partitions all named individuals, supports substitution, honors both result
   policies, and never returns internal/anonymous witnesses.
3. Forward/inverse property values, relationship tests, instance maps, hierarchy,
   merges/cardinality, and same-as all agree with naive entailment and HermiT.
4. Data value returns preserve each relevant explicit lexical literal even when values
   are semantically equal; they do not invent arbitrary existential witnesses.
5. Lazy/refined caches never turn unknown into false; timeout/cancel leaves no partial
   cache advertised as ready.
6. Generated naive-versus-optimized and WPR4 canonical result fixtures pass.

