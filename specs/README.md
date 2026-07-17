# pyHermiT specifications

These documents are the normative implementation contract for pyHermiT. The project
is a source-guided, Python and Rust reimplementation of the core reasoning behavior of
[HermiT](https://github.com/phillord/hermit-reasoner) with no Java dependency in an
installed package or normal test run.

Normative words such as **MUST**, **MUST NOT**, **SHOULD**, and **MAY** are used in the
RFC 2119 sense. If two documents conflict, use this precedence order:

1. [`SPEC.md`](SPEC.md), including its compatibility and scope rules;
2. [`deviations.md`](deviations.md), but only for an accepted, individually identified
   deviation;
3. the domain specification that owns the behavior;
4. the relevant work-package brief;
5. explanatory comments and examples.

An implementation is not complete merely because its work package is complete. The
release gates in [`verification.md`](verification.md) apply to the whole product.

## Normative documents

| Document | Owns |
|---|---|
| [`SPEC.md`](SPEC.md) | Product scope, compatibility definition, architecture, and global definition of done |
| [`reference-scope.md`](reference-scope.md) | Pinned upstream source and the port/replace/exclude fate of every HermiT area |
| [`contracts.md`](contracts.md) | Shared values, exceptions, configuration, backend protocol, canonical result forms |
| [`ontology-model.md`](ontology-model.md) | pyowl-core view/provider input, strict imports, ownership/versions, and pyHermiT OWL 2 DL validation |
| [`normalization-clausification.md`](normalization-clausification.md) | Normalization, role processing, automata, and translation to DL clauses |
| [`tableau-state.md`](tableau-state.md) | Nodes, extension tables, indexes, dependency sets, trail, merge, and rollback invariants |
| [`hypertableau.md`](hypertableau.md) | Rule scheduling, hyperresolution, branching, existentials, cardinalities, nominals, and clashes |
| [`blocking.md`](blocking.md) | Direct/indirect blocking, anywhere blocking, validation, caches, and invalidation |
| [`datatypes.md`](datatypes.md) | Required datatype map, lexical/value equality, restrictions, and datatype satisfiability |
| [`reasoning-services.md`](reasoning-services.md) | Consistency, satisfiability, entailment, classification, realization, and lifecycle behavior |
| [`native-backend.md`](native-backend.md) | Rust accelerator, Python parity, FFI boundary, concurrency, safety, and wheel behavior |
| [`verification.md`](verification.md) | Differential oracle, conformance suites, fuzzing, backend parity, and release gates |
| [`performance.md`](performance.md) | Benchmarks, baselines, budgets, profiling, and regression policy |
| [`deviations.md`](deviations.md) | Bug-fix precedence, deviation records, provenance, and licensing controls |

## Agent work packages

[`workpackages/README.md`](workpackages/README.md) is the assignment index and
dependency graph. [`workpackages/manifest.toml`](workpackages/manifest.toml) is the
machine-readable source of truth for IDs, dependencies, waves, and owned paths. Each
brief states exact deliverables and acceptance criteria for one bounded branch of work.

Agents MUST:

- take one unclaimed work package at a time;
- read every normative section listed under **Read first** before editing;
- respect owned paths and coordinate changes to shared files;
- implement real behavior rather than stubs, `pass`, unconditional skips, or fake
  fixtures;
- run both focused tests and all currently available dependency tests;
- record unresolved semantic uncertainty as a failing test or deviation proposal, not
  as a silent assumption;
- never weaken exact-result gates to make a test pass.

## Primary references

- Pinned HermiT reference:
  [`phillord/hermit-reasoner@37ec30aced32ac81ebecc5e33fad255ddefcb4c3`](https://github.com/phillord/hermit-reasoner/tree/37ec30aced32ac81ebecc5e33fad255ddefcb4c3)
- [OWL 2 Structural Specification and Functional-Style Syntax](https://www.w3.org/TR/owl2-syntax/)
- [OWL 2 Direct Semantics](https://www.w3.org/TR/owl2-direct-semantics/)
- [OWL 2 Conformance and Test Cases](https://www.w3.org/TR/owl2-test/)
- [Hypertableau Reasoning for Description Logics](https://arxiv.org/abs/1401.3485)
- Specification-layout precedent:
  [`city-artificial-intelligence/PyLogMap@3f938103`](https://github.com/city-artificial-intelligence/PyLogMap/tree/3f938103b7a2e7dfbfe7bbfb6596b9604ba3c421/specs)

The shared structural dependency is `pyowl-core>=0.1,<0.2` (import `pyowl_core`). Public OWL
values must be exact core types; reasoner clauses/tableau remain private.
