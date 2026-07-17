# Pinned HermiT reference and source fate map

This document prevents two common failures in a source-guided reimplementation:
accidentally omitting a correctness-critical internal class because it looks like an
implementation detail, and accidentally porting an integration/extension that is not
part of the requested core reasoner.

## 1. Immutable baseline

| Field | Value |
|---|---|
| Repository | [`phillord/hermit-reasoner`](https://github.com/phillord/hermit-reasoner) |
| Commit | [`37ec30aced32ac81ebecc5e33fad255ddefcb4c3`](https://github.com/phillord/hermit-reasoner/commit/37ec30aced32ac81ebecc5e33fad255ddefcb4c3) |
| Commit date | 2017-10-04 08:39:39 UTC |
| Upstream subject | `minor fix, do not affect functionality` |
| SVN origin | migrated revision 1200 |
| Maven coordinate | `com.hermit-reasoner:org.semanticweb.hermit:1.4.0.0-SNAPSHOT` |
| Compatibility label | `hermit-master-37ec30a` |
| Production Java files | 200 |
| Branch/release state | one `master` branch; no Git tags or GitHub releases |

The README history stops at 1.3.8. Master is an unreleased 1.4 snapshot and is the
owner-selected target. Do not substitute a newer OWLAPI fork, Maven Central version,
the 1.3.8 history entry, or a mutable branch. Papers describe algorithmic intent;
pinned source decides implementation tie-breakers subject to the W3C/deviation
precedence in `SPEC.md`.

`tools/reference/manifest.toml` will store this data plus archive/build hashes. The
reference checkout is fetched into an ignored developer cache, never vendored/shipped.

## 2. Fate vocabulary

- **Retain semantics**: all observable/correctness behavior is mandatory, though the
  Python/Rust organization may differ completely.
- **Replace boundary**: HermiT delegates to Java/OWLAPI/integration code; pyHermiT
  supplies a Python-native equivalent needed by the core.
- **Development oracle only**: used to generate evidence, never installed/runtime.
- **Exclude extension/integration**: explicitly outside core and rejected or absent.

No “drop” designation permits losing an OWL 2 Direct Semantics consequence that passed
through that code. For example, Java graph helpers may be replaced, but their role-
regularity and hierarchy results remain mandatory.

## 3. Top-level source fate

All paths are relative to
[`src/main/java/org/semanticweb/HermiT`](https://github.com/phillord/hermit-reasoner/tree/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT).

| Upstream area | Fate | pyHermiT destination/obligation |
|---|---|---|
| `Reasoner.java` | Retain behavior, redesign | `api.py`, services, backend sessions; all core query/lifecycle/change semantics |
| `Configuration.java` | Retain semantic defaults, redesign | frozen `config.py`; omit Java monitor/Protege types |
| `EntailmentChecker.java` | Retain semantics | exhaustive `services/entailment.py`, anonymous roll-up, keys/datatypes |
| `Prefixes.java` | Replace boundary | exact pyowl-core IRI/prefix/syntax values; answers use core full-IRI entities |
| `ProtegeReasonerFactory.java` | Exclude integration | no OSGi/Protege facade |
| `blocking/` (13 classes) | Retain semantics | Python/Rust single/pairwise, ancestor/anywhere, validated/core, cache |
| `cli/` | Exclude integration | no Java CLI compatibility in core |
| `datalog/` | Exclude extension | no `ConjunctiveQuery`, standalone `DatalogEngine`, or result collector |
| `datatypes/` and nine subpackages | Retain semantics | complete Python/Rust datatype/value/range/constraint subsystem |
| `debugger/`, `debugger/commands/` | Exclude integration | no Swing debugger/derivation viewer/interactive commands |
| `existentials/` | Retain semantics | creation-order default and optional individual/EL-style reuse |
| `graph/Graph.java` | Replace implementation | deterministic graph/SCC/closure utilities inside roles/hierarchy/services |
| `hierarchy/` | Split, see §4 | classification, hierarchy, instance manager core; printers excluded |
| `model/` | Split, see §5 | backend-neutral semantic IR; description graphs excluded |
| `monitor/` | Replace minimal concepts | structured events/counters/cancellation only; no pause UI/timers contract |
| `structural/` (8 classes) | Retain semantics | normalization, expressivity, roles, clausification, ABox delta; strip extension branches |
| `tableau/` | Split, see §6 | complete core calculus/state except description-graph manager/paths |

Top-level behavior not represented by a one-to-one Python class is still traced through
tests/provenance. Agents port behavior and invariants, not Java inheritance.

## 4. Hierarchy fate

Correctness-critical classes whose algorithmic behavior must be retained:

- `AtomicConceptElement`;
- `DeterministicClassification`;
- `Hierarchy` and `HierarchyNode`;
- `HierarchySearch`;
- `InstanceManager`;
- `QuasiOrderClassification`;
- `QuasiOrderClassificationForRoles`; and
- `RoleElementManager`.

`ClassificationProgressMonitor` becomes the small structured callback/event protocol.
`HierarchyDumperFSS` and `HierarchyPrinterFSS` are output utilities and are excluded from
core. A later serializer may use the public hierarchy without porting their formatting.

Mandatory algorithms:

- deterministic classification constructs/reads safe models per class, extracts
  subsumers, collapses SCCs, and transitively reduces;
- quasi-order classification maintains known `K` and possible `P` subsumption graphs,
  prunes with premodels/non-subsumers, and targets tests until `P` is empty;
- object/data properties receive semantic classification via role-to-concept/quasi-
  order reductions, not asserted transitive closure; and
- realization retains known/possible class instances and role pairs, same-as classes,
  and lazy sound refinement.

## 5. Model fate

Exclude only description-graph values `DescriptionGraph` and
`ExistsDescriptionGraph`. Retain the semantics represented by the rest, even when
consolidated into enums/dataclasses:

```text
AnnotatedEquality       AtLeast / AtLeastConcept / AtLeastDataRange
Atom                    AtomicConcept / AtomicNegationConcept
AtomicDataRange         AtomicNegationDataRange
AtomicRole              InverseRole / NegatedAtomicRole / Role
Concept                 LiteralConcept / ExistentialConcept
Constant                ConstantEnumeration
DataRange               DatatypeRestriction / InternalDatatype / LiteralDataRange
DLClause                DLOntology / DLPredicate
Equality                Inequality
Individual              Variable / Term
NodeIDLessEqualThan     NodeIDsAscendingOrEqual
InterningManager        (replace with deterministic interning/IDs)
```

Annotated equality, negative roles, at-least predicates, node-order guards, literal
lexical/value separation, and immutable clauses are calculus requirements—not
debugging artifacts. Java serialization of `DLOntology` is excluded; pyHermiT uses the
private versioned IR wire/debug schemas.

## 6. Tableau fate

Exclude `DescriptionGraphManager` and graph-specific node creation/constraint branches.
Retain/reimplement the behavior of:

- `Tableau`, `Node`, `NodeType`, `ReasoningTaskDescription`;
- `ExtensionManager`, `ExtensionTable`, both extension-table implementations,
  `TupleIndex`, `TupleTable`, and `TupleTableFullIndex`;
- `HyperresolutionManager` and `DLClauseEvaluator`;
- `DependencySet`, permanent/union variants, and `DependencySetFactory`;
- `BranchingPoint`, `DisjunctionBranchingPoint`, `GroundDisjunction`, and its header;
- `ClashManager`;
- `MergingManager`;
- `ExistentialExpansionManager`;
- `NominalIntroductionManager`;
- `DatatypeManager`; and
- `InterruptFlag`/`InterruptCurrentTaskException` behavior through the shared
  cancellation/exception protocol.

Append-only indexed binary/ternary tables, delta promotion, compiled joins, dependency
sets, branch checkpoints, equality merge/prune, NI, and rollback are the primary native
kernel—not optional implementation mimicry. Different representations are allowed only
with the same rule/state invariants and exact results.

## 7. Blocking and existentials

All pinned blocking classes are semantically relevant:

```text
AncestorBlocking                 AnywhereBlocking
AnywhereValidatedBlocking        BlockingStrategy
BlockingSignature                BlockingSignatureCache
BlockingValidator                DirectBlockingChecker
SingleDirectBlockingChecker      PairWiseDirectBlockingChecker
ValidatedSingleDirectBlockingChecker
ValidatedPairwiseDirectBlockingChecker
SetFactory (replace implementation)
```

All four existential strategy classes are retained semantically:
`ExistentialExpansionStrategy`, `AbstractExpansionStrategy`, `CreationOrderStrategy`,
and `IndividualReuseStrategy`.

Actual pinned defaults (source overrides stale comments):

- direct blocking `OPTIMAL`: pairwise iff inverse roles, otherwise single;
- strategy `OPTIMAL`: constructs anywhere blocking;
- signature cache on only without nominals and explicit core blocking;
- creation-order existential expansion;
- disjunction learning on;
- buffered changes on;
- fresh entities allowed;
- individual result policy by name;
- unsupported datatypes error;
- inconsistent-query exception on; and
- no per-task timeout.

## 8. Datatype fate

Retain/reimplement `DatatypeHandler`, `DatatypeRegistry`, value-space subset contracts,
malformed/unsupported exceptions, and all handlers/value structures in:

```text
anyuri
binarydata
bool
datetime
doublenum
floatnum
owlreal
rdfplainliteral
xmlliteral
```

The exact pinned datatype inventory is in `datatypes.md`. Public literals always follow
pyowl-core's source-preserving, current standards-canonical model (including its RDF 1.1
mapping). If pinned HermiT's historical `rdf:PlainLiteral` representation affects
compatibility, the compiler creates an explicit private compatibility key; it never changes
public core identity. A standards-incompatible observable answer requires a deviation
decision. Host library types cannot replace lexical/value/facet semantics without
differential proof.

## 9. Structural fate and pipeline trace

Retain all eight structural class responsibilities:

| Class | Required pyHermiT behavior |
|---|---|
| `ExpressionManager` | simplification/NNF expression handling |
| `OWLAxioms` | normalized axiom collections |
| `OWLAxiomsExpressivity` | safe strategy feature summary |
| `OWLNormalization` | polarity-aware normalization/definitions |
| `BuiltInPropertyManager` | top/bottom property semantics |
| `ObjectPropertyInclusionManager` | simplicity/regularity/role NFAs |
| `OWLClausification` | complete immutable clauses/facts/signature |
| `ReducedABoxOnlyClausification` | safe assertion-only delta path |

Strip code paths whose only inputs are SWRL or description graphs. Do not strip ordinary
OWL keys/property chains/negative assertions because they share structural machinery.

Authoritative pipeline:

1. Identity-preserving pyowl-core `OntologyView` capture, strict import closure, and
   pyHermiT OWL 2 DL validation.
2. Simplification/normalization with deterministic internal definitions.
3. Built-in properties and regular role NFA compilation (upstream deliberately avoids
   unsafe/explosive determinization).
4. Clausify to immutable clauses, facts, signatures, and expressivity.
5. Choose blocking/expansion components from actual code defaults.
6. Initialize append-only indexed state.
7. Scheduler: annotated equalities; deltas; permanent/query hyperresolution; unknown/
   known datatype checks; new annotated equalities; deterministic fixed point;
   existentials; a ground-disjunction branch; dependency-directed clash backjump;
   validated-block recheck before SAT.
8. Reduce services to consistency checks and safe cached/optimized classification/
   realization operations.
9. Support limited safe ABox incrementality; conservatively rebuild other changes.

## 10. Public API mapping

Retain semantic groups, not OWLAPI signatures/wrappers:

| HermiT group | Python contract |
|---|---|
| construction/root/config/dispose/interrupt | `Reasoner` lifecycle/properties/context manager |
| buffering/pending/flush | core delta/overlay and transactional private-session update API |
| precomputable/precompute/status | `InferenceType` methods |
| consistency/satisfiability/subsumption | exact bool/check services |
| axiom/set entailment/support | exhaustive logical axiom services |
| class hierarchy/equivalent/super/sub/bottom/disjoint | immutable hierarchy/node sets |
| object property hierarchy/inverse/domain/range/disjoint | object-property services |
| data property hierarchy/domain/disjoint | data-property services |
| types/instances/same/different | realization services and configured grouping |
| object/data values/instances/relationship checks | exact property services |

OWLAPI factories, `Node` wrappers, change listeners, Java `Version`, serialization,
pretty hierarchy dumps, and `getTableau()` internal escape hatches are not public
compatibility requirements. Equivalent Python values/results/errors are.

## 11. Java dependencies and replacement fate

Pinned direct dependencies:

| Java dependency | Fate |
|---|---|
| OWLAPI 4.2.8 | replace public structural/readers/resolver functions with pyowl-core; retain only pyHermiT profile/result/compiler behavior |
| Apache Axiom | replace with hardened XML/XMLLiteral implementation |
| dk.brics automaton | replace with tested role/XSD-regex automata |
| JAutomata | replace with internal role NFA |
| Commons Logging | Python structured warnings/events/logging |
| GNU java-getopt | removed with CLI |
| Protege editor | removed |
| JUnit | pytest/Hypothesis/native Rust tests |

None is shipped or invoked. Parsing stays in pyowl-core and outside the reasoning kernel.
Required input formats are the compatible core release's documented formats, not every
format OWLAPI happened to support.

### 11.1 Other Python ports are not references

As of the specification date, PyPI contains a separate
[`hermit-reasoner`](https://pypi.org/project/hermit-reasoner/) project using the public
import package `hermit`. It targets a different scope (including SWRL/Datalog), API,
license, and conformance state. It is neither a dependency nor a correctness/provenance
oracle, and agents must not copy from it opportunistically. Independent comparisons may
be added only as nonnormative benchmarks with explicit provenance. The planned import
package remains `pyhermit`; WP00 must verify/reserve the normalized distribution name
before publication and record any required distribution-name change without changing
the stable import name.

## 12. Upstream test fate

The snapshot has 60 Java test sources and 124 fixtures (83 `.owl`, 22 `.txt`, 13 `.xml`,
6 `.rdf`). Root `AllTests` consists of `AllQuickTests` plus heavy reasoner tests. A
checked-in historical report records 1,269 passed in 30.20 seconds, but is evidence, not
the pyHermiT release budget.

Required semantic-intent families:

- reasoner datatype classes: `DatatypesTest`, `NumericsTest`, `RDFPlainLiteralTest`,
  `AnyURITest`, `FloatDoubleTest`, `DateTimeTest`, `BinaryDataTest`, `XMLLiteralTest`;
- core black-box: `ReasonerTest`, individual reuse/core blocking,
  `ComplexConceptTest`, `EntailmentTest`, `RIATest`, `SimpleRolesTest`,
  `OWLReasonerTest`;
- heavy classification and individual-reuse classification;
- tableau: tuple index/table, DL-clause evaluation, dependency sets, NI, merge;
- structural normalization/clausification/datatype clausification; and
- applicable OWL WG consistency/inconsistency/entailment/non-entailment manifest cases.

Excluded feature behavior: `RulesTest`, `DatalogEngineTest`, description-graph cases,
and OWLLink transport. Extract the many core import/update/classification/realization/
open-world cases from `OWLLinkTest` despite its class name.

The root quick suite commented out structural tests due parse-order-generated names;
pyHermiT fixes determinism and reinstates semantic/alpha-normalized tests.
`BlockingValidatorTest` was not in `tableau.AllTests`; bring its semantic cases in.
`known-test-failures.txt` describes pre-OWLAPI-4 history and supplies regression leads,
not an accepted failure list.

Fixture redistribution is conditional on the provenance rules in `verification.md` and
`deviations.md`.

## 13. Excluded extras checklist

The following must not appear as implemented/shipped core claims:

- DL-safe SWRL (including its incomplete transitive/chain behavior);
- description graphs;
- datalog/conjunctive/SPARQL/OWL-BGP query engines;
- Protege/OSGi/update-site integration;
- OWLLink transport/server;
- Swing debugger/history/interactive commands/pause timers;
- GNU-getopt Java CLI compatibility;
- explanation/minimal-justification tooling;
- example materializers and Java examples;
- Maven assembly/deployment/nightly scripts or bundled JARs; and
- RDF-Based Semantics/OWL Full reasoning.

An input containing an excluded semantic extension is rejected explicitly. An excluded
UI/integration simply has no public module. Standard OWL 2 behavior is never labeled an
extra merely because an upstream extra test happens to cover it.

## 14. License reference

Pinned HermiT states `LGPL-3.0-or-later`. The recorded owner decision (2026-07-17,
`deviations.md` LIC-001) adopts `LGPL-3.0-or-later` for pyHermiT under the source-guided
implementation mode; `LICENSE` carries the LGPL-3.0 text, `COPYING` the GPL-3.0 text it
incorporates, and `NOTICE.md` the upstream attribution. LIC-001 still blocks release until
file headers, the provenance inventory, source obligations, and artifact metadata are
executed and audited. Removing Java third-party JARs does not remove obligations for
source-guided/directly adapted HermiT material.
