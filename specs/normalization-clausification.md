# Normalization, roles, and clausification

This layer converts a validated OWL 2 DL import closure into immutable DL clauses and
facts suitable for hypertableau reasoning. It is deterministic and backend-neutral.

Primary upstream references at the pinned commit:

- [`structural/OWLNormalization.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/structural/OWLNormalization.java)
- [`structural/OWLClausification.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/structural/OWLClausification.java)
- [`structural/ObjectPropertyInclusionManager.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/structural/ObjectPropertyInclusionManager.java)
- [`structural/BuiltInPropertyManager.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/structural/BuiltInPropertyManager.java)
- [`model/DLClause.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/model/DLClause.java)
- [`model/DLOntology.java`](https://github.com/phillord/hermit-reasoner/blob/37ec30aced32ac81ebecc5e33fad255ddefcb4c3/src/main/java/org/semanticweb/HermiT/model/DLOntology.java)

The formal semantic obligation is equisatisfiability and query-preserving reduction
under [OWL 2 Direct Semantics](https://www.w3.org/TR/owl2-direct-semantics/). Tests also
require pinned-HermiT parity, but Java parse-order-generated symbol names are
canonicalized before comparison.

## 1. Stages and ownership

```text
validated OntologyView with a strict resolved closure
→ expression NNF/canonical simplification
→ normalized axiom records with polarity-aware definition introduction
→ role hierarchy, simplicity, regularity, and automata
→ DL clausification and ground facts
→ clause safety/canonicalization/deduplication
→ expressivity summary and immutable CompiledOntology
```

`normalize/` owns structural rewrites and deterministic fresh definitions. `roles/`
owns property hierarchy and automata. `clauses/` owns the IR and clausifier. None may
import a tableau backend. They iterate core closure/index views directly and never mutate,
flatten, or copy the public view merely to establish ownership.
Compilation explicitly requests canonical iteration/bulk views; default view iteration order
is never used for IDs, generated names, clauses, or branch ordering.

## 2. Normal forms

### 2.1 Negation normal form

Negation is pushed to atomic classes, nominals, or data-range atoms using exact duals:
intersection/union, some/all, minimum/maximum cardinalities, and data-range operations.
Cardinality duals handle zero without underflow. Double complement is removed. Built-in
top/bottom simplifications are applied only when valid for the expression sort.

The normalized public-expression representation MUST NOT contain a complement whose
operand is a compound class expression. Data-range complements remain explicit where
required by datatype constraints.

### 2.2 Definition introduction

Complex subexpressions are named by deterministic internal atomic concepts. Direction
of the defining implication is selected from positive/negative occurrence so that the
translation is equisatisfiable and does not add an unintended converse. If both
polarities occur, both required directions are emitted.

The key for a definition is `(ontology logical hash, expression canonical bytes,
polarity class)`. The same expression reached through different axioms or parse orders
reuses the same name. Internal names are never treated as declared or returned to a
caller.

### 2.3 Axiom normalization obligations

| Input family | Normalized obligation |
|---|---|
| `SubClassOf(C,D)` | implication from normalized `C` to normalized `D` |
| `EquivalentClasses` | cycle/pair of subclass implications preserving all operands |
| `DisjointClasses` | pairwise impossibility clauses, without quadratic materialization when a safe shared encoding is used |
| `DisjointUnion` | equivalence to the union plus pairwise disjointness |
| domains/ranges | role-edge implication to a class/data constraint on the correct endpoint |
| property characteristics | exact first-order/DL consequences; functionality becomes equality-producing constraints |
| assertions | positive/negative ground facts or query-safe normalized definitions |
| same/different individuals | equality/inequality ground facts |
| `HasKey` | named-individual guarded clauses exactly matching Direct Semantics |
| datatype definition | acyclic datatype definition recorded in `DatatypeModel` and referenced by constraints |

`ObjectHasValue` and `ObjectOneOf` use nominal individuals, not fresh unconstrained
concepts. Negative property assertions remain explicit negative facts/predicates and
can produce clashes. `owl:Thing`, `owl:Nothing`, top/bottom properties, and
`rdfs:Literal` receive their exact built-in treatment even if absent from the source
signature.

## 3. Role processing

### 3.1 Canonical role graph

Every named object property has a canonical forward and inverse role. The graph closes
simple subproperty, equivalence, and inverse axioms. It records complex chain
inclusions separately and computes strongly connected components deterministically.
Data properties have a separate hierarchy and cannot enter object-role automata.

The same graph supplies profile validation and clausification. A post-validation
assertion checks that all cardinality/self-sensitive roles are simple.

### 3.2 Complex inclusions and automata

Regular complex role inclusions are converted to finite automata following HermiT's
property-inclusion manager. Automata:

- preserve direction and inverse transitions;
- include transitivity as the appropriate self-composition language;
- are not determinized when that can cause avoidable exponential growth, matching the
  upstream performance/correctness choice;
- use stable state numbering from canonical traversal;
- eliminate unreachable states and duplicate transitions; and
- produce propagation clauses/guard predicates with documented provenance.

The automaton language must accept exactly the role chains that imply its target role.
Property-based tests compare bounded generated words with a slow graph-language oracle,
including inverses, SCCs, transitivity, and overlapping chain prefixes.

### 3.3 Built-in properties

Top and bottom object/data properties are represented explicitly in the role model.
Their universal/empty interpretations are implemented through clauses and specialized
checks that avoid materializing a quadratic top-property relation. Optimizations MUST
be observationally indistinguishable from the Direct Semantics and cover empty
signatures and freshly introduced individuals/data values.

## 4. DL-clause IR

### 4.1 Terms, predicates, and atoms

```python
Term = Variable(index: int) | IndividualTerm(individual_id: int) | DataConstant(source_literal_id: int)

@dataclass(frozen=True, slots=True)
class Atom:
    predicate: PredicateRef
    arguments: tuple[Term, ...]

@dataclass(frozen=True, slots=True)
class DLClause:
    body: tuple[Atom, ...]       # conjunction
    head: tuple[Atom, ...]       # disjunction; empty means false
    provenance_id: int
```

Predicate kinds include atomic/negated concepts, atomic/negated object and data roles,
data ranges and their negations, equality, inequality, at-least restrictions,
annotated equality used by the nominal-introduction rule, internal automaton states,
and internal ordering guards used only to suppress symmetric duplicate matches.

Every predicate declares arity and argument sorts. Equality never compares object and
data nodes. Ordering guards have no ontology semantics and cannot occur in a public
query/result.

Each `DataConstant` resolves through the literal table to both a data-domain identity
ID and a datatype comparison record. Clause equality/inequality and cardinality use
the identity ID; facet/range predicates use the comparison record; returned property
answers retain the source-literal ID. Compilers and backends may intern each layer, but
must not substitute comparison-equality for data-value identity.

### 4.2 Clause invariants

1. Variables are dense `0..n-1` in first canonical occurrence order.
2. Every head variable occurs in a positive, range-restricted body position unless the
   specialized predicate rule explicitly creates a witness.
3. Body and head atoms are canonicalized and de-duplicated; body order is a compiled
   join plan, not source order.
4. Tautological clauses are removed; contradictory or empty-body clauses are preserved
   with exact meaning.
5. Equality/inequality and annotated-equality arguments satisfy their ordering and
   sort invariants.
6. Each clause points to one or more source axioms/generated definitions through a
   compact provenance table used for diagnostics, never rule truth.
7. No unsupported OWL construct is discarded while producing the IR.

### 4.3 Facts and ground disjunctions

Ground unit heads/bodies are extracted into positive/negative facts when doing so is
semantics-preserving. Nondeterministic ground consequences remain
`GroundDisjunctionIR`. An empty-head ground clause produces an initial clash. Duplicate
facts combine provenance but do not create duplicate extension rows.

Named individuals receive `owl:Thing`/internal-named membership when required. If the
ontology has no individuals, tableau initialization still creates one anonymous root
so the object domain is nonempty.

## 5. Clausification by construct

The implementation must maintain a reviewable table in code/tests mapping every model
constructor to a handler. At minimum the following interactions require dedicated
goldens, not only isolated happy paths:

- universal restrictions propagated through simple roles, inverses, and role automata;
- qualified min/max/exact cardinality with equality and pairwise inequality;
- nominals combined with inverse roles and number restrictions;
- keys restricted to named individuals and named shared key values;
- negative object/data property assertions through equivalent/subproperties;
- disjoint and bottom properties;
- reflexive/self restrictions and top object property;
- custom datatype definitions, complements, enumerations, and facets;
- ABox assertions containing complex class expressions;
- punning without cross-sort predicate collision; and
- additional query axioms compiled without mutating the permanent ontology.

Exact rewrite shapes may improve on Java. The gate is equisatisfiability, all public
query answers, deterministic IR, and the focused parity fixtures.

## 6. Query and delta compilation

Entailment/satisfiability reductions create `CompiledQuery` using the same normalizer
and clausifier. Query-local symbols are namespaced by the private compiled fingerprint plus query
hash. A query may reuse permanent definitions but cannot alter permanent role axioms or
expressivity in-place; if it introduces an incompatible role/nominal/non-Horn feature,
the session reports rebuild-required and a temporary full compiled ontology is used.

`CompiledDelta` classifies changes into:

- assertion-only additions/removals eligible for a proven incremental path;
- declaration/signature-only changes;
- changes requiring normalization/role/tableau rebuild; and
- imports/profile-invalidating changes rejected before backend mutation.

Correct full rebuild is always preferable to an unsound incremental shortcut.
The public change source is always a core `OntologyDelta`/`OntologyOverlay`; `CompiledDelta`
is a private backend optimization and cannot become an alternative revision truth.

## 7. Expressivity summary

The compiled ontology records booleans/sets needed for safe strategy selection:
inverse roles, nominals, datatypes, unknown datatype restrictions, complex roles,
number restrictions, keys, non-Horn clauses, bottom properties, and ABox presence.
This summary is derived from final IR and cross-checked against source constructs.
Changing it cannot change semantics; strategy tests force every legal alternative.

## 8. Verification and acceptance

Required tests include:

- upstream structural normalization/clausification cases, with generated-name
  canonicalization rather than raw string equality;
- one unit/golden case per model constructor and polarity;
- randomized semantic differential tests on small finite-model-checkable fragments;
- invariant validation and canonical JSON round trips for every compiled IR;
- parse/axiom/import-order permutation producing byte-identical canonical IR;
- automaton bounded-language equivalence tests;
- permanent-query isolation and delta classification tests; and
- both backends accepting the same IR schema without repair/coercion.

Completion requires no handler default that ignores an axiom and no catch-all clause
translation without an explicit constructor exhaustiveness check.
