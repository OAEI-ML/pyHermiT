# WP06 evidence — deterministic clausification and compiled IR

## Implemented contract

- `pyhermit.clauses` compiles every normalized axiom family through an explicit,
  exhaustiveness-checked handler table into immutable terms, predicates, clauses, facts,
  ground disjunctions, role/datatype metadata, provenance, and expressivity records.
- Dense IDs and canonical bytes are deterministic across input permutations and Python hash
  order. Variables are alpha-canonical, records validate their full relational invariants,
  and canonical JSON rejects non-canonical or unknown input.
- Query overlays append query-local domains without mutating the permanent program. Delta
  compilation returns directly applicable assertion facts only when safe and otherwise requests
  a rebuild. The backend protocol consumes these same concrete records without a second schema.
- Object-role automata, top/bottom properties, qualified cardinalities, annotated equality,
  HasKey named guards, negative assertions, custom datatype definitions, source literals, and
  semantic data identities remain explicit in the compiled model.
- `compile_captured` consumes the immutable pyowl-core view directly. The boundary test checks
  object identity for the captured axiom tuple and verifies that no public ontology/model copy is
  introduced by clausification.
- Cooperative cancellation is polled while role metadata and clause records are built.

The language-neutral schema input is
`tools/clausification/compiled-ir-schema-v1.json` (SHA-256
`20eb1c948b3e15e37da7d12c1f1b22abb49c8419162b8e5a94b6f0896cd12b9d`).

## Correctness evidence

The focused suite covers the complete handler table, typed-domain declarations, permutation and
hash-seed determinism, canonical round trips, u32 and cross-record validation, variable safety,
role NFAs, cardinalities, nominals/NI, HasKey, negative object/data assertions, top/bottom
properties, punning, custom and opaque datatype ranges, semantic literal payloads, linear n-ary
disjointness, query isolation, delta application, limits, and cancellation.

Independent bounded-model evaluators compare compiled propositional and relational clauses over
all interpretations in their finite domains. A small forward application harness separately
exercises NFA universals, equality, keys, custom ranges, negative subproperties, overlays, and
delta rows. The checked-in Java semantic-shape projection is pinned to HermiT commit
`37ec30aced32ac81ebecc5e33fad255ddefcb4c3`; its artifact SHA-256 is
`dd0d5bb9101a96944107723efa6104813ebfa9441e05ea73a2d3398b1755bc68`.
Java is a development oracle only and is neither invoked nor packaged at runtime.

Validation on macOS 26.5.2 x86_64:

| Gate | CPython 3.10.11 | CPython 3.12.3 |
|---|---:|---:|
| WP06 clauses/role boundary/backend protocol/reference policy | 67 passed | 67 passed |
| repository suite available in the local reference environment | 481 passed + 4 subtests | 481 passed + 4 subtests |
| canonical benchmark digests | identical | identical |
| Ruff (Python 3.10 target) | clean | same source tree |
| strict MyPy | 79 source files clean | same source tree |
| import-linter | 2 contracts kept | same source tree |

The repository run excludes only
`tests/unit/tableau_state/test_dependencies_trail.py`: that unrelated WP08 property test imports
the declared `hypothesis` development extra, which was not installed in either local reference
environment and could not be downloaded in the restricted test session. No WP06 test was skipped.

## Reproducible scale probe

Command, run independently with each reference interpreter:

```text
PYTHONPATH=src:../pyOWLCore/src <python> benchmarks/bench_wp06_clausification.py \
  --axioms 1000 --disjoint-classes 1000 --samples 5 --cancellation-axioms 20000
```

The script SHA-256 is
`25089486196f6f5406409c08b19c1bb6ea1e24f608a47b47f16490661f0afa18`.

| Measurement | CPython 3.10.11 | CPython 3.12.3 |
|---|---:|---:|
| 1,000-axiom median compile | 2.3544 s | 2.2555 s |
| median throughput | 424.7 axioms/s | 443.4 axioms/s |
| compile result | 2,257 predicates; 1,758 clauses | same |
| compile digest | `e6373f0f...190d2` | `e6373f0f...190d2` |
| 1,000-way disjoint median | 1.7708 s | 1.5308 s |
| disjoint result | 2,004 predicates; 3,004 clauses | same |
| disjoint digest | `a98b3bf8...9ef98e` | `a98b3bf8...9ef98e` |
| cancellation p95 total (5 ms deadline) | 5.0577 ms | 5.0508 ms |
| cancellation p95 after deadline | 0.0577 ms | 0.0508 ms |

The n-ary disjoint probe confirms bounded linear output (3.004 clauses per source class), not
pairwise quadratic expansion. These are pure-Python preprocessing measurements, not an
end-to-end reasoner or Java-relative speed claim. Later native work packages may accelerate the
same canonical contract without changing its bytes or semantics.
