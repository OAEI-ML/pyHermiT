# WP07 numeric/Boolean foundation benchmark

This evidence covers only the first pure-Python WP07 tranche: core-literal capture,
numeric/Boolean lexical compilation, exact identity records, numeric interval algebra,
finite enumeration, and cooperative cancellation. It is not tableau, native-backend,
or Java-relative evidence and does not mark full WP07 complete.

## Implemented contract

- `CompiledLiteral` retains the exact `pyowl_core.Literal` object and separately stores
  its source structural token, data-domain identity, and comparison record. Integer,
  decimal, and rational aliases share a reduced arbitrary-precision numeric identity;
  Boolean identity cannot collide with Python/numeric zero or one.
- OWL2 lexical mode implements all integer-derived bounds, exact decimal syntax, the
  OWL rational grammar, and the four Boolean lexical forms. It agrees with
  `pyowl_core.validate_lexical_form` wherever core 0.1 exposes the same boundary.
- The explicitly selected `hermit-37ec30a` key isolates pinned source observations:
  case-insensitive/trimmed Booleans, Java `BigDecimal` exponent forms, and a leading
  plus on rational denominators. Source spelling remains untouched in every mode.
- Immutable numeric intervals retain open/closed rational endpoints. Domain membership
  models `integer ⊆ decimal ⊆ rational ⊆ real`; intersection, same-domain
  union, family-relative complement, exact emptiness, finite cardinality, and bounded
  enumeration are implemented. Boolean ranges provide the corresponding exact
  two-element algebra.
- Character, digit, exponent/scale, and enumeration limits fail with stable pyHermiT
  resource errors. Large-number conversion and enumeration poll the shared cancellation
  token. Numeric identities serialize as signed hexadecimal rational components so
  Python's ambient decimal-string safety cap cannot change or reject a value.

The source-guided projections cover pinned HermiT
`NumericsTest.testMinInclusiveInt`, `testMaxInclusiveInt`, `testMinMaxEqual_*`, and
`testDecimalMinusInt_*`, plus `DatatypesTest.testRationalConversion`,
`testDifferentLexicalForms`, `testNegZero*`, and `testRationals*`. The consulted
production classes are `OWLRealDatatypeHandler`, `Numbers`, `NumberInterval`,
`OWLRealValueSpaceSubset`, and `BooleanDatatypeHandler` at immutable commit
`37ec30aced32ac81ebecc5e33fad255ddefcb4c3`.

## Method

`benchmarks/bench_wp07_datatypes.py` performs one warmup plus ten measured samples for:

- compilation of 10,000 already-constructed core literals, evenly split across
  integer, decimal, rational, and Boolean inputs;
- 10,000 mixed integer/decimal interval operations;
- one exact 10,000-digit integer compilation; and
- a 100,000-digit CPU-bound parse with a 5 ms cooperative deadline.

Every measured semantic workload checks a deterministic result digest across samples.
The runner enforces provisional five-second component budgets, a two-second large-number
budget, and the project-wide cancellation p95 below 250 ms.

## Local results

Runner: macOS 26.5.2, x86_64. Results were captured on 2026-07-17.

| Python | 10k compile median | throughput | range median | 10k-digit median | cancellation p95 |
|---|---:|---:|---:|---:|---:|
| 3.10.11 | 0.290 s | 34,466/s | 0.514 s | 0.00331 s | 0.00943 s |
| 3.12.3 | 0.298 s | 33,512/s | 0.349 s | 0.00283 s | 0.00516 s |

Cross-version semantic evidence was identical:

- compile digest: `ae913bd79981f70638d9dfbfe3c33935c4fc2d543d9d337b16ba7e8346c48e27`;
- range digest: `05e7b37bfe249a93a990e2e6b218721f26264fa3444c98ac8d8d8218a927eb0e`;
- 10,000-digit identity digest:
  `8ce45991991fd07e2e5698c283e8f3bdd038a7baad920c6ce7f2a0382e4c62b3`; and
- all cancellation samples aborted through the shared pyHermiT token.

## Reproduction

```text
PYTHONPATH=src:../pyOWLCore/src .reference/venv310/bin/python \
  benchmarks/bench_wp07_datatypes.py
PYTHONPATH=src:../pyOWLCore/src .reference/venv312/bin/python \
  benchmarks/bench_wp07_datatypes.py
```

No regression percentage is claimed because this is the first accepted component
baseline. Future changes can compare the same schema, workload counts, and result hashes.

## Correctness and isolation gates

- Python 3.10 and 3.12: 81/81 datatype tests pass on each interpreter.
- Python 3.12 complete repository suite: 340 tests and four subtests pass.
- Python 3.10 repository suite: 337 tests and four subtests pass when the one unrelated
  pre-existing Hypothesis test module is omitted; the local 3.10 verification environment
  does not contain the declared optional Hypothesis dependency.
- The generated integer range matrix exhaustively compares 10,000 pair intersections
  and unions plus every complement against a finite-set oracle; all Boolean subsets and
  pair operations are exhaustive.
- Ruff, strict mypy for all datatype sources, import-linter, Python 3.10/3.12 compileall,
  subprocess import isolation, and AST forbidden-import scans pass.
- Runtime datatype modules import no Java, JPype, RDF parser, native backend, normalization,
  clausification, or tableau package.

## Deliberately remaining WP07 acceptance

This commit does not implement or claim float/double, strings and language values,
binary, URI, XML, date-time, XSD regex/langRange/length facets, full mixed-family
OWL-data-domain union/complement, custom datatype definitions, the component constraint
solver, tableau SAT/UNSAT integration, Rust parity, or returned-literal query integration.
Those families and their ontology-level acceptance matrix remain open WP07 work.
