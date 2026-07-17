# WP07 built-in values and facets benchmark

This evidence covers the pure-Python float/double and nonnumeric built-in tranche:
source-preserving literal compilation, exact family identities/comparisons, family range
algebra, and the OWL facets implemented by this tranche. It is a component baseline, not
tableau, native-backend, or Java-relative performance evidence, and it does not mark the
whole WP07 work package complete.

## Covered behavior

- XML Schema float and double are parsed with integer arithmetic and
  round-to-nearest-even into explicit IEEE-754 bits. Their value spaces remain disjoint;
  signed zeros retain two data identities but one facet comparison point, and NaN is
  unordered and excluded by ordinary bounds.
- String/plain-literal derived values, language keys, both binary primitives, anyURI,
  XMLLiteral, dateTime, and dateTimeStamp have tagged immutable identity and comparison
  records. Offset aliases can compare equal without becoming one date-time identity.
- Inclusive/exclusive bounds, length/minLength/maxLength, pattern, and langRange compile
  through the stable `FacetRestriction`/`restrict_datatype` boundary. Illegal
  datatype/facet/value combinations fail before tableau work.
- IEEE ranks, date-time zoned/unzoned partitions, binary lengths, and symbolic string/URI
  regular languages provide exact containment, family-relative intersection, union,
  complement, and emptiness. Binary finite cardinality/enumeration is bounded.
- XML parsing rejects DTD/entity declarations and enforces node/depth limits. Numeric,
  binary, XML, regex, and enumeration paths use shared resource/cancellation controls.

The implementation remains independent of Java, JPype, native extensions, RDF parsers,
normalization, clauses, and tableau state. Remaining WP07 work includes mixed-family
data-domain algebra, custom datatype definitions, the component solver, ontology-level
SAT/UNSAT integration, Rust parity, and completing the pinned Unicode-block inventory for
all XML Schema pattern escapes.

## Method

`benchmarks/bench_wp07_builtin_facets.py` performs one warmup plus ten measured samples:

- compilation of 10,000 constructed core literals evenly distributed over float, double,
  token, language-tagged PlainLiteral, hex/base64 binary, anyURI, dateTime, XMLLiteral,
  and NCName;
- 20,000 typed membership checks over float bounds, string length/pattern, langRange,
  binary length, URI pattern, and date-time bounds; and
- symbolic regex intersection/complement/emptiness validation in every range sample.

Every measured workload verifies a deterministic semantic digest across samples. The
runner enforces provisional five-second median budgets for compilation and range work.

## Local results

Runner: macOS 26.5.2, x86_64, captured 2026-07-17.

| Python | 10k compile median | throughput | range median | range p95 |
|---|---:|---:|---:|---:|
| 3.10.11 | 0.583 s | 17,148/s | 0.223 s | 0.247 s |
| 3.12.3 | 0.564 s | 17,725/s | 0.193 s | 0.220 s |

Cross-version semantic evidence was identical:

- compile digest: `d1d9dad3757e895586058e342ef80ad9632abc9a0008cbf61a0348ab1e426783`;
- range digest: `defb3985b0ffacad80d64c4f1cd0b023997806410246c5ed8ba73c7abb6bdb84`;
- range hits: `10002`.

## Reproduction

```text
PYTHONPATH=src:../pyOWLCore/src .reference/venv310/bin/python \
  benchmarks/bench_wp07_builtin_facets.py
PYTHONPATH=src:../pyOWLCore/src .reference/venv312/bin/python \
  benchmarks/bench_wp07_builtin_facets.py
```

No regression percentage is claimed because this is the first accepted baseline for
these built-in families and facets.

## Correctness and isolation gates

- The 133-test datatype matrix passes under CPython 3.10.11 and 3.12.3.
- The complete CPython 3.12 repository suite passes: 425 tests and four subtests.
- The CPython 3.10 suite passes 422 tests and four subtests when the unrelated
  Hypothesis module is omitted; the local 3.10 environment lacks its compiled optional
  Hypothesis dependency.
- Deterministic IEEE round-trip tests cover seeded float32/float64 bit patterns, while
  boundary fixtures cover subnormals, normal transitions, overflow, infinities, NaN,
  and both zeros.
- Range tests exercise zero/NaN complements, binary cardinality, language products,
  regex intersection/complement/emptiness, and zoned/unzoned date-time bounds.
- Ruff lint/format, strict mypy for all datatype runtime modules, import-linter, and
  Python 3.10/3.12 compileall pass.
- Subprocess import isolation and AST dependency scans confirm that datatype runtime
  modules import no Java, JPype, native backend, RDF parser, normalization, clause, or
  tableau module.
