# WP07 conformance, language-tag, and witness evidence

This tranche completes the pinned component-level conformance inventory, exact
`rdf:langRange` behavior, and deterministic witness reconstruction requested before
native datatype work. It remains pure Python and does not start WPR3.

## Conformance inventory and ontology projections

- All 256 datatype-related methods in the pinned HermiT test inventory are hash-bound
  and assigned to an owning lane: 165 datatype-library methods in WP07, 32
  clausification methods in WP06, and 59 ontology/tableau methods explicitly deferred
  to WP12.
- The project-authored ontology projection inventory contains 24 pinned-source cases:
  12 HermiT and 12 W3C. Twenty-three execute as datatype SAT/UNSAT components. The W3C
  `inconsistent-integer-filler` case is marked tableau-only because its contradiction
  requires class subsumption; component tests do not overclaim it.
- External Java sources and W3C ontology bodies remain fetch-only. Runtime tests consume
  only project-authored projections and content-addressed factual metadata.

## Exact language-tag and witness behavior

- `LanguageTagRange` implements Boolean algebra over RFC 4647 basic-prefix predicates
  relative to the exact canonical BCP 47 structural universe exposed by pyowl-core.
  Duplicate variants/singletons, incomplete extensions, impossible one-letter primary
  prefixes, private-use tags, and finite grandfathered cells are handled without
  phantom cardinality.
- Plain-literal complement, emptiness, cardinality, enumeration, and facet membership
  use that tag algebra rather than treating tags as arbitrary nonempty strings.
- Every literal-denotable infinite family has deterministic concrete witness
  reconstruction. Regular-language witnesses use a DFA/exclusion-trie search and do
  not expand Unicode transitions one code point at a time.
- Infinite regions not denotable by a literal identity, notably
  `owl:real` minus `owl:rational`, use an explicit `SymbolicDataWitness` certificate
  keyed by a canonical range digest and stable ordinal. Solver assignments never use
  an ambiguous `None` sentinel and reconstruct distinct witnesses for inequality
  components deterministically.

## Benchmark

`benchmarks/bench_wp07_constraints.py` performs one warmup plus ten measured samples.
Each sample creates 2,000 exact tag/regex witnesses and solves twenty repetitions of
two 12-variable inequality cliques: one over `xsd:string`, and one over the irrational
part of `owl:real`. Every sample verifies stable result digests and a provisional
five-second median budget.

Runner: macOS 26.5.2, x86_64, captured 2026-07-17.

| Python | language median | language p95 | solver median | solver p95 |
|---|---:|---:|---:|---:|
| 3.10.11 | 0.127 s | 0.158 s | 0.300 s | 0.602 s |
| 3.12.3 | 0.124 s | 0.154 s | 0.258 s | 0.523 s |

Cross-version semantic evidence was identical:

- language/regex digest:
  `355e65e08f5d43b440e803fe0f96eafe48e4d4b156bdcfe9f220d59919a14dc7`;
- solver digest:
  `34da800c23df84a5ff82e1faf3033f2c8a88d680996df0aab8f6c419ddac3d75`;
- 2,000 language/regex witnesses and 480 solver assignments per measured sample.

Reproduce with either supported interpreter:

```text
PYTHONPATH=src:../pyOWLCore/src python3.10 benchmarks/bench_wp07_constraints.py
PYTHONPATH=src:../pyOWLCore/src python3.12 benchmarks/bench_wp07_constraints.py
```

## Correctness and isolation gates

- CPython 3.10.11: 244 datatype unit and pinned conformance tests pass.
- CPython 3.12.3: the same 244 tests pass.
- Ruff lint/format, strict mypy over 20 runtime/benchmark modules, and CPython
  3.10/3.12 compileall pass.
- The datatype isolation tests remain in the passing matrix: runtime code imports no
  Java, JPype, native backend, RDF parser, normalization, clausification, or tableau
  state.

## Explicit pre-Rust limitation

WPR3/Rust parity has not started. One standards-completeness item remains in WP07:
`xsd_regex.py` intentionally rejects `\p{Is...}` Unicode block escapes until a
content-addressed OWL/XSD-normative block inventory and its redistribution decision are
pinned. Unicode general-category escapes are currently deterministic on UCD 3.2.0,
but that does not substitute for the missing block-name table. This limitation is
reported rather than silently approximated with the host Unicode database.

The 59 HermiT ontology/tableau methods and the one W3C tableau-only projection are WP12
integration work, not unimplemented datatype-library behavior.
