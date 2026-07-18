# WPR3 canonical native data-range wire evidence

This tranche decodes canonical `DataRangeSemanticPayload` and
`DatatypeSemanticModelPayload` JSON into exact native mixed-family ranges. It does not
reparse literal lexical forms and does not call Python or Java. Facet boundaries and
enumeration values are reconstructed from the canonical `data_identity` and
`comparison` records already emitted by Python.

The existing schema is semantically sufficient. Ordered facets carry exact numeric,
IEEE, or date-time comparison records; length facets carry exact nonnegative integer
identities; pattern and language-range facets carry untagged string identities; and
enumerations carry full data identities. Values above native `u64` length capacity fail
with a typed resource error rather than being truncated.

## Shared oracle

`range_wire_oracle.py` produces `range_wire_oracle_v1.json` deterministically from the
Python semantic compiler and mixed-domain evaluator. The fixture covers all seven
payload kinds, named acyclic definitions, opaque-policy behavior, all nine supported
facet IRIs, every disjoint family, identity aliases, dateTimeStamp family-relative
complement, exact membership and emptiness, and finite/infinite cardinalities. Its
finite cases include a 256-value binary range and a 2,130,706,433-value IEEE interval.

Regeneration check:

```text
PYTHONPATH=src:../pyOWLCore/src python3 \
  native/src/datatypes/range_wire_oracle.py --check
```

## Native verification

The new module was integrated in an isolated copy of the native crate, leaving shared
module and Cargo files untouched. Verification on 2026-07-18:

```text
cargo test --lib --no-default-features
# 146 passed, 0 failed

cargo clippy --lib --tests --no-default-features -- -D warnings
# passed
```

Dedicated hostile tests cover noncanonical and unknown fields, unsorted operands,
dangling and cyclic references, semantic depth, independent JSON nesting, byte and
node ceilings, cancellation, and reject/preserve opaque policies. Internal string/tag
product growth and DNF growth are bounded before downstream use.

## Solver seam

`NativeDataRange` owns its DNF and exposes `all`, `empty`, `intersection`,
`complement`, `cardinality_at_least`, exact finite identity enumeration, and `witness`.
Witnesses prefer deterministic concrete identities. Nonmaterializable regions use a
family-tagged symbolic witness with a SHA-256 digest of the canonical normalized DNF
and the first unused ordinal, so solver code never reconstructs private range state.
