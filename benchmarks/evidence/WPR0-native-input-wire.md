# WPR0 production native input wire evidence

Date: 2026-07-18

This tranche replaces the semantic gap behind the original structural `wire.rs`
skeleton with an isolated production input codec. It does not enable
`full_reasoner` or native automatic selection.

## Boundary and ownership

- Python entry points are exactly:
  `encode_ontology(CompiledOntology) -> bytes`,
  `encode_config(ReasonerConfig) -> bytes`,
  `encode_query(clauses.CompiledQuery) -> bytes`, and
  `encode_delta(clauses.CompiledDelta) -> bytes`.
- Rust entry points consume an owned `Vec<u8>` plus `&DecodeLimits` and return
  `DecodedOntology`, `DecodedConfig`, `DecodedQuery`, or `DecodedDelta`.
- No OWL text/RDF, pickle, bincode, native layout, Python callback, nested object
  graph, or per-axiom call crosses the boundary.
- The decoder drops the source buffer after constructing language-neutral owned
  records. No borrowed Python memory can survive decoding or GIL release.

Schema v1 uses an eight-byte magic, document kind, version, zero flags, `u64`
lengths, SHA-256 content hash, and a checked directory of aligned sections. Every
scalar is fixed-width little endian. Raw string/blob pools and fixed records use
`u32` offsets/counts; absent optional IDs use only the documented `u32::MAX`
sentinel.

## Complete semantic coverage

The ontology/program path retains and validates all concrete `ClauseProgram`
fields:

- all eight dense symbol domains, raw canonical keys, displays and generated/query
  flags;
- all 19 predicate kinds, arbitrary data-range arity, sorts, cardinality/filler,
  role/symbol references, annotations and internal keys;
- variable/individual/data terms with source-literal and data-identity IDs kept in
  separate domains;
- clauses, join orders, positive/negative facts, ground disjunctions and exact
  provenance;
- inverse roles, simple/data/complex inclusions, non-simple components, complete
  NFAs including epsilon transitions, and built-in IDs;
- literal identities, datatype definitions, unknown datatype IDs, and canonical
  semantic payloads;
- expressivity, declared entities, named individuals, core versions, three source
  fingerprints, ontology fingerprint, and permanent-program SHA-256 binding.

Queries retain the permanent SHA binding, all eight prefix cutoffs, predicate
cutoff, optional complete overlay, rebuild reason and result interpretation.
`DecodedQuery::validate_against` checks the digest and byte-semantic predicate/symbol
prefixes against a decoded session ontology. Deltas retain both revision hashes,
compatibility, source digests, exact fact additions/removals and reasons;
`validate_revision` checks the base binding, predicate/term domains, sorts and
polarity.

The datatype JSON is not treated as an accepted opaque extension. The input reader
checks canonical RFC 8259 form and retains every byte; loader integration must pass
it to the existing exact native `datatypes::decode_datatype_range_model` and each
literal payload to `datatypes::decode_literal_semantic`. This is the explicit typed
construction seam for WPR3's already-delivered datatype records.

## Hostile-input controls

- A 512 MiB hard document cap plus configurable byte, string, section and record
  limits are checked before record-vector allocation.
- Offset addition, record multiplication, range ends and alignment use checked
  arithmetic before slicing or allocation.
- Directory overlap, gaps with nonzero padding, trailing bytes, duplicate sections,
  unknown required sections, count/length mismatches and content-hash corruption fail
  deterministically. Explicitly optional diagnostic sections are skipped only after
  the same directory, coverage, alignment and resource-limit validation.
- Every enum, reserved bit, UTF-8/string/blob reference, term sort, arity, dense ID,
  role/datatype/predicate/filler/provenance reference and query prefix is checked.
- Focused semantic-corruption tests modify valid predicate enums, term sorts, ground
  predicate IDs, string offsets and inverse-role ranges, recompute the outer hash,
  and prove the inner validator still rejects them.

## Reproducible golden and checks

`tools.wire.build_native_input_fixture` emits canonical JSON only. The checked
`tests/data/native-input-v1.json` contains SHA-bound role/disjunction ontology,
datatype/literal ontology, config, overlay-query, rebuild-query and delta bytes.
Python proves byte identity with a fresh generator run; Rust independently decodes
those exact bytes and asserts owned semantic fields.

Commands run from this checkout:

```text
PYTHONPATH=src:../pyOWLCore/src .reference/venv310/bin/python -m pytest tests/unit/backends/test_native_input.py -q
5 passed

PYTHONPATH=src:../pyOWLCore/src .reference/venv312/bin/python -m pytest tests/unit/backends/test_native_input.py -q
5 passed

cargo test --no-default-features --test input_wire
8 passed

cargo test --no-default-features
192 unit + 8 input-wire integration + 6 operation-bridge integration tests passed

cargo clippy --no-default-features --test input_wire -- -D warnings
passed

PYTHONPATH=src:../pyOWLCore/src .reference/venv310/bin/python -m ruff check <new Python files>
passed

PYTHONPATH=src:../pyOWLCore/src .reference/venv310/bin/python -m mypy --cache-dir=/tmp/pyhermit-input-wire-mypy3 src/pyhermit/backends/native_input.py
passed
```

The Python test also constructs, validates and bulk-encodes a 20,000-individual /
20,000-fact ontology in one document. The dual deterministic/hash/large-object test
took 2.47 seconds on the recorded local Python 3.10 run; that includes construction
and Python IR validation, not only byte packing, so it is evidence against per-fact
FFI rather than a release throughput baseline.

## Integration seam (not part of this isolated commit)

The PyO3 owner should add `pub mod input_wire;` in `native/src/lib.rs`, decode the
two `create_session` byte arguments with one shared `DecodeLimits`, verify core
metadata and config, then store `DecodedOntology`/`DecodedConfig` in session-owned
state. Query and delta methods call their decoders followed by the binding methods
before opening an operation transaction. `InputWireError.code` maps once to the
existing version/wire/resource native error taxonomy. No change to `wire.rs`, the
PyO3 boundary, session/tableau/result wire, or feature handshake is included here.
