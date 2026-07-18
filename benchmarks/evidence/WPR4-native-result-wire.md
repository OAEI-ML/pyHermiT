# WPR4 native result-wire evidence

Date: 2026-07-17

Scope: versioned compact buffers from the native service boundary into backend-neutral Python
result contracts. This tranche does not enable the native feature handshake or automatic backend
selection.

## Schema and validation

- Fixed 64-byte little-endian header with eight-byte magic, schema/result kind, flags, total
  length, item count, reserved field, and SHA-256 payload hash.
- A 512 MiB validation/output cap and checked count/offset/byte arithmetic before allocation.
- Fixed-width check/check-batch records with nanosecond timing and exact diagnostic counters.
- Canonical hierarchy partitions, offsets, member IDs, direct edges, and top/bottom node IDs.
- Canonical realization same-as partitions, direct-type rows, object/data target rows, and
  different-from group pairs.
- Closed delta-outcome discriminants and zero reserved/trailing bytes.
- Rust validates values before encoding; Python validates bytes before constructing
  `CheckResult`, `HierarchyIds`, `RealizationIds`, or `DeltaOutcome`.
- Python hierarchy contract validation now uses iterative linear DAG validation for the common
  single-parent/deep-taxonomy case instead of repeated whole-edge scans.

## Verification

- Rust focused result-wire tests: 4/4 passed.
- Rust unified no-default suite: 177 unit + 6 integration tests passed; doc tests passed.
- Rust strict all-target Clippy with warnings denied: passed.
- Python decoder/contract tests: 24/24 passed on CPython 3.10 and 3.12.
- Complete Python regression suite: 701 tests + 4 subtests passed on both CPython 3.10 and 3.12.
- Python Ruff and strict Mypy for the codec/protocol: passed.
- Hostile cases cover corrupt magic/schema/kind/flags/length/hash, non-Boolean checks, huge counts,
  truncated/overlapping logical tables, empty hierarchy nodes, cycles/redundant edges, invalid
  realization offsets/rows/group references, and noncanonical different-from pairs.
- A 10,000-node chain decodes and validates iteratively in the focused suite.

## Remaining integration

Native session operations must call these Rust encoders after an operation-local result has fully
committed. The Python native adapter must call the matching decoder and map compiled IDs back to
the retained symbol/literal tables. Input IR/query/delta encoding and the complete composite
tableau remain separate WPR4 work. `full_reasoner` must remain absent until those paths pass the
complete differential suite.
