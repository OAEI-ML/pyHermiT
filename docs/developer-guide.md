# Developer guide

## Architecture and ownership

The runtime pipeline has one public-model boundary:

```text
pyowl-core OntologyView
  -> identity/import/profile validation
  -> deterministic normalization
  -> clauses, facts, roles, datatype model
  -> immutable CompiledOntology
  -> Python or Rust session
  -> entailment, classification, realization
  -> canonical public values
```

`src/pyhermit/inputs.py` coerces an input once and retains a compatible core view by
identity. `core.py` freezes fingerprints and view metadata. `normalize/`, `clauses/`,
`roles/`, and `datatypes/` construct the private IR; `backends/python/` supplies the
readable complete fallback; `native/` owns the Rust engine and wire decoders;
`services/classification.py`, `services/realization.py`, and `facade.py` expose
backend-neutral services.
No backend creates a second public OWL model.

## Calculus and state

Normalization is deterministic and generated symbols are based on canonical structure,
not traversal allocation. The clause program separates positive/negative atoms, facts,
ground disjunctions, role automata, datatype constraints, and provenance. The tableau
combines hyperresolution, dependency-directed branching/backjumping, equality merges,
nominals/cardinality handling, existential expansion, blocking, role propagation, and
datatype components.

Permanent and query operations have explicit roots. A clash, timeout, cancellation,
resource failure, or verification mismatch must either commit a complete immutable
result or restore the root; no partial cache is published. Native and Python schedules
may differ, but their normalized public answers and error classes/codes may not.

## Native boundary

The Rust extension consumes one contiguous, versioned private-IR document when a session
is created. There is no per-axiom FFI callback and no Python semantic callback inside
native reasoning. The handshake checks package version, core API/model/wire versions,
native ABI, IR schema, capabilities, and a self-test. `auto` selects once; an explicitly
requested native backend never silently falls back after a semantic failure.

Unsafe Rust is forbidden by the crate policy. Resource accounting uses deterministic
saturating counters, while timeout/interrupt observation is cooperative. Backend IDs,
branch order, witness identities, and allocation details never cross the public facade.

## Tests and exact comparison

Tests are layered across unit invariants, integration services, committed pinned-HermiT
goldens, Python/native/verify parity, generated interactions, packaging, and performance.
Semantic comparison is exact: Boolean outcomes, equivalence grouping, directness,
literal identity, exception category, and canonical result digests must agree. A timeout,
resource error, and logical answer are distinct outcomes.

The committed [coverage matrix](../reports/coverage-matrix.json) is checked against every
live public `Reasoner` member and the current `pyowl_core.MODEL_CONSTRUCTORS` count.
The schemas in `reports/schema/` are closed to unexpected fields, and release tests verify
that every evidence path exists and each recorded status reduces to the overall report.

The development-only Java oracle under `tools/reference/` is hash-pinned, staged outside
runtime artifacts, network-disabled during execution, and used only for differential
evidence. Ordinary tests and installed packages never invoke it. Golden regeneration is
an explicit reviewed operation.

## Performance evidence

Benchmarks must record input/config/result hashes, cold versus warm phases, all raw
samples, median/dispersion, peak RSS, backend/capability data, and timeout/resource
outcomes. Shared-view measurements begin with the same already-loaded object; standalone
measurements include core loading. Python/native/Java comparisons are accepted only on a
dedicated recorded runner and only after result hashes agree. Microbenchmarks guide
profiling but cannot satisfy the release gate.

## Provenance and release boundary

The implementation is source-guided from pinned HermiT behavior, with project-authored
code and explicit provenance inventories. `LICENSE`, `COPYING`, `NOTICE.md`,
`tests/data/PROVENANCE.toml`, `tools/specs/reference.toml`,
`reports/licensing/adapted-files.toml`, and `tools/specs/dependencies.toml` are part of
the audit surface. Runtime artifacts exclude
Java sources, JARs/classes, the oracle, reference downloads, and test-only goldens.

For `0.1.2`, the owner accepted the remaining 350-check licensed W3C execution, larger
live-reference sample, and controlled performance calibration as post-release follow-up.
The release workflow still requires the complete hosted native-wheel matrix. `LIC-001`
is waived as-is without claiming legal review. The exact scope is recorded in
[the owner release override](../reports/release/0.1.2-owner-release-override.md), and the
fail-closed checker permits publication only while that record remains valid.
