# WPR4 complete native-service integration evidence

Date: 2026-07-18

Scope: local completion of the Python-independent Rust reasoning session, all public service
adapters, the exact Python/native verifier, and the capability handshake required for explicit
native use and one-time `auto` selection. This report supersedes the “remaining integration”
sections in the earlier WPR4 component-tranche reports; those reports remain useful historical
evidence for their isolated kernels.

## Completed boundary

- One Rust-owned permanent session now runs the compiled rule, branching, merge, nominal,
  existential, blocking, datatype, role, classification, and realization components without a
  Python semantic callback or Java runtime.
- Permanent and query operations use complete checkpoints. Query overlays are rolled back, and a
  satisfiable nondeterministic permanent model is restored to its branch-free root while its
  Boolean result is cached. Cancellation, resource errors, malformed input, and failed commit or
  rollback paths publish no partial cache.
- Query programs merge semantic duplicates from the permanent prefix and overlay while unioning
  provenance. Clauses, facts, and ground disjunctions retain dense canonical identifiers.
- Native class/object/data-property classification and realization return the same compact
  backend-neutral ID records as Python. Realization includes direct types, same/different groups,
  object targets (including inverses/subproperties/equality), and exact source-literal data values.
- The native adapter checks the exact Python/native package version, ABI, core versions, IR schema,
  self-test, and a sorted feature tuple. The completed tuple includes `full_reasoner`,
  `incremental_updates`, `classification`, and `realization`; delta handling intentionally matches
  Python's conservative no-op-or-rebuild contract.
- Verify mode executes native first and the callback-free Python shadow second over the identical
  compiled ontology. It compares exact result types/values or public error types/codes and poisons
  on mismatch. A shared cancellation observed during a native callback is not replayed as a
  timing-dependent shadow mismatch.

## Integration defects found and closed

The completed public differential exposed two seams that isolated component tests did not:

1. a query overlay could repeat the entire permanent program, producing duplicate clause/fact/
   disjunction identities in Rust even though Python canonicalized the union; and
2. `RoleAutomatonIR` uses generic canonical-JSON ordering, while native input schema v1 requires
   numeric `(source, role-or-sentinel, target)` transition ordering. The encoder now performs that
   explicit wire canonicalization, including role IDs such as 10 versus 2 and epsilon edges.

Both have focused regressions. The second is covered without loading the extension, so a future
pure-Python codec change cannot silently reintroduce an invalid native document.

## Reproduced gates

| Gate | Result |
|---|---:|
| Rust `cargo test --no-default-features` | 209 library + 8 input-wire + 6 operation-control passed |
| Rust `cargo clippy --no-default-features --all-targets -- -D warnings` | passed |
| Rust `cargo fmt --all -- --check` | passed |
| Default Python suite, CPython 3.10 / 3.12 | 747 + 4 subtests passed on each interpreter |
| Entire default suite forced through native, CPython 3.10 / 3.12 | 747 + 4 subtests passed on each interpreter |
| Public facade lifecycle/update suite in verify mode, CPython 3.10 / 3.12 | 11 passed on each interpreter |
| Complete-service native/verify differential, CPython 3.10 / 3.12 | 16 passed on each interpreter |
| Native input numeric-order regression, CPython 3.10 / 3.12 | 6 passed on each interpreter |

The complete-service matrix runs both forced-native and verify sessions over committed HermiT
black-box goldens; class, object-property, data-property, and individual result tables; non-Horn
choice recovery; cyclic existential blocking; maximum-cardinality equality; role chains,
transitivity, inverses, and equality substitution; source-literal datatype values; inconsistent
failure policy; and deterministic generated permutation/duplicate/query campaigns.

## Release boundary

`full_reasoner` describes an implemented native capability, not a GA conformance attestation. The
repository intentionally contains only the hash/count inventory for the 266-case/350-check W3C
export because redistribution rights for the ontology bodies are unresolved. The licensed W3C
release lane, the larger live-Java sample, hosted cross-platform wheels/sanitizers, and the legal
release checklist remain explicit WP17/WPP0 external gates. Ordinary runtime, wheels, and local
verification remain Java-free.
