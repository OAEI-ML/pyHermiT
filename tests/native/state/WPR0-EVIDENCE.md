# WPR0 native wire and state-kernel evidence

Date: 2026-07-17

## Scope

WPR0 provides the private Rust/PyO3 ABI, strict flat-wire decoder, lifecycle and
resource guards, and the deterministic native state kernel. Semantic reasoner
entry points intentionally raise the public typed `FeatureNotImplementedError`;
this work package does not advertise a completed reasoner.

`native/Cargo.lock` and `native/benches/` are included under the parent-approved
WPR0 ownership amendment.

## Verification

| Gate | Result |
| --- | --- |
| Rust 1.97.1 `cargo fmt --check` | passed |
| Rust 1.97.1 locked all-target check | passed |
| Rust 1.97.1 no-default all-target tests | 10 passed; both benchmark smoke targets succeeded |
| Rust 1.97.1 strict Clippy | passed |
| Rust 1.83.0 isolated locked all-target check | passed |
| Rust 1.83.0 isolated no-default all-target tests | 10 passed; both benchmark smoke targets succeeded |
| Rust 1.83.0 isolated strict Clippy | passed |
| CPython 3.12 native and Python state suites | 89 passed |
| CPython 3.10, loading the same `abi3-py310` binary | 89 passed |
| Ruff on the stub and native tests | passed |
| strict mypy on the stub, Python 3.10 and 3.12 | passed |
| import-linter | 2 contracts kept, 0 broken |

The canonical WP08 state trace produces exact per-operation Python/Rust parity.
The SHA-256 of its newline-joined canonical snapshots is
`0ba539d31e8e6d274711af380f669ad6723515950e35c694f88c6371e03753c9`.

Criterion release-profile measurements on the development host:

- `wpr0_create_index_and_check_512`: 1.2864-1.5755 ms
- `wpr0_branch_mutate_rollback_512`: 1.7923-1.9495 ms

## Integration boundary

The repository-root Cargo workspace membership and Python limited-API wheel tag
belong to packaging work package WPP0. The local setuptools build labels the
artifact with the running interpreter suffix even though the artifact itself
loads and passes the suite on both CPython 3.10 and 3.12.

Miri, sanitizer, and dependency-audit lanes were not available in the local
toolchain and remain release-CI gates. The crate forbids unsafe Rust.
