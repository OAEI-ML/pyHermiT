# WPR3 PyO3 security-audit evidence

The native backend previously pinned PyO3 and `pyo3-build-config` to 0.28.3.
An offline `cargo audit` run against the RustSec advisory database identified two
advisories affecting that release:

- `RUSTSEC-2026-0176`, an out-of-bounds read in PyO3 iterator handling; and
- `RUSTSEC-2026-0177`, a missing `Sync` bound in a PyO3 API.

Both advisories are fixed by PyO3 0.29.0. The native crate, packaging probe, dependency
policy, lockfile, and native-backend specification now pin that exact release together.
PyO3's 0.29 migration notes do not require a source change in the APIs used by this
project.

Authoritative references:

- <https://rustsec.org/advisories/RUSTSEC-2026-0176.html>
- <https://rustsec.org/advisories/RUSTSEC-2026-0177.html>
- <https://pyo3.rs/v0.29.0/changelog>
- <https://pyo3.rs/main/migration>

## Verification

The following gates passed with the updated locked dependency graph:

- `cargo check --locked --all-targets` with the default Python extension feature;
- all 139 Rust tests with `--locked --no-default-features`;
- strict Clippy across all targets with both default and no-default feature sets;
- Rust formatting checks;
- the dependency/specification checker under Python 3.10 and Python 3.12;
- the specification-checker unit tests under both supported Python versions;
- all five packaging-probe tests under Python 3.10 and Python 3.12; and
- an offline `cargo audit --no-fetch --no-yanked` scan of 65 locked dependencies,
  with no remaining advisories.

The audit tool and advisory cache used for this check lived under `/private/tmp`; no
audit tooling or cache was added to the repository or to the package's runtime graph.
