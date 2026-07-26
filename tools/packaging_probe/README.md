# WP00 packaging probe

This directory is a development-only proof of the build policy. It is excluded from
the pyHermiT wheel and sdist.

`python -m tools.packaging_probe.run_probe` copies the nested dummy project to temporary
directories, makes Cargo/Rust unavailable, and verifies:

- `PYHERMIT_BUILD_NATIVE=0` builds a universal wheel;
- `auto` reports the missing Rust compiler, survives failure of its optional
  `RustExtension`, and emits no native output;
- `1` reports the missing Rust compiler, fails, and emits no wheel; and
- a compatible `cp310-abi3` wheel outranks the same-version universal wheel, while a
  simulated unsupported runtime selects the universal wheel.

The dummy crate contains no reasoner behavior and never enters a runtime artifact.

`python -m tools.packaging_probe.release_manifest` creates the schema-2 release manifest
and `SHA256SUMS` only for the exact ten-distribution matrix plus the audited SPDX SBOM.
It binds regular-file bytes, the clean Git revision/tree, release recipes, commit-pinned
actions, pinned build tools, and the Rust production-license inventory. Re-run it with
`--verify` to reject substitutions or unbound members. This local manifest inventories
the staged candidate; the release workflow's later GitHub attestation establishes hosted
build-run provenance.
