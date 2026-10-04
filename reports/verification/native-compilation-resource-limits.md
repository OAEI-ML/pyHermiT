# Native compilation resource-limit verification

Base: `71ab3bcd85491bfd629f373e90036718a16babd7` (`perf/native-pipeline`, published 0.2.2).
Verified on Linux x86-64 with Python 3.12.3, Python 3.10.21 compatibility checks,
Rust 1.97.1, and pyowl-core 0.2.1. Builds and compiled tests ran in an isolated checkout
with a separate Cargo target and one CPU in the existing Slurm allocation.

## Behavior and compatibility

The `native-compilation-resource-limits-v1` capability advertises explicit compilation-work
support and effective encoded-compiler memory allowances. `max_compile_work` is keyword-only,
positive-u64, and omitted by default. Native/AUTO encoded paths accept it; Python, VERIFY,
scalar-wire input and older extensions reject explicit work before silently losing the policy.
Default VERIFY remains covered by the existing tests. Fixed configuration-wire bytes and the
published optional index section are unchanged.

A direct comparison against the actual 0.2.2 base confirmed constructor positions, semantic
items, diagnostic mappings, wire bytes and old pickle fields in seven scenarios, including
strict/index options and callbacks. Both supported Python versions restore historical 0.2.1
and 0.2.2 pickle fixtures and current round trips. The default config-wire SHA-256 remains
`8a711a465f41cfed59bb514ea73ea79fb3daf0c0fff9a8f8b8fee2df383a4fc9`.

Native coverage verifies tiny compiler-memory/work rejection, raised-limit successful queries,
retained/scratch ownership accounting, inclusive work boundaries and checked overflow,
profile-manifest handle-only memory checks, cancellation/reset/transactional retries, combined
index/work/memory deferred identities (strict and non-strict), stale-template rejection,
symbol mappings, wire compatibility and unchanged strict datatype errors.

A separate tiny Exact-OM adapter/bridge fixture passed with all three resource settings:
80 GiB memory, 80 GiB symbol-index estimate and maximum-u64 compilation work. It loaded the
isolated candidate, checked consistency and inferred the expected subclass relation through
one compiled anchor world. This fixture did not modify an experimental environment or perform
full ontology admission, full classification, scientific evaluation or a checkpoint test.

## Local checks

- Rust unit/integration tests: 380 passed (366 + 8 + 6).
- Actual compiled native resource/deferred/strict/wire selection: 239 passed.
- Focused configuration/adapter/pickle/VERIFY tests: 158 passed on each of Python 3.10 and 3.12.
- CI foundation selection: 1,124 passed initially; its one SBOM subprocess failure was a
  missing Cargo executable on the local PATH. The affected check passed after adding the
  existing Cargo directory. The combined SBOM/licensing/release-gate rerun passed all 13 tests.
- Mypy passed all 125 configured source files; both import-boundary contracts passed.
- Ruff check/format, Rust format, work-package/project metadata, documentation links and
  unchanged publication-authorization checks passed.

Representative commands (with the isolated interpreter, source path and Cargo target):

```sh
cargo test --manifest-path native/Cargo.toml --locked --offline --no-default-features
cargo build --manifest-path native/Cargo.toml --locked --offline
python -m pytest -q --ignore=tests/differential/encoded_compiler --ignore-glob='tests/native/**'
python -m pytest -q tests/differential/encoded_compiler/test_permanent_program_assembly.py tests/differential/encoded_compiler/test_native_symbol_limits.py tests/differential/encoded_compiler/test_resource_limit_semantics.py tests/differential/encoded_compiler/test_strict_native_pipeline.py tests/native/encoded_input/test_deferred_fingerprints.py tests/native/encoded_input/test_profile_manifest_memory.py tests/native/wire/test_wire_contract.py
python -m mypy
ruff check .
ruff format --check .
```

The Rust test linker needed a temporary local `libpython3.12.so` symlink to the already
installed shared library; no system package was installed. No answer goldens were regenerated.
Only `config.py` changed among adapted-source inventory entries; its hash was refreshed and
all headers/provenance mappings retained. No license or release-policy authorization changed.

## Remaining gates

Hosted CI and cross-platform wheel validation remain separate gates. No release version was
bumped, no package was published or installed into an experiment, and no live job was rebound.
Full NCIT admission, peak process RSS, runtime and full scientific results remain unmeasured.
Memory controls retain their documented estimate-based scope; independent shape, index,
query and datatype limits remain active. A larger work allowance is not a completion guarantee.
