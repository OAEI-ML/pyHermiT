# Native symbol-index limit verification

Base: `977a83b3c9cb7fe85fa14cdf446f511fac7458e5` (`perf/native-pipeline`).
Implementation: `ee11a1a34f32f0060e1ff6098f5f94f55a278a6f`.
Verified on Linux x86-64, Python 3.12, Rust 1.97.1 and pyowl-core 0.2.1, using an
isolated checkout, compiled Rust extension and separate test environment.

## Behaviour and compatibility

The optional `max_native_symbol_index_bytes` setting is positive-u64, keyword-only and
fixed for a session. The omitted setting retains 64 MiB; legacy JSON export remains
independently bounded. Explicit settings require the new native capability and cannot
silently fall back to Python or disappear on an older extension.

Comparison against the actual base source verified existing constructor parameters,
dataclass field order, semantic configuration and encoded bytes for default, strict-native,
and nondefault legacy configurations. Default encoded configuration SHA-256 remains
`8a711a465f41cfed59bb514ea73ea79fb3daf0c0fff9a8f8b8fee2df383a4fc9`.
A trusted pickle produced by that base version is included in regression coverage:
its nondefault deterministic setting and both callbacks survive deserialization, and the
new limit is unset. Current pickle restoration validates shape and option values.

Native tests cover exact index boundaries, raised/u64-max bounds, all symbol-domain
mappings, resource/cancellation failure on initial construction and cached-owner
reacquisition, recovery, malformed wire records and capability negotiation. Differential
fixtures preserve reasoning answers and strict datatype errors for metadata-only and
logical uses. The separate memory-only profile handoff now supplies its native budget
without requiring a Python cancellation token.

## Local checks

- Python unit, integration, conformance and parity suite: 960 passed.
- Native/differential/facade regression suite: 845 passed; six existing overlay-size warnings.
- Rust unit and integration suites: 374 passed (360 + 8 + 6).
- After the pickle compatibility fix: 12 focused native index/semantic tests passed again.
- Mypy: all 125 configured source files passed.
- Ruff check and format, Rust format, import boundaries, metadata, work-package and
  documentation-link checks passed. The existing release authorization checker passes;
  it is not additional release approval for this change.

Commands used include:

```sh
cargo test --manifest-path native/Cargo.toml --locked --offline --no-default-features
PYHERMIT_BACKEND=python python -m pytest -q tests/unit tests/integration tests/conformance tests/parity
python -m pytest -q tests/differential tests/native tests/integration/facade
ruff check .
ruff format --check .
python -m mypy
lint-imports
```

The first Rust attempt exposed an existing test hard-coded to release 0.2.0; it now
checks Python/Cargo version agreement. No reference answer goldens were regenerated.

## Remaining gates

No installed pyHermiT or pyowl-core package was replaced; recorded package metadata and
native-library hashes stayed unchanged. No running experiment was restarted or rebound.
Full NCIT admission and reasoning were not rerun. Required index capacity, total RSS and
large-ontology runtime remain unmeasured. The memory controls use estimates, and separate
classification/realization limits remain in force. Cross-platform wheels and hosted CI
are separate verification gates. This PR adds no datatype admission exception, package
release, production rollout or scientific result.
