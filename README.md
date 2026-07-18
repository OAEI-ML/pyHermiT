# pyHermiT

pyHermiT is specified as a Java-free Python and Rust reimplementation of the core
HermiT OWL 2 DL reasoner, with a complete pure-Python fallback. It targets Python 3.10+
and uses the Java-free `pyowl-core` package for shared ontology parsing, immutable views,
overlays, composites, and zero-reparse communication with Exact-OM and other consumers.

The pre-release implementation provides the public reasoner facade, complete
pure-Python path, and an optional private Rust backend. The normative architecture,
compatibility rules, backend completeness requirements, and verification plan begin at
[`specs/README.md`](specs/README.md). Built runtime artifacts contain no Java, JVM
launcher, Java bridge, or reference implementation.

The owner has selected the source-guided implementation mode and
`LGPL-3.0-or-later`, matching the pinned upstream declaration. `LICENSE` contains the
LGPL text, `COPYING` the GPL text it incorporates, and `NOTICE.md` the initial upstream
attribution. No release may be published while the remaining `LIC-001` provenance,
file-header, package-metadata, source-obligation, artifact-audit, and legal-review
checklist in [`specs/deviations.md`](specs/deviations.md) is open.

## Development

Use Python 3.10 or newer and install a compatible `pyowl-core`:

```shell
python -m pip install \
  "pyowl-core>=0.1,<0.2" \
  "build>=1.2,<2" "hypothesis>=6.100,<7" "import-linter>=2.1,<3" \
  "mypy>=1.10,<3" "packaging>=24,<27" "pytest>=8.2,<10" \
  "pytest-cov>=5,<8" "ruff>=0.5,<1" "setuptools==83.0.0" \
  "setuptools-rust==1.13.0" "tomli>=2.0,<3; python_version < '3.11'"
PYHERMIT_BUILD_NATIVE=0 python -m pip install --no-build-isolation -e .
python -m pytest
python -m tools.specs.check_workpackages
python -m tools.specs.check_project
python -m tools.specs.check_links
python -m tools.specs.check_release_gate --assert-blocked
ruff format --check .
ruff check .
mypy
lint-imports
cargo deny --manifest-path native/Cargo.toml check --config deny.toml
```

Build and inspect the compiler-free artifacts with:

```shell
SOURCE_DATE_EPOCH=946684800 PYHERMIT_BUILD_NATIVE=0 python -m build
python -m tools.packaging_probe.check_artifact --pure dist/*.whl
python -m tools.packaging_probe.check_artifact dist/*.tar.gz
```

`PYHERMIT_BUILD_NATIVE=auto|0|1` is the only supported build switch:

- `auto` (default) attempts the optional native extension when Cargo is available and
  otherwise produces a truthfully tagged Python-only local build;
- `0` never declares the extension and produces the reproducible `py3-none-any`
  fallback; and
- `1` requires the locked Rust build and fails instead of silently falling back.

The distribution workflow builds the sdist, universal fallback, and the eight required
`cp310-abi3` manylinux 2.17, musllinux 1.2, macOS, and Windows x86-64/ARM64 targets. It
audits Rust advisories/licenses/sources, ABI, and external libraries; installs on CPython
3.10 and 3.12; compares
pure/native metadata and Python payloads, and verifies local-index resolver preference.
The target manifest remains `configured-awaiting-hosted-validation` until those hosted
jobs pass. The release workflow deliberately has no package-index upload action while
LIC-001 remains open.
