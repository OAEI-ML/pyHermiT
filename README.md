# pyHermiT

[![PyPI](https://img.shields.io/pypi/v/pyHermiT)](https://pypi.org/project/pyHermiT/)
[![Python](https://img.shields.io/pypi/pyversions/pyHermiT)](https://pypi.org/project/pyHermiT/)
[![License](https://img.shields.io/badge/license-LGPL--3.0--or--later-blue)](LICENSE)

pyHermiT is specified as a Java-free Python and Rust reimplementation of the core
HermiT OWL 2 DL reasoner, with a complete pure-Python fallback. It targets Python 3.10+
and uses the Java-free `pyowl-core` package for shared ontology parsing, immutable views,
overlays, composites, and zero-reparse communication with Exact-OM and other consumers.

The 0.1.0 production implementation provides the public reasoner facade, complete
pure-Python path, and an optional private Rust backend. The normative architecture,
compatibility rules, backend completeness requirements, and verification plan begin at
[`specs/README.md`](specs/README.md). Built runtime artifacts contain no Java, JVM
launcher, Java bridge, or reference implementation.

## Installation

```shell
python -m pip install pyHermiT
```

A supported native wheel enables Rust acceleration automatically. The universal
wheel provides the complete compiler-free Python backend. Neither installation
contains, downloads, or starts Java.

## Quick start

```python
from pyowl_core import ImportPolicy, LoadOptions, load_snapshot
from pyhermit import Reasoner

ontology = (
    b"Prefix(:=<urn:example#>) Ontology(<urn:example> "
    b"Declaration(Class(:A)) Declaration(Class(:B)) SubClassOf(:A :B))"
)
view = load_snapshot(
    ontology,
    options=LoadOptions(imports=ImportPolicy.RESOLVE_STRICT),
)

with Reasoner(view) as reasoner:
    assert reasoner.ontology is view
    assert reasoner.is_consistent()
    taxonomy = reasoner.classify_classes()
```

See the [user guide](docs/user-guide.md) for backend selection, import
resolution, classification and realization queries, timeouts, updates, and
error handling.

## Release and licensing status

The owner has selected the source-guided implementation mode and
`LGPL-3.0-or-later`, matching the pinned upstream declaration. `LICENSE` contains the
LGPL text, `COPYING` the GPL text it incorporates, and `NOTICE.md` the initial upstream
attribution. For `0.1.0`, the owner explicitly waived the remaining `LIC-001` legal-review
signoff as-is without representing that legal review occurred. The waiver is recorded in
[`reports/release/0.1.0-owner-release-override.md`](reports/release/0.1.0-owner-release-override.md).
The completed repository audits are under
[`reports/licensing/`](reports/licensing/) and
[`reports/release/artifact-audit.md`](reports/release/artifact-audit.md).

## Documentation

Start with the [user guide](docs/user-guide.md) for backend selection, standalone and
shared-view loading, every service family, updates, concurrency, and errors. The
[API reference](docs/api-reference.md) enumerates every stable facade member, and the
[developer guide](docs/developer-guide.md) traces the core-view boundary through the
private IR and Python/Rust engines. The [documentation index](docs/index.md) links the
normative specifications and machine-readable evidence.

Release qualification is recorded in the [release report](reports/release-report-local.json),
[coverage matrix](reports/coverage-matrix.json), and
[benchmark audit](benchmarks/evidence/WP17-local-audit.md). The owner accepted the
remaining external runs and hosted-platform evidence as post-release follow-up for
`0.1.0`; this does not certify unexecuted native targets.

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
python -m tools.specs.check_release_gate --require-publishable
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
jobs pass. The universal Python fallback is the portable production artifact while
additional native wheels complete that hosted validation.
