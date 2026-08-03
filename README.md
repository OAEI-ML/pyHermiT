# pyHermiT

[![PyPI](https://img.shields.io/pypi/v/pyHermiT)](https://pypi.org/project/pyHermiT/)
[![Python](https://img.shields.io/pypi/pyversions/pyHermiT)](https://pypi.org/project/pyHermiT/)
[![License](https://img.shields.io/badge/license-LGPL--3.0--or--later-blue)](LICENSE)

pyHermiT is an OWL 2 DL reasoner for Python: a Java-free reimplementation of the
core [HermiT](https://github.com/phillord/hermit-reasoner) hypertableau calculus
with a complete pure-Python engine and an optional Rust accelerator. It targets
Python 3.10+ and consumes the immutable ontology views of the Java-free
`pyowl-core` package — snapshots, overlays, composites, and providers are retained
by identity and shared with Exact-OM and other consumers without reparsing.

Highlights:

- **Complete reasoning services** — consistency, satisfiability, entailment,
  class/property classification, realization, and buffered updates over one stable
  facade.
- **Two interchangeable backends** — a readable, complete Python engine that runs
  anywhere, and a Rust engine selected automatically when a native wheel fits; a
  `verify` mode cross-checks them answer-for-answer.
- **Zero-reparse integration** — reasoning runs directly over shared `pyowl-core`
  views; the 0.2 native backend can compile the encoded structural-view schema 2
  without materializing a second model.
- **Fail-closed engineering** — explicit backend selection never silently falls
  back, version/ABI handshakes reject mismatches, and timeouts, interrupts, and
  memory limits are distinct outcomes rather than wrong answers.
- **No Java anywhere** — built runtime artifacts contain no JVM launcher, Java
  bridge, or reference implementation.

The normative architecture, compatibility rules, backend completeness
requirements, and verification plan begin at [`specs/README.md`](specs/README.md).

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
    taxonomy = reasoner.class_hierarchy()
```

## Documentation

| Document | Contents |
|---|---|
| [User guide](docs/user-guide.md) | Installation, backend selection, standalone and shared-view loading, worked query examples, updates, timeouts, callbacks, concurrency, and troubleshooting |
| [API reference](docs/api-reference.md) | The `Reasoner` constructor, every stable facade member, `ReasonerConfig`, and result shapes |
| [Error reference](docs/errors.md) | The exception hierarchy, stable error codes, and handling guidance |
| [Developer guide](docs/developer-guide.md) | The core-view boundary, private IR, calculus, native boundary, and release evidence |
| [0.2 migration guide](docs/migration-0.2.md) | Coordinated pyowl-core 0.2 upgrade and persisted-data invalidation |
| [Documentation index](docs/index.md) | Links to the normative specifications and machine-readable evidence |

Existing 0.1 deployments should follow the
[0.2 migration guide](docs/migration-0.2.md) before reusing persisted data or caches.

## Release and licensing status

The owner has selected the source-guided implementation mode and
`LGPL-3.0-or-later`, matching the pinned upstream declaration. `LICENSE` contains the
LGPL text, `COPYING` the GPL text it incorporates, and `NOTICE.md` the initial upstream
attribution. For `0.2.0`, the owner explicitly waived the remaining `LIC-001` legal-review
signoff as-is without representing that legal review occurred. The waiver is recorded in
[`reports/release/0.2.0-owner-release-override.md`](reports/release/0.2.0-owner-release-override.md).
The completed repository audits are under
[`reports/licensing/`](reports/licensing/) and
[`reports/release/artifact-audit.md`](reports/release/artifact-audit.md).

The historical `0.1.1` qualification is recorded in the
[release report](reports/release-report-local.json),
[coverage matrix](reports/coverage-matrix.json), and
[benchmark audit](benchmarks/evidence/WP17-local-audit.md). The owner accepted the
remaining licensed W3C, live-reference, and dedicated-performance runs as
post-release follow-up for `0.2.0`. The release workflow separately requires every
configured native target to pass before trusted publication.

## Development

Use Python 3.10 or newer and install a compatible `pyowl-core`:

```shell
python -m pip install \
  "pyowl-core>=0.2,<0.3" \
  "build>=1.2,<2" "hypothesis>=6.100,<7" "import-linter>=2.1,<3" \
  "mypy>=1.10,<3" "packaging>=24,<27" "pytest>=8.2,<10" \
  "pytest-cov>=5,<8" "ruff==0.15.22" "setuptools==83.0.0" \
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

At runtime, the separate `PYHERMIT_BACKEND` environment variable can steer the
default backend selection; see the [user guide](docs/user-guide.md).

The distribution workflow builds the sdist, universal fallback, and the eight required
`cp310-abi3` manylinux 2.17, musllinux 1.2, macOS, and Windows x86-64/ARM64 targets. It
audits Rust advisories/licenses/sources, ABI, and external libraries; installs on CPython
3.10 and 3.12; compares
pure/native metadata and Python payloads, and verifies local-index resolver preference.
The target manifest remains `configured-awaiting-hosted-validation` until those hosted
jobs pass. The universal Python fallback is the portable production artifact while
additional native wheels complete that hosted validation.
