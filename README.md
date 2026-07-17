# pyHermiT

pyHermiT is specified as a Java-free Python and Rust reimplementation of the core
HermiT OWL 2 DL reasoner, with a complete pure-Python fallback. It targets Python 3.10+
and uses the Java-free `pyowl-core` package for shared ontology parsing, immutable views,
overlays, composites, and zero-reparse communication with Exact-OM and other consumers.

The WP00 foundation contains packaging/build controls, metadata and dependency audits,
work-package validation, no-Java artifact checks, and an intentionally empty public
package marker. It is not yet a usable reasoner. The normative architecture,
compatibility rules, and dependency-ordered implementation work begin at
[`specs/README.md`](specs/README.md).

The owner has selected the source-guided implementation mode and
`LGPL-3.0-or-later`, matching the pinned upstream declaration. `LICENSE` contains the
LGPL text, `COPYING` the GPL text it incorporates, and `NOTICE.md` the initial upstream
attribution. No release may be published while the remaining `LIC-001` provenance,
file-header, package-metadata, source-obligation, artifact-audit, and legal-review
checklist in [`specs/deviations.md`](specs/deviations.md) is open.

## Development checkpoint

Use Python 3.10 or newer. WP00 checks do not install or import the unfinished
`pyowl-core` runtime dependency:

```shell
python -m pip install \
  "build>=1.2,<2" "hypothesis>=6.100,<7" "import-linter>=2.1,<3" \
  "mypy>=1.10,<3" "packaging>=24,<27" "pytest>=8.2,<10" \
  "pytest-cov>=5,<8" "ruff>=0.5,<1" "setuptools>=77" \
  "setuptools-rust>=1.13,<2" "tomli>=2.0,<3; python_version < '3.11'"
PYHERMIT_BUILD_NATIVE=0 python -m pip install --no-deps --no-build-isolation -e .
python -m pytest
python -m tools.specs.check_workpackages
python -m tools.specs.check_project
python -m tools.specs.check_links
python -m tools.specs.check_release_gate --assert-blocked
ruff format --check .
ruff check .
mypy
lint-imports
```

Build and inspect the compiler-free artifacts with:

```shell
PYHERMIT_BUILD_NATIVE=0 python -m build
python -m tools.packaging_probe.check_artifact --pure dist/*.whl
python -m tools.packaging_probe.check_artifact dist/*.tar.gz
```

`PYHERMIT_BUILD_NATIVE=auto|0|1` is the only supported build switch. At this
checkpoint `auto` and `0` produce the pure package; `1` fails because WPR0 has not yet
created `native/Cargo.toml`. The isolated packaging probe separately exercises an
optional native compilation failure and same-version wheel-tag preference.
