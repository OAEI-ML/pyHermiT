# WPP0 — Wheel, sdist, and release packaging matrix

**Goal**: publish one distribution where supported CPython selects a native wheel and
every other supported environment has a compiler-free pure-Python fallback.

## Read first

| What | Where |
|---|---|
| Exact build/wheel decision | `native-backend.md` §§9–12 |
| Packaging gates | `SPEC.md` §6; `verification.md` §9 |
| Build probe/facade | WP00 and WP16 implementations |
| Complete native extension | WPR4 implementation/handshake |
| Official standards | PyPA wheel tags/binary extensions; setuptools-rust optional extension docs |

## Deliverables

- Final `pyproject.toml`, minimal conditional `setup.py`, manifests, version single
  source, Python `>=3.10`, `pyowl-core>=0.1,<0.2`, locked Rust build, provisional/final
  license/notice/package-data/type metadata governed by LIC-001.
- `PYHERMIT_BUILD_NATIVE=auto|0|1` behavior: optional sdist/direct default, reproducible
  universal wheel, forced native release failure on any compiler/extension error.
- cibuildwheel/native jobs for required manylinux/musllinux/macOS/Windows architectures,
  abi3-py310 tags, dependency auditing, SBOM/provenance, and forced-native tests.
- Pure `py3-none-any` wheel and sdist jobs with Cargo hidden, offline install/import/
  semantic suite, artifact inspection, read-only environment tests.
- Local-index resolver test containing all same-version artifacts and proving native
  preference/fallback; TestPyPI/release dry run.

## Depends on

WP16 and WPR4.

## Acceptance criteria

1. Every native wheel installs on its clean target and `backend_info` proves native;
   exact smoke/conformance tests cannot pass via fallback accidentally.
2. Pure wheel contains no extension/Rust/Java/JAR/class/JVM/JNI/JPype/reference/test
   artifacts or dependencies and passes the
   designated complete Python semantic suite without compiler/network/Java.
3. Sdist installs successfully with Cargo absent in auto mode; forced native compiles
   or fails clearly; no runtime compilation/download occurs.
4. A resolver presented all same-version files chooses a compatible native platform
   wheel on supported CPython and `py3-none-any` elsewhere.
5. ABI/IR/package handshake, metadata version/license/notices, `py.typed`/stub, RECORD,
   external shared libraries, and artifact file lists are audited.
6. Release workflow is reproducible, signed/attested as configured, and cannot upload
   artifacts unless forced native/pure matrices are green.
7. CPython 3.10 and 3.12 installed tests cover standalone and shared view/provider inputs,
   core pure/native compatibility, model/wire/adapter mismatch rejection, and no-Java scans.
8. Release workflow cannot upload while LIC-001 is open; closing evidence, exact SPDX
   metadata, notices, source obligations, and provenance inventory are audited.
