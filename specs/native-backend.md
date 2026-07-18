# Rust native backend and packaging

Rust is the optimized implementation language. PyO3 provides the private CPython
extension boundary; no Rust type is part of the stable public API. The complete Python
backend remains installable and semantically equivalent.

Packaging references:

- [PyO3 building and stable ABI](https://pyo3.rs/main/building-and-distribution)
- [setuptools-rust `RustExtension`](https://setuptools-rust.readthedocs.io/en/latest/reference.html)
- [Python wheel compatibility tags](https://packaging.python.org/en/latest/specifications/platform-compatibility-tags/)
- [Maturin portable-wheel guidance](https://www.maturin.rs/distribution.html)

## 1. Architecture decision

The Rust extension owns a complete backend session and all hot mutable reasoning state.
It is not a collection of per-row helper functions. pyowl-core supplies the captured public
ontology view; pyHermiT performs backend-neutral private compilation, transfers that frozen
IR once, then invokes
coarse operations such as check batches, classification, or realization.

The extension module is private:

```text
pyhermit._native
```

Only `pyhermit.backends.dispatch` imports it. Users receive exact pyowl-core OWL values and
normal Python result values from `Reasoner`, never PyO3 classes, capsules, raw pointers, or
Rust-owned views.

## 2. Rust workspace

```text
native/
├── Cargo.toml                 # cdylib crate `pyhermit-native`
└── src/
    ├── lib.rs                 # PyO3 boundary only
    ├── error.rs
    ├── wire.rs                # validated IR/result wire schema
    ├── cancel.rs
    ├── session.rs
    ├── model/                 # primitive compiled IR
    ├── store/                 # arenas, extension rows/indexes, trail, dependencies
    ├── rules/                 # hyperresolution and specialized head handlers
    ├── blocking/
    ├── datatypes/
    ├── roles/
    ├── classify/
    └── realize/
```

Crate dependency direction follows that list: `wire/model` are leaves; store depends on
model; rules/blocking/datatypes depend on store/model; session coordinates; `lib.rs`
converts only. Cyclic module ownership or PyO3 imports in the reasoning core are
forbidden.

The workspace commits `Cargo.lock`, declares a tested minimum Rust version, uses Rust
2024 edition when supported by that MSRV, denies warnings in release CI, and audits
dependencies/licenses/advisories. The implementation pins PyO3 0.29.0, the first line
that resolves RUSTSEC-2026-0176 and RUSTSEC-2026-0177, while retaining its Rust 1.83
MSRV; later updates require the normal lockfile, ABI, wheel, and parity lanes.
Default features are minimal and deterministic.

## 3. Wire boundary

### 3.1 Flat IR

`CompiledOntology`, queries, deltas, and results cross as versioned flat read-only byte
buffers or a small tuple of homogeneous buffers—not nested Python objects per clause or
fact. Schema v1 specifies:

- eight-byte magic, schema version, flags, and total length;
- little-endian fixed-width scalar encoding;
- checked section directory with `(kind, offset, length, count)`;
- dense `u32` IDs and offsets, with `u64` total byte lengths;
- UTF-8 only for diagnostic/symbol sections;
- no native pointer, `usize`, enum layout, padding, or Rust bincode/pickle dependency;
  and
- a content hash/fingerprint binding the payload to the compiled ontology.

Both sides fully bounds-check counts, offset arithmetic, alignment, enum discriminants,
references, sorts, and arities. Unknown required sections/versions fail with
`BackendVersionError`; unknown explicitly optional diagnostic sections may be skipped.
Parsing hostile bytes cannot allocate from an unvalidated claimed count.

The Python serializer and Rust reader have golden byte fixtures, randomized round trips,
corruption tests, and an independent minimal schema validator. Schema changes require
a new version, migration/rebuild behavior, and regenerated fixtures.

### 3.2 Ownership

On `create_session`, Rust validates and takes an owned compact representation before
the GIL is released. It never retains a borrowed `PyBuffer`, pointer into a Python
`bytes`, or reference to a mutable caller buffer for later computation. A single copy
is acceptable; benchmark it separately. Cached serialized IR is immutable and keyed by
fingerprint/schema.

The facade retains the captured `OntologyView` strongly until session close. View/provider
ingestion performs no parse/model copy. Native transfer prefers one immutable bulk buffer or
mmap-backed private-IR cache and permits at most one contiguous copy per created session; it
never serializes OWL text/RDF or calls Python once per axiom/rule.

Results return compact ID buffers copied/moved into Python-owned `bytes` and are
validated/mapped by the facade. No Rust reference survives `NativeSession.close`.

## 4. PyO3 surface

The private extension exposes only:

```python
ABI_VERSION: int
IR_SCHEMA_VERSION: int
FEATURES: tuple[str, ...]

def self_test() -> None: ...
def create_session(ir: bytes, config: bytes, cancellation: CancellationHandle) -> NativeSession: ...

class NativeSession:
    def check(self, query: bytes | None) -> bytes: ...
    def check_many(self, queries: Sequence[bytes]) -> bytes: ...
    def classify_classes(self) -> bytes: ...
    def classify_object_properties(self) -> bytes: ...
    def classify_data_properties(self) -> bytes: ...
    def realize(self) -> bytes: ...
    def apply_delta(self, delta: bytes) -> bytes: ...
    def reset_query_state(self) -> None: ...
    def close(self) -> None: ...
```

The `.pyi` checked into `src/pyhermit/_native.pyi` is authoritative for Python type
checking. Private API changes still require synchronized dispatcher/schema tests.

## 5. Memory and data structures

Preferred representations, subject to profiling and parity:

- append/reuse arenas with generation-checked debug handles for nodes/rows;
- struct-of-arrays for frequently scanned node/row fields;
- dense vectors/bitsets for predicates and small dependency levels;
- small-inline immutable dependency sets with interned bitmap fallback;
- predicate/argument indexes using deterministic-hash or sorted keys where iteration
  can influence scheduling;
- compact trail records tagged by mutation kind;
- contiguous join plans and queues; and
- bounded LRU/generation caches per compiled ontology/session.

All size arithmetic is checked. `max_memory_bytes` accounts for major arenas, indexes,
caches, query buffers, and worker allocations before growth. Exceeding it returns
`ResourceLimitError` at a safe point. Relying on process OOM/abort is unacceptable.

Rust `unsafe` is forbidden by crate lint by default. If profiling proves a necessary
exception, the code block must document validity/aliasing/lifetime/thread invariants,
have focused Miri/sanitizer/fuzz tests, and be approved in a dedicated change with the
measured safe-versus-unsafe delta.

## 6. GIL and threads

IR validation that accesses Python objects runs with the GIL. Long pure-Rust session
operations release it. While released, Rust:

- holds no borrowed Python memory;
- invokes no Python callback or exception constructor;
- writes progress/warning records to a bounded native queue;
- polls atomic cancellation/deadline/resource state; and
- catches all Rust panics before returning to the FFI boundary.

The calling main thread must periodically reattach and run Python signal checks during
long work so `KeyboardInterrupt` is propagated unchanged. After reacquiring the GIL,
events drain on the initiating Python thread and Rust errors map to public exceptions.
A callback error sets cancellation, completes rollback, then re-raises the original
callback exception.

One `NativeSession` serializes mutation and queries unless a later snapshot-safe mode is
proven. Its Rust type is not unsafely `Send`/`Sync`; explicit locking/ownership controls
thread movement. Independent sessions may run in parallel. Internal Rayon or custom
workers are optional, off in deterministic debugging, bounded by config, and must not
oversubscribe callers running multiple reasoners.

The session records its creating process ID. Use after `fork()` raises a stable state
error; callers create a new reasoner in the child. With the PyO3 0.29.0 pin,
native operation in unsupported CPython subinterpreters is disabled and `auto` selects
Python before session creation. Free-threaded CPython uses the universal Python wheel
until a dedicated thread-safety audit and compatible `abi3t`/version-specific wheels
pass the complete matrix; regular `abi3` artifacts must not be mislabeled for it.

## 7. Cancellation, errors, and panic policy

A cancellation handle contains atomics for interrupt, monotonic deadline metadata, and
resource failure. Poll at phase boundaries and bounded inner-loop strides. Rust returns
a typed internal error with stable code and context; `lib.rs` maps it once.

Every exported call is inside `catch_unwind`. A panic:

1. never unwinds across CPython;
2. marks the session poisoned;
3. returns `BackendPoisonedError(code="NATIVE_PANIC")` with a redacted diagnostic
   cause; and
4. prevents reuse except `close`.

Panic catching is containment, not expected control flow. Any panic is release-blocking.
Rust abort panic mode is forbidden for the extension.

Timeout/interruption performs operation-root rollback when proven safe. If rollback
itself cannot complete, poison the session and let the public reasoner rebuild before a
later operation.

## 8. Semantic parity workflow

Native implementation begins component by component only after its Python contract and
serialized transition fixtures stabilize:

1. wire/schema and empty session;
2. stores, indexes, dependencies, trail/backtracking;
3. hyperresolution and clash/ground-disjunction branching;
4. equality/merge, existentials, cardinalities, NI;
5. blocking;
6. datatypes and role automata;
7. complete check session;
8. batched classification/realization; and
9. safe parallel/profile optimizations.

Each stage replays the same operation/state traces in Python and Rust. The native
backend never calls Python to fill an unimplemented semantic handler. Until all features
required by an ontology are declared complete, `auto` chooses the complete Python
backend before creating a session and forced `native` raises a clear feature error.
GA declares all in-scope features complete.

## 9. Build system and compiler-free fallback

Use `setuptools.build_meta` plus `setuptools-rust`, not Maturin as the sole PEP 517
backend, because the source distribution must successfully omit a failing optional Rust
extension. `setuptools_rust.RustExtension(optional=True)` explicitly permits a build to
continue when the extension cannot compile.

Three controlled build modes are mandatory:

| Environment | Extension declaration | Result |
|---|---|---|
| default source build | optional; attempt release Rust build | native local wheel if successful, otherwise working Python-only local wheel |
| `PYHERMIT_BUILD_NATIVE=0` | do not declare/build extension | reproducible `py3-none-any` pure wheel |
| `PYHERMIT_BUILD_NATIVE=1` | nonoptional Rust extension | platform wheel or hard build failure |

A minimal `setup.py`/build configuration reads only
`PYHERMIT_BUILD_NATIVE=auto|0|1` (default `auto`) to construct `RustExtension`; project
metadata remains in `pyproject.toml`. Invalid values fail. Official CI never accepts an
optional failure in native-wheel jobs and inspects wheel contents plus forced-native
tests.

Publish for each version:

- one `py3-none-any` pure-Python wheel;
- compatible `cp310-abi3-<platform>` native wheels (minimum Python 3.10); and
- one sdist containing Python and Rust sources.

Wheel tag ranking should select the compatible platform `abi3` wheel on supported
CPython and the pure wheel on unsupported interpreter/platform combinations. Release CI
tests resolver behavior from a local index containing **all** artifacts. PyPy and
free-threaded CPython use Python-only artifacts until a separately tested stable ABI is
approved.

`abi3-py310` is required because Python 3.10 is the minimum package version. The coarse
boundary uses stable-ABI bytes/scalars and does not depend on a newer zero-copy PyBuffer API.
If profiling proves stable-ABI overhead
material, publish version-specific wheels only through a reviewed spec amendment; the
fallback promise and matrix remain.

## 10. Native wheel matrix

Minimum release targets, subject to availability of maintained PyPA runners:

- Linux manylinux 2.17 x86-64 and aarch64;
- Linux musllinux 1.2 x86-64 and aarch64;
- macOS x86-64 and arm64 with recorded deployment targets; and
- Windows x86-64 and arm64.

Additional platforms may be added after full parity/safety lanes. Linux artifacts are
built in compliant manylinux/musllinux images or with an audited
equivalent, then checked for forbidden external shared libraries. macOS/Windows wheels
receive equivalent dependency inspection. Cargo uses `--locked`; release builds are
reproducible as far as toolchains permit and include an SBOM/provenance attestation.

## 11. Artifact contents and metadata

The pure wheel contains `src/pyhermit` Python/runtime data, `py.typed`, `_native.pyi`,
license/notice metadata, and no native/Rust build artifacts. Native wheels add exactly
one private extension and required permitted runtime libraries. Wheels contain no
tests, benchmarks, Java/reference files, `.jar`/`.class`, JVM/JNI/JPype launcher or
dependency, Cargo target tree, or source checkout. Every artifact declares
`pyowl-core>=0.1,<0.2` and Python `>=3.10`.

The sdist contains Python/Rust sources, `Cargo.lock`, specs needed by contributors,
licenses/notices, and build config. It contains no compiled objects or downloaded
oracle. `cargo package`/sdist file lists are tested.

`backend_info()` reports why auto chose Python (`not_installed`, `unsupported_runtime`,
or similar) without treating normal absence as a warning. ABI mismatch or a present
extension failing `self_test()` is a hard installation/backend error.

## 12. Safety, parity, and packaging gates

- `cargo fmt`, Clippy with warnings denied, dependency/advisory/license audit.
- Unit/property/state-trace tests for the core crate without Python where possible.
- PyO3 FFI fuzzing plus ASan/UBSan, leak/reference checks, focused TSan, and Miri-suitable
  tests.
- Exact complete public suite under forced Python/native/auto; focused verify mode.
- Repeated create/query/cancel/close cycles with stable memory/refcounts.
- All wheel targets install/test in clean containers/VMs.
- Pure wheel and no-Rust sdist path reason successfully without Java/network/compiler.
- Installed CPython 3.10 and 3.12 lanes cover standalone source loading and shared
  snapshot/overlay/composite/provider view inputs plus compatible pyowl-core pure/native variants.
- Archive and dependency scans prove no Java/JVM/JAR/class/JNI/JPype artifact or package.
- Local-index resolver selects native on supported CPython and pure elsewhere.
- Performance and boundary-call/copy budgets in `performance.md` pass.
- Publication is impossible while `deviations.md` LIC-001 remains open.
