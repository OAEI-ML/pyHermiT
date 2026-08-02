# pyowl-core ontology input and OWL 2 DL validation

pyHermiT does not implement a second OWL object model, document parser, RDF-to-OWL mapper,
canonical OWL writer, import resolver, or general ontology store. The canonical Java-free
structural layer is distribution `pyowl-core`, import `pyowl_core`. pyHermiT 0.2.x requires
`pyowl-core>=0.2,<0.3` and Python 3.10 or later.

The shared structural language follows the OWL 2 Structural Specification. pyHermiT remains
responsible for OWL 2 DL profile/global-restriction validation and Direct Semantics
reasoning. Its normalized axioms, role model, clauses, datatype constraints, and tableau
state are private consumer IRs and are never added to or serialized as pyowl-core values.

## 1. Exact shared types

All public OWL values are the exact `pyowl_core` classes, not pyHermiT subclasses, wrappers,
proxies, or copied dataclasses. pyHermiT imports and may re-export by identity:

- `IRI`, `Literal`, `AnonymousIndividual`, entity and annotation values;
- all OWL 2 class expressions, data ranges, object/data-property expressions, and axioms;
- `OntologyDocument`, `OntologySnapshot`, `OntologyDelta`, and `OntologyOverlay`;
- the read-only `OntologyView` protocol and `OntologyComposite` sibling implementation;
- `SnapshotProvider`, `LoadOptions`, `ImportPolicy`, and `ParseLimits`; and
- core resolver, provenance, fingerprint, index, and input exception contracts.

Thus a class, axiom, or snapshot created in Exact-OM, pyELK, or a projector can be passed
directly to pyHermiT. Public results contain the same core entity/literal objects. Numeric
compiled IDs never replace public identity.

The old planned `src/pyhermit/model/` and syntax-specific `src/pyhermit/io/` values/parsers
are removed from scope. A re-export-only module may preserve a previously published import
path, but MUST define no runtime OWL classes.

## 2. Input API and standalone use

Conceptually, every construction API accepts:

```python
OntologyInput = (
    str
    | bytes
    | bytearray
    | memoryview
    | os.PathLike[str]
    | TextIO
    | BinaryIO
    | OntologyDocument
    | OntologyView
    | OntologySnapshot
    | OntologyOverlay
    | OntologyComposite
    | SnapshotProvider
)

def load_snapshot(
    source: DocumentInput,
    *,
    document_iri: IRI | str | None = None,
    options: LoadOptions | None = None,
    resolver: ImportResolver | None = None,
    cancellation_token: pyowl_core.CancellationToken | None = None,
) -> OntologySnapshot: ...
```

`load_snapshot` delegates exactly to `pyowl_core.load_snapshot` and returns a concrete
snapshot. Like the core function it accepts acquisition/document input only
(`pyowl_core.DocumentInput`); core rejects view/provider input to `load_snapshot`, and
pyHermiT never materializes a view to satisfy the concrete return type. Existing views
and providers are passed directly to `Reasoner`, whose `coerce_snapshot` retains them by
identity. Format selection, decoding, source
spans, parse/resource limits, syntax coverage, XML security, RDF mapping, canonical writing,
document IRI handling, import acquisition, and stream ownership are exclusively core
contracts. pyHermiT MUST NOT pre-read and rewind a source, parse it into RDF, or serialize it
to another OWL syntax before core loading.

A plain `str` is a filesystem path, never inline ontology text or a URL. Caller-owned binary
streams require `document_iri`; text streams require both `document_iri` and an explicit
format, exactly as in core. Inline text therefore uses an explicit `TextIO` rather than an
ambiguous string. URL acquisition belongs to an explicitly configured `ImportResolver`.

Core's `parse_document` parses exactly one document and records direct import IRIs without
resolving them. HermiT reasoning requires a closure and therefore uses `load_snapshot` or
`coerce_snapshot`, never treats a bare document's direct axioms as an implicit closure.

Standalone users can pass a path/stream directly to `Reasoner`. Shared callers pass an
existing ontology view/provider. All paths converge once at:

```python
captured = pyowl_core.coerce_snapshot(
    source,
    document_iri=document_iri,
    options=options,
    resolver=resolver,
    cancellation_token=cancellation_token,
)
```

Options incompatible with an existing view propagate core `OptionConflictError`; pyHermiT
never reparses to satisfy them. Before profile validation, it checks `view.capabilities` for
the compatible adapter/model and every complete OWL 2 constructor family. Missing capability
raises core `AdapterCompatibilityError` before private compilation.

## 3. Zero-reparse provider handshake

Coercion has the following normative behavior:

1. A compatible `OntologyView` (`OntologySnapshot`, `OntologyOverlay`, or
   `OntologyComposite`) is retained by identity. No public
   axiom, literal, entity, document, import graph, or shared index is copied.
2. `SnapshotProvider.owl_snapshot()` is called exactly once per reasoner construction.
   Exact-OM implements that protocol when it already owns a snapshot. pyHermiT MUST NOT
   import Exact-OM or traverse its private ontology records.
3. A document is assembled into a strict snapshot by core without reparsing; its imports
   still require the supplied resolver/policy.
4. Only path/bytes/stream inputs invoke core parsers. Each acquired import is loaded at most
   once under core's cache and cycle policy.
5. A legacy/foreign ontology requires an explicit adapter/provider. Structural duck typing
   or a fallback `str(obj)`/serialization path is forbidden.

`pyowl_core.compose_views(*views, delta=None, roles=None)` constructs a zero-copy
`OntologyComposite`, including the Exact-OM source + target + bridge/mapping use case. HermiT
validates and compiles the effective composite closure without concatenating component axiom
collections, while preserving component roles/provenance.

Reasoners communicate through the shared immutable view, not through another reasoner's
compiled data. pyHermiT MUST NOT accept pyELK indexes/saturation state, and pyELK MUST NOT
consume HermiT clauses/tableau state.

## 4. Strict import closure

HermiT validates and reasons over the complete imports closure. `Reasoner` requires every
view component's cached core `OntologyIdentityIndex` and report to prove a complete resolved
closure. The index supplies document keys, declared ontology/version IRIs, the exact
import-manifest digest, and loader-diagnostic digest without materializing a second manifest.
A complete `RESOLVE_LOCAL` view is valid; `RESOLVE_STRICT` is normally used when additional
configured resolvers are intended. A view with ignored, missing, failed, policy-blocked, or
otherwise unresolved imports is rejected
before OWL 2 DL validation with the appropriate core import error or a stable
`IncompleteImportClosureError` carrying stable core import-manifest and loader-diagnostic
digests plus the report's diagnostic codes.

Network access is never implicit. A standalone caller must explicitly supply a resolver and
load options that permit it. Cycles are legal and represented once per resolved document;
document boundaries and anonymous-individual scopes remain intact. pyHermiT does not
flatten the closure into a second public ontology collection.

## 5. OWL 2 DL profile validation

Validation runs over the captured effective closure before normalization. It is pyHermiT
work because it constrains the reasoner's semantic domain; core supplies structural values,
closure iteration, signatures, and generic indexes but does not decide HermiT acceptance.
Consumers use `view.iter_axioms(...)`, `view.signature(...)`, and lazily cached core
indexes/views; they do not reach into a concrete snapshot/overlay/composite layout.

### 5.1 Entity typing and reserved vocabulary

The validator MUST:

- enforce legal entity-type use and OWL 2 DL punning combinations;
- reject illegal reuse between object, data, and annotation properties;
- enforce built-in/reserved-vocabulary constraints;
- validate ontology/version IRIs and datatype/literal restrictions; and
- enforce the Structural Specification's declaration and built-in exceptions across the
  full axiom closure without weakening rules for undeclared property/class kinds.

The validator consumes core signatures/indexes directly and returns a pyHermiT-owned
`OWL2DLReport`. It never mutates or annotates the snapshot.

### 5.2 Object-property global restrictions

Compute the role relation over named properties and inverses, including chains, and verify:

- composite property-hierarchy regularity;
- non-simple-property definition and propagation;
- simple-property requirements for cardinalities, self restrictions, disjointness,
  irreflexivity, asymmetry, and other required positions;
- restrictions on top/bottom object properties and top data property; and
- every position/global condition in OWL 2 Structural Specification section 11.

The validator and HermiT role preprocessor share one private tested `RoleAxiomGraph`; they
MUST NOT maintain divergent algorithms. This graph is derived consumer IR, not a core index.

### 5.3 Datatypes, keys, and anonymous individuals

Validate datatype-definition dependencies, standard-map requirements, n-ary data forms,
keys, anonymous-individual restrictions, axiom closure requirements, and all remaining
global restrictions. Core literal parsing/structural identity is authoritative. HermiT's
datatype compiler derives semantic data-value/facet records without modifying the public
literal.

Validation diagnostics use stable rule IDs and source/provenance references supplied by
core. A failing report prevents normalization and backend selection.

## 6. Literal compatibility boundary

pyowl-core retains source spelling while exposing standards-canonical literal/language and
datatype identity. pyHermiT MUST NOT lowercase or rewrite the public `Literal`, and it MUST
NOT define a second literal equality relation in its public model.

The private datatype compiler may create:

- a source-literal ID for answer round-tripping;
- a standards-defined data-domain identity token; and
- datatype-family comparison/facet records.

Language-tag comparison consumes core's standards-canonical key; source diagnostics and
writers remain able to preserve the original spelling according to core. Any pinned HermiT
quirk is an explicitly named private compiler compatibility key with oracle tests and, when
standards-incompatible, a record in `deviations.md`.

## 7. Fingerprints and cache identity

pyHermiT consumes, without redefining, core fingerprints:

- source byte SHA-256 for acquisition provenance only;
- `document_fingerprint` for a canonical complete document;
- `structural_fingerprint` for the full resolved closure, annotations, import graph, and
  import-policy/resolution manifest;
- `logical_fingerprint` for the logical axiom closure; and
- `signature_fingerprint` for the finite public signature.

The HermiT compilation key binds at least:

```text
logical_fingerprint
+ signature_fingerprint
+ pyowl-core package SemVer and API_VERSION
+ MODEL_SCHEMA_VERSION
+ WIRE_FORMAT_VERSION
+ ADAPTER_PROTOCOL_VERSION
+ pyHermiT normalization/clause schema and semantic configuration
+ pinned HermiT compatibility identifier
```

`structural_fingerprint` and the strict resolution manifest key profile/provenance caches and
remain in capture diagnostics, but annotation/import-graph-only differences with the same
validated logical closure/signature may reuse semantic compiled IR. They MUST NOT reuse an
incompatible profile/import decision or misreport provenance.

It never uses source paths, timestamps, prefix spelling, syntax, parser traversal order,
Python hashes, object addresses, or canonical text serialization. Equivalent snapshots with
equal required fingerprints may share immutable compiled caches. A failed/cancelled compile
publishes nothing.

Anonymous-individual identity and alpha-canonical document scoping are core contracts.
Generated HermiT definition symbols derive from `logical_fingerprint` plus canonical
expression/polarity bytes and compiler schema; query-local symbols additionally include the
query hash. They never enter public answers.

## 8. Revisions, deltas, and overlays

There is no pyHermiT `OntologyRevision` or mutable ontology model. Updates use core values:

```python
next_view = pyowl_core.apply_delta(current_view, delta)
```

The exact immutable delta construction API/field names are owned by pyowl-core; pyHermiT
does not define a look-alike delta.

`OntologyOverlay` is an immutable read-through delta over a shared base view and is a sibling
of snapshots/composites, not a snapshot subclass. Buffered changes
remain pyHermiT-owned pending sets until `flush`; flush validates a proposed core overlay,
then atomically swaps the captured revision/session. A failed validation/compile keeps the
old view and pending changes.

Core alone applies explicit overlay depth/memory compaction policy. pyHermiT must not copy
the unchanged base merely to make an update. A backend may apply a proven `CompiledDelta`
incrementally, but public revision/fingerprint truth comes from the effective core overlay.
All unsupported change classes conservatively rebuild private compiled/session state.

## 9. Ownership, lifetime, and copy budget

Core documents/ontology views are immutable and may be shared concurrently. A
`Reasoner` holds a strong reference to its captured core view for its public lifetime and
through every native borrow. `dispose()` releases private caches/native memory but never
closes or invalidates the shared view; immutable result values remain usable.

Core closes only streams it opens. Caller-provided streams and resolver resources retain
their documented ownership. pyHermiT never stores parser streams or RDF graphs.

Required copy behavior:

- compatible view/provider input: zero reparses and zero structural-model copies;
- Python normalization/clausification: one necessary private HermiT compiled IR plus bounded
  work tables, iterating directly over core closure/index views;
- overlays: O(delta) shared-layer memory before consumer compilation, no eager base copy;
- native transfer: prefer borrowed/mmap/`memoryview` bulk buffers, otherwise at most one
  contiguous private-IR copy per session; and
- no per-axiom/rule Python↔Rust calls, text/RDF intermediate, or Python callback in a native
  hot loop.

These rules do not prohibit optimized private role/clause/tableau structures. They prohibit
duplicating the general OWL structural layer.

## 10. Version and adapter compatibility

- Packaging requires `pyowl-core>=0.2,<0.3`; the current public contract line is 0.2.x.
- Runtime compatibility requires core `API_VERSION=(0, 2)`, `MODEL_SCHEMA_VERSION=2`,
  `WIRE_FORMAT_VERSION=(1, 2)`, and adapter protocol version 1. Older model and encoded-view
  schemas fail before profile validation; they are never interpreted optimistically.
- Compatibility reads `API_VERSION` and parses package SemVer; it never compares
  `__version__` strings lexically.
- Providers/adapters declare `ADAPTER_PROTOCOL_VERSION` and compatible model/API versions.
  Mismatch fails before profile validation with expected/actual diagnostics.
- Core persistence uses only `encode_snapshot`, `decode_snapshot`, and
  `open_snapshot(path, mmap=True, verify=True)`. Its magic is `PYOCORE\0` and its independent
  `WIRE_FORMAT_VERSION=(major, minor)` hard-fails on major mismatch and requires minor 2 or
  later within major 1; unknown optional same-major sections may be skipped.
- Persistent caches bind package/API SemVer, `MODEL_SCHEMA_VERSION`,
  `WIRE_FORMAT_VERSION`, `ADAPTER_PROTOCOL_VERSION`, all required fingerprints, and the
  consumer compiler schema. Incompatible/corrupt caches are discarded and rebuilt, never
  interpreted optimistically.
- HermiT's private clause/native wire is separately versioned and MUST NOT be exposed as a
  pyowl-core snapshot or consumed by another package.

Optional adapters are loaded only by explicit use. Importing pyHermiT performs no adapter
discovery, I/O, native probing, network access, or Java startup.

Standalone and shared use have the same facade:

```python
from pyhermit import Reasoner

with Reasoner("large.owl") as reasoner:          # core loads once
    consistent = reasoner.is_consistent()

view = exact_om_run.owl_snapshot()
with Reasoner(view) as reasoner:                 # same object, zero parse
    coherent = reasoner.is_consistent()

bridge = pyowl_core.OntologyDelta(add_axioms=frozenset(mapping_axioms))
combined = pyowl_core.compose_views(source, target, delta=bridge,
                                    roles=("source", "target"))
with Reasoner(combined) as reasoner:             # no component concatenation
    repaired = reasoner.is_consistent()
```

## 11. Acceptance requirements

1. Every public OWL/core re-export has class identity equality with `pyowl_core`; no
   pyHermiT structural wrapper/model class exists.
2. Path, bytes, text/binary stream, document, snapshot, overlay, composite, and provider inputs produce
   identical validated/compiled semantics. Non-source inputs invoke no parser; provider is
   called exactly once.
3. Reasoner construction accepts only a proven strict resolved closure. Cyclic imports,
   anonymous document scopes, duplicate ontology IDs, limits, and resolver failures follow
   core behavior without a second traversal.
4. The complete OWL 2 DL global-restriction corpus is accepted/rejected over core snapshots,
   with diagnostics linked to core provenance.
5. Syntax/path/prefix/import-order/hash-seed permutations with equal fingerprints produce
   deterministic private IDs/IR/results.
6. Literal tests separate exact shared public identity/source preservation from private
   HermiT data-domain and any compatibility keys.
7. Million-axiom, deep-overlay, and source/target/bridge composite benchmarks show no
   duplicate/concatenated public axiom collection, bounded temporary memory, and no
   serialization intermediate.
8. Version mismatch, corrupt cache, mmap lifetime, caller stream ownership, dispose, failed
   flush, and overlay compaction boundaries are tested.
9. Standalone and Exact-OM-style provider tests run on CPython 3.10 and 3.12 with no Java;
   Java is available only in an explicitly selected development-oracle lane.
