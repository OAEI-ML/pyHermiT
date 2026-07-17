# WP02 — Snapshot ingestion, imports, and OWL 2 DL validation

**Goal**: implement the thin pyowl-core input/provider adapter and complete OWL 2 DL
profile/global-restriction validator. Do not implement or fork a parser, RDF mapper, writer,
resolver, ontology model, or import store.

## Read first

| Authority | Required scope |
|---|---|
| Normative | `ontology-model.md`; `reference-scope.md` structural fate; `verification.md` input gates |
| Shared core | `parse_document`, `load_snapshot`, `coerce_snapshot`, views/imports/limits |
| OWL standards | structural syntax, RDF mapping, OWL 2 DL global restrictions |
| Java behavior | pinned `structural/` validation/role preprocessing observations |

## Deliverables

- `load_snapshot` convenience and one-call `coerce_snapshot` capture for paths, bytes,
  streams (with the core-required root document IRI/format), documents, snapshots, overlays,
  composites, and `SnapshotProvider`, including acquisition cancellation passthrough.
- Exact-OM handshake solely through `owl_snapshot()` with identity/lifetime and counting
  tests; no Exact-OM import or legacy-record conversion.
- Complete-import-manifest enforcement through the cached core `OntologyIdentityIndex`
  before validation (`RESOLVE_STRICT` normally, or a proven-complete local policy);
  rejection carries the core import-manifest and loader-diagnostic digests and never
  silently reasons over partial data.
- Complete OWL 2 DL entity typing, reserved vocabulary, declarations/punning, property
  simplicity/regularity, datatype, key, anonymous-individual, and global-restriction report.
- Shared private `RoleAxiomGraph` contract with role preprocessing, built directly from core
  closure/index views without copying the public ontology.
- Core fingerprint/version/cache capture plus zero-copy document identities and stable
  overlay/import/provenance digests from `OntologyIdentityIndex`.
- Zero-copy `compose_views` support for source/target/bridge inputs with strict resolution
  validation of every component and preserved component roles.
- Adapter/profile property, malformed-provider, strict-import, conformance, memory, ownership,
  and zero-reparse tests; consume core parser conformance rather than duplicate it.
- Delete planned syntax parser/RDF mapping modules. `src/pyhermit/io/` contains only the
  input adapter/re-export compatibility surface if retained.

## Depends on

WP01 and WP05 (shared role-validation contract).

## Acceptance criteria

1. All input forms yield equal semantics; document/snapshot/overlay/composite/provider invokes no
   parser and a provider is called once.
2. Every Reasoner input has a proven strict resolved closure; cycles are handled once and
   ignored/missing imports fail before profile validation.
3. The OWL 2 DL global-restriction corpus is accepted/rejected exactly over the complete
   closure with stable rule IDs and core provenance.
4. Million-axiom snapshot and O(k)-overlay tests show no second public axiom collection,
   serialization intermediate, or pyHermiT-owned base compaction; composites concatenate no
   component axiom collection.
5. Equivalent syntax/path/prefix/import order gives the same required fingerprints, profile
   report, and compiler observations.
6. Model/input/profile tests import neither backend nor Java and run on Python 3.10/3.12;
   caller streams and shared snapshot lifetime follow core ownership contracts.
