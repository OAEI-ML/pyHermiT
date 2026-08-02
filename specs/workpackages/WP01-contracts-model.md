# WP01 — pyowl-core contracts, re-exports, and reasoner boundary

**Goal**: adopt `pyowl-core>=0.2,<0.3` as the sole public OWL structural layer,
freeze pyHermiT's private compiled/backend/result contracts, and remove the planned duplicate
model while preserving exact public core class identity.

## Read first

| Authority | Required scope |
|---|---|
| Master | `SPEC.md` §§3–6 |
| Normative | `ontology-model.md`; `contracts.md`; `deviations.md` licensing sections |
| pyowl-core | 0.2 model, snapshot, overlay, version, adapter, ownership contracts |
| Java semantic IR | pinned `model/`, `Configuration.java`, `Reasoner.java` public defaults |

## Deliverables

- `pyowl-core>=0.2,<0.3` typed dependency and guards for package SemVer/`API_VERSION`,
  `MODEL_SCHEMA_VERSION`, `WIRE_FORMAT_VERSION`, and `ADAPTER_PROTOCOL_VERSION`.
- Exact re-exports for every OWL expression/axiom/entity/literal and core document,
  view, snapshot, delta, overlay, composite, options, resolver, and provider value; no wrapper classes.
- `OntologyInput`, captured-view metadata, deterministic compiler-cache key, and identity-
  preserving core `AdapterCompatibilityError`/`OptionConflictError` propagation.
- Frozen `ReasonerConfig`, backend metadata/protocol, cancellation/events, hierarchy and
  realization result records, and public exception taxonomy.
- `CompiledOntology`/query/delta skeleton records remain private HermiT IR and bind the
  captured core fingerprints/versions without becoming a shared structural model.
- Removal of planned `src/pyhermit/model/` values; a compatibility module, if required by an
  actually published release, contains re-exports only.
- Unit/property tests for core type identity, no-import side effects, configuration, IDs,
  generated names, contract validation, fingerprints, and canonical diagnostic JSON.

## Depends on

WP00 and an available pyowl-core 0.2 contract/release.

## Acceptance criteria

1. Every public OWL type is identical (`is`) to its `pyowl_core` class and every in-scope
   construct is representable without a pyHermiT model class.
2. Public values are immutable/shareable; private IR validates IDs/sorts/schema and exposes
   no backend pointer or generated symbol.
3. Compatible core 0.2 objects pass; incompatible API/model/wire/adapter contracts fail
   before parsing/profile/backend work with expected/actual diagnostics.
4. Generated IDs/names and cache keys are deterministic across hash/order/Python 3.10/3.12
   and use core fingerprints rather than serialized OWL text or source paths.
5. Core literal identity/source preservation is untouched; HermiT data/compatibility keys
   are absent from the public model.
6. Imports do not load parser, tableau, native extension, network, or Java code.
