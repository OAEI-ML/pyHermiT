# Migrating to pyHermiT 0.2

pyHermiT 0.2 moves its shared ontology boundary from pyowl-core 0.1 to 0.2. The
reasoner facade and result shapes are unchanged, but the core model and encoded
structural contracts are intentionally incompatible.

## Upgrade together

Install matching release lines in one environment:

```shell
python -m pip install --upgrade "pyowl-core>=0.2,<0.3" "pyHermiT>=0.2,<0.3"
```

pyHermiT now requires core API `(0, 2)`, model schema `2`, wire format major `1`
with minor `2` or later, and adapter protocol `1`. A 0.1 core installation fails
before ontology profile validation or backend selection.

## Rebuild persisted data

Do not reuse any of the following across the 0.1/0.2 boundary:

- bytes written by `pyowl_core.encode_snapshot`;
- mmap/opened snapshot files created by pyowl-core 0.1;
- encoded structural-view descriptors, fingerprints, or dense IDs; or
- pyHermiT/private consumer caches keyed by a core model, wire, or fingerprint value.

Reload the original ontology source with pyowl-core 0.2, re-encode snapshots as
needed, and allow each consumer to rebuild its cache. pyHermiT validates these
identities fail closed rather than guessing whether old bytes are compatible.

## Native ingestion

The 0.2 native accelerator advertises `encoded-structural-compiler-v2` and accepts
only `pyowl-core/structural-columns` schema 2. Snapshots, overlays, and composites
can use the direct `encoded-native` path. Scalar-only compatible providers continue
to use the complete `scalar-python` or `scalar-wire` paths.

The private pyHermiT compiler-cache, compiled-IR, and native ABI schema constants
remain at version 1 because their record layouts did not change. Cache identity also
includes the core API/model/wire versions, descriptor digest, and fingerprints, so
old entries are still invalidated deterministically.
