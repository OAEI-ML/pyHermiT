# Native symbol-index resource limits

## Motivation and scope

Native symbol lookup maps retained public objects to stable native identifiers without
reconstructing an ontology-sized Python intermediate representation. Its estimated storage
previously shared the fixed 64 MiB ceiling used for legacy service-context JSON export.
A large input can exhaust the index estimate while remaining below its configured operation
memory allowance. This capability makes that one resource ceiling explicitly configurable.
It neither adds datatype support nor changes profile admission, logical axioms, inference,
canonical ordering, public symbol identity or the legacy export ceiling.

## Compatibility contract

- `ReasonerConfig.max_native_symbol_index_bytes` is an optional keyword-only positive u64.
  `None` retains 64 MiB. Existing positional constructor arguments remain unchanged.
- Existing 0.2.1 pickled configurations retain field alignment and load with the new limit
  unset; current round trips validate all fields.
- Omitted options preserve the existing configuration mapping, cache identity and encoded
  configuration bytes. An explicit bound partitions configuration/cache identities.
- A compatible native extension advertises `native-symbol-index-limit-v1`. Explicit requests
  fail before ontology loading on unsupported backends; AUTO cannot silently fall back.
- The bound applies where a native symbol index is constructed. Native scalar-wire and
  verification paths may use Python mappings instead; this is not a bound on those mappings.
  `require_native_pipeline=True` remains the separate native-only admission contract.
- The configuration is immutable for the session. Constructing or reacquiring the native index owner observes
  its memory estimate and cooperative cancellation. Failure publishes no partial index.
- The estimate includes canonical key lengths and existing per-entry overhead. Its boundary
  is inclusive: an estimate equal to the ceiling is allowed, and a larger one is rejected.
  Overflow and invalid values fail explicitly. The general memory control still applies.
- The existing 64 MiB serialized service-context ceiling is independent and unchanged.
- Memory observations are high-water estimates, not additive live allocation or RSS tracking.
  No hard total-memory guarantee or unmeasured ontology-size/performance claim is made.

An internal profile handoff must pass an explicit memory budget to native validation even
when the caller provides no Python cancellation token. Existing cancellation attachment and
default calls retain their behavior. Unsupported datatype declarations and logical uses
continue to follow the unchanged strict admission policy.

## Verification boundary

Required coverage: default configuration and wire goldens; constructor/type/u64 validation;
old-extension capability rejection; AUTO/Python selection; explicit cache partitioning;
exact index boundary and raised-limit success; cached reuse after memory/cancellation changes;
native/legacy symbol identity and ordering; semantic query equivalence; strict datatype
rejection; internal memory-only profile handoff. Tests must exercise compiled Rust in addition
to Python adapters.

Build and test in an isolated checkout/environment. Installed packages and active sessions
are outside this PR's mutation scope. Local fixture verification does not establish full NCIT
admission, completion time, platform-wide wheel compatibility, or release readiness. Do not
publish a package, regenerate reference goldens or replace a running application's wheel as
part of validating this change.
