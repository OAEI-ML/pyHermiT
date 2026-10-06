# Native compilation resource limits

## Scope and compatibility

The encoded native compiler accepts explicit memory and work allowances without changing
ontology admission, inference, canonical identity, datatype policy, or public symbol mappings.
This restores the compilation resource controls independently of the symbol-index allowance.
It does not establish full NCIT admission or a capacity/time guarantee.

`ReasonerConfig.max_compile_work` is an optional keyword-only positive unsigned 64-bit integer.
`None` leaves historical phase defaults (2,000,000,000 units) unchanged. Existing positional
arguments, omitted configuration mappings, wire bytes, and compiler-cache identities remain
unchanged. Old 0.2.1 and released 0.2.2 pickles restore with the new field unset, including on
Python 3.10; current round trips validate the restored fields. Explicit work values partition
cache identity independently of `max_native_symbol_index_bytes` and `require_native_pipeline`.

The compatible extension advertises `native-compilation-resource-limits-v1`. The allowance
travels as an optional private encoded-constructor keyword, without changing fixed ConfigWire
bytes or the existing index section. Python, VERIFY, incompatible extensions, and scalar-wire inputs
fail closed for explicit work requests; AUTO cannot replace them with a fallback that ignores
the request. VERIFY preflight and its Python reference compiler do not implement this work
allowance, so an explicit request is rejected before loading.

## Resource behavior

An explicit `max_memory_bytes` reaches profile validation and context assembly, structural
compiler phases and final permanent-program assembly/serialization. Private diagnostic byte
limits may tighten but never exceed the configured public allowance. Omitted memory settings
retain the historical 512 MiB compiler ownership/manifest defaults. Profile manifest handoffs
also read an explicitly configured cancellation-handle memory allowance, including when no
Python cancellation token was supplied.

Profile accounting distinguishes retained canonical data from temporary encodings, releasing
the latter once copied into a parent. It accounts for traversal marks by their allocated byte
size. Failure reports structured `current_bytes`, `requested_bytes`, and `max_owned_bytes`
where that ownership budget rejects an allocation. These are deterministic internal estimates,
not comprehensive process RSS or additive accounting of every live allocation. OS resource
controls remain the hard process boundary.

The work allowance reaches structural validation, profile checks, symbols, fingerprints,
structural phases, slice merges, and permanent-program assembly. Counters remain checked;
exact-boundary use succeeds and excess or arithmetic overflow fails. Budgets are maintained
by the existing compiler phases and aggregate slice operations, not a new single global counter.
Failures expose `limit=compilation-work` and current/requested/maximum work where available.
Cancellation and timeout checkpoints still run, including with the maximum u64 allowance;
failed construction publishes no partial session and a clean retry remains possible.

The independent 64 MiB default symbol-index estimate, configurable published index option,
legacy 64 MiB JSON export limit, shape/depth limits, strict datatype policy, and query semantics
are unchanged. Increasing one allowance does not raise the others.

## Required validation

Exercise actual compiled native code with small deterministic fixtures: tiny memory/work
rejection then raised-limit semantic parity, canonical scratch ownership release, exact work
boundary and checked overflow, combined symbol/work/deferred identity and mismatch rejection,
and cancellation/transactional retry with explicit raised work. Preserve scalar/native parity,
strict datatype rejection, released configuration wire goldens, constructor positions and
historical pickle compatibility. Run source licensing/hash and existing release authorization
checks without changing their policy. Build only in an isolated checkout/environment; runtime
experiments and installed packages are outside validation scope.
