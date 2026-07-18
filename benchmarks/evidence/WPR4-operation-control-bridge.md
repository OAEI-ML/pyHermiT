# WPR4 native operation-control bridge evidence

This prerequisite connects the object-safe session `OperationControl` to the four
component control contracts needed by a composite `NativeTableau`: datatype, role,
blocking, and existential expansion.  It is pure Rust and imports neither PyO3 nor a
Python callback boundary.

## API and integration shape

`OperationControlBridge::new(&dyn OperationControl)` is one concrete, `Send + Sync`
adapter implementing `DatatypeControl`, `RoleControl`, `BlockingControl`, and
`ExpansionControl`.  A composite call has one mandatory finish step:

```text
let bridge = OperationControlBridge::new(control);
let result = datatype_scheduler.check_dirty(..., &bridge);
bridge.finish_datatype(result)
```

Equivalent one-shot finish methods exist for roles, blocking, and expansion.  The
module also exposes `datatype_error_to_native`, `role_error_to_native`,
`blocking_error_to_native`, and `expansion_error_to_native` for component-originated
failures.  The composite integration needs to declare the module in `lib.rs` and may
re-export those five API names; this tranche deliberately does not edit shared exports.

## Lossless distinction proof

The component cancellation variants cannot represent a session timeout separately,
and their static limit fields cannot represent an arbitrary operation-control context.
Widening four component error enums is unnecessary: before returning the narrower
component token, the bridge moves the first original `NativeError` into an inline
`OnceLock`.  Each `finish_*` method consumes the bridge and extracts that error exactly
once.  Therefore:

- cancellation and timeout retain distinct `ErrorKind`, code, message, and context;
- resource failures retain the exact dynamic limit/observed/allowed values;
- invariant or poisoned operation failures retain their original severity;
- a later component error cannot replace the first operation failure; and
- even an erroneous component `Ok` cannot swallow a failed poll or memory observation.

If no operation-control failure occurred, the typed converters map the component's
own declared semantics directly:

| Component kind | Native kind/code |
|---|---|
| datatype/role invalid | `Wire`, component-specific `NATIVE_*_INVALID` |
| blocking/expansion invalid input | `Wire`, component-specific `NATIVE_*_INVALID` |
| cancelled | `Cancelled`, component-specific `NATIVE_*_CANCELLED` |
| resource | `Resource`, `RESOURCE_LIMIT`, with every present limit field copied |
| blocking/expansion invariant | `Invariant`, component-specific `NATIVE_*_INVARIANT` |

`ExpansionControl::add_work` has no equivalent session-control operation.  The bridge
does not misreport work as memory: expansion retains its own bounded work accounting
and invokes `poll` at the configured intervals.

The successful bridge path adds one inline `OnceLock` and no allocation, lock, dynamic
dispatch beyond the supplied `&dyn OperationControl`, or reference-counted owner.  On
failure, the original `NativeError` is moved rather than cloned; only the temporary
component message required by that component's existing contract is copied.

## Focused coverage

The standalone native integration target compiles the production module without a
`lib.rs` change and proves:

- cancellation versus timeout round trips through datatype and role controls;
- memory/resource context survives a blocking failure and a swallowed `Ok` result;
- invariant operation failures survive expansion's component token;
- multiple component polls keep first-failure precedence;
- all four typed converters preserve stable kinds, codes, and resource fields; and
- one `&dyn OperationControl` bridge implements all four traits and remains `Send + Sync`.

## Verification

Run on 2026-07-18 with rustc/cargo 1.97.1:

```text
cargo fmt --manifest-path native/Cargo.toml -- --check
cargo test --manifest-path native/Cargo.toml --no-default-features
cargo clippy --manifest-path native/Cargo.toml --all-targets \
  --no-default-features -- -D warnings
```

All gates passed in the final worktree.  The native library reported 158 passing tests,
the operation-bridge integration target reported six, and no test failed.
