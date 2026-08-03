# Errors and exceptions

pyHermiT reports failures through three distinct channels, so a caller can always
tell *where* a problem happened:

1. **Python argument-contract errors.** Passing the wrong type or an invalid value to
   a facade member raises ordinary `TypeError` or `ValueError` before any reasoning
   work starts. These are programming errors, not reasoning outcomes.
2. **pyowl-core boundary errors.** Failures during ontology acquisition, parsing,
   import resolution, or resolver execution propagate unchanged from `pyowl_core`.
   pyHermiT never wraps or re-raises them, so existing pyowl-core error handling
   keeps working.
3. **pyHermiT errors.** Everything produced after the pyowl-core input boundary —
   profile validation, backend selection, compilation, and reasoning — derives from
   `pyhermit.PyHermiTError`.

All classes below are importable directly from `pyhermit`.

## Structured error data

Every `PyHermiTError` carries a stable machine-readable payload in addition to its
human-readable message:

- `code` — an upper-case identifier such as `REASONER_TIMEOUT`. Codes are stable
  across releases and are the right key for programmatic handling.
- `context` — an immutable sorted mapping of scalar diagnostic values.
- `as_dict()` — returns `{"code": ..., "context": ..., "message": ..., "type": ...}`
  for logging and structured reporting.

Messages are diagnostic text only; they may change between releases and are not a
compatibility key. Match on the class or the `code`.

```python
from pyhermit import PyHermiTError, Reasoner

try:
    with Reasoner(view) as reasoner:
        reasoner.is_consistent()
except PyHermiTError as error:
    log.error("reasoning failed: %s", error.as_dict())
```

## Exception hierarchy

```text
PyHermiTError                        PYHERMIT_ERROR
├── OntologyInputError               ONTOLOGY_INPUT_ERROR
│   ├── IncompleteImportClosureError INCOMPLETE_IMPORT_CLOSURE
│   ├── OntologyProfileError         ONTOLOGY_PROFILE_ERROR
│   ├── InvalidLiteralError          INVALID_LITERAL
│   └── UnsupportedDatatypeError     UNSUPPORTED_DATATYPE
├── ReasonerStateError               REASONER_STATE_ERROR
│   ├── DisposedReasonerError        DISPOSED_REASONER
│   ├── InconsistentOntologyError    INCONSISTENT_ONTOLOGY
│   ├── FreshEntityError             FRESH_ENTITY
│   └── ConcurrentMutationError      CONCURRENT_MUTATION
├── ReasoningAbortedError            REASONING_ABORTED
│   ├── ReasonerTimeoutError         REASONER_TIMEOUT   (also TimeoutError)
│   ├── ReasonerInterruptedError     REASONER_INTERRUPTED
│   └── ResourceLimitError           RESOURCE_LIMIT
├── BackendError                     BACKEND_ERROR
│   ├── NativeBackendUnavailableError NATIVE_BACKEND_UNAVAILABLE
│   ├── BackendVersionError          BACKEND_VERSION
│   ├── BackendMismatchError         BACKEND_MISMATCH
│   └── BackendPoisonedError         BACKEND_POISONED
├── FeatureNotImplementedError       FEATURE_NOT_IMPLEMENTED (also NotImplementedError)
└── InternalInvariantError           INTERNAL_INVARIANT
```

## Input and profile errors

Raised while validating the ontology before any reasoning session exists.

| Exception | Raised when |
|---|---|
| `OntologyInputError` | The supplied input cannot be accepted at the pyHermiT boundary; parent of the specific classes below. |
| `IncompleteImportClosureError` | Reasoning requires a complete import closure and a required import was ignored or unresolved. Supply a core resolver or pre-resolved view. |
| `OntologyProfileError` | The view violates the OWL 2 DL profile restrictions pyHermiT enforces. |
| `InvalidLiteralError` | A literal is rejected by the HermiT semantic datatype layer. Parse-time `pyowl_core.InvalidLiteralError` values are a deliberately distinct class and propagate unchanged. |
| `UnsupportedDatatypeError` | The ontology uses a datatype outside the supported map and `ReasonerConfig.unsupported_datatypes` is `ERROR` (the default). |

## Reasoner state errors

Raised when an operation is invalid for the current session state.

| Exception | Raised when |
|---|---|
| `DisposedReasonerError` | A semantic, update, precompute, or interrupt operation is invoked after `dispose()`. The `ontology`, `config`, and `backend` properties remain readable. |
| `InconsistentOntologyError` | The ontology is inconsistent and the requested service has no classically meaningful answer. `is_consistent()` itself returns `False` instead of raising; inconsistency is never silently converted to an empty result set. |
| `FreshEntityError` | A query mentions an entity absent from the ontology signature while `ReasonerConfig.fresh_entities` is `DISALLOW`. |
| `ConcurrentMutationError` | The same thread re-enters an active operation, including reentrant `dispose()` from inside an operation. Calls from *different* threads do not raise; they wait and run serially. |

## Aborted operations

A timeout, interrupt, or resource stop is an aborted operation, never a logical
`False` answer. Operation-local state is rolled back before the next query is
allowed, so the reasoner remains usable afterwards.

| Exception | Raised when |
|---|---|
| `ReasoningAbortedError` | Parent class; catch this to handle every cancellation cause uniformly. |
| `ReasonerTimeoutError` | The per-operation `ReasonerConfig.timeout` elapsed. Also a `TimeoutError` for generic handlers. |
| `ReasonerInterruptedError` | Another thread called `Reasoner.interrupt()` during the operation. |
| `ResourceLimitError` | A configured resource bound such as `max_memory_bytes` was exceeded. Carries `limit`, `observed`, and `allowed` attributes. |

## Backend errors

| Exception | Raised when |
|---|---|
| `BackendError` | Parent class for backend selection and protocol failures. |
| `NativeBackendUnavailableError` | `BackendName.NATIVE` (or `VERIFY`) was requested but the extension is missing, failed to import, or failed its handshake. Explicit native selection is fail-closed and never silently falls back to Python. |
| `BackendVersionError` | The extension is present but its ABI, IR schema, core versions, or capability surface do not match this pyHermiT build. |
| `BackendMismatchError` | `BackendName.VERIFY` observed any difference between the native answer and the independent Python shadow. |
| `BackendPoisonedError` | A session refuses further operations after an earlier fatal observation — a verify-mode differential mismatch or an invalid native result. Create a new reasoner. |

## Other errors

| Exception | Raised when |
|---|---|
| `FeatureNotImplementedError` | A declared-but-incomplete feature was reached. Carries a stable `feature_id` and is also a `NotImplementedError`. |
| `InternalInvariantError` | An internal consistency check failed. This always indicates a pyHermiT bug worth reporting, not a caller mistake. |

## See also

- [User guide — time, memory, cancellation, and errors](user-guide.md#time-memory-cancellation-and-errors)
- [API reference](api-reference.md)
- The normative exception contract in [`specs/contracts.md`](../specs/contracts.md)
