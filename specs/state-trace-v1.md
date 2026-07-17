# State trace v1

WP08 freezes this language-neutral replay boundary for WPR0. It is a parity/testing
format, not a public API and not the compiled ontology wire format.

## Envelope and canonicalization

The UTF-8 JSON document has exactly three fields:

```json
{"magic":"PYHERMIT-STATE-TRACE","operations":[],"version":1}
```

Serialization uses lexicographically sorted object keys, no insignificant whitespace,
UTF-8 characters without ASCII escaping, and no trailing newline. Duplicate keys,
floating-point values, unknown fields, unknown operation kinds, and non-JSON runtime
objects are rejected. Arrays retain order. Set-like values such as dependencies and
participants are supplied in their canonical ascending order and validated by the
state primitive that consumes them. SHA-256 is calculated over the exact canonical
UTF-8 bytes.

Nodes are referenced by trace-local string aliases assigned by `create_node`. Aliases
are never Python object representations or memory addresses. Predicates, compiled
atoms/disjuncts, provenance, sources, rows, and datatype components use nonnegative
integer IDs from the private compiled IR/state sequence.

Each operation is encoded as:

```json
{"arguments":{"name":"a","kind":"root"},"kind":"create_node"}
```

The Python source of truth for exact required/optional fields and replay validation is
`pyhermit.backends.python.state.trace`. WPR0 must accept precisely the same schema.

## Operations

| Kind | Required arguments | Optional arguments |
|---|---|---|
| `create_node` | `name`, `kind` | `parent`, `is_owl_named_individual`, `source_individual_id`, `nominal_level`, `cardinality_tag` |
| `begin_operation` | — | — |
| `add_fact` | `predicate_id`, `arguments`, `dependency` | `core`, `provenance_id` |
| `prepare_delta` | — | — |
| `push_branch` | `choice_kind`, `alternatives`, `source_id`, `dependency` | — |
| `advance_branch` | `level`, `dependency` | — |
| `backtrack` | `level` | — |
| `merge` | `left`, `right`, `dependency` | — |
| `prune` | `root` | — |
| `add_disjunction` | `disjunct_ids`, `dependency` | — |
| `take_disjunction` | — | — |
| `install_clash` | `kind`, `dependency` | `participants`, `provenance_id` |
| `enqueue` | `queue`, `value`, `priority` | — |
| `mark_existential` | `node`, `existential_id`, `pending` | — |
| `set_blocked` | `node`, `blocker`, `directly` | — |
| `check` | — | — |

`dependency` is an ascending array of branching levels. `priority` is an integer array
whose tuple must uniquely include the stable ID. `blocker` may be null. Trace queues are
`delta_rows`, `annotated_equalities`, `existential_candidates`, `datatype_components`,
and `blocking_invalidations`; the ground-disjunction queue is changed only by its
dedicated operations.

## Replay result

After every operation the implementation runs the expensive invariant checker and
emits the canonical logical snapshot JSON. WPR0 replays the same operation sequence
and compares every snapshot byte-for-byte. Physical layouts may differ, but node
handles/generations, active rows/supports, delta generations, branches, queues,
disjunctions, and the current clash must match.

Schema changes require a new integer version and new golden fixtures. Version 1 must
never be reinterpreted in place.
