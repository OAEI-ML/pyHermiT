# WPR3 native dirty datatype scheduler evidence

This tranche adds the isolated native scheduler for exact datatype constraint
components. It consumes the already committed `solve_component` implementation and
does not duplicate or approximate datatype satisfiability.

## State and adapter contract

The scheduler is deliberately separate from tableau storage until the session adapter
lands. Every projected variable is keyed by all three values needed for safe reuse:

- the stable concrete-node creation ID used as the solver variable;
- the native node arena slot; and
- the node slot generation.

Constraint records likewise carry slot/generation handles plus a stable diagnostic
participant ID. Reusing a node or constraint slot cannot alias an older generation.
Stable creation IDs cannot silently move to another node handle. Removed generations
remain historical until rollback, so a late queue event fails closed rather than
mutating the replacement object.

The eventual tableau adapter has four explicit obligations:

1. project every active range, fixed value, equality, inequality, and cardinality
   assertion, using one currently sufficient dependency support;
2. call upsert/remove whenever that active projection or its selected support changes;
3. capture `SchedulerCheckpoint` beside the store checkpoint and roll both back as one
   logical operation; and
4. never treat scheduler participant IDs as backjumping support—the committed solver's
   returned `DependencySet` remains authoritative.

The current files implement and test that component boundary; they do not claim that
`TableauKernel` already invokes it.

## Dirty scheduling behavior

- Constraint mutations mark every old and new endpoint dirty and immediately invalidate
  only intersecting certificates.
- Indexed breadth-first traversal starts only from dirty variables. Multiple dirty
  variables in one connected equality/inequality component coalesce into one solver
  call.
- Adding a bridge checks the merged component once. Removing a bridge checks each new
  split component once. Unrelated cached components are neither traversed nor solved.
- Removed last constraints leave generation-stamped orphan dirties that invalidate old
  certificates without creating empty solver components.
- Component, constraint, participant, and variable order uses ordered collections and
  stable IDs; hash iteration cannot affect the schedule or selected clash.
- A detected clash is cached and remains observable until rollback or a mutation of its
  component. Later dirty components are retained rather than allowing an apparent SAT
  result to hide the existing contradiction.

Planning and solving are read-only. Dirty flags and certificates commit only after the
last cancellation poll succeeds. Cancellation, caller memory rejection, scheduler
limits, or solver limits therefore return with byte-for-byte-equivalent logical
scheduler diagnostics. Successful clash detection is a logical result and commits only
the components actually checked before the clash.

## Checkpoint and resource behavior

Checkpoints are owner-stamped snapshots with monotonically increasing sequences.
Rollback restores constraints, indexes, generation history, dirties, certificates, and
revision together; future checkpoint tokens become stale, while the selected checkpoint
can be reused for another branch alternative. Cross-scheduler tokens fail closed.
Checkpoint count and observed snapshot memory are bounded before cloning.

Separate positive limits cover active constraints, active variables, dirty variables,
components per check, scheduler work, checkpoint count, and cancellation-poll stride.
The committed solver independently retains its variable, constraint, and search-step
limits.

## Focused verification

Nine isolated Rust tests cover:

- dirty coalescing and no-work cache hits;
- selective rechecking of one affected component;
- bridge merge and split scheduling;
- exact solver clash dependencies and deterministic participants;
- checkpoint rollback and stale/foreign checkpoint rejection;
- recycled node and constraint generations;
- cancellation, memory rejection, scheduler limits, and solver limits without partial
  mutation;
- persistent visibility of an early clash; and
- bounded checkpoint release.

The isolated module passes the crate-equivalent strict Clippy policy (`all`, `pedantic`,
`nursery`, `unwrap_used`, `expect_used`, and `panic` denied), Rust formatting, and all
nine tests. No Java or runtime reference implementation participates.

Artifact SHA-256 digests at capture time:

| artifact | SHA-256 |
|---|---|
| `native/src/datatypes/scheduler.rs` | `88ea8bf9c81c1049f8db2b30f5436e916b968dc41780c0e470bb34baf4df9144` |
| `native/src/datatypes/scheduler_tests.rs` | `4c301e2c069419ba7713e6519be24ad019e2d95157c126a579b554c5ab40da33` |

## Reproduction after module export

```text
cargo fmt --manifest-path native/Cargo.toml -- --check
cargo test --manifest-path native/Cargo.toml \
  datatypes::scheduler::tests
cargo clippy --manifest-path native/Cargo.toml --lib --tests -- -D warnings
```
