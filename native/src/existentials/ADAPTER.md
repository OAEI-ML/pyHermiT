# Native existential adapter seam

`existentials` is deliberately `std`-only and is tested directly from `mod.rs`.
`adapter.rs` now translates its small values to the crate's `NodeHandle`,
`DependencySet`, `NodeKind`, `GroundAtom`, and `NativeError` at one coarse Rust
operation boundary.

## Integrated `TableauKernel` reads/mutations

- `canonical_handle`, `active_node_handles`, `active_node`, and `node_rank`;
- `candidate_fact_ids` plus `fact` for stable fact/support reads;
- `create_node`, `mark_existential`, `enqueue_node`, and `install_clash`;
- `clash`, `branch`, `push_branch`, and `advance_branch`; and
- a generation-preserving full-kernel checkpoint/restore covering state and
  branch metadata, with `TableauKernel::atomic` available for later measured
  copy reduction.

The adapter uses two narrow queue accessors because `StableQueue` remains private:

```text
existential_candidate_count(&self) -> usize
take_existential_candidate(&mut self) -> NativeResult<Option<NodeHandle>>
```

`take_existential_candidate` must perform the same mutation accounting and
generation-safe stale-handle behavior as the existing integer queue pop.

## Snapshot-owned query-local state

Branch advance must roll back strategy choices, so these cannot be untrailed
fields on `ExistentialExpansionManager`:

```text
reuse_nodes: BTreeMap<filler_predicate_id, NodeHandle>
reuse_disabled: BTreeSet<at_least_predicate_id>
reuse_branches: BTreeMap<branch_level, {
    root, at_least_predicate_id, exact_supports
}>
```

These maps and their get/set/remove operations are now part of `MutableState`.
The coarse `push_reuse_branch` operation inserts the reuse record *before* the
branch checkpoint and then pushes merge alternatives `[0, 1]`; the record
therefore survives `advance_branch`, and exhaustion removes it explicitly.

## Runtime services

- `RuleEngine::dispatch_ground_atom` and `RuleEngine::register_node` already
  cover consequence dispatch and reflexive equality registration.
- `NativeDatatypeExpansion` is the no-callback WPR3 seam for
  `data_value_satisfies` and `data_values_known_different`. Until WPR3 joins,
  `AssertedOnlyDatatypes` returns only consequences already represented by
  explicit range/inequality rows and never invents a datatype answer.
- The blockedness adapter returns
  `kernel_node.blocker.is_some() || blocking_manager.is_blocked(node)`. The
  second term is covered by a real cache-derived-block regression.
- `expansion_program_from_rules` derives role-extension, inequality, cardinality,
  and n-ary data metadata from `RuleProgram`. Session construction supplies the
  compiled top/bottom object/data role IDs and the set of nongenerated public
  atomic fillers eligible for sound reuse.

Inverse roles remain in compiled role orientation: expansion dispatches
`(root, witness)` to the predicate for the normalized inverse role, and the
role rules derive its forward counterpart.
