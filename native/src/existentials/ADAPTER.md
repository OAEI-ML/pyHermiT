# Native existential adapter seam

`existentials` is deliberately `std`-only and is tested directly from `mod.rs`.
The eventual runtime adapter translates its small value types to the crate's
`NodeHandle`, `DependencySet`, `NodeKind`, `GroundAtom`, and `NativeError`.

## Existing `TableauKernel` reads/mutations to forward

- `canonical_handle`, `active_node_handles`, `active_node`, and `node_rank`;
- `candidate_fact_ids` plus `fact` for stable fact/support reads;
- `create_node`, `mark_existential`, `enqueue_node`, and `install_clash`;
- `clash`, `branch`, `push_branch`, and `advance_branch`; and
- a full kernel clone/restore (correct initial checkpoint adapter), with
  `TableauKernel::atomic` available for a later copy-reduction adapter.

Two queue accessors are still required because `StableQueue` is private:

```text
existential_candidate_count(&self) -> usize
take_existential_candidate(&mut self) -> NativeResult<Option<NodeHandle>>
```

`take_existential_candidate` must perform the same mutation accounting and
generation-safe stale-handle behavior as the existing integer queue pop.

## Query-local state that must join `MutableState` snapshots

Branch advance must roll back strategy choices, so these cannot be untrailed
fields on `ExistentialExpansionManager`:

```text
reuse_nodes: BTreeMap<filler_predicate_id, NodeHandle>
reuse_disabled: BTreeSet<at_least_predicate_id>
reuse_branches: BTreeMap<branch_level, {
    root, at_least_predicate_id, exact_supports
}>
```

The kernel adapter needs get/set/remove methods for those maps. Its coarse
`push_reuse_branch` operation must insert the reuse record *before* the branch
checkpoint and then push merge alternatives `[0, 1]`; this is what makes the
record survive `advance_branch`. Exhaustion removes the record explicitly.

## Runtime services

- `RuleEngine::dispatch_ground_atom` and `RuleEngine::register_node` already
  cover consequence dispatch and reflexive equality registration.
- The WPR3 datatype adapter must provide `data_value_satisfies` and
  `data_values_known_different` without a Python callback.
- The blockedness adapter must return
  `kernel_node.blocker.is_some() || blocking_manager.is_blocked(node)`. The
  second term is essential for cache-derived blocks that are manager-owned.
- Program construction can derive role-extension and inequality predicate maps
  from `RuleProgram`. It still needs compiled top/bottom object/data role IDs
  and the nongenerated-public-atomic filler flag used to enable sound reuse.

Inverse roles remain in compiled role orientation: expansion dispatches
`(root, witness)` to the predicate for the normalized inverse role, and the
role rules derive its forward counterpart.
