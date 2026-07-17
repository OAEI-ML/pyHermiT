# WP12 — Complete pure-Python tableau session

**Goal**: integrate all Python components into a terminating complete satisfiability
engine implementing the backend protocol.

## Read first

| What | Where |
|---|---|
| Complete rule/scheduler contract | `hypertableau.md` |
| State and blocking contracts | `tableau-state.md`; `blocking.md` |
| Datatype integration | `datatypes.md` §§6–9 |
| Backend lifecycle | `contracts.md` §§5, 8; `native-backend.md` §8 |
| Java scheduler | pinned `Tableau.runCalculus/doIteration`, `DatatypeManager`, expansion strategies |

## Deliverables

- `BackendSession` implementation for permanent/query initialization, exact schedule,
  delta fixpoint, datatype dirty components, NI, existentials, disjunctions,
  backjumping, blocking validation, SAT/UNSAT completion.
- Query-root isolation, `check_many`, session reset/close, config strategy selection,
  cancellation/deadline/resource checks, poisoned/rebuild behavior, events/statistics.
- Expression/feature compatibility checks for additional query IR and temporary full
  rebuild path where needed.
- Integrated debug invariant mode and complete Python semantic tests across rule-family
  interactions and all strategies.

## Depends on

WP07, WP09, WP10, and WP11.

## Acceptance criteria

1. All in-scope upstream tableau, quick semantic, datatype, role, reuse/core-blocking,
   and curated W3C consistency checks pass in forced Python mode.
2. Scheduler order and validated-block fixed point match the spec; no SAT is returned
   with pending delta/NI/existential/disjunction/datatype/validation work.
3. Query batches are independent; permanent canonical state/fingerprint is unchanged
   after SAT, UNSAT, branch-heavy queries, timeout, and interruption.
4. Every legal strategy toggle gives identical logical answers; unsupported mandatory
   features fail only as temporary development markers and are zero by package finish.
5. Fault-injected cancellation/resource errors leave a reusable validated session or
   explicit rebuild/poison outcome, never a partial answer.
6. Small generated ontologies agree with exhaustive/Java goldens and emit traces usable
   for native implementation.

