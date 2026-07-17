# WP16 — Public facade, backend dispatch, lifecycle, and updates

**Goal**: assemble the stable Python-native product API and exact core-view revision/backend
lifecycle around all pure-Python services.

## Read first

| What | Where |
|---|---|
| Product/public/config/concurrency contract | `SPEC.md` §§5–6; `contracts.md` §§4–8 |
| Full API and updates | `reasoning-services.md` complete |
| Native selection rules | `native-backend.md` §§1, 4, 6–7, 11 |
| Java behavior | pinned `Reasoner` lifecycle, pending changes/flush/precompute, defaults |

## Deliverables

- Stable `pyhermit` exports, `Reasoner` context/dispose/interrupt/config/backend/ontology
  properties, exact core OWL/view re-exports, `load_snapshot`, and every method signature in
  `reasoning-services.md`.
- Backend dispatcher with constructor-over-environment precedence,
  auto/python/native/verify modes, handshake/version/feature checks, and diagnostic
  `backend_info`; no eager native import in Python mode.
- Precompute atomic status and caches; immutable canonical result mapping.
- Buffered/immediate add/remove/pending/flush through core delta/overlay semantics, transactional
  validation/compile/commit, correct assertion-only incremental attempt, conservative
  rebuild, precise/conservative cache invalidation.
- Per-instance locking, callback reentrancy rejection, timeout/interrupt cleanup,
  concurrent independent reasoner and dispose tests.

## Depends on

WP02, WP13, WP14, and WP15. The native adapter may be absent until WPR4; forced native
must fail explicitly, never fake success.

## Acceptance criteria

1. Documented public API exposes no backend IDs/classes and returns immutable typed
   values with exact direct/grouping/literal semantics.
2. Python mode never imports `_native`; selection occurs once; a native operation error
   is never replayed silently in Python; verify raises exact mismatch diagnostics.
3. Every update sequence matches a fresh reasoner over the committed revision;
   pre-flush queries see old state and failed flush retains old state/pending changes.
4. Precompute/status, fresh/inconsistent/disposed/busy/callback errors, timeout, and
   interrupt match configured/public contracts across cached/uncached paths.
5. Same-instance operations serialize safely; independent instances run concurrently;
   no callback reentrant deadlock.
6. Full forced-Python public suite and no-native import/install smoke pass without Java.
7. All `OntologyInput` forms work; compatible views retain identity, providers are called
   once, source/target/bridge composites concatenate nothing, and dispose never closes core.
