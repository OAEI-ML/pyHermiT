# WPR4 — Complete Rust session, classification, and realization

**Goal**: expose one complete native backend implementing every in-scope service and
eligible for automatic selection.

## Read first

| What | Where |
|---|---|
| Backend protocol/results | `contracts.md` §§5–8 |
| Service semantics | `reasoning-services.md` complete |
| Native lifecycle/selection | `native-backend.md` complete |
| Python semantic implementations | WP12–WP15 code/tests |
| Performance/parity gates | `verification.md` §§5–9; `performance.md` |

## Deliverables

- Integrated Rust session scheduler with permanent/query lifecycle, batch checks,
  reset, cancellation/resource recovery, events/statistics, no missing feature path.
- Batched native deterministic/quasi-order class/property classification and
  realization/query caches/results with operation-local commit.
- Python native adapter, handshake (`full_reasoner=true` only at completion), compact
  response validation/mapping, error/panic/poison/close/fork/concurrency handling.
- Full forced Python/native/verify differential suite across W3C, HermiT goldens,
  generated/metamorphic/lifecycle/update query vectors.
- End-to-end profiles and optimization of measured hot paths without semantic changes.

## Depends on

WP13, WP14, WP15, WPR1, WPR2, and WPR3.

## Acceptance criteria

1. Feature handshake enumerates every mandatory core capability; forced native passes
   the complete public semantic/exception/lifecycle suite with exact Python results.
2. Native classification/realization hierarchies, partitions, direct edges, literal
   forms, fresh/inconsistent policies, and cache invalidation match Python/HermiT.
3. No semantic callback/fallback to Python occurs inside a native session; a native
   operation failure is surfaced and never replayed silently.
4. Repeated/batched/concurrent-independent/cancel/timeout/resource/close/fork/panic
   tests show no partial cache, poison leak, deadlock, or memory/refcount growth.
5. Full sanitizer/fuzz/audit and initial native performance gates pass; result hashes
   prove identical work scope.
6. Only now may `auto` select native on a matching ABI/IR/self-test/feature handshake.

