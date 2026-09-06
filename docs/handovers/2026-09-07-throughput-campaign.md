# Handover: Per-Conflict Throughput Optimization Campaign

## Context

Nixie's SAT core has **conflicts parity with cadical** (0.88× — we beat our port source) and a 1.12× conflicts gap vs kissat. The **dominant remaining deficit is throughput**: we process 3.9M propagations/sec vs cadical's 7.0M (1.8×) and kissat's 11.7M (3×). At equal conflicts, we take 1.41× the wall time.

This is pure engineering (data-structure and memory-access optimization), not heuristic tuning. No matched-null needed — the trajectories must stay bit-identical.

## The Measurement (6s167-opt, E-core 10, sequential)

| | nixie | cadical | kissat |
|---|---|---|---|
| wall (ms) | 1 921 | 332 | 659 |
| conflicts | 62 241 | 16 654 | 19 164 |
| propagations | 7.4M | 2.3M | 7.7M |
| **props/sec** | **3.9M** | **7.0M** | **11.7M** |
| ticks/conflict | 325 | 902 | 1 715* |

*kissat search_ticks only.

Per-propagation cost: **~770 cycles** (nixie) vs ~430 (cadical) vs ~256 (kissat) on a ~3GHz E-core.

## Root-Cause Decomposition

Each propagation step processes ~8 entries (BIG binary edges + watch-list watchers). Each entry involves 2-3 cache accesses (entry load, trail value lookup, possible arena clause read). At ~30 cycles per L2/L3 access: 8 × 3 × 30 ≈ 720 cycles ≈ our measured 770.

The four pre-registered targets, ranked by estimated impact:

### Target 1: Clause Arena Locality (biggest win, most work)

**Problem**: `ClauseArena` allocates clauses in insertion order. When the watch scan reads clause data for non-blocked watchers, accesses are scattered across the arena. cadical sorts clauses by size so same-sized clauses are adjacent.

**Fix**: Sort the arena by clause size at each compaction, then rewrite the `refs` table and all `ClauseRef` holders (watchers, reasons). The existing `compact_clause_arena()` in `learn.rs` already does in-place compaction — extend it to sort by size during the move.

**Estimated impact**: 20-40% reduction in arena cache misses. Watch-scan reads would hit adjacent memory for same-sized clauses.

**Key files**: `nixie-sat/src/clause.rs` (arena), `nixie-sat/src/solver/learn.rs` (`compact_clause_arena_if_due`), `nixie-sat/src/watched.rs` (watcher `.r` field rewriting).

**Verification**: Conflicts bit-identical (the sort changes memory layout, not search semantics). Wall time improvement measurable on 6s167/FEC/crypto1.

### Target 2: Watcher Compression (moderate win, moderate work)

**Problem**: `Watcher` is 12 bytes (`clause: ClauseId` (4) + `r: ClauseRef` (4) + `blocker: Lit` (4)). A typical watch list of 5 entries = 60 bytes = 1 cache line. If compressed to 8 bytes, 5 entries = 40 bytes — still 1 cache line but with more room for prefetch.

**Current layout** (`nixie-sat/src/watched.rs`):
```rust
pub struct Watcher {
    pub clause: ClauseId,  // u32 newtype
    pub r: ClauseRef,      // arena byte offset (u32)
    pub blocker: Lit,      // literal code (u32)
}
```

**Fix**: The `clause` id and `r` slot could share encoding if slots were index-based (u32 index into a sorted arena) rather than byte-offset. Or: drop `clause` entirely from the watcher and recover it from `r` via a reverse-mapping table (this is what cadical does — the watcher only stores the reference, the id is looked up on demand).

**Tradeoff**: Dropping `clause` saves 4 bytes but adds an indirection when the id is needed (reason recording, clause deletion). The blocker is needed per-scan.

**Estimated impact**: 10-20% watch-scan cost reduction (fewer bytes to load per entry).

### Target 3: BIG/Watch Single-Pass (moderate win, significant refactor)

**Problem**: Binary clauses and large clauses use two separate iteration passes per propagated literal:
1. BIG CSR span iteration (binary implications)
2. Watch-list scan (non-binary clauses)

Each pass has its own loop overhead, and the two data structures are in different memory regions.

**Fix**: Merge binary edges into the watch list so a single pass handles both. This is what cadical does — binary and large clauses share the watch structure (binary watchers are a special tagged case).

**Warning**: This reverses the BIG-authoritative BCP design decision (2026-09). The BIG is also used by transitive reduction, ELS equivalence detection, and the AND-gate factoring pass. Those consumers would need to work from the watch structure instead, or the BIG would need to be maintained separately.

**Estimated impact**: 15-25% per-propagation cost (removes one loop iteration overhead + one memory region).

### Target 4: `propagate_step_limit` Hoisting (already landed, minimal)

**Status**: Landed at `7fc47eb`. The `Option` pattern-match ran per step but is always `None` during search. Hoisted to a loop-invariant `bool`. Below the measurement noise floor but structurally correct.

## Getting Started

1. **Read the code**: `nixie-sat/src/solver/propagate.rs` (the hot loop), `nixie-sat/src/watched.rs` (watch structure), `nixie-sat/src/big.rs` + `nixie-sat/src/solver/mod.rs` (BIG CSR structure), `nixie-sat/src/clause.rs` (arena).

2. **Profile first**: Build with `--features profiling` and run on 6s167. The existing `ScopedTimer` infrastructure gives per-category breakdowns.

3. **Start with Target 1** (arena locality): extend `compact_clause_arena_if_due` to sort by size during compaction. Verify bit-identical trajectories (conflicts must match exactly).

4. **Then Target 2** (watcher compression): drop the `clause` field, recover from `r` via reverse lookup. Measure the tradeoff.

5. **Measure**: Always compare wall time on the same E-core (10) with the same system load. The standing-table methodology applies (pin to core 10, sequential, same file order).

## Verification Checklist

- [ ] Conflicts bit-identical on corpus files (trajectory preservation)
- [ ] `cargo nextest run -p nixie-sat --all-features` — all 925+ tests pass
- [ ] `cargo clippy --all-features --all-targets -- -D warnings` — clean
- [ ] `./bench/z3_parity/run_parity.sh` — 0 verdict mismatches
- [ ] Wall time improvement measured on 6s167 + 2-3 other anchors
- [ ] No regression on solved-at-cap (run the 5-seed screen on the standard anchors)

## Key Constraints

- **Trajectory identity is mandatory** for pure engineering changes — any change that alters the search path is heuristic-class and needs matched-null discipline
- **E-cores amplify memory-bandwidth differences** — the 1.8× gap may be smaller on P-cores; the engineering targets remain valid
- **The BIG is load-bearing** for multiple passes (transitive reduction, ELS, AND-gate factoring) — Target 3's refactor must update all consumers
- **cadical's tick formula** (`1 + cache_lines(watch_size × watcher_bytes)`) is our accounting baseline — changing watcher size changes the tick counts and thus the restart schedule

## Expected Outcome

Closing the throughput gap from 1.8× to 1.2× vs cadical would move the wall standing from 1.41× to ~0.95× (better than cadical at wall, matching our conflicts advantage). Combined with the existing 0.88× conflicts ratio, nixie would be strictly faster than cadical on the standing corpus.
