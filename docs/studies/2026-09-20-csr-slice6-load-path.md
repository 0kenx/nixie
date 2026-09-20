# CSR commit-B slice 6: the deferred counting-sort load path — measured (2026-09-20, second session)

Addendum to `2026-09-20-csr-commitb-rebuilt.md` (same campaign, next
slice).  Landed: `7f83ba30` (+ merge `aa219f89`, BASELINE re-pinned,
binary cached).

## What landed (all B-gated; the default path bit-identical — gate
1.000/1.000 vs the 6853ba29 pin, suite 1115/1115, shadow/swapped si2
identity 25,930 with zero drift, SCPC OFF=B at 263,857)

1. **`begin_deferred_watches` / `finish_deferred_watches`**: in
   commit-B mode the CLI bulk path defers long-clause watcher attach;
   the finish materializes every watcher in ONE counting-sort CSR build
   over the arena.  Not the full rebuild: the BIG was built
   incrementally during the load (identical edges in id order — the
   deferred-BIG pair's validated equivalence) and the phantom counters
   bumped at the same attach sites, so re-running those passes paid
   their cost twice (the first version DID call the full rebuild and it
   showed as 10.2% of the whole run).  A guard falls back to the full
   rebuild if any overflow content predates the latch.
   `add_clause` stores its selected pair at `lits[0..2]`, so the
   counting sort re-derives exactly the pairs incremental attach would
   have registered — the bit-identity check (si2 / b21 / Carry_Bits /
   SCPC, conflicts-identical OFF vs B-deferred) confirms it end to end.
2. **The reused scan scratch**: the session kernel's span copy reuses
   one `Vec` across scans (clear + copy-in; write-back; next scan).
   Surprising negative finding: this barely moved instructions (78.8G →
   78.7G pre-fix-rebuild) — the per-scan `Vec::with_capacity` was being
   served from the allocator's fast path; the real costs were
   elsewhere.  Kept (it is strictly less work and kills the
   allocator's per-scan traffic under pressure).
3. **The packed CSR snapshot**: `WatchSnapshot` stored
   `csr: Option<CsrWatchLists>` via derived `Clone` — duplicating every
   per-literal overflow header (18.7M empty headers ≈ 450 MB on the
   9.4M-var class) inside lucky's entry snapshot: 3% of the run and a
   ~1 GB transient.  Now packed (overflow as one buffer + per-literal
   ends, the exact shape the `Vec` side's snapshot uses).  Peak RSS
   −410 MB on 14.normalised; instructions flat (the 18.7M-slot walk
   remains — see the flip-time list).

## The measured standing (deterministic instruction counts — wall is
void under this box's load: GP_190's OFF arm swung 26.7 s → 14.8 s
between reps)

| instance | OFF | B | ratio |
|---|---|---|---|
| GP_190_225_30 (570 MB, load-dominated) | 58.9G | 59.9G | **+1.7% (parity)** |
| 14.normalised (9.4M vars, 25.2M clauses) | 68.4G | 75.1G | +9.8% (was 79.8G) |
| 1.normalised | 219.7G | 240.8G | +9.6% |

The normalised-class residual decomposes (profiled) into the named
flip-time items below; the load itself is now CHEAPER in B than OFF
(`add_clause` + `attach_watchers` + `scan_clause_for_attach` all
smaller; the mimalloc realloc traffic gone).

## The flip-time list (each changes CsrWatchLists's shape — do them at
the Vec deletion, not before)

1. **Sparse overflow**: `overflow: Vec<Vec<Watcher>>` pays 18.7M
   headers (~450 MB) for mostly-empty lists — at construction, at every
   `adopt_layout` (clear + resize = drop + re-grow storm per rebuild),
   and in every snapshot walk.  A sparse map (or per-literal
   `Option<Box<[Watcher]>>`) empties to zero bytes; the take/put and
   push paths key it identically.
2. **The in-place span scan** (the kickoff's split-borrow design): the
   two copies per scan are the propagation-side residue; on 0-conflict
   / propagation-heavy classes (17.4M propagations) they are most of
   the +9.6%.  The WatchCursor is already raw-pointer based; the B
   instantiation can take `(ptr, len)` span bounds beside `&mut
   CsrWatchLists` (the only `entries` writer is the cursor itself,
   confined to the scanned span; the dedup reads other literals'
   spans — disjoint by construction, and the scanned literal's own
   view is empty under take semantics).
3. **The dead `Vec<Vec<Watcher>>` field**: 450 MB of headers + the
   reset/fill machinery — deleting it is the flip commit itself and
   repays B's remaining RSS excess (~550 MB on 14.normalised).

## Traps added

15. A deferral `finish` that calls the FULL rebuild pays for passes the
    incremental path already did (BIG + phantom) — the 2026-09-18
    study's fast-path deferred-BIG verdict repeated itself through the
    back door; materialize exactly what was deferred.
16. Wall-clock on this box is void even for "obvious" wins (GP_190's
    OFF arm moved 1.8× between reps at load 5-9) — instruction counts
    only, per the standing rule.
