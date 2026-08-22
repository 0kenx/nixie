# Binary clauses without redundant watchers (BIG-only propagation): pre-registration (2026-08-23)

## Motivation (from the accumulated cost map)

worker550 — the hardest timeout-residue file — is 93,713 vars / 10.3M
clauses, nearly all **binary**. OxiZ double-bookkeeps every binary clause:
a BIG edge pair (`binary_graph`) **and** two arena watchers
(`attach_watchers`), because every attach site adds both. In `propagate`,
the BIG pass runs first for every dequeued literal and covers *all* binary
implications, so the watcher visits on binaries are provably no-ops (the
blocker is the other literal, already made true — or the conflict already
returned — by the BIG pass). On worker550 that is ~20.6M watcher entries
(≈250 MB and their scan time) doing nothing. kissat/cadical keep binaries
only in watch/BIG structures; we keep full arena clauses (unchanged here)
but can drop just the redundant watcher copies.

## Change

1. Stop attaching watchers for clauses of length 2 at every attach site
   (`mod.rs` add_clause binary branches, `learn.rs` learned-binary + HBR,
   `equiv.rs` `rebuild_watches_and_binary_graph`, `preprocessing_core.rs`
   rebuild). BIG is the sole propagation engine for binaries — which it
   already effectively is.
2. **Preserve the tick input exactly**: the propagate tick formula reads
   the watch-list length (it drives restart/reduce/probe schedules; the
   comment at the formula explicitly forbids changing the accounting
   without matched-null discipline). Phantom count per literal =
   `binary_graph` edges under it, minus a per-literal counter of
   congruence **sentinel** edges (which never had watchers). Maintained at
   the congruence derive site; cleared wherever `binary_graph` is cleared
   (rebuild, reset).
3. Deletion paths unchanged: `purge_binary_edges` drops the edge,
   `WatchLists::remove_clause` no-ops on absent watchers — the pairing
   that keeps the phantom count equal to the old watcher count.

Long clauses that later shrink to length 2 keep their (already attached)
watchers and gain edges only at the next rebuild — either way the sum
watchers + edges stays constant, so tick parity holds at every point.

## Change class

Path-preserving by construction (same assignments, conflicts, learned
clauses; same schedule inputs). The null is trajectory identity itself.

## Go / no-go (pre-registered)

* **Gate 1 — trajectory identity**: 94-file corpus, `PRESET=cadical`,
  default seed; counters (decisions/propagations/conflicts/restarts/
  learnt) + verdict identical on every comparable file. One-arm-timeout
  cells re-run longer to confirm identical counters.
* **Gate 2 — instructions-to-verdict**: symmetric both-solve selection
  (15 s cap), geomean(base/new) over ≥ 60 cells **≥ 1.005** with no more
  than 2 cells worse than 1.01, AND at least one of worker550/rbsat
  improving **≥ 1.2×** (the motivating binary-heavy class; worker550 may
  legitimately TO both arms at the cap — then rbsat carries the criterion).
* Metric: PMU `cpu_core/instructions`, serial CPU-pinned, process-group
  kill on timeout.
* Soundness: full `oxiz-sat` suite + workspace suite; watch-invariant
  tests; `diff_equiv` 200k fuzz.

## Results

**Verdict: REVERTED — the motivating criterion failed.**

* **Gate 1 (trajectory identity): PASS** — 94/94 files, 0 diffs, 0
  unresolved. The phantom-tick construction (long watchers + BIG edges −
  sentinel edges) preserved every schedule input exactly; the design was
  right about semantics.
* **Gate 2 (corpus): 1.0066 geomean** over 72 both-solve cells, new faster
  on 30/72, worst cell 0.991 (binary-free uf100 paying the extra edge-count
  load in the tick formula). Meets the 1.005 corpus bar.
* **Motivating criterion (worker550/rbsat ≥ 1.2×): FAIL.** rbsat
  519G → 499G = **1.04×**; x9-09054 1.01×; worker550 and crypto1 TO at
  240 s in both arms.

## The closing datum

Eliminating ~20.6M redundant watcher entries (the entire binary population
of worker550, ≈250 MB and their no-op scans) moves binary-heavy instances
by **4%**, not the projected 2×+. Combined with the three prior studies,
the propagate-side cost map is now closed end-to-end:

| hypothesis | measured |
|---|---|
| watcher-entry layout (12B vs 8B) | ±1% |
| flat arena vs per-list | −4.5% |
| minimizer allocation | ~1% on the motivating file |
| redundant binary watchers | **1–4%** |

Binary watcher scans were already near-free: one contiguous load + compare
per no-op, with the BIG pass having done the work. worker550's 11.4M
instructions per conflict live in the **conflict analysis walk over
2679-literal clauses and their reasons** — clause-arena locality, the one
layout surface not yet touched (and the one the flat-arena study's
post-mortem already named).

The sentinel-edge counter machinery and the phantom-tick formula are
sound (Gate 1 proves the bookkeeping); if a later change makes binaries
BIG-only for *memory* reasons on constrained targets, this study's patch
is the verified starting point — re-measure, do not assume.

Reverted on main per pre-registration; worktrees deleted.
