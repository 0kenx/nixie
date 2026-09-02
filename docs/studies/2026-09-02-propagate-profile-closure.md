# Propagate hot-loop closure: profile map, one more null result (2026-09-02)

Where the standing-gap program stands after lever 1 (arena compaction,
`5d318f9`) landed: the throughput factor (0.82× vs kissat, i.e. kissat is
1.22× cheaper per conflict) is concentrated in `propagate`, and this
session mapped it end-to-end and closed its last constant-factor lever
with a measurement. The profile data below is the map for anyone opening
the BCP loop again; the remaining gaps are lever 2/3 (heuristic class).

## The map (mrpp_4x4, the corpus's throughput outlier: 3.5× per-conflict vs cadical)

`perf` on `stats_solve` (symbols build), 249k conflicts / 25.5M props /
67.4G instructions (8.9 s):

* `propagate` = **74.8 %** of cycles. `LLC-load-misses ≈ 1.2M` total —
  **not memory-bound**; this is instruction-count and branch-mispredict
  cost.
* **2640 instructions per propagation**; instrumented counters (1.01 G
  watch visits ⇒ ~40 visits/propagation; 66 % blocker hits, 0 deleted
  skips, 200 M watch moves, replacement scans avg 2.08 steps over clauses
  averaging 15.7 literals at miss visits) ⇒ ~50 instructions per visit,
  where a blocker hit needs ~6–10.
* Branches: 13.7 G total, **833 M misses (6.1 %)** concentrated in the
  data-dependent BCP branches (replacement-scan triage, first-watch
  value, BIG-edge triage) — `BR_MISP_RETIRED` sampling puts 80 % of
  misses inside propagate, spread across the semantic branches, no
  single silly predictor victim.
* Inner-loop spills visible in the disassembly (`mov 0x28(%rsp),%rdi`
  etc.) — register pressure from holding watcher + two indices + clause
  slice + three structure pointers; intrinsic to the loop's live set,
  not a borrow-split artifact fixable in isolation (the
  `check_hyper_binary_resolution(&mut self)` call in the unit path takes
  the whole solver mutably, defeating per-field borrows).

## The experiment (pre-registered shape, negative result)

**Blocker-hit fast path**: load only the blocker word on the hit
majority; copy the full 12-byte watcher only on the miss path (34 %) and
on keep-after-drop. Identical stores everywhere ⇒ trajectory-identical.

* Gate 1 (trajectory identity): not run — Gate 2 decides first, per the
  watcher-8byte pre-registration (same shape, same threshold).
* **Gate 2 (instructions-to-verdict, PMU `cpu_core/instructions`,
  symmetric both-solve selection at 20 s, 39 corpus cells): geomean
  base/new = 1.0004×** — sub-threshold noise (revert threshold ≥ 1.02).
  LLVM already sinks the unused word loads past the blocker branch.

**Verdict: REVERTED.** Watcher word-splitting joins the measured closure
list.

## BCP constant factors are now closed — four data points

| experiment | result | verdict |
|---|---|---|
| flat watch arena (`2026-08-flat-watch-arena.md`) | −4.5 % | reverted |
| 8-byte watcher (`2026-08-watcher-8byte.md`) | +0.7 % | reverted |
| propagate write elision (`2026-09-propagate-write-elision.md`) | landed (slice a reverted) | kept |
| blocker word-split (this study) | +0.04 % | reverted |

The loop is compiled near-optimally for its shape; the per-visit cost is
the real work (watcher load, blocker value load, occasional clause load +
scan). Making propagate cheaper now means doing *less work* — visit-count
and watch-move policies — which is heuristic class (matched null
required), not codegen.

## Where the remaining gaps actually live (measured this session)

* **worker_550 memory (1425 MB vs kissat 282 MB)**: peak is during
  *search*, not preprocessing — arena buffer capacity 268 MB (binary
  clauses are never reduced: legacy reduce skips len ≤ 2), watch lists
  ~250 MB, and the lucky snapshot's ~900 MB transient was *not* at the
  peak moment (fixing it moved peak only 1425 → 1407 MB; landed anyway as
  `c1958bf` — 10 M+ mallocs of snapshot overhead removed). Closing the
  search-time gap is lever 2: tiered retention / binary-clause GC.
* **Search path (1.33× corpus, 5.7× on FmlaEquivChain)**: lever 3,
  unchanged — the matched-null study (target phases, retention) is the
  next campaign.

## Harness notes

`RUSAGE_CHILDREN.ru_maxrss` is a cumulative max across all children of a
process — measuring several runs from one parent silently reports the
first run's peak forever (bit me twice; every RSS cell must come from a
fresh parent). The instructions gate script reuses the watcher-8byte
methodology: pinned core, `perf stat -x,` (parse
`cpu_core/instructions` — the atom cluster reports `<not counted>`),
verdict from `result=`, both-solve symmetric selection.
