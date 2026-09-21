# The aggregate-measurement log: contaminated runs and what stands

**Date:** 2026-09-20 evening (the post-landing measurement session).

## The state of the standing table

The **third snapshot** (`bench/smt_perf/README.md`, calm load) remains
the honest standing record: **QF_BV 54/60 vs z3 53/60 (nixie leads),
QF_LIA 32/60, zero disagreements**.  Two subsequent re-run attempts were
**load-contaminated and discarded** (never committed):

- the BV-extract session's run (load 26–35; z3 itself dropped four
  cells — recorded in that study),
- this session's run (load 7 → 43 mid-run): `bench_11463` (6.5 s calm)
  and `bench_16217` (9.9 s calm) timed out at 10.07/10.19 s — exactly
  the wall-watch readout's flagged fragile cells — and z3 lost
  `bench_13079`.  Per-cell diff confirmed load-shape; the file was
  reverted.

**The aggregate measurement stays pending a calm window** (load ≤ ~8
sustained for 25 min).  What it will measure when it runs: the extract
rules + gcd kernels + the SAT-core/graph/ctx_simplify landings +
item 96's flag-gated channel (off by default — the table measures
defaults).

## Deterministic signals from the (discarded) run

- **Zero disagreements** at every attempt — the soundness canary held
  under all landings.
- QF_LIA solved-count stable at 32/60 across all three runs; the
  aggregate conflict counter moved 4 224 → 5 517 (the compounded
  trajectory drift of many agents' semantics-inert landings —
  gate-verified individually; the counter level is the nixie-vs-nixie
  datum to re-baseline at the next calm snapshot).
- The CAV probes with item 96's channel flag
  (`NIXIE_LIA_BRANCH_LEMMA=1`): still timeout — consistent with the
  pivot-storm addendum's finding that the per-LP churn (not the tree)
  gates that family; the Bareiss/row-denominator layer remains the
  prerequisite.

## Standing fragile cells (unchanged from the wall-watch readout)

`bench_16217` (9.9 s) and `bench_11463` (6.5 s) sit within 1.6× of the
10 s cap — every loaded table run will bounce them.  The tactic-cascade
route (solve-eqs over the SAGE concat definitions) owns the former;
SAT-core capacity the latter.

## 2026-09-21 (morning): the branch-channel default shows in the standing counters; walls await calm

Three table runs on `precompile/cf8e497c` (the tree with the branch
channel default `0edc05fc` + Bareiss + assert-fold + the sat arc's
BVE landing):

- **Load-robust signals (consistent across all three):** QF_LIA solved
  **33/60** held, zero disagreements, and **conflicts 4502 → 3209**
  (−1293: the branch channel's effect on the standing slice —
  consistent with the rung-3 campaign's 42 recoveries).  QF_BV 52-54/60
  vs z3 52-54 (the at-cap cells bouncing with load; z3's own set moves
  too — no nixie-attributable change).
- **Walls untrusted in all three:** one run rode a concurrent
  symbolized build (my mistake — median nixie/z3 1.88 against every
  calm measurement's ~0.52; discarded), two rode other agents'
  campaigns at load 10-83 (medians 2.03/2.67, z3's own geomean
  inflated ~1.7×; discarded per the discipline).  The standing wall
  record remains the campaign snapshot (`661fb774`'s, in the tracked
  results file): LIA par2 9088, median 0.52, geomean comparison only
  against same-load pairs.
- The 45-vars churn probe (`problem__022`) still produces no verdict at
  30 s — the pivot VOLUME (internal B&B) is unchanged, as mapped; a
  fresh symbolized profile of it is in the Bareiss study's addendum
  (the follow-up question resolved negative, ≤2 %).
