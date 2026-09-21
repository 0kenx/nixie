# Design: the wide-driver priority gate — the CAV 011/034 restoration candidate

**Date:** 2026-09-22 (small hours).  **Status:** design + validation plan,
NOT built.  **Entry:** the request-cadence handoff's open item 1, per the
piece-level bisect (`2026-09-22-cav-regression-attribution.md` addendum:
S1/S2 — the unified wide-driver rewrite owns the damage, the preserve
pair is innocent).  **Prerequisite:** the calm-load LIA standing table
on `precompile/9a114017` (still load-blocked; run before ANY fix lands).

## The surgical observation

Current `find_violating` (`simplex/mod.rs`, post-`2a7dc324`): narrow
basics scan smallest-index-first, then the WIDE store's basics join the
SAME smallest-index competition — a wide basic with a small index
PREEMPTS every narrow repair.  The pre-driver shape: `make_feasible`
converged the narrow store ALONE; wide violations were handled by
`check`'s separate loop — one wide repair per round, then a full narrow
re-feasibilization (budget 32).  The CAV cells (wide via pivot
accumulation, mostly-narrow tableau) thrash under the unified order:
costly exact wide pivots preempt the cheap rational repairs that used
to batch first.

## Candidate (A): the priority gate — one line

In `find_violating`, scan the wide store ONLY when the narrow scan
found no violation (`if worst.is_none()`).  This restores the old
PRIORITY (narrow-feasible corner first, then wide repair) while KEEPING:

* the unified operator (`make_feasible` still pivots wide leaving
  basics via `find_wide_pivot_col`; `check`'s classification stays
  repair-free),
* the preserve-resting-nonbasics pair (S1-innocent, pins stay green),
* the branch-request cadence (`9a114017`).

## The risk this must be measured against — orbit resurrection

The smx campaign's layer analysis attributed the i445/i129 limit cycles
to the SPLIT driver (layer 1) AND the re-snap loops (layers 2/3).  The
preserve pair (layers 2/3) is landed and stays.  But S1 did NOT test
the orbit members — preserve-only on `7687dc39` was measured on CAV
cells only.  If layer 1 (the interleave itself) was ALSO load-bearing
for the orbit fix, the priority gate could resurrect i445/i129-class
cycles.  The gate is NOT the old split driver (still one operator, one
loop, no per-round re-feasibilization pass in `check`) — but the claim
"the gate keeps the orbit fixed" is a measurement, not an argument.

## The validation bar (in order — nothing lands before the table)

1. **Baseline**: the calm-load LIA standing table (par-2/geomean/
   both-solved median readout) on `precompile/9a114017`, sustained
   load ≤ 8, never next to a build or campaign.
2. **Candidate build (A)** on main; back-to-back A/B at generous caps:
   * CAV: `problem__011` (target: sat ≤ ~30 s), `problem__034`
     (sat ≤ ~10 s), `problem__025` (must STAY sat — the cadence
     landing recovered it).
   * The orbit family must NOT regress: `i129` (reproducer
     `docs/studies/assets/2026-09-21/simplex-tail-i129.smt2`), `i202`,
     `i445`, `i116` (the cadence landing's own list).
   * The wide-cycle pins: `nixie-solver/tests/arith_wide_literal_
     regressions.rs` (`rederivation_preserves_*`).
3. **Matched null** (this is a trajectory change — the bar applies):
   the null is the INVERTED priority (wide-first-always: scan wide
   first, narrow only when wide is feasible) — same physical work, same
   code path, opposite semantic content.  Report treatment/null, not
   treatment/baseline; ≥10 seeds on the fixed-seed corpus if the
   one-seed deltas are not gross.
4. **The surveys** (fixed + fresh) after the default lands — the
   request-cadence trap: survey the LANDED binary, not the candidate.
5. Full battery: suite, clippy/fmt/doc, parity (z3 4.16.0), perf gate.

## Fallback (B) if (A) resurrects the orbit

Restore `check`'s interleaved repair loop VERBATIM from `7687dc39`
(one wide repair + narrow re-feasibilization, budget 32) but WITH the
preserve pair retained — the layers-2/3 fixes applied to the old layer
1.  Bigger diff, closer to the exact pre-regression semantics; same
validation bar.

## Fallback (C)

The dive-level landing (bound the internal B&B per CHECK harder than
the 64-node cadence) — but `9a114017` already showed the cadence does
not cure 011/034, so (C) means a qualitatively different dive shape;
belongs to the search-level campaign, listed for completeness.
