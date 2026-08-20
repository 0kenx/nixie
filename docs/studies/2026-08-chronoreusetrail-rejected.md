# Chronological trail-reuse port (`chronoreusetrail`): rejected — trail-design conflict

Date: 2026-08-20
Status: **negative result, fully reverted** (working tree back to `626b73a`).

## Motivation

The last unexplained large term on binary-dense instances: on `6s167-opt`
CaDiCaL's chronological statistic is **23 %** of conflicts (37 % on
`qwh.50.1250`), while our port fires **1.1 %**. Log replay of a
`--log`-instrumented CaDiCaL showed the entire difference is the
`chronoreusetrail` case (`analyze.cpp::determine_actual_backtrack_level`):
on *short* jumps (distance ≤ `chronolevelim`, where the plain helper just
backjumps) CaDiCaL finds the most-recently-bumped variable in the
to-be-discarded trail region and backtracks only to *its* level, keeping
the trail content above it — 3 819 firings on 6s167 (target level median
35), 1 202 on qwh. Our engine had no such case at all.

## What was ported (then reverted)

A faithful `determine_actual_backtrack_level` (including the off-by-one in
the level-boundary walk that the first cut had — `level_start(res+2)` vs
cadical's `control[res+1].trail`), a matched null
(`OXIZ_CHRONOREUSE_NULL`: xorshift-scrambled bump key, same scan, same
work, no selection semantics), and — after the first soundness failure —
cadical's level-filtered backtrack (`backtrack_level_filter`: unassign by
recorded level, compact out-of-order kept literals above the boundary,
rewind the propagation head to the boundary so the kept region is
re-examined).

## Why it cannot land in this engine (the finding)

**Our trail's position/level duality is incompatible with reuse stops.**
`Trail::backtrack_to_with_callback` unassigns a *positional* suffix
(everything above `level_starts[level+1]`); a reuse stop deliberately
leaves literals recorded at levels ≤ stop sitting **above** the stop
boundary (out-of-order, exactly CaDiCaL's SAT'18 design). That poisons
every *later* plain backtrack: it pops those kept literals positionally
even though their recorded level is ≤ its own stop — reproduced directly
(`UNASSIGN -65 (rec level 8) at cur_level 9` through the plain
`backtrack_with_phase_saving` path), and the resulting state breaks the
hanging-unit invariant at the next fixpoint (`pmres::test_pmres_stratified`
panics: `clause ClauseId(65) [-65,64,62] levels=[0,8,3]` is a hanging unit
— caught by the debug invariant, i.e. a **latent false-answer risk**, not
merely wasted search). The level-filtered backtrack fixes the reuse stop
itself, but any suffix backtrack that follows re-breaks the trail.

Making this sound requires **all** backtracks to be level-filtered with
out-of-order compaction (CaDiCaL's actual design), which is a
whole-engine trail redesign: conflict analysis, restarts, phase saving,
theory notifications, and the assumptions loop all assume
"trail position ⇒ level order" today (the `assign_propagation_at`-recorded
levels already violate it subtly, which is why `analyze` carries the
`analyze_scan_pivot` guard). That is a multi-day change with its own
soundness campaign, not an evening port.

## Measurements before the soundness wall (for whoever retries)

- Off-by-one fixed, single seed: qwh 32 G (treat) vs 700 G (null) — the
  mechanism is real and large when it works; 6s167 207 G vs 141 G.
- 10-seed × 6-file, default arm: treat vs scrambled-key null **geomean
  0.614×, treat faster 29/47, sign p = 0.14** — per-file wins qwh 5.4×,
  stable-300 2.9×, constraints 2.1×; not significant at n = 6 files.
- Canonical-seed 94-file tracking: aggregate 0.879× (worse) with big wins
  on the worst files (crypto 5.2×, qwh 3.8×, frb65 3.2×) and mid-file
  losses — single-seed noise dominates both directions.
- CaDiCaL cross-check: it uses the mechanism heavily on exactly the files
  where our port won (qwh: 37 % chrono), so the port direction is right.

## Verdict

Rejected as unsound-in-this-engine; the enabling prerequisite is the
level-filtered-backtrack-everywhere redesign. Do **not** retry the
`determine_actual_backtrack_level` port alone — the bug is not in the
level arithmetic (that was fixed and verified), it is that any later
positional suffix backtrack corrupts the out-of-order trail the reuse case
creates. Start from the trail, not the heuristic.
