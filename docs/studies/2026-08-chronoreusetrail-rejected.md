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


## Follow-up (2026-08-20): prerequisite LANDED — level-filtered backtracks everywhere; port reapplied behind a default-off flag

The enabling redesign is in: `Trail::backtrack_to_with_callback` now unassigns
by **recorded level** and compacts kept out-of-order literals in place (cadical
`backtrack.cpp` semantics), with the propagation head clamped to the level
boundary (`propagated = assigned`).  Every backtrack in the engine flows
through it.  Two supporting fixes landed with it:

- **The pre-change suffix-pop was a real latent hole, now proven**: with
  `chrono_always` (cadical `chronoalways`, exposed as a debug knob) the
  `pmres` stratified test panics on the hanging-unit invariant under the OLD
  trail — out-of-order asserting literals dropped positionally — and passes
  under the new one.  Regression: `chrono_trail_level_filter_regression.rs`
  (repeated assumption solves under `chrono_always`) plus the oxiz-opt pmres
  test itself.
- **The scheduled inprocess entry now backtracks to root itself** (mirroring
  `try_scheduled_elimination` and cadical): previously the interval only fired
  on conflicts that happened to backjump to level 0 — on instances whose
  conflicts resolve at non-zero assertion levels the schedule silently never
  triggered (caught by `inprocess_drat_deletion`, whose deletions vanished
  after the trail change shifted the trajectory).

The `determine_actual_backtrack_level` port (including the fixed
`control[res+1].trail` boundary arithmetic) is reapplied as
`SolverConfig::chrono_reuse`, **default off**: cadical defaults
`chronoreusetrail=1`, but our measurements stay neutral-to-negative
(single-seed canonical tracking: trail-only 0.837× paired vs pre, trail+reuse
0.921×, both bimodal per file; the earlier 10-seed null study p=0.14), and the
canonical-seed headline moved 19→28 (trail-only) / 19→23 (with reuse) files
above 1.5× of cadical.  Completions did improve (79→83/82 of 94).  Revisit
with a full ≥10-seed study before flipping the default.  Matched null:
`OXIZ_CHRONOREUSE_NULL=1` (scrambled bump key).

## Open thread (next session): pre-existing false SAT under `chronoalways` + full inprocessing stack

While validating, `dominator_hbr_subsuming_original_promotes_resolvent`
(**in-repo permanent reproducer**: `OXIZ_CHRONO_ALWAYS=1 cargo nextest run -p
oxiz-sat dominator_hbr`) answers **sat on UNSAT input** — under BOTH the old
and new trail (A/B-verified), i.e. a pre-existing bug the suffix-pop trail
masked in the final verdict and the level-filter trail exposes.  Bisected to
one elimination round: dumping the live DB (with level-0 trail facts) after
every inprocessing sub-pass shows equi-satisfiability breaking inside a single
`elim_round` that eliminated exactly one variable (idx 1032 / DIMACS 1033);
occurrence lists match ground truth at elimination time and the 4 added
resolvents match the (small) parent set — the break is in the round's
periphery (backward strengthening / satisfied-skip / garbage retirement /
unit forcing), not yet isolated.  Two full dump artifacts were produced
(`/tmp/dbdumps/db_012*`, `db_013*`, cadical-verdict-checked) but the
instrumentation was removed before landing; the recipe is in the session
record.  Default configs are unaffected (needs the opt-in stack +
`chronoalways`), but it is a real soundness bug — top of the queue.
