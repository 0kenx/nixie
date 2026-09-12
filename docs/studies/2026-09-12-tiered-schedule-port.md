# The tiered per-mode schedule port: pre-registration (2026-09-12)

> **Result (same day): measured dead as a default; the arm stays as
> documented-negative, env-gated infrastructure.**  Treatment screen
> (54 files × seeds 0-4, 60 s cap, baseline = the fresh `8082e335`
> re-baseline cells): solved-at-cap **180 → 174**, both-decided conflicts
> geomean **1.267× worse** (n = 100 cells), 0 verdict disagreements.
> Both clauses of the pre-registered decision rule failed → **the null
> is not built**.  Full table below.

Priority-2 from the round-8 close.  Every single-knob exit in the
(dec/conf 1.5–2×) residual space is measured dead: flat/gated/ramped
restart margins (rounds 1–7), floors, portfolios.  What remains is the
kissat-shaped **system**: per-mode restart/phase/branching policy, as one
coherent arm.  This file pre-registers the arm, its constants, and its null
before any measurement.

## The reference (kissat 4.0.4, `src/{mode,restart,rephase,decide}.c`)

- **Mode schedule** (`mode.c`): focused phases are *conflict*-budgeted —
  first `modeinit` (1e3) conflicts, then `modeint (1e3) × count ×
  log10(count+9)^4` conflicts (`count` = completed focused phases).  Stable
  phases are *tick*-budgeted at exactly the previous focused phase's
  consumed search ticks.  Switches do NOT reset the glue EMAs
  (`init_averages` has an `initialized` guard — averages run continuously;
  no per-mode swap).
- **On →stable**: enable reluctant doubling (period 1024, limit 2²⁰);
  push any missing active variables back into the score heap
  (`update_scores`).  **On →focused**: disable reluctant; reset the VMTF
  search cache to the queue tail (`reset_search_of_queue`); re-arm the
  focused restart limit.
- **Restart** (`restart.c`): focused = Glucose `fast ≥ 1.10 × slow`,
  gated by a min-gap `restartint (1) + log10(restarts+9) − 1` conflicts
  re-armed after every focused restart (≈ log₁₀ of the restart count —
  the condition is *not* re-evaluated every conflict before that).  Stable
  = reluctant triggered only.  Reuse-trail on (VMTF stamps focused /
  heap scores stable).
- **Rephase** (`rephase.c`): **stable-only** — focused mode never rephases
  (and therefore never walks).  Schedule `(best, walk, inverted, best,
  walk, original)^ω`; after every rephase `target ← saved`,
  `target_assigned = 0` (`best` also resets `best_assigned`).  Interval
  growth `rephaseint (1e3) × count × log10(count+9)³` conflicts.
- **Phases** (`decide.c`): stable consults *target* phases first, then
  saved; focused consults saved only (plus a periodic initial-phase flip
  keyed on `(switched>>1)&7` — ported as a no-op deviation, our saved
  phases subsume it).

Known deviations (recorded, deliberate): our EMA swap machinery stays
(continuous averages are the kissat shape — under the arm we *skip* the
swap, matching kissat); the initial-phase flip is not ported; reorder
(`reorder.c`, Jeroslow–Wang heap refresh) is **Slice B**, not in this arm.

## The arm

`NIXIE_TIERED=1` (env-gated, default off = bit-identical), one switch that
replaces the cadical stabilize schedule with the kissat schedule above:

1. `check_stabilize` takes a tiered branch: conflict-budgeted focused
   phases (1e3 × count × log10(count+9)⁴), tick-budgeted stable phases
   (= previous focused phase's ticks, on the summed tick counter), no
   `glue_current`/`glue_saved` swap, with the two switch hooks (heap
   re-push on →stable; VMTF cursor reset + restart-limit re-arm on
   →focused).
2. Focused restarts: the Glucose condition is evaluated only past the
   growing min-gap (`max(1, log10(restarts+9))` conflicts since the last
   focused restart / switch), re-armed on fire.  The every-2-conflict
   check window of the default path is not used in the arm.
3. Rephase: stable-only, `(B, W, I, B, W, O)^ω`, target/best resets, and
   `1e3 × count × log10(count+9)³` growth; `update_target_and_best` gains
   the arm's stable-only gate (focused never consults target).

## The null (pre-registered, built only if the screen is positive)

`NIXIE_TIERED_NULL=1`: the **schedule** (when phases switch, conflict/tick
budgets, growth) runs exactly as the treatment; the **policy coupling** is
severed — at each phase boundary a PRNG coin assigns that phase's policy
set (focused-policy vs stable-policy: restart rule, rephase eligibility,
target-phase consult, branching heap) independently of the phase's
position in the alternation.  Same policy set, same phase count, same
code paths, same magnitudes; only the mode↔policy correlation carries
information in the treatment.  Report treatment/null per file and
aggregate; T/N ≤ 1 ⇒ nothing, however good the raw number.

## The screen

Standing 54-file corpus × seeds 0–4, 60 s cap, conflicts-to-verdict
primary, verdict agreement mandatory; baseline = the fresh
`precompile/8082e335` re-baseline cells.  Decision rule (pre-registered):
corpus solved-at-cap must not drop and both-decided conflicts geomean
must improve ≥ 3% before the null is built; the Break/summle/j3037-class
target files are the diagnostic rows, not the decision.

## The screen (treatment vs the 8082e335 baseline, both 60 s / 5 seeds)

Solved cells 180 → 174; both-decided conflicts geomean **1.267×** (n=100);
**0 verdict disagreements** (SAT cells model-checked, UNSAT cadical-checked).
Per-file ratios (treat/base, n = matched seeds):

| big losers | ratio | | big winners | ratio |
|---|---|---|---|---|
| ITC2021_Early_3 | 4.35× | | ng-2-s25242449 | **0.023×** (43× better) |
| pb_300_09_lb_07 (5/5→3/5) | 3.63× | | circuit_64in64out (0/5→2/5) | — |
| mp1-Nb7T42 (4/5→1/5) | 3.53× | | noL-11-14 (1/5→4/5) | 1.52× (conflicts worse, verdicts better) |
| qwh.50 | 2.94× | | x9-09054 (3/5→4/5) | 1.03× |
| FmlaEquivChain | 1.86× | | barman-pfile06 | 0.84× |
| constraints_17 | 1.77× | | worker_20_40_20 | 0.89× |
| af-synthesis | 1.72× | | Break_06_07 | 0.94× |
| 6s167-opt | 1.63× | | worker_550 (5/5→4/5) | 1.26× |
| frb65-12-2 | 1.43× | | rbsat (4/5→0/5) | — (wall-censored) |

Shape checks confirm the port does what it says: j3037 (0/5 both arms)
dec/conf 3.13 → **1.56** (below kissat's measured ~1.9) with restarts
5,319 → 457 — the restart collapse comes from the *continuous* EMAs (no
per-mode swap: the default path's swap restores a stale fast/slow pair at
every mode re-entry, which is what re-fires Glucose back-to-back), plus
the log-growing min-gap.

## What the result establishes

1. **The tiered system is real where restarts are the pathology** —
   ng-2 43×, circuit_64in64out 0/5→2/5, noL 1/5→4/5, x9-09054 +1,
   worker_20/barman/Break improved — the same winner set as the margin
   family's semantic content (round 6).
2. **The loser set is the restart-hungry class** — qwh/mp1/pb_300/
   constraints/frb65/ITC/6s167/FmlaEquivChain pay 1.4-4.4× — the same
   loser set as the margin family and the flat floor.  This is now the
   **third independent intervention family** (margin ladder, adaptive
   margin, tiered system) that produces the same per-family sign split.
   The corpus genuinely mixes classes with opposite restart-rate demand;
   no single schedule — however faithfully ported — wins both.
3. The pre-registered exit applies: not landable as a default, null not
   built (both decision clauses failed).  `NIXIE_TIERED=1` stays as
   documented-negative infrastructure.

## Recorded for the next attempt

The only untried shape left in this space is **per-class adaptation on a
measured class signature** — the dec/conf EMA gate is measured dead
(round 7), the glue gates are measured dead (drought study), and the
portfolio exit is measured dead (budget arithmetic).  What has *not* been
measured is a signature from the restart-demand axis itself (e.g. the
search's own restart-gap distribution at phase granularity, or the
conflict-cost response to a probe restart pair — an A/B probe inside the
run).  That is a pre-registration for a future session; the measured
per-family table above (three families, same split) is the design input.

The tiered arm's winner-class conversions (noL 4/5, circuit64 2/5, ng-2
43×) remain available as portfolio-arm material if the budget arithmetic
is ever solved.
