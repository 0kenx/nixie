# The tiered per-mode schedule port: pre-registration (2026-09-12)

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
