# The elimination bound never grew: round-local rescheduling and the phase-completion gate (2026-09-13)

Round-10 handoff item 2 (the Timetable elimination-schedule family).
The recorded state said our elimination matched cadical's algorithm
("bound, limits, OTF shrink, backward pass all verified identical" —
and-gate study) and the residual gap was "phase-yield starvation" fed
by subsume strength.  That framing was wrong in one load-bearing
detail, found by putting `marks=`/`bound=` into the `NIXIE_LOG_ELIM`
phase line: **our elimination bound never grows at all.**

## The measurement that broke the old framing

Timetable, HEAD-before (`8082e335` lineage), 60 k conflicts, 7 phases:

```
phase 1 start: conflicts=2000  marks=279524 bound=0   → round 1: eliminated=74535 complete=true
phase 2 start: conflicts=6003  marks=10721  bound=0   → 1732+379
phase 3 start: conflicts=12166 marks=203008 bound=0   → 3596+28
phase 4-7:     marks≈199000    bound=0      → 120/60/28/21
```

`bound=0` through every phase — `increase_elimination_bound` never
fired, because `phase_complete` was unreachable.  (The and-gate study's
"bound growing 0→16 on schedule" was a misreading; its own anatomy
tables show the collapse the stuck bound predicts.)

cadical on the same file (`--verbose=2`, 7 elim phases, 147 478 total):

| phase | round(s) | scheduled | eliminated | completed | bound after |
|---|---|---|---|---|---|
| 1 | 1 | 279 461 (mark-all) | 91 067 (10 M resolutions, incomplete) | no | 0 |
| 2 | 2,3 | 13 688 / 17 889 | 32 / 2 358 | no (round limit) | 0 |
| 3 | 4 | 2 878 | 27 | **yes** | 0→1 |
| 4 | 5 | 185 975 (mark-all) | **21 103** | **yes** | 1→2 |
| 5 | 6 | 164 872 | 10 705 | yes | 2→4 |
| 6 | 7 | 154 164 | 2 444 | yes | 4→8 |
| 7 | 8 | 151 720 | 19 742 | yes | 8→16 |

**53.9 k of cadical's 147 k variables are eliminated in the
bound-growth cycle** (bounds 1-16) — the phase-completion exit is not a
detail of the schedule; it *is* the amplitude.

## The two defects (both cadical-semantics corrections, `107b7868`)

1. **Round-local vs persistent rescheduling.**  cadical's
   `elim_update_removed_lit` (retirements during a round) pushes into
   the *round's* schedule — it never touches the persistent
   `flags.elim`/`stats.mark.elim` candidate set.  Our port called
   `mark_elim_one` (persistent) for every literal of every clause the
   eliminator itself removed or shrank.  Consequence: the eliminator
   self-perpetuated — `elim_mark_count > 0` after every round, so (a)
   `eliminating()` fired a phase at every clock tick, (b) round 2 of
   every phase always ran, (c) the phase always exited at the round
   limit with `phase_complete = false`.

2. **The completion gate's mark accounting.**  cadical's
   `subsume_round()` captures `old_marked = stats.mark.elim` at entry
   and returns whether the subsumption pass *itself* created new
   candidates; the phase loop continues on that return value.  Marks
   that predate the pass do not continue the phase.  Ours continued on
   any `elim_mark_count > 0`.

Both fixed in `107b7868` (plus `marks=`/`bound=` in the diagnostic
phase line).  The bound now grows where the inter-round subsume
quiesces — measured on noL-11-14: `bound=1` from phase 2 (was 0
forever).

## What the fix does NOT yet fix (the recorded open items)

- **Timetable still never completes a phase**: the inter-round
  `subsume_round` finds 260-800 subsumption/strengthening removals
  every phase (→ 2-3.5 k new marks) where cadical's finds none after
  its round-side backward pass has fully absorbed the resolvent
  residue.  This is precisely the erratum's "subsume-phase strength"
  item (round hit-rate / candidate generation) — the next lever for the
  Timetable class, now with an exact gate to measure: *phase completes
  iff the inter-round subsume creates zero marks*.
- **Phase-1 yield gap at the same budget**: 74 757 eliminated at the
  10 M-resolution cap vs cadical's 91 067 (same 279 k schedule, same
  cap, same bound-0).  The and-gate study's "matched algorithms"
  conclusion needs revisiting against this 16 k residual.

## Screen

`precompile/107b7868/benchmark/runs/sc24f/` (54 files × seeds 0-4,
60 s cap, model-checked SAT / cadical-agreed UNSAT, rebaseline runner
protocol at the new sha).  Against the `8082e335` baseline on the 270
common cells:

| | 8082e335 | 107b7868 |
|---|---|---|
| solved cells | 180 | **229 (+49)** |
| verdict disagreements | — | **0** |
| conflicts geomean (both-decided, n=110) | 1.000 | 1.048 |

Because `107b7868` carries *both* of today's fixes, the +49 was
attributed by re-running the 54 gained cells with the model-fix-only
binary (`32c88866`, runner script in this study's assets):

- **43 cells are the false-witness fix** (the old binary solved them;
  its broken models failed the verification gate and the cells were
  recorded `unknown`) — summle×15, si2×5, circuit_48×14, j3037×4,
  g2-slp×4, 64_25×1.  The "0/5-at-60 s class" of the 2026-09-12
  program was in large part this measurement corruption, not solving
  weakness.
- **11 cells are schedule-fix conversions** — Timetable (the first
  solved cell on the #1 diagnosis target of the whole amplitude
  program), frb45×3, mp1-klieber×2, af-synthesis, g2-slp, j3037,
  shuffling, 64_25 — against 5 lost marginal cells (noL, pb_300,
  rbsat, af, frb45) on the 4.8 % both-decided conflicts increase.

## Follow-up (same day): the inter-round fixpoint does not unlock Timetable (`6ee26fda`)

The completion fix made `NIXIE_ELIM_SUBFIX`'s dead verdict stale, so the
arm was re-measured and extended with a second slot (inter-round
subsume to fixpoint, bounded 8 rounds, same flag).  Anatomy on
Timetable: the pre-phase fixpoint slot shrinks the inter-round residue
471/795 → 52/72 removals per phase, and the new inter-round slot
absorbs the residue to a zero-yield round — but the marks created *by
the absorption itself* keep `elim_mark_count > marks_before`, so round
2 still runs and the round limit still blocks completion.  The bound
stays 0 on this file; the arm remains default-off infrastructure.

The blocker is not scheduling but trajectory: our phase 1 eliminates
74 757 of cadical's 91 067 at the same 10 M-resolution budget, so every
later state — including its residue structure — diverges from
cadical's, whose phases 4-7 genuinely quiesce in one round.  The
next-session lead for the phase-1 gap: the **reschedule order** —
cadical's `schedule.update(idx)` re-scores the existing entry in place
while our BinaryHeap push adds a ranked duplicate, so pops proceed in
different orders and the two engines spend the same resolution budget
on different elimination opportunities.  A same-state differential
(eliminate one var with both orderings, diff the resolvent sets) is
the cheap experiment.

## Follow-up 2 (same day): the schedule-order hypothesis CONFIRMED, the default still loses (`281de4c0` + revert `29364160`)

A position-mapped schedule (`IndexedSchedule`, cadical's
`heap<elim_more>` `update`-in-place semantics, same score formula) was
implemented and measured on Timetable:

| | BinaryHeap (duplicates) | IndexedSchedule | cadical |
|---|---|---|---|
| round-1 pops | 729 023 (drained) | **401 333** | 403 731 (8 444 remain) |
| round-1 eliminated | 74 757 @ 10 M (incomplete) | **75 149 @ 8.58 M (complete)** | 91 067 @ 10 M (incomplete) |
| bound growth | never | **0→1 (phase 1 completes)** | 0→1 at phase 3 |
| phase-2 yield | 1 949 | **26 781** | 21 103 |
| total @ 21 k conflicts | ~78 k | **~103 k** | — |

The order hypothesis is confirmed end-to-end: duplicate pushes popped
occurrence-widened variables at stale better ranks, burning the budget
on big lists ahead of turn; one-entry-per-variable with in-place
re-scoring restores cadical's pop count *and* unlocks the bound cycle.

**But the 60 s corpus screen loses: 220 → 200 solved cells** (records
under `precompile/281de4c0/benchmark/runs/sc24f/`; 0 disagreements,
conflicts gm 1.049; 14 files lose, 2 gain).  The amplitude arrives too
early: our first phase fires unconditionally at `lim_elim = 2k`
conflicts, while cadical's marks gate holds its first phase to ~12.5 k
(probing/subsumption must feed candidates first) — easy files pay the
richer elimination before their search has done its work.

Reverted from the default (`29364160`; trajectory re-verified
bit-identical to `107b7868`); the `tried=/remain=` diagnostics stay on
the round line, and the `IndexedSchedule` implementation is preserved
in `281de4c0`'s history for revival as an arm.  **The recorded next
experiment**: gate the first phase on cadical's marks condition (or
raise `elim_interval`) so the bound-growth cycle fires at cadical's
cadence — the amplitude is now *reachable*; the open question is only
when it should run.

## Follow-up 3 (same day): cadical's `scale()` clock also loses — the flat-2k default is defended from both sides (`93703871` + revert `951b1a53`)

The recorded next experiment (gate phases to cadical's cadence) was
run as the faithful port: `lim.elim = conflicts + scale(elimint ×
(phases+1))` with cadical's `limit.cpp` `scale()` — `log2(live_
irredundant / active_vars)` when the ratio exceeds 2, applied to the
initial limit at solve entry and at every phase end.  Timetable's
cadence matches cadical exactly (phase 1 at 5 279 conflicts, phase 2 at
18 066 vs cadical's 12.5 k/18.7 k — the residual gap is cadical's
marks-gated first phase).

**The screen loses symmetrically: 229 → 205 solved cells (−24)**
(records under `precompile/93703871/benchmark/runs/sc24f/`; 0
disagreements) — but with the *opposite* sign on conflicts: geomean
**0.968** (the search itself is 3 % cheaper per both-decided verdict)
while conversions collapse (g2-slp −5, mp1-klieber −4, rbsat −3,
summle −3: files whose early elimination the flat clock was feeding).

The two experiments bracket the default:

| arm | clock | schedule | cells | conflicts gm |
|---|---|---|---|---|
| indexed (`281de4c0`) | flat 2k | update-in-place | 220 → 200 | 1.049 |
| **default (`107b7868`)** | **flat 2k** | **duplicate heap** | **229** | 1.000 |
| scaled (`93703871`) | log2-ratio | duplicate heap | 229 → 205 | 0.968 |

Neither single-step departure from the default wins: earlier-and-
richer elimination overruns easy files; later elimination starves the
files that needed it.  The search (restarts, phase saving, probe
interleave) has co-adapted to the flat-2k schedule over the whole
2026-09 program — cadical's clock assumes cadical's search.  The
amplitude levers are real and now individually reachable (the indexed
schedule unlocks the bound cycle; the scaled clock matches cadical's
cadence) — but each must arrive packaged with a cadence *our* search
tolerates, which is a joint search, not a clock swap.  Recorded for
the next session as the standing question of the Timetable class.

## Verdict

**Landed as the default** (`107b7868`): +11/−5 solved cells at the
60 s cap including the first Timetable solve, 0 verdict disagreements
across 270 cells and the full workspace suite, at a mild 1.048×
both-decided conflicts cost.  Both changes are reference-semantics
corrections (the old behavior was a port bug — a schedule that could
never complete a phase), not tuned heuristics, so the old/new
differential *is* the comparison of interest; no matched-null
machinery applies.

The path to the remaining Timetable amplitude (81 k → 147 k) is now
exactly gated: *phase completes iff the inter-round subsume creates
zero new marks* — on Timetable it leaves 260-800 removals (2-3.5 k
marks) per phase where cadical's leaves none.  That is the erratum's
"subsume-phase strength" item, plus the phase-1 yield gap
(74 757 vs 91 067 at the same 10 M-resolution budget) for the next
session.  The `marks=`/`bound=` phase-line fields make every
candidate hypothesis measurable before building it.
