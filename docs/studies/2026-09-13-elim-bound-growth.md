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

## Follow-up 4 (same day): the 2×2 matrix completes — the combo loses too (`06011ff4`, worktree-only, never landed)

The obvious untested cell: indexed + scaled together (the scaled clock
fixes indexed's early-phase overrun; indexed's completing phases could
recover what scaled's lateness starved).  Both reimplemented on a
worktree (reverts-of-reverts), anatomy on Timetable: phase 1 at 5 279
conflicts eliminates a best-yet **79 079** complete in 8.5 M
resolutions — but its richer residue re-blocks completion (inter-round
subsume 4 696/19 568 → 22 852 marks; the bound stays 0).

**Screen: 229 → 214 (−15)**, conflicts gm **1.061** (worst of the
four), 0 disagreements.  The complete matrix (cells under
`precompile/06011ff4/`, binary preserved):

| clock \ schedule | duplicate heap | indexed |  |
|---|---|---|---|
| **flat 2k** | **229 (1.000)** | 200 (1.049) |  |
| **log₂-ratio** | 205 (0.968) | 214 (1.061) |  |

The default dominates its entire measured neighborhood.  The
elimination-clock/amplitude thread closes here: the schedule is a
measured local optimum, and the remaining amplitude routes are the
deeper ones already recorded — the inter-round subsume quiescence
(the erratum's "subsume-phase strength": a completing round's residue
must not create marks) and a joint search redesign (cadence + schedule
+ restart policy measured together, not swapped piecemeal).

## Follow-up 5 (same day): the residue is classified — everything funnels
to the phase-1 gap (`a6982d5a`)

`residue_old=`/`residue_fresh=` on the inter-round line (solve-start
id watermark: original-file vs eliminator-created):

| config | phase 3 | phase 4 |
|---|---|---|
| default | old 214 / fresh 257 | old 122 / fresh 138 |
| SUBFIX | old 16 / fresh 36 | old 5 / fresh 23 |

The pre-phase fixpoint does quiesce old-vs-old redundancy; the
persistent blocker is ~2/3 resolvent-involving — tens of removals per
phase, each re-marking variables.  cadical's equivalent inter-round
(verbose=2) *checks 1.08 M clauses and creates zero marks* — and its
resolvents are `mark_added`-scheduled exactly like ours
(`new_clause(false)`), so the asymmetry is **state, not scheduling**:
its phase 1 eliminated 16 k more variables and every downstream
formula — including which resolvents exist to subsume what — differs.

**The elimination-amplitude thread therefore has one root left**: the
phase-1 yield gap (74 757 vs 91 067 at the same budget and schedule).
Closing it needs the same-state differential (eliminate one variable
with both engines on identical state, diff the resolvent sets) — the
next session's concrete entry point for the Timetable class.

## Follow-up 6 (same day): the differential ran — small-file near-parity, divergence is upstream (`d1fe26d5`)

Tools built: `NIXIE_LOG_ELIMDTL` (per-variable decision trace —
outcome + per-pair class counts, landed) and a LOGGING-enabled cadical
(`cp -r ../temp/cadical/{src,scripts,contrib,configure,test,LICENSE,README*,makefile*,VERSION} /tmp/cadical-log/ && ./configure -l && make` — the
reference tree untouched; LOG gates on `--log=true`, *not* verbose).

6s167-opt differential (both engines fully traced): **cadical 3 280
eliminated whole-run vs ours 3 228 — 1.6 % apart.**  The core
eliminator semantics agree at small scale; the Timetable 75 149-vs-91 067
gap does **not** reproduce here.  The ordered traces diverge at pop #0
(ours: a one-sided var; cadical: an eliminated var — upstream
preprocessing/pure-literal/probing removed different things), so trace
alignment cannot isolate the eliminator on diverged states.

Timetable-side aggregate anatomy of our round 1 (the dtl trace, 384 k
decided tries): too_many_res 72.3 %, elim 19.6 %, one_sided 4.6 %,
occ_limit 3.5 % — and the occ-limit gate's raw-vs-flushed divergence
offers ~4.3 k recoverable vars (raw in (100, 140]); the 69 %-too-many-res
mass is where cadical's extra eliminations live, but the bidirectional
outcome mismatches (593 ours-elim/cad-refuse vs 437 reverse) confirm
state contamination rather than a one-sided gate strictness.

**The recorded controlled experiment** (next session): dump our formula
at Timetable phase-1 entry (originals + units; search at 2 k conflicts
has fired no inprocessing yet), feed the identical CNF to both
eliminators (cadical `-P1` with probe/condition off; ours with the
phase forced on it), diff the per-var traces from a truly common
state.

## Follow-up 7 (same day): the occ-limit live-gate hypothesis REFUTED — the raw gate is load-bearing

The cheaper alternative above (close the raw-vs-flushed occ-limit gate
divergence, est. ~4.3 k recoverable vars) was implemented faithfully
(sort-free `compact_live` for the borderline raw>100 population only,
cadical-exact live-count re-gate) and measured:

- **Timetable round 1: 74 757 → 74 759 (+2).**  The 4.3 k raw-in-(100,140]
  vars fail the resolvent bound anyway — the yield hypothesis is dead.
- **mp1-Nb7T42 destroyed**: 16 805 conflicts (bit-stable across every
  prior change of the program) → Unknown at 60 k, restarts 1 202 →
  4 196.  The raw gate is load-bearing for our co-adapted trajectories —
  the third independent confirmation (after the clock matrix) that
  piecemeal cadical-parity changes to the elimination schedule lose.
- 6s167 unchanged (no borderline vars at that scale).

Reverted (working tree returned to `d1fe26d5` byte-identical; no commit
needed).  The raw-gate divergence stays as a *documented* divergence,
not a defect: cadical parity here costs a solving file.  The controlled
same-formula differential (follow-up 6's design) is the remaining
route, with the gate difference noted as a known state confounder to
neutralize in the harness.

## Follow-up 8 (same day): the controlled differential RAN — the root cause found and armed (`3036fe32`)

The same-formula experiment executed with the new
`NIXIE_DUMP_ELIM_ENTRY` (dumps originals + level-0 units at the first
elimination phase) and a LOGGING cadical with every pass but
elimination disabled (`-P1 --probe=false --subsume=false …`):

- **cadical eliminates 123 841 variables on OUR OWN dumped formula**
  where our eliminator eliminates 74 757 — the gap was *inside the
  eliminators*, not upstream state;
- the first divergence at pop #0: cadical's first pops are one-sided
  variables being ELIMINATED (`elim_resolvents_are_bounded` returns
  `lim.elimbound >= 0` for them — true from phase 1): zero resolvents,
  retire the pure side with the pure literal as the extension witness.
  Our port SKIPPED one-sided vars ("leave it to the pure-literal pass")
  — a decision predating sound witness reconstruction; 17 572 such
  skips in round 1 are the cascade starter;
- **`NIXIE_ELIM_ONESIDED`** ports it (in-round one-sided elimination
  via the existing `elim_retire_pivot_clauses` witness machinery):
  Timetable round 1 **74 757 → 91 788** — parity with cadical's
  own-pipeline 91 067;
- the 60 s screen: 229 → 221 (−8 cap conversions, 0 disagreements) but
  **conflicts geomean 0.974 — the best aggregate of every elimination
  variant tried** (all clock/schedule variants were ≥ 1.0).  Per the
  landing bar (completions must not lose) it ships default-off as the
  sixth amplitude arm; the default is bit-identical to `107b7868`;
- mp1 model validity with the arm on: total model, 0 falsified clauses
  (the one-sided witness reconstruction works).

The program-level conclusion sharpens: the 60 s mini-bench cap
anti-correlates with elimination amplitude **five independent ways**
(indexed schedule, scaled clock, combo, live gate, one-sided
elimination) — while the aggregate-conflicts direction favors the
amplitude arms (this one at 0.974).  Whether the standing screen's cap
is the right acceptance metric for elimination work is the recorded
program question.

## Follow-up 9 (same day): the wide-cap check — losses are cap artifacts, but no reversal

The 60 s losers + hard-class files re-run at the 300 s cap, default vs
`NIXIE_ELIM_ONESIDED` (9 files × 5 seeds × 2 arms):

- **every file 5/5 on both arms** — the −8 cells were pure cap
  artifacts (6.5 k-conflict Timetable solves simply cost more wall than
  60 s allows at that clause mass);
- but the arm does **not** convert that into wide-cap wins: cell-equal
  everywhere, conflicts mixed and mostly worse on this sample
  (j3037 1.22 M vs 506 k, af-synthesis 2.65 M vs 1.57 M,
  g2-slp 1.71 M vs 1.38 M; si2 better 134 k vs 144 k; frb45 and
  mp1-klieber bit-identical — no one-sided variables in their rounds);
  **Timetable itself times out under the arm at 300 s** (default: 5/5,
  ~6.5 k conflicts average) — the better round-1 elimination does not
  translate into a better search trajectory on the very file it was
  aimed at.

The program question gets its nuance: the 60 s cap *does* misjudge
amplitude arms (five-way confirmation + this), but the one-sided arm is
not a wide-cap winner either — its best datum remains the corpus-wide
0.974 conflicts geomean.  It stands as measured infrastructure; the
amplitude→search-trajectory translation (why a 17 k-variable-richer
elimination can still slow the solve) is the deeper open question this
program now ends on.

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
