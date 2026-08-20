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


## Hunt log (2026-08-20, session 2): root cause narrowed, not closed

Continued from the landed prerequisite.  Established this session, in order:

1. **DB-dump bisect (7 824 tagged dumps, cadical-verdict-checked, level-0
   trail facts included):** equi-satisfiability flips UNSAT→SAT inside ONE
   `elim_try_variable` call (dump 5623 → 5624) — an elimination of DIMACS
   1076 retiring 4 parents and adding 3 resolvents.
2. **The occurrence lists are complete at every try.**  A per-try ground-truth
   check (live ORIGINAL clauses containing ±pivot vs `ctx.noccs`) printed no
   gap anywhere (an earlier inverted-comparison false alarm is documented).
   At the fired try: occs +v=3 −v=4, ground truth identical.
3. **The bound path refuses correctly** (instrumented pair-by-pair: 12
   resolvents > bound 7 → REFUSED in rounds 1–2).  In the final round the
   three `[-1072,±1076,…]` originals are gone (retired earlier, soundly) and
   the fired elimination is **3×1 = complete over the live originals** —
   hand-applying exactly that transform to dump 5623 as a standalone CNF
   reproduces the SAT flip, so the transform itself is textbook.
4. **The final model is fully consistent with the live DB** (0 violations of
   live originals after reconstruction) yet violates **52 INPUT clauses**
   (e.g. `[-868,874]`, `[-871,874]`, `[-880,886]` — all variables that were
   eliminated).  So the corruption is in the **retirement/reconstruction
   chain**, not the resolution arithmetic.
5. The violated clauses do **not** pass through `retire_clause` near the end
   (provenance watcher on 2+-literal overlap: zero hits) — they left the DB
   earlier in the stack (earlier elim rounds' `elim_retire_clause_lits`,
   subsume retirement, or an in-place strengthen).

Hypotheses ranked for the next session:
- `bve_def` incompleteness: a positive-side clause of an eliminated variable
  retired/rewritten **without** being recorded, so `save_model`'s
  all-satisfied → FALSE reconstruction picks the wrong value.  Test:
  provenance per INPUT clause id from parse time (which pass retired/rewrote
  it), plus a debug `save_model` that checks each reconstructed var against
  its *original* positive side.
- An unentailed "learned" clause surviving into the DB (the 69-clause
  `-1076` population is mostly learned; one unentailed member would explain
  5623's UNSAT and the flip being benign).  Test: RUP-verify the learned
  population over originals under `chronoalways` at reduction time.

Reproducer (unchanged, in-repo): `OXIZ_CHRONO_ALWAYS=1 cargo nextest run -p
oxiz-sat dominator_hbr` (false SAT; needs the opt-in stack:
BVE+INPROCESS+PROBE+HBP — every proper subset answers UNSAT).  Default
configs remain unaffected.


### Session-2b addendum: three more suspects DISPROVEN; conclusion sharpened

- **`bve_def` completeness verified** (per-eliminated-var scan at
  reconstruction: zero live originals still containing +v — every positive
  side fully retired and recorded; no empty-def leaks).
- **Reconstruction is conservative-sound**: the satisfaction test counts only
  definite True/False (Undef → not satisfied → v=TRUE, the direction that
  satisfies the `(v ∨ A_i)` parents), iterated in reverse elimination order.
- **The probe's dominator-HBR retirement site re-audited** against cadical's
  `red = !contained || reason->redundant` — the learned-R arm (retire R, keep
  the binary learned) is sound because learned-R is entailed by the *clause
  set*, and the original-R arm promotes the binary. No hole.

Therefore, by elimination: the final model satisfies every live clause, every
eliminated var's positive side is fully recorded, and the reconstruction is
conservative — yet input clauses are violated.  Some **covering clause
(resolvent or promoted binary) vanished from the live DB** after the parents
it covered were retired — the only remaining class.  Surviving suspects:
cross-pass interactions where a clause that became load-bearing (promoted or
resolvent) is *deletable* (learned-flag set) and a later reduction/inprocess
round removes it while its covered originals are already gone; or an in-place
strengthen of a load-bearing resolvent.  Concrete next step: tag every
resolvent/promotion with its load-bearing bit and assert at each deletion
site that no live-retired original depends on it (one debug build, one run
of the reproducer).


### Session-2c: the vanish is CONFIRMED in the in-place strengthen paths

Env-gated A/B on the reproducer (all reverted; determinism holds per arm):

| arm | verdict |
|---|---|
| baseline | **false SAT** |
| subsume-strengthen off | **pass** |
| vivify off | **pass** |
| elim backward-strengthen off | still false SAT |

Each strengthen site *alone* disables the failure; the backward pass does
not.  (All-three-off fails again — disabling passes shifts the inprocessing
schedule onto a different trajectory where the same latent bug re-fires;
per-arm results are the signal.)  Strengthening a resolvent keeps coverage
(the stronger clause implies the weaker), so a *correct* strengthen cannot
uncover a parent — the implication is a **bug inside one/both strengthen
paths themselves** (literal removal, watch/BIG re-attachment, or the
satisfaction-test interaction with out-of-order trails), not in the
schedule.  Next session: differential instrument `remove_literal_and_rewatch`
+ `vivify_clause` under the reproducer, RUP-verifying every strengthened
clause at rewrite time — the two passing arms above are the regression
seeds.


### Session-2d: strengthen OUTPUTS are sound — the corruption is a side effect

RUP-flagged every in-place strengthen (both sites) under the reproducer
(fixpoint-without-conflict flags are expected — resolution chains are not
RUP), then ground-truthed 84 of the 340 flagged clauses against the
**original input** with CaDiCaL (`input ∧ ¬clause`): **84/84 entailed,
0 unentailed**.  The clauses the strengthen paths produce are correct.

Combined with 2c (either strengthen site off → the false SAT disappears):
the corruption is a **side effect of the strengthen machinery** — watch-list
/ binary-graph / usage-bookkeeping damage during the rewrite, or state
damage in vivify's probe (save-level/decide/propagate/backtrack cycle) —
not the strengthened clauses themselves.  Next session's first move is now
precise: run `debug_check_fixpoint_invariants` + a watch/BIG consistency
sweep after every `remove_literal_and_rewatch` / `vivify_clause` call under
the reproducer (the debug invariant suite already exists; one env knob).


### Session-2e: causal confirmed (control experiment) + invariant sweeps clean

- **Control**: `rephase` off (unrelated to the failure chain) → **still false
  SAT** (and via a different failure surface: the debug
  `debug_verify_model` net catches the model violating a **live** clause,
  `learn.rs` model-violation panic).  So the 2c strengthen-off passes are
  **causal**, not schedule luck.
- **Invariant sweeps after every strengthen call** (both sites: watched
  literals, reason-liveness, post-vivify trail level + propagation fixpoint)
  → all clean.

Standing picture: strengthen sites causally involved; produced clauses
entailed (84/84); post-rewrite state passes every existing invariant — yet
the failure needs them.  Remaining suspects (next session):
- `mark_elim_vars` re-arming after strengthen → the *next* elimination round
  resolves through strengthened parents; combined with the reason-position
  (`lits[0]`) bookkeeping after `swap_lits`, a live reason may be deletable
  (the `reduce_clause_database` is_reason check reads `lits[0]` — a swapped
  reason literal evades the guard → deletion of a live reason → unentailed
  *learned* clauses, which were never sampled in the 84/84 ground-truth).
- The debug-model-violation failure surface under the rephase-off arm is a
  second, independent reproduction seed worth keeping.


### Session-2f: reason-deletion guard verified holding

Instrumented `reduce_clause_database` to flag any deletion of a clause that
is the live reason of ANY of its literals (the `lits[0]`-only guard's
hypothetical hole): **zero hits** under the reproducer.  That suspect is
down; the ranked-remaining list is now: mark_elim_vars re-arm interaction
with the *next* elimination round's occurrence construction, and the
binary-implication-graph edge bookkeeping across `remove_literal_and_rewatch`
(a strengthened-away literal's BIG edges surviving, or vice versa).


## Hunt 3 (2026-08-20, session 3): the "second seed" was an invariant false alarm; causal picture weakened honestly

- **The rephase-arm restart-consistency panic was our own bug**: the check
  assumes rephase's leading root backtrack ran, but `OXIZ_REPHASE_OFF` (the
  A/B knob) made rephase a no-op *after* `rephasing()` had already gated the
  check on — so the check fired on the conflict handler's legitimate
  level-14 backtrack.  Fixed (`rephase_skipped` flag; check skipped for the
  no-op round) — a real landed fix, independent of the hunt.
- **Consequence for the causal claim**: with the false alarm cleared,
  `OXIZ_REPHASE_OFF=1` now *passes* the reproducer (28.6 s, correct UNSAT).
  So THREE unrelated knobs (subsume-strengthen off, vivify off, rephase off)
  each disable the false SAT — the single-pass "causal localization" of hunt
  2c is trajectory-shaped after all, and the earlier "control confirmed
  causal" reading is RETRACTED (the control passed only because the false
  alarm aborted that arm early).  Every "X off → passes" result in this file
  is a trajectory observation, not causal localization.
- What survives: the DB-equi-satisfiability bisect (hunt 2, dumps 5623→5624)
  is a *stateful* fact — some pass between those snapshots loses
  obligations — and the produced clauses are entailed.  The bug is
  state/order-dependent and masked by many schedule perturbations.
- Revised method note: stop using pass-off A/Bs entirely.  The productive
  oracle is the DB dump bisect at finer granularity (it found the flip
  window); next session should dump *between* the retire call and the
  resolvent-add inside `elim_add_resolvents`/`elim_retire_pivot_clauses`
  for the 1076 window (the flip was pinned to try_1075→trybw_1075, i.e.
  inside `elim_try_variable(1075)` — resolution, retire, or its backward
  clause — with occurrence lists verified complete and the fired resolution
  verified complete; the backward clause ran with the *new* resolvents
  already attached, which is the remaining unexamined interaction).
