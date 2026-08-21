# Arithmetic negated-atom enforcement: two false-SAT holes mapped, fix attempt reverted (2026-08-21)

Status: **not fixed on main** — this records a root-cause map, a complete but
unlanded fix design, and the regression that forced the revert. All findings
verified on clean-HEAD worktree binaries (commit `3bfd6bf`).

## The bug class (pre-existing on main)

Several UNSAT instances answer `sat` because **theory atoms assigned their
negative polarity are not enforced against the final arithmetic model**:

| instance | logic | z3 | oxiz (main) |
|---|---|---|---|
| `smt-lib/non-incremental/QF_UFIDL/pete/5s.smt2` (also cxs-bp, cxs-bp-ex, cxs-bp-safety) | QF_UFIDL | unsat (0.03s) | **sat** (0.8s) |
| `smt-lib/non-incremental/QF_ANIA/20190429-UltimateAutomizerSvcomp2019/avg40…TraceCheck_0.smt2` | QF_ANIA | unsat (3.8s) | **sat** (2.5s) |

Historical differential snapshots show these as *timeouts* — the false-SATs
became reachable when the search got fast enough to reach a bad full
assignment inside the 10 s cap.

### Hole A — negated `=` atoms never reach the arithmetic solver

`process_constraint` (theory_manager.rs) sends a **positive** `Eq` atom to
`arith.assert_eq` (tableau row), but a **negative** `Eq` atom (`(= a b)`
assigned false ⇒ a ≠ b) only asserts an EUF disequality (+ BV when
applicable). Nothing ever forces the *arithmetic* model to give the two
sides different values: `nelson_oppen_combine` propagates arith-entailed
equalities into EUF, but only when arithmetic *entails* the equality —
equal-by-accident model values (two free vars both at 3) never conflict with
the EUF diseq. Model-based combination only checks same-EUF-class ⇒ same
arith value, not the dual. Result: `sat` over a theory-inconsistent
assignment.

### Hole B — RETRACTED (scanner artifact) and superseded by the pin experiment

The originally reported "Hole B" (a negated `Le` atom, var 223, `-t ≤ 0`
assigned false with model `t = 1`) was a **misdiagnosis**: `var_to_parsed_arith`
carries a **`Le` placeholder for `Eq` atoms** (encode.rs stores it so the
positive polarity can assert both bounds), and the first scanner version
evaluated every parsed form as a comparison — misreading a negated `=` atom
(`t448 ≠ t456`, model 2 ≠ 3: **satisfied**) as a violated `≤`. With the
scanner fixed (comparison checks only for genuine `Lt/Le/Gt/Ge` constraints),
it reports **zero per-atom violations** on 5s's accepted assignment.

What actually characterizes the bug (z3-certified):

* oxiz answered `sat` on 5s with model `pc0 = -1, dmem0 = -1, a1 = -1,
  ZERO = -2` (and **no UF interpretations** in the printed model);
* `F ∧ (= pc0 -1)` is **UNSAT** — the pinned constant *alone* refutes the
  formula (verified by minimization over the 4 pins: every proper subset is
  sat);
* every assigned atom is individually consistent with the theory model
  under oxiz's opaque values for UF-application variables.

So the missing enforcement is **not** at the atom level: the formula entails
`pc0 ≠ -1` through a chain (pinned constant → ite-condition resolution →
equal-argument congruence on UF applications → a contradictory
equality/disequality), and oxiz's final_check accepts an assignment that
breaks that chain — the negated-equality/congruence conflict is never
derived. This is Hole-A-shaped (negated `=` enforcement) but at the level of
*propagated/congruent* facts rather than asserted atoms: the operands whose
equality congruence forces are themselves UF results whose equality only the
combination loop can see.

## The fix attempt (reverted)

A complete `assert_diseq` for `ArithSolver` was implemented and validated at
the unit level (3 focused tests + a 400-case random brute-force oracle over
±5 grids, all passing):

* `assert_diseq(terms, rhs, reason)` records the constraint; `check()`
  enforces it via split-on-demand DFS: find the first diseq the current LP
  model violates → probe both split sides in scratch simplex scopes
  (integers: exact `≤ rhs-1 ∨ ≥ rhs+1`; reals: delta-strict `<`/`>`) →
  commit a feasible side in its own scope, flip on dead ends.
* Commit bookkeeping distinguishes **forced** sides (the other side refuted
  ⇒ the bound is a consequence of the atom; tight conflict cores may cite
  the atom) from **choice** sides (both feasible ⇒ any dead-end core citing
  it is not implied; fall back to the full asserted-atom core, justified by
  the exhausted DFS).
* All commits unwind at check exit; branch-and-bound's integral model is
  re-checked against the diseqs (the fractional LP value can hide a
  violation that every integral leaf has).
* Wired into the manager's negative-`Eq` and positive-`Diseq` arms (gated
  `!dl_pure`, see below). **With this wiring pete answered `unsat`**
  (correctly) until later enforcement fixes reshuffled the search trajectory
  (see the Hole B retraction below for what that residual failure is).

### Integration bugs found while landing it (all real, all with reproducers)

1. **Zombie disequalities across `reset()`**: `resync_theory_state` does
   `arith.reset()` + replay, but `reset()` did not clear the new
   `disequalities` vector — constraints of dead assignments survived into
   later rounds and over-constrained them (false `unsat` on
   `storeinv/swap_sf` sat-side tests; z3-verified the dead-end systems were
   genuinely unsat, proving the *state* was wrong, not the search).
   Lesson: **any new assertion vector added to a solver must be cleared in
   `reset()` and truncated in `ContextState`** — the replay re-feeds.
   The same replay also re-feeds every assigned atom per MBQI round →
   dedup `assert_diseq` on (form, rhs).
2. **Simplex `pop()` can restore a stale assignment with
   `assignment_current` still set**: `check()` snapshots the level *before*
   testing staleness, so a stale-at-snapshot-time assignment is restored
   verbatim; the next `check` skips `crash_basis` and `pivot`'s incremental
   delta propagation builds on inconsistent values (the
   `delta propagation mismatch` debug invariant fires; in release the
   assignment silently diverges). Fix (not landed): mark the assignment
   stale unconditionally on every pop — Dutertre–de Moura ("only bounds are
   backtrackable") promises exactly that. If this panic is ever seen on
   main, the fix is ready here.
3. **DL-purity cliff**: feeding a diseq on the pure-DL path called
   `break_dl_purity()` → qlock/queen (751-node DL graphs) degrade from
   1.8 s to timeout (simplex B&B over rows the dense core already decided;
   the pre-existing comment at the `!dl_pure` skip of
   `propagate_euf_equalities_to_arith` documents the same cliff). Gate the
   feeds on `!dl_pure`.

## Why it was reverted

The differential suite (270 pinned instances) flagged a NEW wrong answer:
`QF_UFLIA/wisas/xs_8_13.smt2` — `unsat` on main (correct, 6.4 s), `sat`
with the machinery (fast). With pete still false-SAT (per the then-believed
Hole B; per the corrected analysis below, the residual failure is the
combination-chain gap), the change was net-negative: it traded one pre-existing false-SAT for a
regression on a previously-correct family. Everything was reverted;
`git log` around `3bfd6bf` has the full implementation in the WIP if
resumed (or re-derive from this doc — the design above is complete).

## Diagnostic tooling (committed with this study's follow-up)

* **`OXIZ_SCAN_VIOL=1`** (debug builds): at `check_core`'s `Sat` exit, walk
  every assigned theory atom and print the first one the final theory model
  violates (`theory_manager/debug_scan.rs`; comparison checks only for
  genuine `Lt/Le/Gt/Ge` — see the module doc for the placeholder trap).
  Negative result is itself informative: it localizes the failure *below*
  the atom level.
* **Pin experiment** (external, z3): solve, take the model's constant
  assignments, check `F ∧ pins` with z3, then minimize the pin set. A
  refutable pin proves the `sat` verdict wrong without any internal
  instrumentation — this is what certified the 5s bug (`pc0 = -1` alone).
* **SMT2 dead-end dump** (from the reverted machinery work): at a DFS
  terminal dead end, dump equalities + bounds + diseqs as QF_LIA and ask
  z3 — distinguishes "search unsound" (z3: sat) from "state wrong" (z3:
  unsat ⇒ look for zombie/stale assertions).
* Bisect discipline: test in a `git worktree`, never stash/restore the
  shared tree; rebuild the harness binaries per commit.

## ROOT CAUSE (found 2026-08-21, follow-up session): non-convex combination incompleteness

The congruence-gap probe (`debug_scan_congruence_gaps`, committed with the
scanner) settles the mechanism on 5s's accepted assignment:

```
[cgap] PROPAGATION GAP: apps TermId(188) vs TermId(729) — args arith-equal
       in the model, EUF-distinct (merge never propagated)   [×4 more pairs]
```

`nelson_oppen_combine`'s arith→EUF direction only merges **entailed**
equalities (`entailed_equal_reason` = two scratch simplex proofs). When the
refutation requires merging two arguments that the arith model merely
*assigns* equal (not entails — e.g. two opaque UF-result variables the LP
happened to co-locate), the probe correctly declines, the merge never
commits, congruence never fires on the UF applications, and the negated-`=`
atom between the (would-be congruent) results never conflicts. The search
then reports `Sat` over an **arrangement that was never jointly checked** —
the textbook non-convex Nelson-Oppen gap. Per-atom scanning cannot see it
(each atom is individually consistent); the pin experiment certified it
(`F ∧ (= pc0 -1)` is unsat while the model pins `pc0 = -1`).

### Fix shape (z3/cvc5 `th_combination` / arrangement-based, NOT landed)

Tentative-arrangement round at `final_check`:

1. Collect the model-equal candidate pairs the cgap probe finds (interface
   terms that are UF arguments, grouped by arith value — the existing
   `by_val` machinery already builds this set).
2. Tentatively merge them in EUF **inside a scope** (EUF needs push/pop or a
   rebuild-on-exit; today only `reset()`+replay exists — the cheap route is
   snapshotting the merge list and unmerging is NOT sound in general, so a
   scoped EUF or a replay is required).
3. If EUF conflicts under the tentative arrangement, the assignment implies
   `¬(x₁=y₁ ∧ … ∧ xₖ=yₖ)` over the merged pairs — learn that **interface
   disjunction lemma** as a clause over the pairs' `(= x_i y_i)` SAT atoms
   (encodable whenever the pairs are formula atoms, which the pete family's
   `(= app1 app2)` atoms are; pairs without a SAT variable cannot be
   learned — skip them, staying incomplete-but-sound there).
4. Drop the tentative merges and continue the search. Iterate.

Sound because the lemma is a logical consequence of the (refuted) tentative
conjunction; incomplete only for pairs lacking SAT atoms.

The reverted `assert_diseq` machinery is complementary, not sufficient: it
enforces negated-`=` atoms *inside* arithmetic once operands are interned,
but the pete refutation needs the arrangement merge FIRST (congruence over
equal args) to make the negated-`=` fire — which is why wiring it flipped
pete only along some trajectories.

## Remaining steps

1. Land the arrangement round per the design above (scoped EUF merges +
   interface disjunction lemmas); regression: 5s/cxs-bp* → `unsat`,
   differential 0 new unsound.
2. Re-validate `QF_UFLIA/wisas/xs_8_13.smt2` (the earlier machinery
   regression): check whether main also goes false-SAT there under a
   different seed/schedule before blaming the added enforcement.
3. Full bar + differential + parity per AGENTS.md.
