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

## Resume plan

1. Root-cause why the accepted assignment's `pc0 = -1` pin is not refuted
   internally. The chain to instrument: arith pins `pc0` → bound propagation
   resolves ite conditions (`is_dl_family` Tighten mode) → equal arguments
   reach EUF (congruence) → a negated `=` atom between congruent UF results
   must conflict. Prime suspects: UF-application results never interned as
   arith interface terms (so `nelson_oppen_combine`'s model-equal probe
   never sees the pair), and negated `=` atoms reaching EUF only (Hole A).
2. Re-land the `assert_diseq` machinery (design above; unit tests + oracle
   are re-derivable) once (1) explains why it helped pete and why wisas
   regressed: re-validate `QF_UFLIA/wisas/xs_8_13.smt2` FIRST — check
   whether main also goes false-SAT on wisas under a different seed/schedule
   before blaming the DFS (the machinery reshuffles trajectories; the study
   of the SAT side documents 7× swings from seed alone).
3. Only then re-run: full bar + differential (0 new unsound required) +
   parity, per AGENTS.md.
