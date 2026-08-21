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

### Hole B — negated comparison atoms unenforced at the final model

Diagnostic recipe (method below): on today's `5s.smt2` false-SAT the
violated atom is a **`Le`** atom, var 223, form `-t ≤ 0`, **assigned false**
(the formula demands `t < 0`), while the final model has `t = 1`.
`process_constraint` was called for this atom 656 times (always
`is_positive=false`, at 24+ different levels), each call allegedly running
`arith.assert_gt` — the row still does not constrain the final model
(candidate mechanisms: scope/pop divergence between the manager replay and
the simplex bound trail; stale `lia_model` snapshot read by the value
extraction; the processed-lits guard skipping a re-assert after a
backtrack-resync). **Unresolved** — this hole alone keeps pete false-SAT
even after Hole A is closed.

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
  (correctly) until the search trajectory moved and Hole B took over.

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
with the machinery (fast). With pete still false-SAT through Hole B, the
change was net-negative: it traded one pre-existing false-SAT for a
regression on a previously-correct family. Everything was reverted;
`git log` around `3bfd6bf` has the full implementation in the WIP if
resumed (or re-derive from this doc — the design above is complete).

## Diagnostic tooling recipe (rebuild when resuming)

* **Theory-model violation scanner**: wrap `final_check` to return through a
  checker that walks every assigned `var_to_constraint` atom, evaluates
  Eq/Diseq via `euf.value`/`arith.value` and Le/Lt/Ge/Gt via
  `var_to_parsed_arith` sums, and prints the first atom whose polarity
  contradicts the model (`is_pos != model_holds`). This is how Hole B was
  found (env-gate it; ~60 lines).
* **SMT2 dead-end dump**: at a DFS terminal dead end, dump
  `int_equalities` + per-var bounds + diseqs as QF_LIA and ask z3 —
  distinguishes "search unsound" (z3: sat) from "state wrong" (z3: unsat,
  look for zombie/stale assertions).
* Bisect discipline: test in a `git worktree`, never stash/restore the
  shared tree; the harness binaries in `/tmp` must be rebuilt per commit.

## Resume plan

1. Fix Hole B first (it blocks pete even with Hole A closed): instrument the
   Le-negation path — why `assert_gt`'s row does not constrain the final
   model. Prime suspects: the processed-lits guard vs resync replay
   interleaving, and `lia_model` staleness in `value()`.
2. Re-validate the `assert_diseq` machinery against wisas (the regression
   may be Hole-B-shaped: the new conflicts reshuffled the search into a
   hole that main's slower trajectory never visited — check whether main
   also goes false-SAT on wisas with a longer seed/schedule before blaming
   the DFS).
3. Only then re-run: full bar + differential (0 new unsound required) +
   parity, per AGENTS.md.
