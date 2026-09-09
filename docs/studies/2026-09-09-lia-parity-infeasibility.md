# LIA parity-infeasibility with unbounded variables (open, the jain_2 root)

**Status: OPEN — arithmetic solver completeness.  This is the last blocker
on the compound-sum jain class; everything on the quantifier side of that
chain now works.**

## The sharpest repro (k7)

```smt2
(set-logic LIA)
(declare-const y Int) (declare-const S Int)
(declare-const q Int) (declare-const r Int)
(assert (= y (+ (* 2 S) 1)))
(assert (= (- y 1) (+ (* 2 q) r)))
(assert (>= r 0)) (assert (<= r 1))
(assert (< (+ (* 2 q) 1) y))
(check-sat)   ; unsat (z3); nixie: unknown
```

Substituting the equalities gives `r = 2(S-q)` with `q ≤ S-1`, so
`r ≥ 2` against `r ≤ 1` — a **global parity conflict**: LP-feasible
(fractional points exist), integer-infeasible in every region, variables
unbounded.  The substituted single-row form (k8, same constraints with
`y` eliminated by hand) refutes fine — only the two-equality routing
through the extra variable fails.

## Why each existing mechanism misses it

* **Branch-and-bound diverges**: every branch region re-optimizes to the
  next fractional point on an unbounded ray; the conflict is global
  (parity), so enumeration never closes it.  Measured walk:
  `a := -1/2, -3/2, -5/2, …` to the depth cap → `TheoryResult::Unknown`
  → the resource gate turns the whole goal `unknown`.
* **Gomory cuts do not fire**: the GMI derivation assumes nonbasic
  variables rest at bounds; free (two-side-unbounded) nonbasics rest at
  crash-basis defaults where the cut formula does not apply.
* **`integral_dive`** (the 2026-09 sat-side repair) correctly declines:
  equality probes at floor/ceil are inconclusive when the region has no
  integral point at all — that is an UNSAT witness, which the dive is not
  allowed to conclude.
* **`cached_int_eq_verdict`** (the Diophantine/GCD elimination) handles
  pure-equality classes; the strict inequality row breaks purity.

## What a fix needs (Z3 reference)

Z3's `theory_arith_int` closes this class with its **Gomory mixed-integer
cut machinery over the free-variable tableau** (cuts derived from rows
even when nonbasics are not bound-resting, via the mixed cut form) plus
**branch history-guided cut regeneration** — `mk_gomory_cut` in
`src/smt/theory_arith_int.h` and the `bnb` cut-then-branch loop.  The
alternative is a Cooper-style parity projection for two-variable rows of
the shape `r = a·x + b·y` with small bounded `r`.

## The chain this blocks (all quantifier-side pieces work)

`(exists s0..s3. y = 2·Σs + 1)` (skolemized, ground) with
`(not (exists v. 2v+1 = y))` (derived guarded universal):

1. the symbolic linear witness `(y-1) div 2` IS now solved and emitted
   every round (`solve_linear_witnesses` no longer gates on
   `counterexamples.is_empty()`),
2. its instance `not (2·((y-1) div 2)+1 = y)` IS added with the Euclidean
   axioms interned,
3. and the ground discharge of that instance reduces **exactly to k7**
   (with `q := (y-1) div 2`, `r := (y-1) mod 2`) — where the arithmetic
   layer answers `unknown`.

Fix k7 and the whole jain/Ultimate compound class flips to `unsat` with
no further quantifier work.

## Attempt log (2026-09-09, second session): the `constrain_free_vars` port

Z3's actual mechanism was located and confirmed in
`src/smt/theory_arith_int.h`: **`constrain_free_vars`** internalizes
`v >= 0` case-split atoms for the free variables of a cut-target row, so
the DPLL layer bounds them and `is_gomory_cut_target` (all nonbasics at
bounds) starts holding.  A theory-internal port was implemented and
measured on k7:

* **Sign-split recursion** (`u >= 0` / `u <= -1`, exhaustive over the
  integers, depth ≤ free-var count, capped at 8): with the free list
  collected from fractional rows *and* free fractional basics, and with
  each leaf re-entering the full cuts-then-B&B, the split closed **6 of
  14 branch children with real unsat cores** — the mechanism derives the
  parity conflicts it exists for.
* **The remaining 8 children diverge** because the leaf's cut re-entry is
  refused: `gomory_cut` rejects any nonbasic resting at a
  `BRANCH_REASON` bound ("a cut using one is only valid inside that
  branch, never at root where cuts are asserted").  Inside a split scope
  that rejection is over-strict — the cut would be scoped to the branch —
  but allowing it requires auditing how `BRANCH_REASON` sentinel ids flow
  through `bnb_unsat_core` and the exported conflict clauses (a sentinel
  in a SAT-level core would be a soundness hazard).
* **Reverted** rather than half-landed: 2^k branching in the hot LIA path
  without closing its motivating repro failed the measured-merit bar.

### Resume here

1. Add a scoped flag allowing branch-reason bounds in `gomory_cut` when
   the cut lives inside a split scope; audit `note_bnb_conflict_reasons`
   and `bnb_unsat_core` for sentinel handling first.
2. Re-measure k7 (expect all 14 children Unsat → `unsat`), then the jain
   compound class, then the full differential gates — the 2^k split needs
   a matched-null performance check on QF_LIA (the branch factor lands on
   every LIA check with ≥1 free var, i.e. nearly all of them; Z3 avoids
   the blowup by splitting only row-local free vars of cut targets).
