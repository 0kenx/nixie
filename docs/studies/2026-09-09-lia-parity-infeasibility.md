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
