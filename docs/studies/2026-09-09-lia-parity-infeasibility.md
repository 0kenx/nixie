# LIA parity-infeasibility with unbounded variables (k7+k9-div closed)

**Status: MOSTLY CLOSED (2026-09, fifth session).  k7 (two free vars)
closes via the free-variable sign splits with split-scoped Gomory cuts;
the k9 *div-driven* shape closes via the combined fix — MBQI-instance
div terms axiomatized in-round, remainder case enumeration, and the HNF
Diophantine solver refuting the pinned-remainder parity combination
(k1/jain_2 now `unsat`; classic LIA/UFLIA/AUFLIA sample agree 169 → 178,
0 wrong).  Still open: the hand-written four-free-variable shape without
a div term (below) and the deeper jain unrollings — which **time out
rather than refuse** (i_4 still searching at 60 s: a performance
profile, not a capability gap; candidate cause is the per-round
`instantiate_arith_axioms` re-walk whose idempotence check is
O(defined-terms) per MBQI round).**

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

### Resume here (updated after the third session)

The first two resume items are DONE: the sentinel audit passed
(`note_bnb_conflict_reasons` already filtered `BRANCH_REASON`;
`bnb_unsat_core` builds only from filtered reasons with a sound
full-reason fallback), the scoped flag landed as
`ArithSolver::cuts_in_split_scope`, and k7/k2 now refute — measured with
no QF differential cost (par2 2177.9 vs 2171-2177 baseline band; the
split only triggers when a fractional row's cut was refused for free
nonbasics, which the common path never hits).

**jain per-round perf (twelfth session) — hypothesis rejected, reverted.**
The deep unrollings' timeout was attributed to the O(defined-terms)
idempotence re-walk in `instantiate_arith_axioms` (called per MBQI round
since the k9 fix).  An insertion-ordered log + watermark (scan only new
terms; zero-divisor congruence pairs persisted across batches) was
implemented and measured: the *solving* variants were already at 0.02 s
(the re-walk was never material at these sizes), and the timing-out
variants (i_4+) still time out — the cost lives elsewhere.  A 12 s
`perf record` on i_4 shows the time dominated by `memmove`/hash-churn
in a per-round loop the stripped binary cannot name (~4 % self, ~10 %
children on anonymous frames; no `instantiate_arith_axioms` frame in
evidence).  **Reverted** (measured neutral, added state).  Resume: build
a symbols release, profile i_4, and look at MBQI round internals —
candidate loop shapes are the completed-model clone per round
(`assignments` reaches ~1150 entries on Rodin-class files), the
candidate-cache rebuild, or SAT-clause re-addition of duplicate
instantiations across rounds.

**Remaining (k9, four-plus free vars):** the split leaves close some
branches with real unsat cores but the rest churn — the leaf cut loops
exhaust `LIA_MAX_CUT_ROUNDS` (24) without closing the four-variable
parity, then B&B diverges on the still-open sides.  Candidate directions:
GMI cut *aggregation* across the split scope (sum the defining rows
before deriving), raising/deriving a single *total-parity* lemma
(`2a+2b+2c+2d+1` is odd ⇒ `(y-1) div 2 = a+b+c+d`) at the div-axiom site
instead of through cuts, or Z3's row-local split refinement (split only
the nonbasics of the *div row*, not every free var, keeping the leaf
count at 2^|row| not 2^|all|).

**Fourth-session probe — remainder case enumeration (measured neutral,
reverted):** asserting `(or (= (mod m n) 0) … (= (mod m n) (|n|-1)))`
alongside the Euclidean axioms (cap |n| ≤ 16) makes the remainder's
finite domain visible to CDCL.  Sound, cheap — and flips nothing: with
`mod (y-1) 2` pinned, the `r = 0` side closes linearly as predicted, but
the `r = 1` side is precisely the total-parity conflict
(`2q − 2a − 2b − 2c − 2d + 1 = 0`, all-integer coefficients, odd
constant), which the enumeration cannot reach.  Classic sample 169 agree
/ 0 wrong (unchanged), differential 0 disagreements, parity 174/175 —
so the enumeration was reverted rather than kept as speculative hot-path
weight.  **The eventual k9 fix should combine it with the total-parity
lemma** (emit, at div-axiom time for constant divisor n, the conditional
`(and (= (mod m n) 0) (= (div m n) m/n))` under the guard `n | m` where
divisibility is read off the tableau row of `m` — the r = 1 side then
never arises); the enumeration alone is necessary-but-insufficient.
