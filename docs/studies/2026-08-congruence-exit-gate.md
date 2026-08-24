# Trajectory-independent closure of the non-convex Nelson-Oppen gap: the final congruence honesty gate (2026-08-24)

## Trigger

The trie-vivify false-SAT post-mortem (pete/cxs-bp, reverted in
`ec2a06a`) recorded the follow-up: *the arrangement round closes the
pete false-SATs on the trajectories it was measured on; a clause-DB
perturbation suffices to re-cross the boundary.  Coverage must become
unconditional or the residual gap an honest `Unknown`.*  This lands the
honest-gap half.

## Design

The arrangement round's coverage is a property of the trajectory that
reached the candidate: its pair caps (64), merge cap (32), and the model
value-grouping all admit misses under perturbation.  The gate instead
fires on the **gap itself**, at the only point where a wrong answer can
escape: the final `Sat` commit.

`Solver::model_violates_euf_congruence` — already the quantified path's
backstop (pr30#3) — checks the *built model*: two applications of one
function whose arguments the model maps to equal values but whose
results differ cannot be extended to a real interpretation.  Wired at
the quantifier-free `Sat` exit, immediately before the verdict commits:
violation ⇒ `Unknown` (model dropped), never `Sat`.

**Placement is load-bearing**: the check runs AFTER the refinement chain
(int case split, arrangement splits, array axiom instantiation).  A
first version placed it in the early `_gate` block with
block-and-re-search, which starved the productive lemma paths of
candidates — wisas exploded past 400 s (256 blocking rounds learning
nothing) versus ~6 s `unsat` before.  After the chain, wisas is `unsat`
again and the gate costs nothing on trajectories that refute.

## Results

* **Pete family: uniformly `unsat`** — 5s, cxs-bp, cxs-bp-ex,
  cxs-bp-safety, cxs-bp-ex-inp-safety, 6stage-flush, **and 25s**, which
  had never been solved.  wisas xs_8_13: `unsat`.
* **Differential**: 0 wrong verdicts; one honest downgrade in 270 —
  `sorted_list_insert_noalloc1` `sat`→`unknown` (z3: sat).  The
  candidate model there cannot be certified (its function results
  conflict under congruence); a real model exists, so the downgrade is
  the honesty/completeness trade, not a soundness claim.
* Gates: 10 083 tests (incl. the new cxs-bp fixture regression, which
  pins `unsat` for the exact instance that flipped), clippy/fmt/doc,
  Z3 parity 168/168.

## Recorded follow-ups

1. **Model-builder congruence canonicalization** (would rescue honest
   downgrades like sorted_list): when completing the model, group each
   function's application results by their arguments' model values and
   force a single representative result — when a consistent choice
   exists the `sat` is restored, and the gate then fires only when no
   congruent interpretation is compatible with the pinned values (the
   genuinely unsat-shaped candidates).  Until then, the gate converts
   trajectory-luck false-SATs and some true-SATs alike into honest
   `unknown`s.
2. **The arrangement round's caps remain trajectory-shaped**; the gate
   makes their misses honest instead of wrong.  Lifting coverage (no
   caps, or value-class-partition enumeration) is optional once the
   gate exists — a miss costs completeness, not soundness.

## Disposition

Landed.  The false-SAT class this closes: *any* non-convex
combination-gap escape, regardless of which candidate the search
reached — the wisas wall-clock lesson and the cxs-bp trajectory lesson
both reduce to "a correct verdict that depends on trajectory luck is
not closed", and this gate removes the luck from the `Sat` exit.

## Erratum (2026-08-24): SUPERSEDED by the root-cause fix

The gate this study landed is REMOVED. The actual root cause — truncated pair enumeration in the arrangement round — was found afterwards (see `2026-08-arrangement-chain-root-cause.md`) and fixed with a complete spanning-chain Phase 2; with the fix, the pete family is `unsat` and no exit gate is needed. The gate hid the bug (converting the wrong `sat` into an honest `unknown` and greening the suite) and duplicated certified mode's verification.
