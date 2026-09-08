# Dispatch unification: pure QF_BV routes through the unified core (stage 4)

**Date:** 2026-09-07 (stage 4, the campaign's last open row)
**Stage 3:** `docs/studies/2026-09-07-bv-order-dispatch.md` (baseline
`precompile/76f26e5`).

**Verdict: flipped on.**  Flip condition 1 – "QF_BV corpus sample: geomean
≥ 1.15×, zero verdict mismatches, parity 100 %" – measured and met:
**geomean 1.36×** over the committed 300-file sample (dispatch-default vs
same-binary `NIXIE_BV_DISPATCH_UNIFIED=0` control, 127 pairs > 20 ms),
**zero verdict mismatches** against the previous default across all 300
files, net +5/−3 timeouts at 35 s, Z3 parity 169/169 decisive.

## What landed

- **Routing** (`bv_dispatch_unified`, default on, `=0` restores the
  dispatch): `goal_is_pure_bv` declines pure goals without wide
  multipliers, the unified window opens for the all-blastable fragment,
  and the general path's link pass owns the goal end-to-end (order
  encoding for big `distinct` included).  Ring-dominated goals keep their
  existing general-lazy routing; wide-`bvmul` (≥ 32 bits) goals keep the
  dispatch for its CEGAR machinery.
- **Preprocessing parity**: the dispatch's equivalence-preserving
  preprocessor (solve-eqs, SOM/poly-identity rewriting) runs at `check`
  entry and its rewrite is asserted *alongside* the originals – implied
  units, sound both ways (the wienand distributivity family folded to
  `false` and refuted on the spot; it had timed out without the pass).
  Gated off when **ring elimination** fired: that pass is only
  *equisatisfiable*, not implication-preserving, and asserting a
  non-implied rewrite refutes satisfiable goals.
- **Bool-selector linking**: `ite` selectors that are bare Bool variables
  get their circuit var tied to the leaf's main-core var (the unified
  analogue of the lazy path's `assert_bool_value` echo; read-only lookup,
  so pure-propositional goals never mint vars).

## Two soundness bugs found and fixed on the way

1. **Pre-existing false `sat` in the ring-elimination preprocessor**
   (whole `30c049c` lineage, exposed by this routing answering the same
   files correctly): solving `3n + 3n² = 3` for `n` produced the
   self-referential `n = 3⁻¹(3 − 3n²)` and *dropped* the equation,
   discarding the constraint that ties `n` to `n²`.  The parity
   obstruction family (`3n(n+1)+1 = y ∧ y = 4`, unsatisfiable because
   `n(n+1)` is always even) answered `sat` with a model violating its own
   assertions.  Fixed: the eliminated variable must occur in **no other
   monomial** of its equation (linearity); the regression test that had
   enshrined the bug (`ring_solve_eqs_model_reconstruction`) is rewritten
   around the satisfiable twin `y = 1`, and
   `ring_elimination_respects_nonlinear_occurrences` pins the obstruction.
2. **Unified-path ite-selector float** (stage 1 latent): a bare-Bool
   selector's circuit var was never tied to the main core, so
   `(ite c #x01 #x02) = x ∧ ¬c ∧ x = #x01` read `sat`.  Fixed by the
   selector linking above.

## Cells (release; stage-3 binary vs this build's default)

| cell | stage 3 | unified default |
|---|---|---|
| pure sat n=300 w=16 | 3.0 s | **0.92 s** |
| pure sat n=2000 w=16 | 23.8 s | **11.8 s** |
| pure sat n=600 w=10 (dense) | 1.85 s | 3.1 s |
| pure unsat n=2000 w=16 | 1.45 s | 17.8 s |
| mixed cells (stage-1/2 tables) | — | unchanged |

The dense-cell and explicit-unsat regressions are the known costs of the
routing (embedded dispatch handled those shapes better); the corpus A/B
shows the aggregate is decisively positive, and `NIXIE_BV_DISPATCH_UNIFIED=0`
restores the previous architecture per file or session.

## Verification

Workspace **10644/10644**; clippy/fmt/doc clean (plus a drive-by fix of a
pre-existing broken intra-doc link on main, `find_interned` → private
`intern`); Z3 parity 169/169 decisive; 300-file corpus 0 mismatches vs the
previous default, +5/−3 timeouts at 35 s; the whole prior campaign battery
(order/differential/guards) green under the new default.
