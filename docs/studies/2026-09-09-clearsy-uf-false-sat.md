# CLEARSY UF false-`sat` on negated existentials over uninterpreted sorts

**Status: FIXED (2026-09-09, `fix(mbqi): make finite-exhaustion Satisfied
prove real domain coverage`).**  The issue was pre-existing (not introduced
by the 2026-09 quantifier-ownership work — the pre-fix binary answered the
same wrong `sat` via the free-Boolean hole rather than via model approval).

**Resolution summary:** the file refutes through E-matching depth nixie does
not yet have, so it now answers the honest `unknown`.  The false `sat` came
from the finite-exhaustion `Satisfied` path trusting model-derived coverage
arithmetic (an 8-value truncated universe) while the actual enumeration was
a pool-replaced, 10-entry truncated sample over a model with 2270 distinct
`U` values.  Working hypothesis 1 below was closest: the coverage claim and
the enumeration were computed from different sources.  See
`mbqi_exhaustion_soundness.rs` for the pinned regressions (including a
constants-only shape that reaches genuine `unsat` post-fix).

## Reproducer

```
smt-lib/non-incremental/UF/20190906-CLEARSY/0016/00779.smt2   (:status unsat)
```

- 2531 declarations/axioms of the B set-theory encoding over one
  uninterpreted sort `U` (`mem`, `*i`, `idiv`, ...), goal
  `(not (exists ((l U) (r U)) (and (mem l g) (mem r g) ...)))`.
- z3 4.16.0: `unsat`. Nixie (2026-09, both pre- and post-ownership-fix):
  `sat`.
- The minimized shape (one sort, one `mem` fact, same negated exists)
  **works**: `unsat` on both engines – the wrong `sat` needs the full theory
  present.

## What it is not

- Not the boundary-quantifier free-Boolean hole: after the ownership fix the
  negated existential is rewritten to `∀l r. ¬(…)` and *registered*; the
  wrong `sat` is now produced by the quantifier engines approving a candidate
  model (which `Satisfied` exit exactly – C/D/sat_certify – was not traced
  before the session ended).
- Not the big-`IntConst` abstraction: no wide constants in this file.

## Working hypotheses (for the next session)

1. `sat_certify`'s Ge–de-Moura complete-instantiation path may be declaring
   saturation over an uninterpreted-sort universe it did not actually cover
   (universe completion choosing a degenerate/too-small universe for `U`,
   making `∀l r. ¬(mem l g ∧ …)` vacuously or trivially true).
2. Model completion pins `mem` incompletely on the candidate universe, so
   the counterexample search finds no witness and `Satisfied` fires without
   the finite-exhaustion precondition really holding for `U`.
3. E-matching simply never derives the nonemptiness chain (completeness
   gap) *and* the model check that should have caught the bogus candidate is
   the actual soundness bug – i.e. the answer should have been `unknown`.

## Where to look

- `nixie-solver/src/mbqi/sat_certify.rs` (`collect_fragment_instances`:
  saturation over uninterpreted sorts),
- `nixie-solver/src/mbqi/model_completion.rs` (universe choice for `U`),
- the `MBQIResult::Satisfied` exits in `nixie-solver/src/solver/mod.rs`
  (exit C/D gates exist for *unowned* quantifiers; this goal's quantifier
  is owned, so no gate applies – the engines' own model check must be
  sound here).

## Screening context (2026-09-09, 20 s, z3 4.16.0)

Classic SMT-LIB families, stratified 965-file sample: `WRONG` 1 (this file),
`agree` 186, `gap_z3_only` 463, `both_unknown` 262. The gap is dominated by
UFLIA (163/244 z3-only) and LIA (108/112) — E-matching throughput and
nonlinear-in-LIA contract strictness, both recorded as follow-ups in
`docs/quantifier_handling.md`.
