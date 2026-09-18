# The rehome wide-rational blowup: the ±1-divisor folds exonerated, the exact-rational simplex convicted (by profile)

**Date:** 2026-09-18
**Trigger:** `rehome_does_not_fabricate_a_crossing_on_a_referenced_slack`
went from 7.5 s to >180 s (nextest kill) on main after the ±1-divisor
identity folds (`458a3ba5`, arrived via the `cd0430a5` merge; the
"docs(study)" commit `51adf259` first carried them in a suite run).

## Verdict: the folds are innocent; they unmasked a pre-existing pathology

The folds (`div(t, 1) → t`, `div(t, -1) → -t`, `mod(t, ±1) → 0`) are
correct and only *remove* structure. The instance contains two
`mod(·, 1)` terms; applying the same simplification **by hand** to the
instance and running it on the **pre-fold binary** (`740c16bd`) is
equally slow:

| run | binary | time | verdict |
|---|---|---|---|
| original instance | pre-fold `740c16bd` | **7 s** | sat |
| original instance | current main (folds) | **564 s** | sat |
| hand-folded instance | pre-fold `740c16bd` | **691 s** | sat |

The folded *shape* is the slow thing; the fold just produces it. CDCL
trajectory reshuffle made fast-then-slow, not wrong-then-right — the
verdict stays `sat` (model `xi = 658812288346769706`) throughout.

## Where the time goes (perf, release + symbols)

> 31.0% `<BigUint as Integer>::gcd`
> 15.0% `biguint_shr2`
> 9.1% `div_rem_cow`
> 5.9% `BigInt::div`
> 5.1% `num_rational::Ratio::reduce`
> 4.3% `Ratio::mul`
> 3.7% `Simplex::eval_big_raw`
> 3.0% `Simplex::update_assignment`
> 2.5% `Simplex::propagate_bounds_in`
> 2.0% `Ratio::cmp`
> 2.0% `Simplex::derive_var_bound_big_parts`

Over 60% of the runtime is bignum GCD/shift/division under exact
`Ratio` arithmetic in the wide-literal simplex rows. The instance's
div/mod axioms carry denominators 3, 4, 5, 7, 10; every pivot compounds
them and every `Ratio` operation pays a full bignum GCD reduction, on
numerators seeded by ±2³¹ and −2⁶² literals. Classic exact-rational
simplex blowup — the standard cures are fraction-free (integer-preserving)
tableaus or delayed normalization; **naive deferral is unsound here**
because `Ratio`'s canonical form is load-bearing for its `Ord` (the
solver compares bounds through it).

## The delta-debugged minimal shape

`docs/studies/assets/2026-09-18-rehome-wide-rational-blowup-*.smt2`
(original, hand-folded, minimal). The minimal core — still >100 s on
both binaries:

```scheme
(set-logic QF_LIRA)
(declare-const xi Int)
(assert (and
  (not (or (= (mod (* 1 xi) 4) (div (- (+ 60 (* 2 xi) 20) 3) 3))
           (not (and (>= (+ (+ (* 2 xi) (* -1 xi) 62)
                            (+ -2147483648 -4611686018427387904))
                         (mod (* 10 xi) 7))))))
  (not (or (< (* 10 xi) (div (* 3 xi) 7))))))
(check-sat)
```

(unsat; the shrinker's verdict drifted from the original's sat — the
slowness survives the verdict change, so both files are kept.)

## What landed

- The big test is `#[ignore]`d out of the default suite with the
  explicit-run recipe (the `pete_cxs_bp` precedent), a 25×60 s nextest
  override for that explicit run, and the un-ignore condition named
  (fraction-free tableaus / delayed normalization — the item-76 design).
  **The defect it guards stays covered in the default suite** by the
  two-disjunct core (`rehome_false_unsat_seed_20261102_core_decides_sat`,
  34 s), which pins the same item-69 fabricated-singleton false refutation.

## For the arith owner

This is your item-76 machinery: `eval_big_raw` / `derive_var_bound_big_parts`
/ `update_assignment` are the hot frames under the `Ratio` churn. The
profile above is the whole story — denominators compound per pivot, GCD
per operation. If the bound-shadowing fix design includes a
normalization policy, this reproducer pair (original vs folded, same
verdict, 80× apart) is the regression to measure it against.
