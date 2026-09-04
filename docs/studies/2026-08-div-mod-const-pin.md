# div/mod constant args of quantified functions: the pin class one shape deeper (2026-08-24)

## Probe

The quantified-UF pin study recorded a residual: `div`/`mod` constant args
stay unpinned (opaque terms in the linear extractor).  Probing whether the
false-`sat` class actually fires there:

| input | nixie (before) | z3 |
|---|---|---|
| `y = 3 ∧ f(y) ≠ f(div 6 2)` | **sat** | unsat |
| `y = 3 ∧ f(y) ≠ f(mod 11 4)` | **sat** | unsat |
| `y = −4 ∧ g(y) ≠ g(div (− 7) 2)` | **sat** | unsat |
| `y = 2.5 ∧ f(y) ≠ f(/ 5.0 2.0)` (UFLRA) | **sat** | unsat |

Four live false-`sat`s — the class was open for every division shape.

## Fix

`pin_quantified_uf_const_arg` now evaluates in three layers:

1. **Int `div`/`mod` of closed constants** — Euclidean per SMT-LIB, the
   same semantics `arith_axioms` axiomatises (`m = q·n + r ∧ 0 ≤ r < |n|`).
   Rust's `rem_euclid`/`div_euclid` match it exactly; the quotient is
   computed as `(m − r).checked_div(n)` so `i64::MIN` folds are skipped,
   not wrapped.  Operands evaluate via `arith_axioms::int_constant`
   (now `pub(super)`) — the *same* checked evaluator the div/mod axioms
   use, so the pin and the axiomatisation can never disagree on a value.
2. **Linear extractor** (the existing layer) — literals, `Neg`, compounds.
3. **Real `div` of closed rational constants** — exact `Rational64`
   division.

**Zero divisor ⇒ no pin, in both Int and Real.**  `(div m 0)` is
*uninterpreted* per SMT-LIB (any value admissible); pining a value would
fabricate a semantics the logic does not define.  The control test pins
this: `y = 1 ∧ f(y) ≠ f(div 1 0)` must stay `sat` (z3: sat).

## Results (z3 parity, 7/7)

- div, mod, Euclidean-negative, Real-div cases: `unsat` ✓ (were false `sat`)
- controls (`mod 9 3` = 0 ≠ y; `div 7 2` = 3 ≠ −4; zero divisor): `sat` ✓

18 pr30 tests (4 new), full bar 10 090 tests, clippy/fmt/doc;
differential 0 wrong verdicts, solved 160 byte-identical (QF corpus: pins
empty); canaries unchanged; Z3 parity 168/168.

## Residuals

- `ite` constant args of quantified functions remain unpinned (the
  condition is genuinely not closed-form — the term is not a constant
  until the SAT core assigns the condition; a pin would have to be a
  *conditional* constraint, which is not a tautology).
- Out-of-`i64` magnitudes: skipped by `int_constant`'s checked folds
  (missed pairing only).
