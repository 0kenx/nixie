# Real→FP conversions: exact single-rounding (`((_ to_fp eb sb) RM real)`)

**Date:** 2026-09-08 (late) · **Follow-up of:** `docs/studies/2026-09-08-fp-const-folding.md`
(rung: "`(_ to_fp e s)` real-conversion folding") · **Found by:** directed probe ·
**Status:** soundness FIXED; conversion parsing was already correct, the rounding was not.

## What the probe found

The applied-indexed parsing (`((_ to_fp 11 53) RNE x)`) already worked — the
earlier session note had probed a nonstandard spelling without the rounding
mode.  The real gap was the conversion's **rounding**:

```smt2
(declare-const x Float64)
(assert (= x ((_ to_fp 11 53) RTZ (+ 1.0 (/ 1.0 4503599627370496.0) (/ 1.0 9007199254740992.0)))))
(assert (= x (fp #b0 #b01111111111 #x0000000000002)))   ; the RNE double-rounded value
(check-sat)   ; z3: unsat   nixie: sat   ← FALSE SAT
```

The concrete model builder evaluated the real expression as an **`f64`
first** — itself an RNE rounding — and then "rounded" the already-rounded
value, which makes every directed mode a no-op: `RTZ` of `1 + 2^-52 + 2^-53`
pinned the RNE value `1 + 2·2^-52` instead of the true truncation
`1 + 2^-52`, and the wrong datum *verified*.

## The fix (three pieces)

1. **Exact rational evaluation** (`fp_fold::eval_rational`): an iterative,
   memoized post-order evaluator over `IntConst`/`RealConst` and the exact
   arithmetic connectives (`+`, `-`, `*`, unary `-`, `/` with a nonzero
   divisor), on `BigRational` — no `f64` anywhere.  Anything outside the
   fragment returns `None` and every caller degrades honestly.
2. **First-principles grid rounding** (`fp_fold::rational_to_fp`): the
   `BigInt` analogue of the fpboundary oracle — `floor(log2(n/d))` by bit
   lengths, the normal/subnormal grid unit, exact `divmod` for the cell and
   remainder, the halfway comparison `2·rem vs den`, per-mode `round_away`,
   carry into the smallest normal, and per-mode overflow saturation
   (`RTZ`/inward-directed → max finite, else ±inf).  General `(eb, sb)`.
   (The unit test pins an assembly bug found on the way: the final overflow
   check compared the *biased field* against the *unbiased* maximum,
   turning every value with exponent ≥ 1 into +inf — `2.0` converted to
   infinity.)
3. **Model-builder + fold integration**: the `RealToFp` arm of the concrete
   model builder now pins through (1)+(2) — a non-representable real
   outside the rational fragment declines (`None`), never double-rounds.
   The fold pass gained a `FromReal` shape: literal operands fold with a
   **unit** clause; compound operands fold under the guard atom
   `(operand = value-literal)` **only when arithmetically clean** — a guard
   mentioning `div`/`mod`/numeric-`ite` is deliberately axiom-less in real
   mode (see `instantiate_arith_axioms`), and minting one trips
   `arith_defs_incomplete` and downgrades the whole verdict; the fold pass
   also moved *before* the arith-axiom instantiation so its guards'
   sub-terms are axiom-eligible in the same check.

## Scope after the fix

| shape | verdict |
|---|---|
| sat side, any representable/non-representable rational (dyadic, 1/3-style, integers, `(+ …)` sums) | decided by the exact model builder (`sat`) |
| unsat side, literal or arith-clean operand | refuted by the fold's unit/guard clause (`unsat`) |
| unsat side, `div`-bearing operand (e.g. `(/ 3.0 2.0)`-defined `x` vs a wrong datum) | honest `unknown` — no valid guard atom exists; never a wrong answer |

## Validation

* Directed probes: the false-`sat` battery (`RTZ/RTP/RTN` × dyadic halfway
  sums, both polarities), integer magnitudes `2`, `89524`, `2^53−1`,
  `1/3` under RNE — all z3-consistent.
* Differential (`convgen`, 3 seeds × ~160 cases: random dyadics and
  random rationals under all five modes, bare + exact-datum probes):
  **zero semantic mismatches, zero unknowns**; the only disagreements are a
  *pre-existing parser limit* — decimal literals with >i64 integer parts
  fail to parse (an honest error, surfaced by the generator; scoped below).
* Standing family: fpboundary medium **168/168**, full medium sweep
  **170/170**, small+stress-heavy **152/152** — zero bad/unknown/timeout.
* Gates: nextest workspace `--all-features` **10717/10717**; clippy/fmt/doc
  `-D warnings` clean; z3 parity **170 entries / 0 wrong** (record
  unchanged).  New tests: `real_to_fp_directed_mode_is_a_single_exact_rounding`
  (the false-`sat` fix, both polarities), `real_to_fp_dyadic_conversion_decides`,
  `real_to_fp_integer_values_are_exact`, `real_to_fp_one_third_rounds_correctly`,
  and the `rational_to_fp` unit pins.

## Scoped follow-ups

1. **Decimal literals beyond i64** (the generator's ERR class): the
   decimal parser's integer part is an i64 path; `309485009821345068724781056.0`
   is a parse error.  A `BigInt` decimal path (parser hardening).
2. **Int-literal coercion in Real position** (`((_ to_fp e s) RNE 3)` with
   an Int literal): z3 coerces; nixie's parser errors.  Same hardening.
3. `SBVToFp`/`UBVToFp` exactness (BV→rational→grid) — same recipe, not yet
   probed.
