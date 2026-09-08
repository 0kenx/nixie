# Exact FP → bit-vector conversions (`((_ fp.to_sbv m) RM x)` / `fp.to_ubv`)

**Date:** 2026-09-09 · **Follow-up of:**
`docs/studies/2026-09-08-parser-hardening-bv-to-fp.md` (scoped rung 1) ·
**Status:** landed.

## Semantics (z3-probed, then implemented)

* The pinned operand's exact value rounds to the **integer grid** under the
  mode (one rounding step — the same first-principles grid logic as
  `rational_to_fp`, on `BigInt`), then encodes at the target width
  (two's-complement for `fp.to_sbv`).
* **Underspecification is exactly "the rounded value does not fit the
  width"** — z3 rounds FIRST (`to_ubv` of −0.5 under RNE is the *defined*
  `bv0`); only an out-of-range rounded value leaves the result free (z3:
  any probe satisfiable — verified for 0/42/128/255 at width 8).
* NaN and ±∞ decline (underspecified/huge — no fabricated value).

A sign bug on the way (unit-pinned by the probes): `fp_value_rational`
initially dropped the sign bit, computing `RTN(−3.7) → 3`.

## Implementation

1. **Fold shape `ToBv`** (`fp_fold.rs`): the operand resolves through the
   existing FP pin machinery (literal / class witness / define chain /
   in-pass pins); in-range values emit the guarded unit
   `(operand-pin guards) → (conv = bitvec-literal)`; out-of-range, NaN and
   ∞ **decline**, leaving the conversion's atom free — which is precisely
   the underspecified semantics.  The helper `fp_value_rounded_to_integer`
   (exact `FpValue → BigInt` per mode) is shared with the model builder.
2. **Model builder**: `eval_bv` evaluates `BitVecConst` and
   `fp.to_sbv/ubv` over pinned operands exactly, and the `Eq` fallback
   consults it for BV-sorted equalities (needed by the FP-fold
   fall-through's verification); `eq_satisfiable_via_underspecified_conv`
   lets an underspecified conversion equated with a constant verify as
   **sat** — the free value is chosen, never fabricated.

## Validation

* Differential (`tbvgen`, 4 seeds × 140: widths 8/16/32, both
  conversions, all five modes, exact dyadic values, in-range
  right/wrong-datum probes and underspecified any-probe):
  **1120/1120 agree, zero unknowns** — even the underspecified cases
  decide `sat` through the wildcard verification.
* Directed probes r1–r8 (rounding, two's complement, overflow wildcards):
  all z3-consistent.
* Standing surfaces: fpboundary + full sweep **170/170**, stress
  **152/152**; z3 parity **170/0**; nextest workspace **10731/10731**;
  clippy/fmt/doc clean.  Tests: both-polarities rounding, negative
  two's-complement, overflow-free-not-fabricated.

## Probe-construction notes (recorded for future batteries)

* SMT-LIB numerals have **no scientific notation** — `1.5e3` is rejected
  by z3 itself (an error followed by a vacuous `sat`); spell dyadics as
  exact plain decimals (`format(Decimal(f), 'f')`).
* `to_ubv` of a negative input is NOT automatically underspecified — only
  the rounded value's fit matters (a battery bug this cycle caught twice).

## Scoped follow-ups

1. Real QF_FP corpus ingestion (all conversion directions now exact).
2. `fp.to_real` / `fp.to_ubv`-style chains through variables (the fold
   handles pinned operands; unpinned free FP variables stay with the
   witness synthesis).
