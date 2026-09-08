# FP operation congruence: operand merges propagate through `fp.*`

**Date:** 2026-09-09 · **Follow-up of:** the FP constant-semantics arc
(`254ff45`…`fab65f8`) · **Status:** landed.

## The gap

FP operations were opaque EUF leaves: `(= a b)` did NOT derive
`(= (fp.abs a) (fp.abs b))` — z3 refutes those goals (its `fpa` theory
keeps the operator table in the e-graph); nixie could only decline.

## What landed

1. **`intern_operands` learned the fp operations**: every fp arithmetic
   operation interns as a congruence application whose function symbol
   encodes `(op, rounding mode)` (`FP_FUNC_BASE + op·5 + rm_slot` — the
   mode is part of the symbol, so `fp.add RNE` and `fp.add RTZ` never
   merge).  Operand-class merges now propagate through every operation,
   exactly like uninterpreted `f`.
2. **Honesty-gate refinement**: the FP gate now exempts only the atoms
   the EUF layer owns — the arithmetic operations (congruence + value
   marks decide their equalities).  Predicates and every CONVERSION in
   either direction stay gated: conversions are *not* congruence
   applications, and un-gating them re-opens the free-atom false-`sat`
   the d-series regression pins (caught live by the landed tests when the
   first version of this refinement over-exempted).
3. **Same-class strict-comparison refutation**: `fp.lt x x` and
   `fp.gt x x` are FALSE for every `x` (NaN included).  FP predicates are
   now recorded as `Constraint::BoolApp`, and a positive assignment whose
   operand terms intern into the same e-class conflicts immediately, with
   `explain_eq`'s merge justification as the clause core.  The fall-through
   extends to shapes carrying such candidates (`fp.lt`/`fp.gt` over
   syntactically different terms) — `leq`/`geq` are NOT candidates
   (the NaN exception makes same-class non-refutable).

## Measured

| shape | before | after | z3 |
|---|---|---|---|
| `(= a b) ∧ ¬(= (fp.abs a) (fp.abs b))` | unknown | **unsat** | unsat |
| `(= a b) ∧ ¬(= (fp.add RNE a a) (fp.add RNE b b))` | unknown | **unsat** | unsat |
| `(= a b) ∧ (fp.lt (fp.abs a) (fp.abs b))` | unknown | **unsat** | unsat |
| `(= a b) ∧ (distinct (fp.mul RNA a a) (fp.mul RNA b b))` | unknown | **unsat** | **timeout** (nixie decides it, z3 does not) |
| `(= a b) ∧ ¬(= (fp.add RNE a a) (fp.add RTZ a a))` | sat | sat | sat (mode separation) |

Corpus cost check: the QF_FP screen corpus stays instant-`unknown`
(15–19 ms — its `leq/geq` chains are not fall-through candidates).

## Gates

nextest workspace `--all-features` **10749/10749** (three new regression
tests: congruence through unary/binary ops and `distinct`, strict
comparisons over congruent operands, mode separation); clippy/fmt/doc
clean; z3 parity **170/0**; obligation fuzzer medium **170/170** +
stress **152/152**; the real→fp and fp→bv regression batteries re-run
clean on this build.
