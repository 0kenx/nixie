# Parser hardening + exact bit-vector→FP conversions

**Date:** 2026-09-08 (night) · **Follow-ups of:**
`docs/studies/2026-09-08-real-to-fp-exact-rounding.md` · **Status:** landed.

## The four gaps (each probe-first, z3-verified)

1. **`(_ bvN W)` indexed bit-vector literals** — the standard spelling for
   wide BV constants — did not parse.  `build_indexed_op` now recognizes
   `bv<digits>` names: exactly one index (the width), the value must fit it,
   zero application arguments; built through `mk_bitvec` (the term graph's
   BV constants are already arbitrary-precision).
2. **`Int` literals in conversion position** (`((_ to_fp 11 53) RNE 3)`):
   SMT-LIB `Int` is a subset of `Real`; the dispatch now accepts Int-sorted
   operands with the real-conversion semantics (the exact-rational path
   evaluates `IntConst` operands directly).  Was a parse error; z3 coerces.
3. **Decimal widening**: the decimal parser's raw numerator (digits × 10^k)
   went through `i64` checked arithmetic, rejecting literals whose *reduced*
   rational fit.  The path is now exact `BigInt` with a gcd reduction — a
   decimal parses whenever its reduced numerator/denominator fit `i64`
   (the term language's `RealConst(Rational64)` contract), and a genuinely
   unrepresentable one refuses with a constructive message ("spell it as a
   division of integer literals").  Note the class this widens is exactly
   *long fractions of small values* (`0.5000…0` with ≥ 20 fraction digits):
   an integer-part overflow implies the value itself exceeds the literal
   range, no matter the reduction.
4. **Exact `SBVToFp`/`UBVToFp`**: the conversions had **no evaluation
   anywhere** (model builder: no arm; fold: no shape) — every instance was
   an honest `unknown`.  Both sides now evaluate exactly: the model builder
   decodes a `BitVecConst` operand (two's-complement for `SBV`) and rounds
   the exact integer through `rational_to_fp`; the fold emits the guarded
   unit `(operand = witness) → (conv = value-literal)` with the witness
   resolved from the operand itself (literal), its e-graph class (re-checks),
   or a definitional `(= v const)` conjunct of the assertions (the
   pre-propagation entry state).  A deduped-but-live lemma now also counts
   for the fall-through signal (the search must run whenever fold structure
   exists, not only when a *fresh* clause was added this check).

## Validation

* New differential (`bvgen`, 2 seeds × 130: widths 32/64/100/128, values at
  and below the top bit, both `to_fp`/`to_fp_unsigned`, all five modes, bare
  + zero-probe): **520/520 agree**, zero unknowns.
* Widened-decimal differential (`bigdec`, 120 cases of the exact class):
  **114/114 agree** (the 6 skipped cases construct digits that reduce to
  themselves within i64 — not the widened class).
* Conversion probes: `b2` (Int literal), `b4`/`b8` (BV conversions, both
  verdicts), `q1`/`q2`, variable-pinned `v2` — all z3-consistent.
* Standing surfaces: fpboundary + full medium sweep **170/170**, stress
  **152/152**; z3 parity **170/0** (record unchanged).
* Gates: nextest workspace `--all-features` **10728/10728**; clippy/fmt/doc
  `-D warnings` clean.  New tests: Int-literal coercion, indexed-BV-literal
  conversion (both polarities), variable-pinned BV witness, long-fraction
  decimals, and the refuse-not-garble pin for oversized decimals.

## Scoped follow-ups

1. `((_ fp.to_sbv m) RM x)` / `fp.to_ubv` evaluation (the reverse
   conversions) — same recipe.
2. The `FromBv`/`FromReal` guards could share one pin-resolution helper with
   the define pass (mechanical refactor).
3. Real QF_FP corpus ingestion (the original motivation): now unblocked at
   the parser level — worth a corpus differential run of its own.
