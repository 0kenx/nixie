# The BV multiplier-identity class closed: extract window arithmetic in the preprocessor

**Date:** 2026-09-20 (the BV identity session, handoff step 3).
**Input:** the standing table's QF_BV residual — the z3-decidable-at-**0-conflicts**
losses (`2017-BuchwaldFried/counterexample.dump.ia32_Mul_*`,
`Sage2/bench_16217`, `sage/app12/bench_2780`), attributed to "the wienand/SOM
preprocessor class, uncovered shapes".
**Landed:** four extract-normal-form rules in `bv_preprocess.rs`; the
BuchwaldFried residual collapses at the preprocessor with **zero SAT
conflicts**.  Seven unit pins.

## The mechanism (found by dumping the post-cascade residual)

`NIXIE_BV_DUMP_PRE` on the counterexample instance shows the preprocessor
had *already* reduced the whole 19 KB synthesis goal to **one assertion
over two variables** — two equalities that are pure ring identities:

1. `extract[31:0]( zext₆₄(a) · zext₆₄(b) )  =  a ·₃₂ b`  (the low half)
2. `extract[63:32]( zext₆₄(a) · zext₆₄(b) )  =  extract[63:32]( zext₉₆(a) · zext₉₆(b) )`
   (extension-width invariance of a shared window)

Neither folds with the existing SOM/cancellation machinery because the
products live at different zero-extension widths — they are equal as
*functions* but not as *terms*.  z3's qfbv preamble answers `unsat` with
`sat-mk-var 1`-scale work.

## The rules (all in the `BvExtract` arm, all term-identical rewrites)

1. **Full-width extract is the identity** — `extract[w-1:0](X) = X`.
   Completes the narrowing fixed point (below): a `lo = 0` window over an
   all-`(hi+1)`-wide product leaves the bare product.
2. **Extract-over-extract fusion** — `extract[hi:lo](extract[h₂:l₂](X)) =
   extract[hi+l₂ : lo+l₂](X)` (typing guarantees the window is in range).
   Kills the double-window pieces narrowing produces on piecewise-concat
   operands.
3. **Extract-over-concat pushback** (Z3 `bv_rewriter::mk_extract`): a
   window inside one concat arm reads the arm; a spanning window splits at
   the seam.  Folds `extract[w-1:0](zext x) = x` on the spot.
4. **Extract-window narrowing over products** — the multiplier-class rule:
   *product bits `[hi:lo]` depend only on operand bits `[hi:0]*
   (`(A·B) mod 2^N = (A mod 2^N)·(B mod 2^N) mod 2^N`, carries propagate
   upward).  Every factor of a `bvmul` under `extract[hi:lo]` is read at
   width `hi+1`: wider factors truncate (a fresh extract, so rules 1–3
   apply to it), narrower factors zero-extend, the product itself runs at
   `hi+1`.  Products become canonical **modulo the zero-extension width**,
   and the two BuchwaldFried identities collapse to syntactic equality
   with zero search.

Applied only to `bvmul` chains — deliberately conservative: the same
principle holds for `bvadd`, but rewriting every extract-over-add would
reshape the adder trees the bit-blaster builds (the `bvadd` arm's own
comment documents how sensitive those families are).

## Evidence

- `counterexample.dump.ia32_Mul_*`: timeout → **unsat, 0 conflicts, 311 ms**
  (deterministic preprocess fold — load-immune).
- `Sage2/bench_16217`: timeout → **unsat** (39 860 conflicts; ~1 s at
  normal load).
- `sage/app12/bench_2780`: timeout (25 s idle) → **sat** at ~4.4 s user
  (borderline under the table's 10 s wall cap under load).
- `sage/app7/bench_2014` remains parser-blocked (the 65 536-deep let-chain
  class — the nec-smt/deep-encoding family, not an identity issue).
- `asp/BlockedNQueens/*` is **not** in this class (332 `bvuge`, no
  `bvmul`): z3 spends 94 707 conflicts there; the gap is SAT-core
  capacity, not preprocessing.
- Full bar: 12 067 tests pass, clippy/fmt clean, parity **176/177, 0
  disagreements**, perf gate **PASS (1.013 ≤ 1.05)**.
- The standing-table snapshot taken during this session was
  **load-contaminated** (load average 26 from concurrent agents' builds —
  z3 itself dropped four cells) and was not committed; re-run
  `bench/smt_perf/run_perf.sh` at normal load to record the official
  post-landing table (expected: QF_BV +1..+3, QF_LIA unchanged).

## Soundness envelope

Every rule rewrites to a *semantically identical* term of the same width:
window arithmetic (`extract`/`concat` composition) and modular arithmetic
(the narrowing rule).  No rule decides a truth value it did not derive
structurally.  The seven unit pins cover each rule as an unsat identity
over free variables (all valuations), plus a satisfiability guard
(`narrowing_keeps_high_windows_decidable`: high windows of wide products
stay decidable — the rewrite must not overfold them to constants).
