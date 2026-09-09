# Structural concat/extract rewriting for QF_BV — screened out (unsound by interaction, zero measured payoff)

**Date:** 2026-09-10. **Task:** Tier A item 2 of
`docs/handovers/2026-09-10-qf-bv-gap-tier-a.md` (structural rewriting for
`bitrev1024`, `sage/app7/bench_4443`, `calypto/problem_14|19`,
`2017-BuchwaldFried`, `brummayerbiere3/maxandminor016`).

**Verdict: not landed.** The port of Z3 `bv_rewriter`'s structural rules was
implemented and measured end-to-end. It closed **zero** of the seven target
files, produced a **false `unsat`** on the `RWS` family (11 corpus files) via
an interaction whose root cause was not isolated within budget, and a
matched-null A/B over the 509-file corpus showed **no cell differences at
all** (268 = 268 with `NIXIE_BV_STRUCT_RW` on/off). A win-less rewrite family
that is unsound anywhere does not ship; the code was reverted (nothing
landed).

## What was implemented (all reverted)

Z3 `src/ast/rewriter/bv_rewriter.cpp` rules, in `BvPreprocessor`, behind
`NIXIE_BV_STRUCT_RW` (default on during the experiment):

- const-amount `bvshl`/`bvlshr` → concat/extract wiring (`mk_bv_shl`/
  `mk_bv_lshr`), `bvashr`-of-`bvashr` merge;
- extract-of-extract composition, extract-of-concat split (`mk_extract`);
- adjacent-extract concat fusion (`mk_concat`);
- `bvnot` through concat (`mk_bv_not`);
- constant-mask AND/OR run decomposition (`mk_bv_or`'s "OR is a mask",
  mirrored for AND — Z3 routes AND through NOT/OR first);
- the disjoint-concat OR merge (`mk_bv_or`'s `is_zero_bit` walk) with flat
  per-side bit tables;
- a recursive normalizer for freshly built nodes (the memoized DAG walk only
  revisits *original* nodes; merge-built pieces need their own pass).

## Findings

1. **The bitrev mechanism works but does not terminate in budget.** With the
   rules live, `bitrev0064` reassembles `rev(rev(x)) = x` syntactically and
   refutes in 0.06 s — but `bitrev0128` still needs 2–3 s, `bitrev0256`
   14–16 s, `bitrev0512/1024` time out: the binary-concat seam splits and
   the 1-bit mask runs of the alternating masks leave ~1024-piece spines
   whose repeated re-splitting is super-linear. Full closure needs **n-ary
   concat spines** (z3's `mk_extract` picks covered pieces in O(pieces),
   not by recursive binary seam-splitting) and an extract-range interval
   representation. The other six targets (bench_4443, calypto,
   BuchwaldFried, maxandminor016) did not close at all: z3's wins there
   come from further pipeline stages (`propagate-values`, its own
   `solve-eqs` with 34 eliminations on BuchwaldFried, AIG-level
   simplification after blasting), not from these rules alone.
2. **Two soundness-grade bugs found in my own implementation before any
   landed:** the disjoint-concat bit table filled `[0, high)` for constant
   pieces (a high piece's zeros overwrote the low pieces' unknown bits —
   every merge bailed at the first seam) and then pushed `high - wl` as the
   high operand's top (off by the low width). Both fixed in the experiment;
   both are exactly the class of bug the brute-force equivalence test
   (`struct_rules_are_equivalence_preserving`, random-value
   substitute-and-fold at widths 9/12/63) exists to catch.
3. **The residual false `unsat` was NOT in the rules.** After the fixes,
   per-rule and full-pipeline random-value equivalence tests pass, but
   `RWS/Example_1.txt.smt2` (reduced deterministically to a 49-assert
   prefix, z3: `sat`) still answered `unsat` with the family on and `sat`
   with it off, via only six `bvlshr`-by-1/2/3 rewrites firing at width
   126. The rewriter is term-level sound, so the defect is an
   **interaction** — most plausibly the bit-blaster's encoding of the
   rewritten concat/extract shapes (a 125-bit extract of a 126-bit operand
   under `bvand` chains), or a rule interaction the width-≤63 random tests
   miss. Not root-caused within budget; recorded here as the blocking
   follow-up if this family is revived.
4. **Matched-null A/B (the decisive measurement):** same binary,
   `NIXIE_BV_STRUCT_RW=1` vs `=0`, 509-file re-screen, 4 pinned cores,
   25 s cap — **268 vs 268 solved, zero per-file verdict differences**.
   The family changed nothing measurable on the corpus while it was
   default-on, so even without the soundness issue there was nothing to
   keep.

## What NOT to retry unchanged

- Binary concat spines with per-node seam splits for wide alternating
  masks — the piece-count blowup is structural, not an implementation
  accident.
- Landing any rewrite family without the brute-force equivalence net in
  the same change; two of three bugs here were caught only by it.
- Trusting "z3's simplifier solves it" as evidence these rules suffice:
  the per-tactic trace (`z3 -v:10`) shows which stage actually decides each
  target; only `bitrev*`/`bench_4443` fall to the simplifier itself, and
  `bench_4443` needs more of it than these rules.

## Revival path (if Tier A item 2 is picked up again)

1. Root-cause the width-126 `bvand`/`lshr`-chain false unsat first (the
   reduced 49-assert prefix and the six fired rewrites are the entry
   point; the blaster's concat/extract encoders are the prime suspect).
2. Move to n-ary concat piece lists (Vec<(TermId, width)>) with interval
   arithmetic for extract/split/fuse — the binary-spine overhead is what
   kills bitrev0512+.
3. Re-run the matched-null A/B; only land on a strictly positive cell
   delta with zero regressions and the equivalence tests green.
