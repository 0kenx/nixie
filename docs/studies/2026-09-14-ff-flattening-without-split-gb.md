# Definitional flattening of `ff.mul` operands without split-GB: a negative result

**Date:** 2026-09-14
**Verdict:** do not ship. The technique cvc5 pairs with split-GB does not
stand alone here: it trades mid-size wins for larger-goal regressions, and
the root cause is structural (re-expansion through pivot substitution and
S-pairs), not tunable. Split-GB (Phase 7) is the prerequisite.

## What was tried

Motivated by the remaining `bench/ff` refusals (all Gröbner-cascade
budgets) and the design's own domain note — circuit constraint systems
are "overwhelmingly linear-plus-a-thin-layer-of-rank-1-quadratics"
(`docs/FF_THEORY_DESIGN.md` §0) — the encoder was changed to flatten
every multi-term `ff.mul` operand into a fresh definition variable:

- `(ff.mul (ff.add a b c) (ff.add d e f)) − k` encodes as the binomial
  `t·u − k` plus two linear definitions `t − (a+b+c)`, `u − (d+e+f)`,
  instead of the expanded 9-term quadratic;
- definitions were appended as linear generators (deterministic mint
  order, so certificate replay reproduces them), each carrying the
  origin of the literal whose encoding minted it;
- the linear core treated definition variables as **opaque** to the
  nonlinear part (substituting `t = A` back into `t·u − k` re-expands
  the product the flattening exists to avoid).

Ideal-preserving by construction (a definition extends the ideal by a
graph isomorphism on its variety), so soundness was never in play — the
oracles passed throughout. The question was capacity.

## Measurements (bench/ff, debug build, before → after)

| goal | before | with flattening |
|---|---|---|
| bn254 sparse planted 16×24 | honest `unknown`, ~11 s | **sat, 0.4 s** |
| bn254 sparse planted 32×48 | honest `unknown`, ~14 s | **sat, 1.0 s** |
| bn254 sparse planted 64×96 | sat, ~7.5 s | `unknown`, 27 s |
| goldilocks sparse planted 64×96 | sat, ~1.6 s | `unknown`, 93 s |
| bn254 planted (dense) 8×14 | sat, ≤0.1 s | `unknown`, 15 s |
| bn254 sparse planted 128×192 | `unknown`, ~18 s | no verdict in 120 s |

The generator count after the front end *grows* (dense 8×14: 14 → 32;
sparse 64×96: → 222, one connected component), and the Gröbner cascade
explodes on the inflated system.

## Root cause (why no threshold fixes this)

The definitions cannot stay opaque, at two layers:

1. **Pivot substitution.** RREF pivots on the *smallest* variable of a
   row; a definition `t − w₁ − w₂` leads with `w₁`, so its pivot row
   expresses `w₁` *in terms of* `t`. Substituting that pivot into any
   binomial mentioning `w₁` re-expands the product. Marking only the
   `t`-pivots opaque does not help — the re-expansion rides in on the
   `w`-pivots.
2. **S-pairs.** Even with substitution disabled, Buchberger's S-pair of
   a definition row and a binomial reconstructs the expansion inside
   the cascade (`S(t−w₁−w₂, t·u−k) = u·w₁ + u·w₂ − k`).

Making the definitions effective therefore requires keeping them out of
the cascade entirely — which is exactly the split-GB architecture:
separate bases over variable clusters, exchanging only the consequences
each admits. cvc5's `split_gb.cpp` exists for this reason; the design
lists it as Phase 7 with a pre-registered experiment, and this study is
that experiment's motivation section.

## What was kept

The provenance fix is independent and correct: bitsum definition
generators now record the literal whose encoding minted them (previously
an empty origin set), so a core that leans on a bitsum definition names
the fact that required it. Committed alongside this note.

## What not to retry

- Flattening with per-product term-count thresholds: the re-expansion is
  structural; the corpus's 2×3-operand products (6-term expansions) both
  help when flattened (16×24) and hurt (64×96) — no local rule separates
  them.
- Flattening plus "substitute only constant-valued pivots": defensible,
  but it neuters the linear core's propagation and leaves the S-pair
  re-expansion untouched.
