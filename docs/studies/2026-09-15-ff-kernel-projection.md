# Kernel projection for FF flattening: the second negative result

**Date:** 2026-09-15
**Verdict:** do not ship. The definitional-layer structural issue *is*
resolvable — this experiment proved it, producing exactly the clean
binomials predicted — but resolving it by projection trades the
re-expansion problem for two measured new ones: **dense image relations**
and **destruction of the component decomposition**. Split-GB remains the
architecture that gets both properties at once.

Follows `2026-09-14-ff-flattening-without-split-gb.md`, which diagnosed
the re-expansion; this study tested the resolution proposed in the
discussion that followed.

## The construction (as implemented, sound throughout)

1. **Flattening**: every `ff.mul` operand that is not a constant or a
   monomial in definition variables is named by a fresh `t`
   (`t − poly` joins the generator list). Each generator's affine part
   is collapsed into a definition variable as well, so *no nonlinear
   generator mentions a raw user variable*.
2. **Projection**: variables appearing only in linear generators — the
   user variables — are eliminated by restricted-pivot Gaussian
   elimination (pure linear algebra, no Gröbner work), producing:
   - `I_L`: the image relations — linear consequences over the
     surviving `t` variables (the graph ideal's intersection with
     t-space), and
   - one extraction row per eliminated variable (`w = −(Σ c·v + k)`,
     evaluated in reverse pivot order at model time).
3. The Gröbner cascade then runs on `binomials ∪ I_L` in t-space only.

Satisfiability is exactly preserved (proved by construction; the oracle
suites stayed green throughout — the exhaustive oracle additionally
caught a collapse bug (`monomials · t_ℓ` instead of `+ t_ℓ`) and an
extraction-ordering bug during development).

## What worked

- **The binomials came out clean.** The projected generators for the
  chain corpus are exactly `x_i·x_j − k` — the re-expansion failure mode
  of the first study is gone at the definitional layer, as predicted.
- One corpus goal improved: sparse 32×48 at BN254 went
  `unknown` → `sat` (0.4 s).

## What did not (measured, before → after)

| goal | before | with projection |
|---|---|---|
| bn254 sparse planted 32×48 | `unknown` (~14 s) | **`sat`, 0.4 s** |
| bn254 sparse planted 64×96 | `sat` (~7 s) | `unknown` (4 s) |
| bn254 sparse planted 16×24 | `unknown` (~11 s) | `unknown` (~15 s) |
| bn254 chain planted 16×24…256×384 | all `unknown` | all `unknown` (slower) |
| bn254 planted (dense) 8×14 | `sat` (0.1 s) | `unknown` (25 s) |
| goldilocks planted 8×14 | `sat` | `unknown` (10 s) |
| bn254 mutated 8×14 | `sat` | `unknown` (25 s) |

## Root causes (both were predicted as caveats; now measured)

1. **Dense image relations.** `I_L` is the left kernel of the definition
   matrix. Even for the *locality-structured* chain corpus (sliding
   3-variable windows), the kernel vectors are **dense** — banded
   structure with random entries does not make a sparse kernel. The
   dumped `I_L` rows carry 8–11 terms over far-apart `t` variables, and
   every Gröbner reduction through them re-inflates exactly the way the
   binomial naming was supposed to prevent. The term explosion didn't
   vanish; it moved from the products into the relations.
2. **Decomposition loss.** Components over the *unprojected* system
   exploit variable sharing among the raw constraints (sparse 64×96: 18
   components, sizes [205, 1, …]). The `I_L` rows span the whole
   t-space, collapsing everything into ONE component (159 generators).
   The per-component Gröbner scaling that carried the previously-`sat`
   goals is destroyed.

## Conclusion

The question this experiment set out to answer — *is the structural
issue resolvable?* — has a precise answer now: **yes at the definitional
layer, and the resolution is representable as clean binomials; but the
projected system concentrates the coupling into dense linear relations
and loses the decomposition, so the net effect on real-shaped goals is
negative.** The hardness of `V(binarials) ∩ L` is intrinsic to the
coupling, not to the representation.

What would get both properties — binomial cleanliness AND decomposition
— is maintaining separate bases over variable subsets *in the original
space*, exchanging only elements whose support fits another cluster:
split-GB. Both flattening studies now converge on the same
recommendation, and Phase 7's experiment is pre-registered twice over.

## What is kept

- The **chain corpus** (`bench/ff/bn254_chain_planted_*`): locality-
  structured R1CS goals that today answer honest `unknown` at every
  size — the cleanest capacity marker for the split-GB experiment (one
  component, so the current component decomposition cannot help them at
  all).
- This study.
