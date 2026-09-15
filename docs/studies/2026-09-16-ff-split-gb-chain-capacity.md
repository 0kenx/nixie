# Split Gröbner bases for the FF chain corpus — the Phase-7 pre-registered experiment

**Date:** 2026-09-16
**Scope:** `docs/HANDOFF_FF_THEORY.md` open-work item 1 (Phase 7 capacity),
pre-registered twice over (by both flattening studies). cvc5's
`split_gb.{h,cpp}` consulted as the reference ([split-GB] paper's SplitGb /
admit discipline).
**Verdict:** **ship** — the chain corpus solves at 16×24 and 32×48 (every
size answered `unknown` before), the sparse family improves across the
board, and no previously-solved goal regressed. The capacity frontier
moves to chain ≥64×96, still honest `unknown`.

## The architecture that shipped

`grobner_path` (`nixie-theories/src/ff_theory.rs`), per connected
component, in order:

1. **The monolithic basis first** — exactly the pre-split computation and
   budget semantics. Nothing that used to complete loses anything.
2. **On the monolithic budget-out, the split fallback**: the component's
   generators partition by degree into a LINEAR ideal and a NONLINEAR
   ideal; each gets its own Gröbner basis; cvc5's `admit` discipline
   exchanges consequences to a fixpoint — the linear ideal accepts every
   linear consequence of either basis (it stays linear under Buchberger:
   S-pairs of linear polynomials are linear), the nonlinear ideal accepts
   only **linear binomials** (`x − c`, `x − y`), so dense linear content
   (RREF rows, definitions) never re-enters the cascade. That is the
   exact re-expansion failure both flattening studies root-caused, closed
   by construction.
3. **FindZero over the merged union** (not itself a basis; every element
   is an ideal member, which is all the branchers consume — with one
   exception, below), with two changes:
   * **Lazy honest round-robin**: the positive-dimensional brancher no
     longer refuses p > 10⁶ outright; it enumerates 0, 1, 2, … up to a
     256-value horizon, and an emptied stack over truncated branches
     reports `OutOfBudget`, never `Exhausted`. Wrong guesses on a chain
     die in one node (the branch literal contradicts a product row), so
     the effective branch factor is tiny though the theoretical one is p.
   * **Element-bootstrapped children**: each branch recomputes its basis
     from the node's REDUCED basis elements plus the branch literal —
     same ideal, but the branch avoids re-running the original cascade.
     This also accelerates the monolithic path (sparse 128×192: 38 s →
     8 s release; the old per-branch recompute from raw generators was
     the hidden cost).

## Measurements (release build, shared machine — treat near-threshold deltas as noise)

| goal | before | after |
|---|---|---|
| bn254 chain planted 16×24 | `unknown` | **`sat` 0.06 s** |
| bn254 chain planted 32×48 | `unknown` | **`sat` 67 s** |
| bn254 chain planted 64×96…256×384 | `unknown` (>120 s) | `unknown` (budget, ≤121 s) |
| bn254 sparse 8×12 | `sat` ~0.1 s | `sat` 0.3 s |
| bn254 sparse 16×24 | `unknown` ~11 s | **`sat` 0.2 s** |
| bn254 sparse 32×48 | `unknown` ~14 s | **`sat` 0.1 s** |
| bn254 sparse 64×96 | `sat` ~7.5 s | **`sat` 0.3 s** |
| bn254 sparse 128×192 | `unknown` ~18 s (38 s release when it solved) | **`sat` 8.0 s** |
| bn254 dense 12×20 | `unknown` ~0.15 s | **`sat` 0.1 s** |
| goldilocks sparse 16×24 / 64×96 | `sat` / `sat` 1.6 s | `sat` 0.3 s / `sat` 1.0 s |

Step counts (`NIXIE_FF_STATS`, deterministic) recorded in the run logs;
the verdict column is the load-stable fact.

## The false `unsat` the corpus caught (and the oracle could not)

The first cut of the lazy round-robin dropped the truncation gate: the
search stack emptied over branches that had enumerated only 256 of p
values and reported `Exhausted` — a **false `unsat` on the
planted-satisfiable `bn254_sparse_planted_8x12`** (the landed pre-split
binary answers `sat`). The tiny-prime exhaustive oracle cannot see this
class (p ≤ 256 never truncates — the horizon always covers p), which is
exactly why the planted-BN254 corpus is a standing gate. Pinned by two
regressions in `ff_solver_regression.rs`: the reproducer file itself
(`planted_bn254_sparse_8x12_is_never_unsat`) and a minimal all-solutions-
beyond-the-horizon shape (`all_big_solutions_stay_honest`).

## Negative results recorded (do not retry without new structure)

* **Operand flattening under the split** (name each multi-term linear
  `ff.mul` operand by a definition variable): kills the chain. The
  named products are pairwise coprime in their leading monomials, the
  Gebauer–Möller criteria skip exactly those S-pairs, and the cheap
  linear consequences (`k_{i+1}·xᵢ − kᵢ·x_{i+2}` from products that
  SHARE a variable) never appear — the split fixpoint deadlocks with
  nothing exchanged and FindZero falls to round-robin at a 254-bit
  prime. Variable sharing between products IS the asset; flattening
  destroys it structurally (this is the third flattening variant
  measured across the studies — all three lose).
* **Split-first** (run the split before any monolithic attempt): starves
  goals the monolithic path completes (sparse 64×96 at BN254 and
  Goldilocks regressed `sat` → `unknown`), because the separated ideals
  never derive the cross-basis elimination consequences (super-linear
  univariates) the brancher feeds on. The split is a FALLBACK, not a
  replacement.
* **A ⅛-budget completion slice** (one bounded monolithic run over the
  merged elements between split and search): regresses the same goals —
  the slice is smaller than the budget they need. Superseded by
  monolithic-first.

## Soundness accounting

Every exchanged polynomial is a member of the ideal its basis generates,
and inductively of the component's ideal — a constant in either basis
refutes the component. The merged union is consumed only by rules that
need ideal membership (univariate branching, linear univariates,
whole-ring detection); the minimal-polynomial rule (whose quotient
arithmetic needs a true basis) is gated on `is_gb`, true only for
monolithic or per-branch recomputed bases. Split-path refutations carry
the component's origins as the core and **no certificate** — certified
mode honestly downgrades those (the monolithic path keeps its traced
certificates unchanged). All oracle suites green: exhaustive tiny-prime
(10/10), planted fuzz at Goldilocks/BN254/BLS12-381, 51 solver FF
regressions, 88 theory FF tests, Z3 parity 177 (100% decisive, Z3
4.16.0).

## What remains open

Chain ≥64×96 (the completion AND the split's lazy search both budget
out — genuine MQ hardness at this frontier), F4-style batched reduction,
NTT. The next lever for the chain is branch-variable selection in the
round-robin (currently first-unassigned; a product-variable-first order
would propagate earlier), which is a heuristic change inside a chaotic
search and needs the matched-null discipline of `docs/BENCHMARKING.md`.
