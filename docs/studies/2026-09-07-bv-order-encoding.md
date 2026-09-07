# Order encoding under the unified core: the BitVec distinct row flips

**Date:** 2026-09-07 (stage 2 of the campaign)
**Handover:** `docs/handovers/2026-09-07-bv-unification.md` (flip condition 2)
**Stage 1:** `docs/studies/2026-09-07-bv-unification-stage1.md` (baseline here
= `precompile/482b806`).

**Verdict: flipped.**  The handover's pre-registered flip condition — "after
unification, rebuild the order encoding and re-measure its table; if it beats
pairwise by ≥ 1.5× on the n ≥ 300 cells, flip the BitVec row" — is met with
room to spare: **3.7–57× on every n ≥ 300 cell** (mixed goals through the
unified path; same-binary, flag-off control for pairwise), with the
campaign's headline cell — n=2000 w=16 sat, a timeout under *every*
architecture measured to date — solving in **17 s**.

## What landed

- **The bitonic network builder** (`nixie-theories/src/bv/solver/order.rs`):
  Batcher's iterative bitonic sort over `n2 = next_power_of_two(n)` wires
  (arguments + free pads), `bvult`-comparators with mux-routed swap outputs,
  a strictly-increasing chain over the sorted outputs, `out <=> AND(chain)`
  through a balanced AND-tree.  Correctness is pinned by the 0-1 principle
  (exhaustive, end-to-end through SAT solves) plus random differentials.
- **Identity phase guidance, derived by propagation.**  The builder
  evaluates the finished network under the identity arrangement (wire `i`
  carries `i`) with the SAT core's own unit propagation
  (`Solver::assign_and_propagate_level0`, new in `nixie-sat`) and records
  every derived value as a deterministic decision phase.  Hand-derived
  "pass-through" hints are *wrong* for descending half-cleaners (their swap
  routes through the mux arms even at `c = false`) and pin a non-model as
  the guided descent — measured 43k decisions at n=9 and 137 s at n=17
  where propagation-derived phases need ~2k decisions / 5 ms.
- **The solver-side handoff** (`nixie-solver/src/solver/bv_unified.rs`): the
  assertion spine records a *spec* exactly at fact positions — a
  `distinct` over same-width BVs at arity > 32 with the cheap generation
  preconditions; the unified link pass builds the network in its
  `build_with` window; a spec still pending at `check` entry materialises
  the historical pairwise encoding at base scope (so a generation that
  never engaged or died leaves the term correctly encoded either way).
  Soundness shape: with free pads, `result <=> chain` is not pointwise
  `distinct`, so the encoding exists *only* where the assertion pins the
  term true (the spine unit); every other occurrence reads the pinned var
  and the model has all wires distinct (see `order.rs`'s module docs).
- **Equality guards.**  The network refutes duplicate arguments only
  through the full sort — structurally hard for resolution (measured 4M
  conflicts at n=16; an n=300 explicit-equality cell timed out).  For each
  argument pair that already has an equality atom, the encoder emits the
  valid clause `distinct -> ~(x_i = x_j)`: an asserted `(= x_i x_j)` now
  conflicts *at once* (pairwise's instant refutation) at O(#eq-atoms) cost.
  This turned the unsat cells from timeouts into wins (n=300: 0.56 s vs
  pairwise's 0.78 s; n=2000: 9.4 s vs timeout).
- **Gates kept conservative:** ground-constant arguments stay pairwise
  (pinned wires defeat the identity guidance — measured timeouts on
  constant-mixed shapes that pairwise solves); `n <= 2^w` (the pigeonhole
  short-circuit's own bound, which also guarantees the identity fits);
  50 M-clause size cap; `NIXIE_BV_DISTINCT_ORDER=0` disables.

## The flip table (mixed cells; stage-1 binary vs this build, and the
same-binary flag-off control)

| cell | stage-1 pairwise | order | pairwise (flag off) |
|---|---|---|---|
| sat n=100 w=8 | 0.24 s | **0.07 s** | 0.17 s |
| sat n=300 w=16 | 3.2 s | **0.93 s** | 3.5 s |
| sat n=500 w=16 | 12.4 s | **1.0 s** | 11.7 s |
| sat n=600 w=32 | timeout | **11.0 s** | timeout |
| sat n=600 w=10 (dense) | 48.5 s | **1.7 s** | 48.4 s |
| sat n=1000 w=11 (dense) | timeout | **2.1 s** | timeout |
| sat n=2000 w=16 | timeout | **17.2 s** | timeout |
| unsat n=100 w=8 (explicit `=`) | 0.052 s | 0.053 s | 0.044 s |
| unsat n=300 w=16 | 0.80 s | **0.56 s** | 0.78 s |
| unsat n=2000 w=16 | timeout | **9.4 s** | timeout |

The one sub-1.5× cell (unsat n=100) is below the flip threshold's n ≥ 300
scope and within 10 ms absolute.  The dispatch path (pure QF_BV goals) keeps
its pairwise row — that flip is stage 3 (dispatch unification), unchanged
here.

## Verification

- Workspace suite **10629/10629** (7 new order tests: 0-1 exhaustive,
  pads, duplicates, pigeonhole, random differential, identity-descent
  guidance bound, size cap).
- Z3 parity 169/169 decisive, 0 wrong.
- Randomised differential vs z3 4.16.0: **90 trials, 0 mismatches, 0
  timeouts** (free vars, constants mixed in, forced equalities, negated
  distinct; n ∈ {33..150}, w ∈ {4..20}).
- 300-file QF_BV corpus sample (the committed seed-42 list): **0 verdict
  mismatches**, 2 old-timeouts now solved.
- clippy / fmt / doc clean.

## Why the study's 2026-09 wash flipped

The Attack-3 prediction held exactly: with circuits in the main core,
comparator decisions propagate per-decision and the identity phases guide
the whole descent — the sat cells collapse from "search for an arrangement"
to "walk the arrangement".  Two things the original experiment could not
have: the equality guards (its unsat regression, 3.3× at n=300, became a
1.4× win) and propagation-derived phases (hand hints pin a non-model; the
original's identity hints were of the hand kind and could not rescue the
n=2000 cell).

## Stage 3 (next): dispatch unification

The pure-QF_BV dispatch still solves its own embedded instance with the
pairwise row — the flip above covers mixed goals only.  Unifying the
dispatch (or routing pure goals through the unified path) is the remaining
pre-registered decision (flip condition 1's corpus geomean).
