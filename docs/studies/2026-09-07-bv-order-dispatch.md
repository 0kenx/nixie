# Order encoding on the dispatch path: the pure-BV distinct cells close

**Date:** 2026-09-07 (stage 3 of the campaign)
**Stage 2:** `docs/studies/2026-09-07-bv-order-encoding.md` (the unified-path
flip; baseline here = `precompile/4689d14`).

**Verdict: landed.**  The order encoding now also serves the **eager
pure-QF_BV dispatch** (`BvSolver::assert_formula_true`'s `Distinct` arm):
the campaign's original headline cell — n=2000 w=16 free-variable
`distinct`, pure QF_BV — goes from **timeout to 23.8 s**, n=1000 w=11 from
timeout to 6.3 s, and the dense n=600 w=10 cell improves 8.4×.  The
corpus has **zero** regression surface: an exhaustive scan of the 46 191
QF_BV extracts found **no file with `distinct` arity > 32**, so the new
arm cannot fire on any real corpus input.

## What landed (`nixie-theories/src/bv/solver/{solver,order}.rs`)

- `assert_formula_true`'s spine: an eligible `distinct` at a **fact**
  position builds the bitonic network (the same
  `encode_distinct_order_network` the unified path uses) and pins its
  result true.  Fact positions only — the free-pad soundness shape of
  `order`'s module docs; nested or negated occurrences keep
  `encode_bool_node`'s exact pairwise definition.
- **Pads are anonymous SAT variables** here (no `TermId` needs to exist
  for a wire only the network sees), so the arm needs no `&mut` manager.
- **Dispatch-side equality guards**, both assert orders: the spine's `Eq`
  arm records asserted-equal pairs (permanent in the single-shot
  dispatch); the network build refutes outright if an already-asserted
  equality hits two arguments, and a later `assert_eq` between two
  arguments of a built network refutes it the other way.  Without a
  guard, an explicit `(= x_i x_j)` must refute through the full sort —
  resolution-hard (stage 2 measured 4M conflicts at n=16).
- Eligibility mirrors stage 2's gates: arity > 32, all arguments blasted
  same-width bit-vectors, no ground-constant argument (pinned wires
  defeat the identity guidance), `n ≤ 2^w`, size cap,
  `NIXIE_BV_DISTINCT_ORDER=0` disables (the one knob now governs both
  paths).

## Cells (pure QF_BV, release, prev = `precompile/4689d14`, pairwise =
same binary with the flag off)

| cell | prev | order | pairwise |
|---|---|---|---|
| sat n=100 w=8 | 0.21 s | 0.47 s | 0.11 s |
| sat n=300 w=16 | 6.1 s | **3.0 s** | 3.7 s |
| sat n=600 w=10 (dense) | 33.9 s | **4.1 s** | 34.6 s |
| sat n=600 w=32 | 42.3 s | **15.8 s** | 36.8 s |
| sat n=1000 w=11 (dense) | timeout | **6.3 s** | timeout |
| sat n=2000 w=16 | timeout | **23.8 s** | timeout |
| unsat n=100 w=8 (explicit `=`) | 0.017 s | 0.013 s | 0.009 s |
| unsat n=300 w=16 | 0.035 s | 0.040 s | 0.033 s |
| unsat n=2000 w=16 | 1.38 s | 1.45 s | 1.39 s |

Unsat cells at parity (guard- or blast-bound); the bounded small-n loss
(n=100 w=8, 0.36 s absolute) is below the flip's n ≥ 300 scope and has no
corpus exposure.  The embedded instance handles the network measurably
worse than the unified main core (n=300 w=16: 3.0 s here vs 0.93 s
unified; n=100 w=8 loses here, wins unified) — an argument for the
remaining stage-4 question (routing pure goals through the unified path),
not against this landing.

## Verification

Workspace 10640/10640 (3 new dispatch-arm tests: free-vars sat, both
guard directions); clippy/fmt/doc clean; Z3 parity 169/169 decisive;
randomised differential vs z3 on pure-BV distincts (free vars, constants
mixed in, forced equalities, duplicate-argument aliases, negated; n ∈
{33..100}, w ∈ {4..16}): **87 trials, 0 mismatches, 0 timeouts**;
hand battery (both guard orders, real duplicate args, pinned arguments,
pigeonhole, negated) green under both flag states; 100-file corpus subset
0 mismatches (and the full-corpus scan shows the arm unreachable there).

## Campaign state after this landing

| row | architecture | state |
|---|---|---|
| mixed goals, BV atoms | unified main-core circuits (stage 1) | landed `482b806` |
| mixed goals, `distinct` n>32 | order encoding + eq-atom guards (stage 2) | landed `4689d14` |
| pure QF_BV, `distinct` n>32 | order encoding + assert-order guards (this) | landed |
| pure QF_BV, everything else | eager dispatch, pairwise atoms | open (stage 4: route through the unified core; flip condition 1's corpus geomean) |
