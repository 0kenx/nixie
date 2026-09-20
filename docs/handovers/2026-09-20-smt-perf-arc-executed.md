# Handoff: the SMT perf-gap arc executed — BV leads z3, LIA's owners named, the measurement layer hardened

**Date:** 2026-09-20 (night).  **Arc:** the `2026-09-19-mbqi-closed-perf-attributed` handoff's
program — the arith eq-chain dissection, the BV identity preprocessor, the branch-channel
build, the LP-cost slice, and the measurement infrastructure.  **Goal for the next agent:**
two owned projects remain — the **Bareiss/row-denominator layer** (the LIA class's last
structural blocker) and the **ctx-simplify fold pass** (the prp/nec both-solved 47× wall
class) — plus one cheap closure: the calm-load table re-run with the fixed z3 parser.

## Where things stand (all landed on main, `9870026e` at handoff)

- **QF_BV leads z3 on the standing table**: 54/60 vs 53/60, zero disagreements (third
  snapshot, calm load).  The multiplier-identity class is closed outright — the
  **extract-window arithmetic** in `bv_preprocess.rs` (four rules: full-width-extract
  identity, extract-over-extract fusion, extract-over-concat pushback, and product-window
  narrowing — `extract[hi:lo](A·B)` depends only on operand bits `[hi:0]`) folds the
  BuchwaldFried counterexample residual at **0 SAT conflicts, 25 ms** (was timeout);
  `bench_16217` timeout→unsat, `bench_3238` timeout→sat-at-4.1 s where z3 times out.
- **The LIA patch move + Z3's cut budget landed** (earlier in the arc):
  `Simplex::patch_int_columns` (Z3 `patch_basic_columns` — the cheap integrality move,
  exact-read acceptance, all-or-nothing rollback) and `LIA_MAX_CUTS_PER_ROUND` 16→2
  (Z3 `get_gomory_cuts(2)`).  QF_LIA holds 32/60 throughout (no lost cell at any step —
  verified bit-identical counters at each landing).
- **The gcd kernels landed**: power-of-two fast paths + a `u64` kernel + the i128
  delegation.  Direct counting showed **37 % of all `gcd_i64` calls carried an operand of
  exactly 1** (full binary loop each); measured **2× on the substitution operand
  distribution** (35→69 Mops/s), ~1.55× projected where gcd is 73 % of wall.
- **The CDCL-visible branch channel is landed — by the arithmetic arc (item 96,
  `63cae24b`)**, flag-gated `NIXIE_LIA_BRANCH_LEMMA=1`, with its matched null.  This arc
  built an independent implementation first, measured it, and **handed it over on
  collision** (see negative results).  Their rung-3 default-flip campaign is
  pre-registered (`ca675e2e`) — their territory.
- **The z3-counter harness bug is fixed** (`9870026e`): `run_perf.sh` grepped
  `:conflicts`; the QF_BV path prints `:sat-conflicts` — **every z3 conflict count in
  every recorded snapshot was 0**.  Two standing-table attributions were re-based on
  direct `z3 -st` evidence (see the correction study).

## The territory (what owns which gap now)

- **QF_LIA 32/60 vs z3 ~52**: two layers, both diagnosed to entry points.
  1. *The per-LP churn* (the binding one): ~2 s per post-cut degenerate re-feasibilization
     on the CAV family — **the branch channel cannot pay until this lands** (measured:
     emission fires, no round-trip completes; `problem__022` burns 20 000 internal B&B
     nodes ≈ 80 k pivots ≈ 500 M gcd calls per check).  The fix is **Bareiss-style
     row-common-denominator rows** in the narrow store (integer numerators + one shared
     denominator per row; substitution becomes integer mul-sub + one row-level
     reduction; projected ~3× on the substitution mass beyond the gcd-kernel 2×).
     Design brief: `docs/studies/2026-09-19-lia-pivot-storm-dissected.md` (the mirror),
     its 2026-09-20 addendum (the wide store is EXONERATED post-cut-fix — `wide_rows=0`
     throughout now; the perf "BigUint::gcd" frames are LTO/ICF twins of `gcd_i64`),
     and `2026-09-20-gcd-kernels-slice.md` (what landed, what remains).  This is an
     own-session project touching `simplex/mod.rs`.
  2. *The branch channel*: landed flag-gated; the rung-3 campaign decides the default.
     With the churn fixed, expect the CAV family to start completing round-trips.
- **QF_BV 54/60**: preprocessing closed for the identity class.  The fragile cells
  (`bench_16217` at 9.9 s, `bench_11463` at 6.5 s) are **SAT-capacity cells** — z3 uses
  2 371 conflicts where nixie uses 39 860 (17×) — the SAT arc's territory (their CSR/
  surgery campaign), NOT preprocessing.  The remaining real preprocessing route is the
  **ctx-simplify fold pass** (the prp-3-18/problem_2__014 47×-wall class, plus the
  nec-smt unknowns' other half): the 2026-09-19 attribution study's step-zero-closed
  section is the design entry ("a genuine ctx-simplify-style pass — collect condition
  literals recursively, case-split prune ite branches, iterate" — own-session, in
  `query/simplify.rs`'s memoized harness).

## The cheap closure first: the honest table

Re-run `bench/smt_perf/run_perf.sh` at **sustained load ≤ ~8** — three attempts this arc
were load-contaminated (both solvers lose cells; the fragile ones bounce; the runs were
discarded, per-cell evidence in `2026-09-20-aggregate-measurement-log.md`).  With the
fixed parser this run also records **real z3 conflict columns for the first time** —
re-baseline the aggregate counters and the wall-watch readout's three standing checks
(fragile-solve inventory, counter-checked per-cell wall deltas, both-solved median
ratio — now meaningful both ways).

## Negative results (do not retry blind — all with mechanisms in the studies)

- **Entering-rule magnitude guard** (keep |coef| ≥ max/8): mirror-positive (63→45 pivots,
  55→41-bit entries) but **regressed two standing cells sat→timeout** — CDCL chaos eats
  mirror merit.  Reverted; a table-positive variant needs a powered matched-null.
- **Node-budget cuts on the internal B&B** (512): converts solvable instances to unknown
  (the wide-literal bnb pin needs >512 nodes) — an internal budget can't pay the way
  z3's per-check budget does without CDCL-visible branching.
- **Loose patch acceptance** (basic-only reads, no rollback): "flips" problem__022 by
  riding a wide-stale fabricated read laundered through the model validator — the
  documented false-sat class, not a win.
- **Solve-eqs for the SAGE family**: withdrawn — the definition vars have ~500 uses;
  substitution is explosive; z3's own `max_occs=2` would refuse.
- **The branch-channel duplicate**: this arc's independent build was reverted on
  collision with item 96 — the measurements landed instead (the default-off
  bit-identity bar 32/32, the v20 budget trade, the churn gating).  Do not re-implement;
  item 96 owns the feature.
- **binary-vs-Euclid gcd** is benchmarked-settled (binary wins 34.8 vs 25.1 Mops/s on
  the measured distribution); Lehmer has ≤2× headroom on ≤25 % of wall — not worth it.

## Repo conventions and traps (this arc's additions)

- **Never trust a "z3 at 0 conflicts" claim from the table harness** — the counter
  column was junk until `9870026e`; verify against `z3 -st` directly (the BuchwaldFried
  claim survives: `sat-mk-var 1`, no conflicts line).
- **Perf on this tree**: LTO/ICF folds `gcd_i64` into num-bigint's `BigUint::gcd`
  symbol — trust symbolized `gcd_i64` self-time and direct counters, not the BigUint
  attribution.  Use `CARGO_PROFILE_RELEASE_DEBUG=1 CARGO_PROFILE_RELEASE_STRIP=none` +
  a root-fs `CARGO_TARGET_DIR` (the /media/data disk fills; other agents' 48 GB
  debug caches live there).
- **The i64-truncation cast trap**: delegating i128-range values through `as i64`
  truncates values in `(i64::MAX, u64::MAX]` negative — the wide-literal pins catch it;
  pinned forever in `gcd_u64_matches_reference_and_fast_paths`.
- **The under-merge landing convention** was exercised heavily (four landings through
  dirty trees, one through direct overlap): overlap check → 3-way or hand-off →
  `update-ref` → `reset` → materialize ONLY your files → verify.  When the overlap is
  the same *feature*, hand off (the item-96 precedent).
- **Load discipline**: two table runs discarded this arc; z3 losing cells is the
  contamination signature.  The qfidl/`scope_rebase` heavy differentials flake their
  budgets at load >40 — re-run in isolation before believing a failure.

## Adjacent arcs (don't collide)

- **Arithmetic arc** (item 96 → rung 3): `solver.rs`, `theory_manager.rs`,
  `int_case_split.rs`, arith `solver.rs`.  Their handoff
  (`2026-09-20-arithmetic-arc-item96-handoff.md`) names the J5 class next.
- **SAT arc**: the CSR-watches/surgery campaign (`solver/mod.rs` SAT-side, watch
  internals); owns the fragile BV cells by the re-attribution.
- **Graph** (tests dirty in the tree at handoff), **realsort**, **ctx-simplify**
  (landed the memoization; the fold pass is the follow-up), **let-printer**.

## Ordered next steps

1. **The calm-load table** (the cheap closure; see above).
2. **Bareiss/row-denominator rows** (the LIA structural layer; own session; entry via
   the pivot-storm studies + `ddm_mirror.py` in `docs/studies/assets/`).
3. **The ctx-simplify fold pass** (the prp/nec class; own session; entry via the
   2026-09-19 study's step-zero-closed).
4. After 2 lands: coordinate with the arithmetic arc's rung-3 verdict — the channel
   default-flip and the churn fix should land in one measured campaign, not two.
5. Binaries: `precompile/<sha>/` for every landing (`9870026e` pending its next build).
