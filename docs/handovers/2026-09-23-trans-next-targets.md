# Handoff: Transcendental theory (δ-ICP) — status after the fragment-widening round

**Session:** 2026-09-23, continuing `docs/handovers/2026-09-23-trans-next-targets.md`.
**Landed:** `970a2f4a` (this round; binary `precompile/970a2f4a/nixie`),
on top of `8131ba44` (perf round) and `df8017a2` (the theory).
Read `docs/TRANS.md` first — the "Semantic decisions" section is the contract.

## What this round landed (all verified: 12 356/12 356 workspace tests,
## clippy/fmt/doc clean, z3 parity unchanged, perf gate PASS 1.000/1.000)

### Fragment widening (the verdict wins)

1. **Ground UF over Reals is decided** (was honest-`unknown`).  The
   dispatcher Ackermannizes every ground application before the Tseitin
   abstraction: applications become fresh Real vars, congruence
   `(a=b ∧ …) ⇒ v=v'` joins the Boolean skeleton, the dPLL loop carries
   exactly EUF's ground semantics.  The old decline test flipped to
   `unsat` (the EUF answer).  `(get-value (f x))` publishes the fresh
   var's value (the `ack_apps` map through `install_trans_model`).
   Implementation: `AckermannizeTactic::ackermannize_assertions` in
   `nixie-core/src/tactic/ackermann.rs` (new public core; the pipeline
   method now delegates to `substitute_and_constrain`).
2. **`distinct` over any sort** expands to pairwise negated equality
   atoms (arity ≤ 16; bigger honestly declined).  Negated Eq atoms
   compile to `Cmp::Ne` constraints.
3. **`≠` prunes in whole-box form**: conflict when the root interval
   lies wholly inside the EXACT δ-window (`admissible_exact`, compared
   in exact rationals via `f64_exact_rational` — the f64 pruning
   interval's δ+ε widening points the WRONG way for `Ne`).  Pointwise
   split-to-exclude remains not attempted (disjunctive).

### Hot-path fixes (t19 312→53 ms solve-quiet, t16 65→35, t13 17→10)

Profiling showed the 303 ms of t19 was NOT branches — it was ~90%
BigUint work in the exact-rational layer (the dead counters hid this;
`branches`/`witness_tries` are now wired):

1. `rational_dyadic` (nixie-math): the `*_rational` enclosures build
   dyadic fractions; reduce by trailing zeros instead of gcd+division.
   Bit-for-bit identical, pinned by test.
2. `asin_enclosure` memoized (op 5 in the point cache) — it runs a
   ~500-bit isqrt plus two atan series per call and `contract_sin_like`
   calls it twice per Sin/Cos propagation.
3. `evaluate_at_exact`: monotone arms (exp was 4 calls → 1 per distinct
   endpoint); **sin/cos over a non-degenerate bracket** now widens the
   endpoint hull by the rigorous curvature remainder `w²/8` clamped to
   `[-1,1]` (`sin_cos_exact`) — the hull alone is NOT an enclosure when
   the bracket spans a monotonicity break (reachable via nested
   transcendental args, e.g. `sin(exp x)`; was a latent false-dalse-δ-sat
   path in the witness check; pinned by `sin_cos_exact_probe` tests).
4. `propagate`: sweep-level convergence check (every 256 steps compare
   total interval mass; <1e-9 relative improvement ⇒ ulp-creep ⇒ let the
   brancher take over).  Sound: only pruning power is lost.
5. `branch_split_point`: periodic-aware first split — when the branch var
   DIRECTLY feeds a Sin/Cos node and the window spans ≥ π/2, split at the
   nearest multiple of π/2 (both halves on monotone-segment boundaries;
   asin contraction engages immediately).  Pure guidance; midpoint
   fallback; the 1-ulp interior margin is required.

### Root-cause fix OUTSIDE trans (do not re-break)

`collect_structural_children` (nixie-solver/src/solver/term_walk.rs)
omitted all six transcendental kinds — every term under a `sin/exp/…`
was invisible to every structural walk (UF gate found it: `(exp (f x))`
reported no Apply).  This is the "no silent fallthrough" pattern; if a
new TermKind appears, that match must grow with it.

### Options

`:trans-max-branches`, `:trans-max-propagations` join `:delta`
(`trans_max_branches`/`trans_max_propagations` on `SolverConfig`).

## Ranked next targets

1. **t19's remaining ~40 ms** is ~1000 uncached `asin_point` calls on
   fresh arguments (each: `rat_sqrt_bracket` isqrt + 2 `atan_point`
   Ifx-series).  Options: a cheaper asin (single Ifx series on
   `y/√(1−y²)` without the f64 round trips), or skip contraction when
   the Sin node's value interval is unchanged since the last
   contraction (per-node memo of (v.lo,v.hi)).  Low priority — t19 is
   no longer an outlier.
2. **Trail-based undo for `BranchInto`** (the handover's original
   target 1, second half): full re-enqueue is O(N·fixpoint) per
   backtrack.  Now measurable with the wired counters.  The trap
   stands: an "only the split var" re-enqueue left the box
   inconsistent; write a real undo log + a debug assertion that the
   re-propagated fixpoint matches snapshot semantics on the corpus.
3. **dReal corpus import** (`bouncing_ball`, `diode`, …) as the scale-up
   benchmark; run `dreal4` as a differential oracle like the z3 parity
   suite (linking is banned, running the binary is fine).
4. **Period folding for unbounded periodic refutations**
   (`sin²+cos²=0` over ℝ; ~10 s to honest-Unknown today via budget
   exhaustion) — reduce `x mod 2π` once the box exceeds a period.
   dReal also punts; optional polish.
5. **`Int`-sorted arguments in UF congruence atoms** still decline at
   `intern_term` (honest); an Int→Real widening of ground congruence
   atoms would admit `f(Int)` in trans goals.

## Traps recorded (cumulative; do not re-learn)

- **Purification × δ** (8131ba44): keep the six transcendental kinds in
  `is_arith_constructor`; per-atom δ-weakening doubles through proxy
  chains.
- **Ulp-edge convergence**: PRUNE_ULPS slack needs interior room for the
  exact witness; if tightened, re-run t15/t16.
- **1-ulp branch loop**: never bisect when `next_up(lo) >= hi`; any new
  branching site must skip (see `pick_branch_var`, `branch_split_point`).
- **BranchInto staleness**: the whole subtree is stale after `restore()`;
  the full re-enqueue is load-bearing until a trail rewrite proves
  equivalence.
- **`admissible_exact` is per-constraint at build time** — never
  re-derive from an engine-side δ (they drifted once).
- **`Ne` pruning must use the EXACT window**, not the f64 `rhs_interval`
  (the ε-widening fires conflicts on boxes that are δ-outside).
- **nextest deadlines flake under load**: the full suite must run on a
  quiet machine (137 s quiet vs flakes at load 30+; qfidl_qlock_11 and
  five slow tests are the usual suspects — pass solo).
- **Bench wall times are load-contaminated**: check `uptime` before
  recording TSVs; the verdicts are load-independent.

## Verification bar for any change here

`cargo nextest run -p nixie-theories -E 'test(trans)'` (37) +
`cargo nextest run -p nixie-solver --test trans_delta_icp` (27) are the
fast canaries.  Then the standard battery — workspace tests, clippy,
fmt, doc — plus `./bench/trans/run_bench.sh precompile/970a2f4a/nixie`
(24 goals; never re-run recorded cells, add files freely).  The z3
parity suite and the perf gate must stay clean whenever solver-wide
walks change (`collect_structural_children` is on general paths).
