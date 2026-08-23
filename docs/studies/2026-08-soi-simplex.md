# SOI simplex driver (established-candidates Priority 2): sound, end-to-end neutral, default stays off (2026-08-23)

## Pre-registration

Per `docs/2026-08-established-research-candidates.md` Priority 2: an
alternate feasibility driver for `Simplex` (King/Barrett/Dutertre,
FMCAD'13; cvc5 `soi_simplex.cpp`), flag-gated (`SimplexConfig::enable_soi`,
default off; `OXIZ_ARITH_SOI=1` experiment knob), objective over exact
delta-rationals, existing degeneracy discipline, **the current
one-violation path as fallback, and all conflicts through the existing
exact explanation path** (no new certificate surface — the doc's own
requirements, which this slice followed exactly).

Go/no-go: deterministic work metrics on the arithmetic corpora; a reduced
pivot count is insufficient if row work increases; Z3 parity required.

## What was implemented

`make_feasible_soi` in `oxiz-theories/src/arithmetic/simplex/mod.rs`:

* error collection over basics; the sum-of-infeasibilities linear form
  built exactly over the current nonbasics (all rational steps checked,
  `None` → resource limit);
* dual-like steps: steepest-`|c_j|` entering (Bland after a degenerate
  streak), min-ratio leaving over the column plus the entering column's
  own opposite bound (bound flips), exact delta propagation;
* **frozen-focus discipline** (added mid-experiment, cvc5
  `adjustFocusAndError` parity): the objective is built from a frozen
  error set and driven to its box minimum before re-focusing — rebuilding
  the objective every iteration lets the total violation ratchet (fix
  error A by creating error B; each round's own sum decreases while the
  union does not) and the descent wanders;
* fallback to the standard driver on: no eligible entering column
  (unimprovable focus), unbounded-improvement anomaly, any exact-arithmetic
  overflow (flag cleared first, state unchanged by the transactional
  pivot), Bland patience exhausted, or SOI budget exhaustion;
* `Ok(())` + `resource_limit` keeps the standard give-up contract.

## Results

* **Soundness: clean.** Differential vs the standard driver on 1 800
  random systems (4 shapes × 400 seeds) plus 200 degenerate boxes:
  every answered pair agrees; every SOI-feasible answer is backed by a
  row-consistent, in-bounds assignment; give-ups excluded by contract.
  Full suite (10 071), clippy/fmt/doc, Z3 parity 168/168 clean.
* **End-to-end: neutral.** Paired 40-cell A/B over the QF_LIA/QF_UFLIA/
  QF_IDL/QF_UFIDL/QF_NIA differential sample (15 s matched caps,
  CPU-pinned, process-group-safe): solved 19/40 in BOTH arms, one flip
  (`1527.smt2`, `unknown` → timeout — a file that bails quickly off-arm).
  Spot timings: c10_i 19.5→20.3 s, hash_sat_05_06 9.0→9.2 s.
* **Pivot metrics: inconclusive on a toy generator.** The random-system
  bench makes extremely degenerate boxes where BOTH drivers thrash
  (~6 000-10 000 pivots per check at 8-16 variables); it cannot resolve a
  ratio. Recorded as a bench-design lesson, not evidence either way.

**Verdict: the flag stays default-off.** No deterministic-work evidence of
a win; end-to-end neutral. This is the go/no-go gate doing its job.

## Why the simplified driver is neutral (the delta to the published gains)

cvc5's SOI is not "a global objective instead of one violation" — that
simplification is what this slice measured neutral. The published gains
rest on machinery this slice deliberately did not port:

1. **ErrorSet with signals** (`error_set.cpp`): incremental error tracking
   and `SUM_METRIC` selection — not a per-iteration rebuild;
2. **witness-improvement classes** (`ConflictFound / ErrorDropped /
   FocusImproved / ...`): step acceptance and Bland arming keyed on
   classified outcomes, not raw objective deltas;
3. **the SOI conflict certificate** (`generateSOIConflict` + conflict
   builder + `quickExplain`/`greedyConflictSubsets` minimization): Farkas
   certificates off the SOI row, which let SOI answer UNSAT directly
   instead of falling back to the primal driver. My slice delegates all
   conflicts, so every "SOI would have concluded here" moment costs a full
   primal restart.

A faithful port is a real project (cvc5: ~1 000 lines + ErrorSet +
LinearEqualityModule integration). The enabling pieces this slice leaves
behind: the exact SOI linear-form builder, the frozen-focus loop, the
bound-flip delta propagation, and the differential harness.

## Measurement lessons (recorded for the next agent)

1. **A verdict-flip table built from mismatched runs is garbage.** The
   first A/B compared a 10 s-cap differential run against quick off-runs
   whose output parser returned `?` for 45 cells — reported as "45
   regressions", which a proper paired rerun reduced to **one** noise
   flip. Same file, same caps, real verdict extraction, or nothing.
2. **Toy generators can be unmeasurable.** Random ±1-3-coefficient rows
   over tie-heavy boxes produce degenerate thrash in both drivers; a
   pivot-ratio bench needs instances shaped like the target corpora
   (e.g. sampled real files), not uniform random systems.
3. The `Ok(())`-plus-`resource_limit` give-up contract must be honored by
   test harnesses: an inconclusive answer is not a false feasible
   (the first differential version classified give-ups as verdict
   mismatches).
