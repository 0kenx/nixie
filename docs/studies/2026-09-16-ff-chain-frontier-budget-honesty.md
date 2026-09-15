# The chain ≥64×96 frontier: budget honesty, lm caching, and the measured cost of the certificate tracer

**Date:** 2026-09-16
**Scope:** `docs/HANDOFF_FF_THEORY.md` open-work item 1's remainder
(chain ≥64×96). Pre-registered levers considered: F4-style batched
reduction, round-robin branch-variable selection. What the measurement
actually demanded first: three T5 budget-honesty fixes and leading-
monomial caching in the Gröbner engine.
**Verdict:** ship the honesty + caching work (no verdict changes; every
previously-solved goal held or improved; blowup refusals get
budget-bounded instead of grinding). Chain ≥64×96 remains capacity-
bound — now with the blocker precisely measured and named: **the
certificate tracer's cofactor-row maintenance costs ~1 s per S-pair on
96-input cascades**, which no budget policy can fix.

## What was measured (release build, `--profile perf` + `perf record`)

`bn254_chain_planted_64x96`: the monolithic-first attempt ran **700 s+
without exhausting its 2^24 tick budget** (one stats line, nothing
else). Profiles across four iterations:

1. First profile: 23 % `MPoly::add_term`, 16 % `SmallVec::from`,
   14 % `FieldCtx::add`, 13 % `reserve_rehash` — term-churn.
2. After lm caching: the `lm()` scans vanished from the profile —
   `lm()` was a **full terms-map scan** (`max_by` over keys) consulted
   twice per candidate in the pair-selection scan and once per
   candidate in every reduction scan: O(selections × pairs × terms).
3. With a `[gb-dbg]` probe: **~1 s per S-pair** on the 96-generator
   cascade, with elements still small (max 21 terms, basis 148 at pair
   100) and the budget barely touched (2^23 left). The cost is NOT the
   polynomial arithmetic — it is `TracedPoly::sub`/`mul_monomial`/
   `scale` maintaining the **cofactor row over all inputs** per
   operation (96+ polynomial clones/subtractions per reduction step,
   plus the `reduce_traced` entry clone of the whole traced poly).

## What shipped

* **Selection-scan charging** (T5): one unit per pair-key computed in
  the selection scan — the scan is O(#pairs) per selection, quadratic
  over the cascade, and was entirely uncharged.
* **Cofactor-row charging** (T5): each reduction step now charges
  `n_inputs × sub_terms` alongside the polynomial cost — the tracer's
  row maintenance was doing ~n_inputs× the charged work (the
  wall-vs-budget gap's root cause).
* **Bloat circuit breaker**: `basis.len() > 8×inputs + 64` or any
  element over 512 terms aborts the cascade as `Err(Budget)` — a
  deterministic capacity decision that hands the remaining time to the
  split fallback instead of burning it on a hopeless monolithic run.
* **Leading-monomial caches**: `lm_cache` computed once per basis
  snapshot, threaded through `pair_key_lms`, `criterion_applies_lms`
  and `reduce_traced` — the selection and reduction scans no longer
  rescan term maps.

Corpus (release, before → after): sparse 128×192 `sat` 8.0 s →
**4.6 s**; sparse 64×96 0.33 s → 0.09 s; every other solved goal held;
chain 16×24/32×48 `sat` (0.07 s / 53 s); chain 64×96+ still honest
capacity-bound.

## The measured blocker (what the next agent should attack)

The tracer is the price of §8's certificates, and on wide-input
cascades it costs ~1 s per S-pair regardless of budget policy. Three
candidate directions, in rough order of expected value:

1. **Sparse cofactor rows**: rows are typically 2-nonzero-out-of-96;
   the dense `Vec<MPoly>` forces zero-entry churn (allocation per
   op). A sparse representation (or an `.is_zero()` fast path that
   moves instead of cloning in `sub`/`mul_monomial`/`scale`) could be
  ~10–50×.
2. **Untraced fast path**: run the monolithic attempt without the
   tracer; if it completes and a certificate is wanted, replay the
   (now-known-trajectory) cascade traced — the healthy cascade is
   fast the second time. Complexity: trajectory must be deterministic
   (it is) and the replay verified.
3. **F4-style batched reduction** (the pre-registered Phase-7 lever):
  replaces the S-pair loop wholesale — orthogonal to the tracer cost,
   which it would inherit unless (1) or (2) lands first.

Round-robin branch-variable selection was NOT reached — with the
monolithic attempt refusing honestly, the split fallback does run on
64×96 within the budget, and the remaining time goes to the split's
own traced cascades (same cofactor cost). Fixing the tracer first
makes every later lever measurable.

## Soundness accounting

All changes are capacity/speed only: charging more per unit makes
budgets fire EARLIER (never later), the breaker only aborts (never
invents), and the caches are read-only snapshots of values the code
recomputed anyway. No verdict changed on any corpus goal or oracle;
804 nixie-math + 88+16 theories FF + 55 solver FF tests green.
