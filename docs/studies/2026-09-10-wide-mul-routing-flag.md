# The wide-`bvmul` routing flag is dead — and reviving it loses (measured)

**Date:** 2026-09-10 (Tier-B triage session). Binary: `9f68746e` lineage,
A/B `6a5a1cee` (same binary both arms, `NIXIE_BV_WIDEMUL_FLAG` gate).

**Verdict: keep the flag dead; do not re-route wide-mul goals to the
eager dispatch.** Reviving it measured **−6 files** on the 509-sample
(284 → 278, zero verdict changes — pure timeout shifts). Documented so
the next routing experiment starts from the measurement, not the intent.

## The finding

`has_bv_wide_mul` has exactly one setter: the `BvMul` arm of
`encode_depth_uncached` (the Bool Tseitin encoder). That arm requires the
*encoder* to visit the mul node — but for well-typed input the encoder
mint-a-var-and-stops on every theory-sorted term, and muls only ever
appear under comparison/equality atoms, which it never descends into.
Measured: **every** corpus goal with wide products — `Sydr/cjpeg`
(64-bit), `brummayerbiere2/smulov*` (512–1024-bit), BuchwaldFried
(32-bit) — reported `wide_mul=false`. The stage-4 routing clause "wide-
`bvmul` goals keep the dispatch for its CEGAR machinery" has therefore
been vacuous since it landed: **every goal routed unified**, and the
stage-4 measurement ("unified default, geomean 1.36×") was effectively
an everything-unified measurement.

## The experiment

Corrected detection in `track_theory_vars` (the walk that actually sees
every BV sub-term of the asserted comparisons; condition mirrors the
CEGAR abstraction's own gate: width ≥ 32, non-constant operand),
env-gated, same binary both arms, load ≈ 6:

| arm | solved of 509 |
|---|---|
| flag OFF (status quo = dead flag) | **284** |
| flag ON (wide-mul goals → dispatch + CEGAR) | 278 |

Six files regress `sat`/`unsat` → `unknown` (lamport_nonatomic,
maxxor016, lfsr_004_015_112, fft/Sz512_15368, mcm/54,
shift1add.13988); zero improve. One instructive counter-point:
`smulov3bw0512` itself got *faster* under the dispatch+CEGAR (1.6 s vs
3.8 s unified) — the dispatch is not strictly worse per file, but the
aggregate says the unified path is the better default even for the class
the CEGAR was built for.

## Consequences for Tier B

- The Sydr/cjpeg, s3_clnt, spear, BuchwaldFried, smulov2/umulov losses
  are **not** a routing problem. Routing them to the existing dispatch
  (with or without division abstraction) does not close any of them.
- The lever for those files is the dispatch's CEGAR itself (refinement
  tiers, division abstraction) or the unified path's word-level
  reasoning — improvement in place, not re-routing.
- If the flag is ever revived, it must come with a per-class win, not
  the current aggregate loss.
