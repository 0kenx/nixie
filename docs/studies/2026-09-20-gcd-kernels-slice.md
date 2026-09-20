# The gcd kernels: 2× on the measured operand distribution — the LP-cost layer's first slice

**Date:** 2026-09-20 (the LP-cost session; the pivot-storm addendum's
item 2, first contained slice).
**Landed:** power-of-two fast paths in `gcd_i64`/`gcd_u64` + the
`u64`-kernel delegation and binary form for `gcd_i128`.  Unit benchmark:
**35 → 69 Mops/s (2×)** on the measured substitution operand
distribution; projected ≈ 1.55× end-to-end on substitution-dominated
searches (gcd ≈ 73 % of wall there).  Full bar: 12 074 tests, parity
176/177 with 0 disagreements, gate PASS 1.013, clippy/fmt clean.

## The measurement that motivated it

Direct counting on `CAV/45-vars/problem__022` (the standing probe):

- **37 % of all `gcd_i64` calls carry an operand of exactly 1** — each
  paying the full shift/subtract loop (~20-60 iterations) to rediscover
  the answer 1.
- **58 % carry a power-of-two operand** — `gcd(2^j, 2^k·m) = 2^min(j,k)`
  for odd m: two `trailing_zeros` and one shift, no loop.
- `gcd_i128` was plain software-128-bit Euclid — `__umodti3`, the
  historically dominant cost the `checked_ratio_i128` comments document.

## The changes

1. `gcd_u64` kernel: the existing binary loop with the power-of-two
   early-out; `gcd_i64` delegates (sign handling only).
2. `gcd_i128`: zero early-outs, **u64-range delegation to the kernel**
   (kills `__umodti3` for the common case), power-of-two shift path,
   binary loop above `u64` range.
3. Pins: full-equivalence against Euclid over a corner-rich operand
   grid, plus the exact range corner that bit during development — see
   the trap below.

## The trap (recorded for the next kernel edit)

The first version of the i128→kernel delegation cast through
`as i64`: values in `(i64::MAX, u64::MAX]` TRUNCATED negative and
`unsigned_abs` produced `2⁶⁴ − a` — **four wide-literal regressions
failed** (the exactness pins caught it; brute-forcing the u64 kernel
alone had not, because the bug was in the delegation's range, not the
kernel).  The fix is the u64-typed kernel call; the pin
`gcd_u64_matches_reference_and_fast_paths` covers the corner forever.

## What this does NOT close

The 2× is on the gcd mass; the remaining structural item is unchanged:
the per-term rational substitution itself (~6 250 gcds per pivot at
3-4 per fused op).  The row-common-denominator / Bareiss representation
(the projected further ~3×) remains the map's item 2 — this slice is
the cheap half.  The standing table re-run at calm load measures the
aggregate (wall was 16-45 load at landing; the gate's counter identity
1.013 and the SAT-side bit-identity carry the inertness evidence).
