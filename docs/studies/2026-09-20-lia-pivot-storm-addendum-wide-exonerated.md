# Addendum (2026-09-20, later session): the wide store exonerated — the wall is now pivot-volume arithmetic

Re-measured after the cut-budget landing (`LIA_MAX_CUTS_PER_ROUND` 16→2)
and the patch move, with symbolized release builds and direct counters.
**Every number below supersedes the corresponding claim in the parent
study's "next session" map.**

## The wide store never runs anymore

On `CAV/45-vars/problem__022` (the standing probe): **80 000+ pivots,
`wide_rows = 0` throughout.**  The 24×16 cut flood was what pushed
determinant-ratio entries past `Rational64` width; at 24×2 the table
stays narrow for the whole search.  The parent study's item 2 ("the
wide-store arithmetic layer — per-op bigint gcd is 90 % of wall") is
therefore **resolved by the adjacent fix**, not open: the item to keep on
the map is its narrow-store generalization (below).

(Profiler note for whoever re-reads perf data here: LTO/ICF folds
nixie's `gcd_i64` into num-bigint's `BigUint …::gcd` symbol — the flat
profile shows "BigUint::gcd 60 %" where the real frame is
`simplex::gcd_i64`.  Trust the symbolized self-time of `gcd_i64` and the
direct counters, not the BigUint attribution.)

## The current wall, precisely

* ~**500 M `gcd_i64` calls in 15 s** (counted), ≈ 73 % of wall
  (symbolized flat profile: `gcd_i64` 12.6 % self + its ICF twin at
  60.7 %).
* Volume = 80 k pivots × ~45 rows × ~45 terms × ~3 rational ops —
  the per-pivot substitution arithmetic, nothing else.
* Operand histogram (counted): 46 % ≤ 8 bits, decaying tail, ~8 %
  ≥ 45 bits.  The *mid/large* mass dominates cycles; the small mass
  dominates call count.
* 80 k pivots on a 40-row LP = the internal 20 000-node B&B budget
  burned inside ONE theory check (~2-3 pivots per node) — z3-old does
  the whole instance in 44 pivots + 4 CDCL-visible branches.  **The
  pivot VOLUME is the architectural item, unchanged in priority.**

## The gcd implementation itself is settled (benchmarked)

Microbenchmark of the measured operand distribution (log-mixture
matching the histogram, 20 M pairs, this hardware): binary
(shift/subtract) **34.8 Mops/s** vs hardware-div Euclid **25.1** vs
hybrid **29.9**.  The code's own comment ("binary wins for the mixed
magnitudes") is confirmed — do not revisit.  A Lehmer-style u64 gcd has
at most ~2× headroom on this distribution (~25 % of wall best case);
not worth a hot-path change in exact arithmetic.

## The one real arithmetic lever left: fraction-free rows (narrow store)

The 6 250 gcds per pivot are *all* in the per-term rational
substitution.  Representing each row as **integer numerators + one
common denominator** (Bareiss-style; the substitution becomes integer
mul/sub + one exact rescale per row) removes the class entirely —
projected ~3× on substitution-dominated searches (022: ~15 s → ~5 s,
under the table's 10 s cap).  This is the parent study's item 2 in its
correct modern form — an own-session project (`LinExpr` consumers in
`simplex/mod.rs`), now *narrow*-store work.

## Updated ordered map

1. **CDCL-visible branch channel** (unchanged; owns the LIA class).
2. **Fraction-free narrow rows** (replaces "wide-store arithmetic" —
   the wide store no longer runs on the probe family).
3. Warm-start scoped checks (unchanged).
4. The standing-table snapshot re-run at normal load (the BV session's
   study also awaits it; load was 26–35 from concurrent agents).
