# The Bareiss layer landed: fraction-free pivot substitution (narrow store)

**Date:** 2026-09-20/21 (the LP-cost session taking the pivot-storm addendum's
item 2).  **Input:** the addendum's wall — ~500 M `gcd_i64` calls in 15 s
(≈73 % of wall) on `CAV/45-vars/problem__022`, all in the per-term rational
substitution (`x + f·y` at ~3.5 gcds/term × 45 rows × 45 terms per pivot).
**Landed:** integer common-denominator rows (`IntRow`) with a
pointer-validated cache, substituted as integer multiply-subtract + one
row-level gcd chain + one single-gcd canonical write-back per term —
**bit-identical output** to `substitute_row_fast` (same canonical values,
same term ORDER, same zero-drop), so the search trajectory and every
deterministic counter are unchanged (gate 1.000/1.000).  **All-integral
substitutions stay on the historical integer fast path** (gate: at least one
side carries a fraction) — the ungated version taxed integral cells ~1.1×.

## Why rows must PERSIST in integer form (the design finding)

A transient fraction-free conversion does not pay: converting a canonical
per-term row to a common denominator costs an lcm chain (k gcds), and the
canonical write-back costs one gcd per term regardless — the fused
multiply-add's 3-3.5 gcds/term drop to ~2, not to ~1.  The 3× projection
requires the row to LIVE in integer form between pivots, so the read side
is free and only the write-back pays.

The landed shape threads that through WITHOUT changing the tableau's
representation (`Arc<LinExpr>` stays authoritative — every other consumer
untouched):

* `IntRow { terms: SmallVec<[(VarId, i128)]>, const_num, denom }` —
  `x_B = (Σ nᵢvᵢ + c)/D`, `D > 0`, every `|nᵢ|, D ≤ 2^62`
  (`INT_ROW_BUDGET`; 2^62 not 2^63 so the substitution products
  `D_e·n_v + n_e·m_v ≤ 2^125` cannot overflow `i128` — no checked math on
  the hot path, no decline-by-overflow).
* `int_rows: FxHashMap<VarId, IntCacheEntry{src: Arc<LinExpr>, row}>` —
  the entry is read ONLY when `Arc::ptr_eq(entry.src, tableau.get(var))`.
  Rows are content-replaced, never edited in place (the file's standing
  invariant), so pointer identity IS content identity: **a stale encoding
  is structurally unreachable**, no epoch/version counter needed.
  `row: None` is a NEGATIVE entry (this exact content exceeds budget) so
  the over-budget tail never re-derives the lcm chain.
* Substitution `row + (n_e/D_r)·entering`: numerators
  `N_v = D_e·n_v + n_e·m_v`, denominator `D_r·D_e`, one joint gcd chain
  (early exit at 1) → joint-canonical form (proved minimal: a prime power
  of D absent from every term's reduced denominator would divide every
  numerator, contradicting gcd = 1) → per-term `checked_ratio_i128`
  write-back (the single gcd/term) → `LinExpr` + optional re-admitted
  `IntRow` in one pass.
* Budget/width declines fall through to the UNCHANGED historical ladder
  (`substitute_row_fast` → `substitute_row_big` → wide store); the
  equivalence grid pins that ff's declines are exactly the rational
  path's declines on final width (identical values; ff has no failing
  intermediates within budget).

## Cache maintenance (the complete mutation-site set)

Rows leave/replace at: pivot commit (leaving removal, entering insert,
per-row substitution commits, wide captures), the `update_row_exact`
narrow→wide migration, and `reset` — each mirrors into `int_rows`.
`pop` never removes rows (the Dutertre–de-Moura backtrack contract; the
`row_scope_trail` field is vestigial — never pushed), so no pop-time
invalidation exists.  `intern_row` inserts stay lazy (first substitution
builds and parks the entry).  Dead entries cannot be mis-read: a dead
VarId never owns a row again (ids are not recycled).

## Evidence

* **Standing table (the landing snapshot, `0963911e`):** QF_LIA 32/60
  held with **bit-identical counters** (5517 conflicts — the third
  full-corpus identity checkpoint), geomean-all **246 → 144 ms** (−41 %,
  now under z3's 164.7), both-solved median nixie/z3 **1.71 → 0.55**
  (~1.8× faster than z3 on the common LIA mass, n=32); par2 9449 → 9429
  (timeout-dominated — the branch channel owns the count).  This is the
  aggregate the completing-cell medians pointed at, at calm load.

* **Bit-identity:** perf gate PASS — conflicts 1.000, decisions 1.000
  (n=9 SAT corpus); the 40-cell CAV 30/45-vars sweep: zero verdict
  disagreements, zero conflict-count differences.
* **Self-time shift** (12 s window on 45-vars/problem__022, symbolized
  builds): `BigUint::gcd` alias (the rational-kernel ICF twin)
  21.5 % → 5.5 %; the new cost centers are the write-back
  (`checked_ratio_i128` 11.9 %) and the chain (`gcd_i128` 7.8 %) — the
  work moved off per-term fused rational arithmetic into one-reduction
  canonical output.
* **Completing-cell walls** (medians, load-contaminated — treat as
  directional; the calm-load table is the standing record):
  30-vars/026 ~2.2×, 30-vars/033 ~2×, 30-vars/035/034 ~2.6×,
  45-vars timeouts unchanged (the B&B churn volume is the architectural
  item — unchanged priority).  30-vars/017 exposed the integral tax
  (~1.1×) → the fraction gate; post-gate it is noise-level.
* **Unit pins:** `substitute_row_ff_matches_rational_reference_seeded_grid`
  (4000-case LCG grid, order+values+declines), `int_row_budget_boundaries`
  (2^62 edges), `int_row_cache_pointer_coherence_after_pivots` (every
  cache entry ptr-eq the live row after a solving session with push/pop),
  `ff_encoding_is_faithful` helper (value + minimality per row).

## What this does NOT close

* The pivot-volume/architecture item (the CDCL-visible branch channel,
  item 96's rung 3): 45-vars/022 still burns its 20 k-node internal B&B —
  now with a cheaper substitution inside each node.  The channel is the
  remaining owner of the LIA class.
* `build_pivot_expr` still runs per-term division (~k gcds ONCE per
  pivot — 1/46th of the substitution mass; the zero-gcd integer
  re-denomination from the leaving row's `IntRow` is the natural
  follow-up if it ever shows in a profile).
* The wide store (`BigLinExpr`) is untouched — it remains the honest
  escape past the i64/i128 cliff; `scale_exact_row` (parse-side) and
  `scale_big_to_narrow` (intern-side) still pay per-term gcds on rare
  rows.

## Traps recorded

* The shared `target/` on /media/data is volatile under disk pressure
  (ENOSPC → someone's wholesale purge mid-session; also one binary
  vanished earlier mid-A/B).  Isolate measurement builds:
  `CARGO_TARGET_DIR=/tmp/...` on the root fs.
* The equivalence grid's generator must build rows through CHECKED
  merges — `LinExpr::add_term`'s `+=` is num-rational's unchecked add
  (debug builds panic on intermediate overflow long before the canonical
  row would).
* A grid generator bug produced an "entering row references the entering
  variable" case (impossible in the real pivot — the solved form is FOR
  that variable); the ff path's `row.contains` append-guard correctly
  dropped it.  Worth knowing: that guard is load-bearing for exactly the
  no-op case, not a bug.

## Addendum: the named follow-up resolves NEGATIVE (post-branch-channel profile)

Re-profiled the churn probe (`CAV/45-vars/problem__022`, 12 s window)
after the branch channel became the default (`0edc05fc`): `pivot` self
36.3 % (the inlined integer loop — the work), the canonical write-back
family `checked_ratio_i128` + `gcd_i128` + the `BigUint::gcd` ICF twin
≈ 31 % (the per-term single-gcd floor of `LinExpr` output), and the
residual per-term rational callers (`Ratio::reduce` + `CheckedMul/Add`
≈ 11 % — the cut/patch/B&B machinery, not the substitution).  The
entering-solve follow-up (zero-gcd re-denomination from the cached
`IntRow`) is 1/46th of the substitution mass ≈ **≤2 %** — below any
hot-path-change bar.  Not taken; do not revisit without a profile that
moves it.  The owning item on this family remains the pivot VOLUME
(the internal B&B's node count), architectural, per the standing map.
