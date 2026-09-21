# Design brief: the integer tableau — lazy canonicalization past the write-back floor

**Date:** 2026-09-21.  **Status:** a design brief for an own-session(s)
project — nothing built.  **Entry context:** the warm-start negative
study's profile map — both LIA churn probes are substitution-volume
cells where the fraction-free machinery's CANONICAL WRITE-BACK
(`checked_ratio_i128`'s per-term gcd + the row chain) plus the integer
loop are ~78 % of wall.  The Bareiss layer made the arithmetic cheap;
the remaining cost is paying for OUTPUT nobody reads.

## The observation that opens the project

`substitute_row_ff` computes each substituted row TWICE, in effect: once
as an `IntRow` (integer numerators + shared denominator — what the next
pivot will consume, held in the ptr-coherent cache) and once as a
canonical `LinExpr` (one `checked_ratio_i128` gcd PER TERM — what the
tableau's store requires).  During a make-feasible cascade, the
canonical form of the 45 substituted rows is read by almost nobody:

* the delta-propagation loop reads ONE coefficient per row (the leaving
  basic's) — available from the `IntRow` as `N_v/D` without reduction;
* the column-diff maintenance reads only the term VAR SETS — the
  `IntRow` has them;
* the entering rule (`find_pivot_col`) reads ONE row per round (the
  violated basic's) — signs and eligibility are `IntRow`-readable;
* `eval_expr` on the entering solved form is once per pivot.

The canonical form is needed by the SLOW consumers only — propagation
(`propagate_bounds_in`), Gomory cuts, branch bounds, model extraction,
`row_ids` content-addressing on intern.  Those fire O(violations), not
O(pivots).

**The project**: make the `IntRow` the tableau's PRIMARY storage, with
the canonical `LinExpr` a lazily-materialized memo per row — built on
first slow-consumer access, invalidated (dropped) on row replacement.
The write-back then happens once per (row, slow-consumer-touch), not
once per pivot.

## The architecture sketch

* `tableau: FxHashMap<VarId, Arc<IntRow>>` — the primary store (the
  cache and the store merge; the ptr-coherence question dissolves, the
  `IntRow` becomes the identity).
* `lin_cache: FxHashMap<VarId, (Arc<IntRow>, Arc<LinExpr>)>` — the
  materialization memo, validated by `Arc::ptr_eq` on the `IntRow`
  (exactly the current cache's discipline, inverted).
* `fn lin_form(&mut self, var: VarId, manager-scratch) -> Arc<LinExpr>`
  — the single materialization choke point.  Every current
  `tableau.get(&var)` consumer that needs coefficients routes through
  it (49 internal sites + the accessors `tableau_iter`,
  `tableau_keys`, `tableau_coef_of`, `defining_row`).
* Hot-path rewrites read the `IntRow` directly:
  * `build_pivot_expr` becomes the zero-gcd re-denomination
    (numerators negated, denominator := entering numerator — the
    Bareiss study's follow-up, which was negative AS A STANDALONE
    because the entering solve was 1/46th of the mass; as part of THIS
    project it is simply how the solved form is born);
  * the delta-propagation coefficient and the column-diff var sets
    read the integer forms;
  * `find_pivot_col`/`find_violating`/`find_bland_pivot_col` take an
    `IntRow`-read view (sign of `N_v`, magnitude comparisons via
    cross-multiplication against `D` — no reduction).
* Width discipline unchanged: `INT_ROW_BUDGET` (2^62) admission, the
  exact `BigLinExpr` wide store as the escape, `LinExpr`-only consumers
  unchanged semantically (they see the same canonical rows, later).

## Sizing and staging

Phase 1 (the bridge): keep `tableau: Arc<LinExpr>` as the store but let
the pivot commit store rows as `IntRow + pending-canonical`, with
`lin_form` materializing on access and the commit loop no longer
writing canonical forms eagerly.  This isolates the change to the
pivot's commit + the consumer choke point.  Measured gate: the churn
probes' write-back share (currently ~40 %) collapses; counters
BIT-IDENTICAL (same canonical content, produced lazily — the search
must not move).

Phase 2: move `find_pivot_col` et al. onto the integer view
(entering-rule semantics preserved exactly: the same comparisons over
the same values — the mirror can verify the pivot SEQUENCE is
unchanged, pivot-for-pivot).

Phase 3 (optional, only if a profile still shows it): the entering
solved form as a born-integer row.

## The soundness rails (what makes this tractable)

* The canonical content is a PURE FUNCTION of the `IntRow` — the
  current `substitute_row_ff` write-back already proves it (the
  equivalence grid pins value-identity).  Laziness changes WHEN, never
  WHAT.
* Row identity for `row_ids` content-addressing: intern-time rows are
  canonical already (they come from parsing); only pivot-derived rows
  lazify, and `row_ids` never addresses those (they are slacks'
  substituted forms — the intern path content-addresses the REQUESTED
  form pre-substitution).  Verify this claim in phase 1 with an
  assertion-level test: no `lin_form` call from `intern_row_cached`.
* The wide-row escape ladder must keep its exact semantics: an
  `IntRow` that declines budget never becomes primary — the row lives
  in `wide_rows` as today, canonical `BigLinExpr` and all.  The
  narrow/wide boundary code paths are the highest-risk sites; the
  wide-literal differential pins are the guards.
* Scope discipline: `pop` never removes rows; row replacement happens
  at pivot commits and wide migrations only — the memo's invalidation
  set is the same complete set the `IntRow` cache already maintains.

## What this does NOT buy

The pivot COUNT (Layer 3 — the internal B&B volume) is untouched: this
project makes each pivot cheaper, not fewer of them.  If the arithmetic
arc's branch-channel campaign drains the CAV class by search-shape,
re-profile before starting this — the write-back floor's absolute share
falls with it.

## Measurement plan (pre-registered)

* Primary: the churn probes' substitution-family self-time share
  (`pivot` + `checked_ratio_i128` + `gcd_i128`), before/after — expect
  the write-back component (≈ the latter two) to collapse to <10 %.
* Identity: perf gate 1.000/1.000 AND the standing table's conflict
  totals bit-identical (phase 1 must not move the search); the mirror's
  pivot-for-pivot check for phase 2.
* End-to-end: the standing table at calm load, par-2/geomean readout;
  the CAV completing cells' medians.
* Full bar: nextest, clippy/fmt/doc, Z3 parity, the wide-literal
  differentials.

## Execution record: Phase 1 landed (Stages A and B, same day)

**Stage A (`c5e8026a`)** — the bridge, behavior-identical: `TableRow`
storage, the memoizing `row_lin` choke point, the `&self` Cow view
(`row_lin_view`), form-independent `term_vars`; every insert still
`Lin`.  Verified: theories 1670, solver 1198, probe counter identity.

**Stage B** — the win: `substitute_row_ff` loses its canonical
write-back (returns the `IntRow`; the write-back could never decline
where the 2^62 admission passed, so the path partition is unchanged),
pivot commits store `TableRow::Int`, the delta-propagation reads its
one coefficient from the integer form (one `checked_ratio_i128` per
row — the deferral's only per-pivot residual), and the old
ptr-validated `int_rows` cache is DELETED (the store holds Int natively;
a `LinNoInt` negative variant prevents per-pivot rebuilds on the
over-budget tail; commit-time int-form builds are the same k-gcd cost
the cache paid).

**Measured (problem__011, the standing churn probe):**
`checked_ratio_i128` — 21.9 % of wall — VANISHES from the profile
(the write-back is dead); `materialize_lin` (the lazy path) is 2.3 %;
`pivot` self drops 39 % → 11.6 %; `gcd_i128` absorbs the residual
chain reduction (17 % → 22 %).  End-to-end: 17.6 s → 14.9 s (~1.18×),
counters BIT-IDENTICAL (the laziness changes WHEN a row is canonical,
never WHAT it is).  Gate PASS 1.000/1.000; parity 176/177 clean; CAV
40-cell sweep identical (one baseline-leg cap timeout under load).

The remaining arithmetic mass is the substitution's gcd CHAIN plus the
entering/leaving row materializations — Phase 2/3 territory (the
entering-rule trio and `build_pivot_expr` still materialize one
canonical row per pivot round; the born-integer solved form is
Phase 3).  The write-back floor itself is CLOSED.
