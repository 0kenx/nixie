# Adaptive retention signal: rank by glue only when glue ranks usage (2026-09-02, pre-registered)

Follow-up to `2026-09-02-retention-signal.md`: usage-ranked reduce is
~47× on the 6s167 class but 1.4–1.7× *worse* on mrpp/summle. Hypothesis:
**the glue signal's informativeness varies by instance** — where
low-glue clauses are no more reused than high-glue ones, ranking by glue
is ranking by noise (or anti-signal), and usage should rank instead.

## Treatment

`OXIZ_REDUCE_ADAPT=1` (implies the cadical-reduce schedule): at each
reduction, after tier protection, compute one signal over the candidate
set —

* sort candidates by glue (asc), take the best-glue quartile (the ones
  glue-ranking would KEEP) and the worst-glue quartile (the ones it would
  DELETE);
* `glue_informative = mean(used | keep-quartile) > mean(used | delete-quartile)`.

Rank **by (glue desc, size desc)** when `glue_informative`, else **by
(used asc, glue desc)**. Everything else (schedule, tier protection,
deletion counts, target %) is identical to both prior arms.

## Matched null

`OXIZ_REDUCE_ADAPT_NULL=1`: the *same* signal computation, same threshold,
same code path and same two rankings — but the choice is **inverted**
(`glue_informative → rank by usage`). Identical physical operations and
per-instance decision counts, opposite semantic correlation. If the
signal carries information, treat < null; under chaos they are
indistinguishable.

## Cells and gates

12 instances (the retention-signal list) × 10 seeds × 2 arms + the
unchanged base for context. Metric: median conflicts-to-verdict, CRN via
`SEED=`. Decision metric **treat/null**.

* **Advance**: T/N geomean ≤ 0.90 **and** ≥ 2/3 families ≤ 0.95 →
  corpus-wide null-checked run before any default consideration.
* **Drop**: T/N ≥ 1 or heterogeneous null-dominant tails → record, both
  switches stay `doc(hidden)` default-off.
* Sanity: on a 6s167 spot-check the adaptive arm must pick usage-ranking
  on early rounds (the class where usage measured 0.28 vs null), and on
  mrpp it must pick glue-ranking — the signal must fire as designed
  before its effect is believed.

## Prior

The 6s167 evidence (usage 909–18.9k over 10 seeds vs glue-ranked 121k,
random 9–11k) says glue ranks *anti-informatively* there; mrpp/summle at
1.4–1.7× the other way. If the quartile-mean signal separates those two
regimes online, the adaptive arm should capture most of the 6s167 win at
~no cost elsewhere. If the signal does not separate them, the result is a
clean negative on "cheap online signal detection" and the lead passes to
per-instance portfolio policies.
