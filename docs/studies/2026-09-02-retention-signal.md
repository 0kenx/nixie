# Retention signal: usage-ranked vs glue-ranked reduce (2026-09-02, pre-registered)

Open question left by the 2026-08-22 cadical-reduce study
(`2026-08-sat-cadical-policy-ports-negative.md`): on `stable-300`,
**random** deletion at the cadical trigger points beat **glue-ranked**
deletion ~2× (median over 10 seeds) and beat both the baseline schedule
and the treatment. Its own note: "the retention *signal*, not just the
schedule, may be wrong." This study is the follow-up: replace the signal.

## Arms

All three run the cadical-reduce schedule (first reduction at conflict
300, then `25·√conflicts`, ×log₁₀(irr/1e4) above 1e5 irredundant) with
the same tier protection (glue≤2∧used>0 keep; glue≤6∧used≥30 keep) and
the same deletion count (75 % of candidates):

* **base** — legacy tiered reduce (the standing-table default arm).
* **treat** (`OXIZ_CADICAL_REDUCE=1 OXIZ_REDUCE_BY_USED=1`) — candidates
  ranked **least-used-first** (used asc, then glue desc): clauses that
  have not participated in conflicts die first, regardless of glue.
* **null** (`OXIZ_CADICAL_REDUCE_NULL=1`) — identical trigger points and
  counts, uniform-random selection (partial Fisher–Yates; the existing
  matched-null arm).

The decision metric is **treat/null** (median conflicts-to-verdict,
10 seeds, CRN-paired via `SEED=`); base is reported for context. The
claim under test is "the usage signal ranks clauses better than chance";
the null removes the signal while keeping the schedule, counts and
perturbation.

## Cells

12 instances × 10 seeds × 3 arms (the 2026-08-22 study's list): 6s167-opt,
crn_11_99_u, constraints_17, mrpp_4x4, qwh.50.1250, summle_X4044,
stable-300, frb65-12-2, si2-b03m, Break_unsat_06_07,
g2-ak128boothbg2msisc, barman-pfile06-022. 60 s cap, pinned core,
`stats_solve`, deterministic counters only.

## Gates (pre-registered)

* **Advance**: T/N geomean ≤ 0.90 with ≥ 2/3 of families ≤ 0.95 →
  promote to a full corpus null-checked run before any default flip.
* **Drop**: T/N ≥ 1 overall, or heterogeneous with null-dominant tails
  (the 2026-08-22 shape) → record, switch stays doc(hidden) default-off.
* Sanity: treat and null arms must show identical deletion counts per
  trigger point on one instrumented spot-check (the null contract).

## Rationale for usage over glue

The used-stamp already exists in the port (cadical's decrementing stamp,
bumped to 31 on conflict participation). Glue is a *learning-time*
property that goes stale as the search moves; usage is a *running*
measure. If the stable-300 anomaly is real signal (not chaos), usage is
the minimal hypothesis that explains it: what the search actually reuses
should be kept, independent of how the clause was born.

## Results (2026-09-02, same day — 12 × 10 × 3 cells, 60 s cap)

| instance | treat med | null med | T/N | verdicts |
|---|---|---|---|---|
| 6s167-opt | 2 528 | 9 041 | **0.280** | Unsat all arms/seeds |
| crn_11_99_u | 5 305 | 7 428 | 0.714 | Unsat |
| constraints_17 | 25 720 | 21 451 | 1.199 | Sat |
| mrpp_4x4 | 11 686 | 8 175 | 1.429 | Unsat |
| qwh.50.1250 | 97 459 | 121 201 | 0.804 | Sat |
| summle_X4044 | 37 889 | 21 970 | **1.725** | Sat |
| stable-300 | 279 807 | 284 683 | 0.983 | Sat |
| frb65-12-2 | 54 131 | 60 384 | 0.896 | Sat |
| si2-b03m | 36 875 | 36 690 | 1.005 | Sat |
| Break_unsat_06_07 | 34 428 | 35 152 | 0.979 | Unsat |
| g2-ak128booth | 0 | 0 | — | both solve pre-search |
| barman-pfile06 | 1 041 | 1 302 | 0.799 | Unsat |

**T/N geomean 0.9039, 5/11 families ≤ 0.95 — the advance gate (≤ 0.90 AND
≥ 2/3 families) is NOT met. Per pre-registration: heterogeneous, switch
stays `doc(hidden)` default-off.** Same shape as the 2026-08-22 reduce
study: no consistent treatment/null separation.

### The two findings that survive

1. **6s167-opt is a usage-signal stronghold, seed-robust**: treat spans
   909–18 881 conflicts over 10 seeds (median 2 528) vs the legacy base's
   115–149k band — ~47× at median, with Unsat (seed-independent) on every
   arm. Spot-check (default seed): usage-ranked 909, glue-ranked 121 248,
   random 11 303, legacy base 118 191. Per-trigger deletion counts match
   the null contract (total deletions differ only because the treat runs
   are ~50× shorter). Even *random* deletion beats *glue-ranked* 10× on
   this instance today — the glue ranking is actively harmful on this
   class, and usage is the strongest single signal measured here.
2. **The 2026-08-22 study's arm cells no longer reproduce on the current
   tree**: its 6s167 null (random) median was 127 562 then; the same arm
   measures ~9–11k now (glue-ranked still ~121k, matching). The tree moved
   under it (default-elimination bundle, rephase/walk, arena compaction
   since). **Old study arm numbers must not be reused as baselines** —
   re-measure the arm you need on the tree you're changing.

### Not pursued (recorded as leads)

* Per-instance policy selection (usage-ranked here, glue-ranked there) is
  the hindsight-oracle trap quantified at 2.26× in §8 of BENCHMARKING.md.
* A *state-based* hybrid — e.g. fall back to usage-ranked reduction when
  DB churn stops correlating with progress — is a new design, needs its
  own pre-registration; the 6s167 evidence makes it the candidate.
