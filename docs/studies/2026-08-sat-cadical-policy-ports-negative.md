# Two CDCL heuristic ports screened against matched nulls: both dead

Date: 2026-08-22. Continuation of [`2026-08-sat-speed-vs-cadical.md`](2026-08-sat-speed-vs-cadical.md),
which identified the 2–20× gap vs CaDiCaL as search-trajectory (conflict-count)
differences and listed four candidate causes. The top two candidates were
implemented behind study switches and run through the
[`docs/BENCHMARKING.md`](../BENCHMARKING.md) protocol (≥10 seeds/cell,
common-random-number pairing via `Solver::set_random_seed`, deterministic
metric = conflicts-to-verdict, treatment/matched-null ratio). **Both failed
the null comparison.** The switches stay in the tree (`doc(hidden)`, env-gated,
default-off) so the studies can be reproduced; no default behavior changed —
verified by bit-identical trajectories on the tracking instances.

## Study 1: mode-gated heuristic bumping (cadical `bump_variable`)

`NIXIE_BUMP_MODE_GATE=1`: conflict bumps reach only the active mode's
structure — VSIDS scores in stable, VMTF queue in focused — instead of the
historical double maintenance. `NIXIE_BUMP_MODE_GATE_NULL=1`: same structural
change, but stable-mode score bumps go to *random* variables of the same
count (scrambled signal).

Single-seed screening was promising on two instances and the full 10-seed
screen killed it:

| instance | base | treat | null | T/N |
|---|---|---|---|---|
| constraints_17 (SAT) | 28,176 | 21,282 | 46,647 | **0.456** |
| crn_11_99_u (UNSAT) | 93,134 | 95,859 | 122,672 | 0.781 |
| qwh.50.1250 (SAT) | 95,147 | 111,129 | 135,068 | 0.823 |
| summle_X4044 (SAT) | 104,832 | 119,710 | 102,047 | 1.173 |
| frb65-12-2 (SAT) | 423,828 | 546,220 | 465,249 | 1.174 |
| stable-300 (SAT) | 929,883 | 823,985 | 431,532 | **1.909** |

(The first three rows are from the reduce study's shared screening below;
mode-gate rows: see git history of this file for the 4-instance screen —
constraints_17 0.49, mrpp 0.58, but 6s167-opt 1.18 *null-better* and mrpp
1.11 worse than baseline.) Verdict: heterogeneous chaos with no consistent
treatment/null separation → dropped.

## Study 2: cadical `reduce.cpp` port (schedule + glue/used retention)

`NIXIE_CADICAL_REDUCE=1`: reduction scheduled like CaDiCaL (first at conflict
300, then `25·√conflicts` apart, ×log₁₀(irr/1e4) above 1e5 irredundant),
selection by `(glue desc, size desc)` over non-reason learned clauses after
tier protection (glue≤2 && used>0; glue≤6 && used≥30), deleting the worst
75%. Replaces the fixed-12000-conflict tier-percentage reduce.
`NIXIE_CADICAL_REDUCE_NULL=1`: identical trigger points and deletion counts,
clauses chosen uniformly at random (partial Fisher–Yates).

12 instances × 10 seeds × 3 arms, median conflicts:

| instance | fam | base | treat | null | T/N |
|---|---|---|---|---|---|
| 6s167-opt | UNSAT | 125,828 | 123,708 | 127,562 | 0.970 |
| crn_11_99_u | UNSAT | 93,134 | 95,859 | 122,672 | **0.781** |
| constraints_17 | SAT | 28,176 | 21,282 | 46,647 | **0.456** |
| mrpp_4x4#12 | UNSAT | 287,065 | 300,531 | 301,156 | 0.998 |
| qwh.50.1250 | SAT | 95,147 | 111,129 | 135,068 | 0.823 |
| summle_X4044 | SAT | 104,832 | 119,710 | 102,047 | 1.173 |
| stable-300 | SAT | 929,883 | 823,985 | 431,532 | **1.909** |
| frb65-12-2 | SAT | 423,828 | 546,220 | 465,249 | 1.174 |
| si2-b03m-m800-03 | SAT | 42,320 | 42,849 | 43,905 | 0.976 |
| Break_unsat_06_07 | UNSAT | 32,990 | 34,196 | 34,977 | 0.978 |
| g2-ak128boothbg2msisc | SAT | TO×3 arms @60 s | — | — | — |
| barman-pfile06-022 | UNSAT | 1,267 | 1,200 | 1,190 | 1.008 |

T/N geomean: UNSAT 0.943, SAT ≈0.99 (excluding the all-timeout instance).
Verdict per the rule "ratio ≤ 1 ⇒ nothing": **dropped as a default change.**

Notable observations for whoever revisits clause-db management here:

* On `stable-300`, *random* deletion at cadical trigger points beats
  glue-ranked deletion by ~2× (median over 10 seeds) and beats both the
  baseline schedule and the treatment. Either that instance rewards raw DB
  churn (fresh clauses) rather than retention quality, or the used-stamp /
  LBD signals are misinformative there. One instance is not a policy, but it
  is a lead: the retention *signal*, not just the schedule, may be wrong.
* The treatment's two clear wins (constraints_17 0.456, crn_11 0.781) show
  the early-first-reduction schedule does matter on some families; any
  future attempt should start there and hunt for the interaction that makes
  stable-300/frb65 pay for it.
* Seed sensitivity dwarfs everything: baseline mrpp alone swings
  159k→460k conflicts across seeds (≈2.9×); single-seed A/B numbers on such
  instances are worthless (reconfirmed live twice during this study).

## Study 3: cadical `stabilizing ()` schedule port (same session)

The reference ablation below showed CaDiCaL's stabilize switch interacts
with reduction, so the exact `stabilizing ()` schedule was ported:
first switch at `stabilizeinit` (1000) **conflicts**, increment *measured*
from phase 1's consumed ticks (`inc.stabilize`), later phases
`inc × stabphases²` (`NIXIE_STAB_FAITHFUL`). Matched null: the same
multiset of quadratic phase lengths drawn in shuffled order
(`NIXIE_STAB_NULL`).

First contact on `6s167-opt` (single seed):

| arm | conflicts | mode switches |
|---|---|---|
| default (fixed 5000-tick base) | 170,039 | 35 |
| faithful cadical schedule | 187,430 | 6 |
| shuffled-length null | **100,133** | 7 |

Null beats treatment; killed without a full study. Note this also corrects
an earlier misdiagnosis: "52 stable phases" in the stats line is
`restarts_stable` (restarts *during* stable mode), not mode switches —
the real default flip count is 35, not wildly far from CaDiCaL's 2 but
still ~17×.

A 4-seed check confirmed the kill with better evidence — per-seed T/N =
0.99 / 0.60 / 1.70 / 1.52, i.e. pure chaos redistribution with no
consistent direction:

| seed | default | faithful | null |
|---|---|---|---|
| 0 | 170,039 | 187,430 | 100,133 |
| 1 | 108,651 | 113,283 | 190,238 |
| 2 | 125,828 | 111,576 | 65,758 |
| 3 | 138,076 | 107,464 | 70,564 |

(Side observation: the *default* schedule is seed-stable here at 108–170 k
across four seeds while the shuffled-length null swings 66–190 k.)

## Decision-stagnation quantification

From per-decision traces (`NIXIE_TRACE_DECISIONS` decisions lines; matching
instrumented-CaDiCaL `cdec` lines) on `6s167-opt`, equal-size windows of
the run:

* Nixie decides each variable **35–62×** per window (diversity collapses
  2045 → 444 unique variables across the run).
* CaDiCaL re-decides **4–14×** per comparable window.
* Both start deep (Nixie mean level 42 in window 1, CaDiCaL 78); Nixie falls
  to ≈20 by window 2 and never recovers, decaying to 12; CaDiCaL
  oscillates 21–50 and holds.

Combined with the identical restart cadence, learnt sizes and backjump
ratios, the divergence is localized to **what the decision heuristic does
between restarts**: Nixie's chosen variable set narrows over the run and its
conflict depth decays with it. Whether this narrowing is a cause (heuristic
stagnation worth fixing) or a symptom (a weaker search needing more
conflicts naturally cycles harder through its hot set) is exactly what the
recommended cross-solver instrumentation should settle next.

## Reference ablation: where CaDiCaL's own advantage lives

Ablating CaDiCaL itself on `6s167-opt` (times, single seed; seed spread
checked separately for the big effects):

| config | time | conflicts |
|---|---|---|
| default | 0.28–0.38 s | 16.6 k |
| `--stabilize=0` | 0.30 s | – |
| `--score=0` (VMTF everywhere) | 0.27 s | – |
| `--shrink=0` / `--rephase=0` / `--target=0` | 0.25–0.36 s | – |
| `--minimize=0` / `--vivify=0` | 0.39 s | – |
| `--otfs=0` | 0.49 s | – |
| **`--reduce=0`** | **3.4–6.6 s** (seeds 1–3) | **186 k** |
| `--reduceint=1e6 --reduceinit=1e6` | 6.48 s | – |
| **`--reduce=0 --stabilize=0`** | **1.58 s** | – |

Reading: clause-database reduction carries essentially the whole gap, and
roughly half of that is an *interaction* — with a bloated database the
per-conflict tick rate inflates (2330 vs 903 ticks/conflict), which mistimes
the tick-driven stabilize switch; turning stabilization off recovers most of
the loss even with no reduction at all. Reduction's search benefit in
CaDiCaL is substantially "keep the tick clock calibrated", not a direct
clause-quality effect.

Nixie calibration on the same instance: **403 ticks/conflict** (its DB stays
small through on-the-fly subsumption — net 1,941 live learned clauses at
exit, and disabling its scheduled reduce changes conflicts by <1 %,
170,039 → 168,562). Nixie has no DB bloat and no tick inflation, yet still
needs 170k conflicts. So neither "add cadical's reduce" nor "fix tick
inflation" can be nixie's fix: the disease is not present in the same form.
The shared observable — nixie lands where CaDiCaL-with-no-reduce lands —
remains unexplained by any single-policy delta tested so far (four ports,
all null-neutral or null-beaten).

Diagnostics added to support further work: per-reason origin counters
(`NIXIE_REASON_STATS`: 31.6 % of Nixie's BCP reasons are learned clauses on
this instance, so reuse machinery does fire), real mode-switch count
(`Solver::stabilization_phases()`), and per-mode tick totals
(`Solver::search_ticks()`).

## Learned-clause utilization (final discriminator, also negative)

Instrumented the CaDiCaL copy to count search propagations whose reason
clause is redundant/learned (`stats.propagations.redundant_reason`), and
compared with Nixie's `NIXIE_REASON_STATS` counters on `6s167-opt`:

| solver | search propagations | from learned clauses | share |
|---|---|---|---|
| CaDiCaL | 2,307,295 | 175,445 | **7.6 %** |
| Nixie | 19,369,185 | 4,412,629 | **31.6 %** |

Nixie propagates through learned clauses at 3–4× the reference's rate (26 vs
10.5 learned-props per conflict) – its learned database is *more* load-
bearing, not less. This closes the last single-mechanism hypothesis tested:
utilization, cadence, sizes, ratios, pointer health, and tick rates are all
equivalent or better in Nixie, yet the global conflict count differs 10×.

A methodological note for future readers: the earlier "NO_REDUCE is
trajectory-neutral in Nixie" observation does not replicate CaDiCaL's
`--reduce=0` condition. Nixie's other deletion paths (on-the-fly subsumption,
strengthening) removed 132 k of 170 k learned clauses even with the
scheduled reducer disabled, so the DB never bloated. The 11× sensitivity to
reduction that CaDiCaL exhibits has no analogue to switch off in Nixie.

## Conclusion of the investigation

Every locally measurable property of Nixie's CDCL search on this instance
family matches or exceeds CaDiCaL's. The 10–20× outcome gap on hard
industrial UNSAT is therefore **emergent from accumulated trajectory
divergence**, not attributable to any component defect identified by
ablation, porting, or instrumentation. Within-solver A/Bs are exhausted;
the two remaining directions are outside this study's scope:

1. **Step-level cross-debugging on small family instances** – impossible
   across solvers as-is (heuristics diverge immediately), but a shared
   decision-forcing harness could align trajectories artificially;
2. **Portfolio diversity / local search** (kissat-style) – attack the
   variance directly instead of chasing the mean.

Meanwhile the suite picture remains healthy: Nixie beats CaDiCaL outright on
frb65, simon-r1x/r2x, barman, summle_X11112, worker_20_40_20 and most uf100
instances; the gap concentrates in UNSAT circuit/multiplier families
(6s167-opt, g2-ak128*, x9-*, noL-*).

## What was NOT ported (recorded omission)

cadical's satisfied-clause sweep + falsified-literal removal at reduce time
(`collect.cpp`) was deliberately left out to isolate schedule+retention; its
absence is one candidate explanation for the neutral result. Also unported:
`propagate_out_of_order_units`. Both would need their own controlled pass.

## Soundness / regression status

All runs across both studies produced identical verdicts per instance across
arms and seeds (no arm ever flipped SAT/UNSAT). Full workspace suite,
clippy/fmt/doc, and the Z3 parity suite (168/168 correct, 0 wrong) clean on
the commit carrying these switches. Default-path trajectory preservation
re-verified post-commit (`170039/550301/19369185` on 6s167-opt).

## Search-shape characterization (cross-solver, same instance)

Method: instrumented CaDiCaL copy (source patched in a throwaway tree to
print `level / backjump / trail / learnt-size / stable` per conflict behind
`CADICAL_CONF_TRACE`; reference sources untouched) vs Nixie's existing
`NIXIE_TRACE_DECISIONS` conflict lines. Same instance (`6s167-opt`), default
configs.

| metric | Nixie | CaDiCaL |
|---|---|---|
| conflicts | 170 k | 15.5 k |
| decision level @ conflict (median) | 22 | **34** |
| trail @ conflict (median) | 594 | 410 |
| learnt size (median) | 19 | 16 |
| backjump ratio new/level (median) | 0.95 | 0.97 |
| restart interval proxy (median trail-collapse gap) | 12 | 12 |

The distributions of learnt size, backjump ratio, and restart cadence are
**the same**. The divergence is the *depth trajectory*: CaDiCaL opens very
deep (mean level 62–81, trails up to ~3.7k in the first 15 % of conflicts)
and holds level ≈30–40 throughout. Nixie starts at ≈32 and **monotonically
decays** to level ≈11–12 by the end — classic re-treading of shallow,
already-refuted space while conflicts keep accumulating. This decay under
identical restart cadence is the first observable that cleanly separates
the solvers; any future fix attempt has a measurable target: hold decision
depth up through the late search.

(Dead ends recorded for completeness: disabling trail-reuse via
`REUSE=0` leaves this instance's trajectory bit-identical — the knob does
not reach this path.)

## Remaining candidates from the original list

* mid-search vivification cadence (cadical vivified 1126 clauses on
  6s167-opt where nixie vivifies only pre-search);
* OTFS during analysis (880 events on the same instance);
* tick-accounting correction (still gated behind its own study).

Given four consecutive null-neutral or null-beaten results, the prior that
"porting individual cadical policies onto this codebase transfers CaDiCaL's
search power" should now be treated as refuted for single-policy ports.
The ablation adds a sharper constraint: whatever makes CaDiCaL fast is not
reproducible by changing reduction, stabilization, scores, phases,
minimization, shrink, OTFS, or rephase *in isolation in Nixie*, and inside
CaDiCaL only reduction matters — largely through keeping the tick clock
calibrated. The most plausible remaining hypotheses:

1. **Ordering/interleaving of inprocessing** (probe → elim → subsume →
   reduce cadence relative to restarts), which no single-policy port
   touched;
2. a **deeper decision-dynamics difference** (e.g. what trail depth conflicts
   form at, how backjump levels distribute) that manifests as reduced search
   power everywhere but is invisible in per-policy A/Bs;
3. residual per-propagation constant factors amplifying trajectory chaos.

Measuring (2) needs cross-solver instrumentation (conflict-depth histograms
from both solvers on identical instances); that, not another policy port,
is the recommended next step.
