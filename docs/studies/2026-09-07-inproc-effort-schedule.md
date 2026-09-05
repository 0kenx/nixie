# Inprocessing effort schedule: cadical `SET_EFFORT_LIMIT` for the mid-search rounds (2026-09-07, pre-registered)

Follow-up to `2026-09-04-inprocessing-standing-corpus.md`.  That study measured
the mid-search inprocessing bundle as a **1.4–5.7× conflicts-to-verdict win on
the clause-DB-heavy tail** (6s167 0.56×, FmlaEquivChain 0.345×, mrpp 0.531× at
10 seeds) and a **no-go as a default** (9 files sat→TO; corpus on/off geomean
1.44×).  Its decomposition attributed the losses to cap-burning inside the
rounds' own propagation work, and left "a gating policy for the rounds" as the
open lever.  This study replaces the gating-policy idea with the reference
solvers' actual mechanism.

## What the references do (read before designing)

cadical `limit.hpp SET_EFFORT_LIMIT`: **every** inprocessing pass gets
`effort‰ × (search work since that pass's last run)`, and is **skipped
entirely** when the allowance is below `thresh × clauses` (kimits: probe 8‰,
vivify 50‰/thresh 20, subsume 1000‰, factor 50‰).  Round interval
`inprobe.cpp`: `25 × inprobeint × log10(rounds + 9)` conflicts — log-growing,
not flat.  kissat `kimits.h` is the same shape (effort-per-mille windows,
`probeint × nlogn × size-factor`).

Our port before this study: flat `inprocessing_interval = 4000` conflicts
forever, and **absolute** budgets — vivify 10M props **per round** (measured:
g2-slp spends 5–9M round props against ~2.9M search props per interval; the
rounds cost 0.4–3.6× the search work between them, vs the references' 5–100‰).
No skip threshold anywhere.

## Treatment (implemented, env-gated, default off = bit-identical legacy path)

`NIXIE_INPROC_SCHED=1` + `INPROCESS=1`:

1. **Interval growth**: `interval × log10(rounds + 9)` (cadical form; base =
   the configured 4000).
2. **Round window**: search propagation since the last round's end
   (`inproc_search_props_mark`); round-internal propagation is excluded via
   `inproc_round_props_total`, so the window is pure search work.
3. **Pass budgets** (cadical constants): vivify `50‰ × window`, **skipped**
   when below `20 × live clauses` (`vivifythresh`); subsume checks
   `cumulative-search-props` clamped `[1e6, 1e9]` (`subsumeeffort` 1000‰);
   transred `100‰ × window` steps (`transredeffort`).
4. `NIXIE_INPROC_VIVON=1` disables the vivify skip (τ=0 arm): vivify still
   budget-bound, never threshold-skipped.

Per-pass cost/yield attribution added to `NIXIE_INPROC_TRACE` (propagation per
pass; the old trace attributed only yield, and `shr` counts conflict-side
minimization, not vivify — vivify's cost was invisible).

### Matched null (lag-2 window scramble)

`NIXIE_INPROC_SCHED_NULL=1` (implies the schedule): round `r` is budgeted from
the window observed at round `r−2` instead of round `r`'s true window
(`inproc_window_ring`).  Identical budget magnitudes, timing, code paths and
round counts; the *correlation* between "work since the last round" and "this
round's budget" is severed.  Windows on this corpus vary 2–3× across adjacent
rounds, so the null genuinely perturbs.  Rounds without two predecessors use
their true window.

## Screening (default seed, conflicts-to-verdict; NOT the decision measurement)

| file | off | sched (τ=20) | sched+τ0 | flat bundle (2026-09-04) |
|---|---|---|---|---|
| 6s167-opt | 118 191 | 87 900 (0.74) | **72 288 (0.61)** | 82 063 |
| FmlaEquivChain | 2 147 581 | **419 157 (0.195)** | 844 540 (0.39) | ~375 k |
| g2-slp | 344 655 | **134 715 (0.39)** | TO | TO (loser) |
| worker_550 | 106 143 | 55 320 (0.52) | **28 320 (0.27)** | 0.36× |
| shuffling-2-s25 | 23 130 | 15 021 (0.65) | **8 950 (0.39)** | 0.27× |
| summle_X4044 | 62 927 | 82 399 (1.31) | **11 212 (0.18)** | 0.38× |
| noL-11-14 | 1 673 202 | TO | **1 072 731 (0.64)** | TO (loser) |
| mrpp_4x4 | 249 027 | 234 680 (0.94) | **167 804 (0.67)** | 106 k (0.43×) |
| x9-09054 | 249 455 | **93 368 (0.37)** | 619 692 (2.5×) | 0.25× |
| qwh.50 | 134 048 | **130 737 (0.98)** | 280 087 (2.1×) | 0.37× |
| 170058440 | TO | TO | **Sat @ 2 247 600** | TO |
| Timetable_C_392 | 32 841 | TO | TO | TO (loser) |
| 64_25 | 4 500 | 4 638 | TO | TO (loser) |
| rbsat | 305 112 | TO | 724 302 (2.4×) | TO (loser) |
| mp1-Nb7T42 | 106 295 | 631 118 | 191 690 | TO (loser) |

Round cost collapsed 100–1000× (g2-slp 5–9M → ~5k props/round; crypto1
~300k → ~60) with subsumption yield preserved.  **No observable separates the
τ=0 winners from the τ=0 losers** (DB size, window ratio, SAT/UNSAT all mix) —
the split is chaos-dominated, consistent with the 2026-08 rephase study's
null-beats-signal finding at decision points of this kind.

`Timetable` root-caused during screening: any single round — even zero-yield,
zero-prop (interval 8 000/20 000/50 000, probing off) — re-rolls its
walk-solved trajectory (off solves via walk #2's phase descent at 33 k
conflicts; the round's root backtrack is trajectory-identical in shape to a
restart, and restarts already interrupt descents every ~23 conflicts there).
It is a variance file, not a mechanism casualty: 64_25 (22.6 M clauses) is the
same class — off's 4.5 k-conflict solve is lucky, any round re-rolls it.

## Arms (decision measurement)

| arm | env | role |
|---|---|---|
| `off` | (env-unset) | baseline — must reproduce stored `aa293fc` cells bit-exactly (identity gate) |
| `sched` | `INPROCESS=1 NIXIE_INPROC_SCHED=1` | treatment (cadical-literal τ=20) |
| `sched-vivon` | `INPROCESS=1 NIXIE_INPROC_SCHED=1 NIXIE_INPROC_VIVON=1` | treatment variant (τ=0) |
| `schednull` | `INPROCESS=1 NIXIE_INPROC_SCHED_NULL=1` | matched null (lag-2) |

- 54-file corpus (`precompile/corpus-sc24f/`), default seed, serial, pinned
  core, 60 s wall cap (scoring only).  Primary metric conflicts-to-verdict;
  propagations-to-verdict secondary; solved-at-cap + flip lists reported.
- 10-seed tails (1..10, `SEED=`, CRN): the 6 measured winners (6s167, FEC,
  worker_550, noL-11-14, mrpp, summle) and the 4 re-rolled losers (Timetable,
  64_25, rbsat, g2-slp), both treatment arms.
- Null arm on the better-geomean treatment arm, over the tails (T/N).

## Go / no-go (pre-registered)

- **Go (default-on landing candidate: enable_inprocessing = true in the
  CaDiCaL preset with the effort schedule as the mid-search behavior):**
  corpus geomean ≤ **0.95** vs off AND solved-at-60s ≥ **50/54** AND T/N ≤
  1.05 AND ≥ 2/3 of winner-tail medians ≤ 0.95 AND parity/differential clean
  at the new default.
- **Neutral**: geomean in (0.95, 1.05] — report, no landing.
- **No-go**: geomean > 1.05 or solved < 50/54 — negative result documented
  here with per-family data; the schedule stays env-gated default-off.

Falsification: apparent wins living only on high-variance files (§6), or
inverting at fresh seeds, or solved-at-cap losses — trajectory reshuffle, not
effect.  A geomean win with a score loss is **not** landable at default, but
the negative result must name the flip list and its seed-stability.

## Results

### Corpus (54 files, default seed, serial pinned core 3, 60 s cap)

All 162 cells recorded (suite `sc24f-effort`, sha `5ca1eaf`, binary sha256
`35b78fedf929cc0f…`); verdicts differentially verified across arms, 0
verdict disagreements.

**Identity gate**: the `off` arm reproduces the stored standing-table cells
(0223f8e suite) — 36/36 decisive cells conflicts-bit-identical, 0 mismatches
(the other 18 stored cells are concurrent-layout TOs, not comparable).  The
default binary is trajectory-identical to the shipped baseline.

| arm | solved / 54 | conflicts geomean vs off (both-decisive, n=31) | sat / unsat split |
|---|---|---|---|
| off | **50** | 1.00× | — |
| sched (τ=20) | 44 | 0.972× | 1.065× (n=22) / **0.779×** (n=9) |
| sched-vivon (τ=0) | 44 | 0.979× | 1.059× (n=22) / **0.809×** (n=9) |

The geomeans sit **inside the ±5 % neutrality band** (and miss the ≤ 0.95 go
bar); the solved-at-cap bar (≥ 50/54) fails outright — **6 sat→TO flips per
arm, 0 gains**:

* sched loses: mp1-klieber, Timetable, noL-11-14, af-synthesis, frb65-12-2,
  rbsat.
* sched-vivon loses: mp1-klieber, Timetable, pb_300_09, g2-slp, crypto1,
  64_25.
* **Every loss is a SAT file the off-arm solves by a short lucky trajectory**
  (walk descent or early model); the flip sets differ between arms with no
  observable separating winners from losers — the τ-split screening found the
  same wall (DB size, window ratio, SAT/UNSAT all mix).

The per-family structure is consistent and real: **UNSAT-family 0.78–0.81×**
(refutation benefits from the maintained clause DB — 6s167 0.74×, FEC 0.195×,
  x9-09054 0.37×, worker 0.52×), **SAT-family 1.06×** (model-finding files pay
for rounds that cannot help them).  This is the same split the 2026-09-04
study measured for the flat bundle, now with round cost no longer a
confounder: the 100–1000× round-cost collapse did not rescue the SAT side —
the harm is the rounds' trajectory perturbation, not their cost.

**Verdict: no-go per the pre-registered rule** (solved < 50/54; geomean in
the neutral band).  The schedule stays env-gated, default off.  What the
study did establish as reusable: the cost/yield attribution telemetry, the
budget plumbing (window marks, per-pass budgets), the cadical-faithful round
shape, and the measured fact that **the mid-search inprocessing lever is a
refutation-side lever on this corpus** — its wins and losses are verdict-class
correlated, which any future gating policy must respect.

### Tails (10 seeds winners / 5 seeds losers, CRN, 330 cells recorded)

| file | off med | sched med | vivon med | null med | T/N paired | sched/off | vivon/off | TOs (o/s/v/n) |
|---|---|---|---|---|---|---|---|---|
| 6s167-opt | 123 801 | 86 992 | 78 437 | 56 562 | **1.546** | 0.662 | 0.628 | 0/0/0/0 |
| FmlaEquivChain | 1 250 207 | 576 547 | 671 844 | 511 718 | **1.371** | 0.494 | 0.461 | 0/0/0/0 |
| worker_550 | 50 870 | 17 996 | 15 155 | 45 734 | **0.746** | 0.585 | 0.470 | 0/0/1/2 |
| summle_X4044 | 81 122 | 67 458 | 79 275 | 75 768 | **0.781** | 0.694 | 0.855 | 0/0/0/0 |
| mrpp_4x4 | 275 267 | 243 154 | 201 547 | 154 664 | **1.670** | 1.015 | 0.803 | 0/0/0/0 |
| noL-11-14 | 2 851 084 | TO 10/10 | 1 723 271 | 815 582 | — | — | — | 9/10/9/8 |
| Timetable_C_392 | 458 262 | TO 5/5 | TO 5/5 | — | — | — | — | 2/5/5/– |
| af-synthesis | 397 619 | 210 605 | 145 163 | — | — | 0.464 | 0.340 | 1/0/2/– |
| frb65-12-2 | 349 098 | 679 071 | 294 722 | — | — | 3.622 | 0.537 | 1/0/0/– |
| g2-slp | 414 236 | 387 143 | 336 822 | — | — | 0.867 | 0.712 | 2/1/0/– |
| rbsat | TO 5/5 | 321 902 | 824 606 | — | — | — | — | 5/2/4/– |
| 64_25 | 8 315 | 4 746 | TO 5/5 | — | — | 0.932 | — | 0/4/5/– |

Three findings the tails add beyond the corpus row:

1. **The corpus flip list was substantially seed-luck, in both directions.**
   `off` itself TOs 2–9 of 5–10 seeds on six of the "lost" files
   (Timetable's default-seed solve of 33 k sits 14× below its 458 k
   median; rbsat TOs 5/5 under `off` while `sched` solves it 3/5; g2-slp
   and af-synthesis, corpus "losers", are 0.71×/0.46× WINS for `vivon`
   across seeds).  Per §11.1 the flip *list* is the evidence: the only
   seed-robust systematic loss is **Timetable (TO 5/5 under both
   treatments)**; noL-11-14 is a borderline file in every arm (off TOs it
   9/10).  A single-seed 44-vs-50 corpus score is not a P(solve)
   statement — the definitive score experiment is the pre-registered
   multi-seed corpus below.
2. **The tail WINS are seed-robust and large**: 6s167 0.63–0.66×, FEC
   0.46–0.49×, worker 0.47–0.59×, af-synthesis 0.34–0.46×, frb65-vivon
   0.54×, g2-slp-vivon 0.71× — every one wins at every paired seed.
3. **T/N (reactivity) is negative**: 1.546 / 1.371 / 1.670 vs 0.781 /
   0.746, aggregate ≈ **1.156** — the lag-2 scrambled window beats the
   reactive window on 3 of 5 anchors, and the null's medians are the best
   of all arms on 4 of 6.  The *reactivity* (budget ∝ work since the last
   round) carries no positive signal — whatever value the schedule has
   lives in the budget LEVEL (rounds bounded to a small share of search)
   and the interval growth, not in tracking the window.  This joins the
   repo's matched-null-beats-treatment series (random deletion vs glue
   ranking, random rephase vs action selection).

### Verdict

**No-go per the pre-registered rule** (corpus solved 44 < 50; geomean
0.972/0.979 inside the ±5 % band).  The effort schedule stays env-gated,
default off.  Landed as reusable infrastructure: the window/budget plumbing,
the per-pass cost attribution telemetry, and the measured decomposition —
mid-search inprocessing on this corpus is a **refutation-side lever**
(UNSAT-family 0.78–0.81×, seed-robust) whose harm concentrates on
walk-luck SAT trajectories; round cost was exonerated (100–1000× collapse
changed nothing about the SAT side).

Context: kissat runs its full inprocessing pipeline on these same files
(Timetable: 4 probings, 2 eliminations, backbone/factor/kitten sweeps) and
solves them — the fragility is our search's dependence on lucky
walk/descent trajectories, not inprocessing per se.

### Open follow-ups (pre-registered next steps)

1. **Multi-seed corpus P(solve) run** (54 × {off, sched-vivon} × 5 seeds,
   ≈ 540 cells): the single-seed corpus score bar measured luck on
   seed-unstable files; the tails show the flip set collapsing to
   ~1 systematic loss (Timetable).  Go bar: paired P(solve) not lower
   than off AND conflicts geomean ≤ 0.95 over both-solved.
2. **Flat-budget variant**: T/N ≈ 1.16 says drop the window reactivity —
   budget = fixed per-mille of a long-horizon EMA, cadical's tier-scheduled
   vivify (glue-weighted candidate selection, per-tier budgets) as the
   faithful shape.
3. **The 3.7× learned-clause-usage residue on 6s167** (kissat reuses each
   learned clause 5.8×) remains the largest untouched structural gap —
   tier-structured retention (core/tier1/tier2 by glue with `used`
   promotion) is the untested shape; the 2026-09-02 signal studies tested
   ranking-within-cadical-reduce, not kissat's tier structure.

   **Follow-up #3 screen (same day — closed at the telemetry rung):** the
   `NIXIE_KISSAT_REDUCE` arm implements exactly that shape on top of the
   cadical-reduce port — per-mode used-by-glue histogram (kissat
   `statistics.used[mode].glue[glue]`, bumped at the analysis-use site),
   dynamic tier bounds at the 50 %/90 % usage quantiles (kissat `tiers.c`,
   fallbacks 2/6), deletion fraction growing 50 %→90 % with the reduction
   count (kissat `reducelow`/`reducehigh`), rank unchanged
   (glue desc, size desc). Identity-verified (env-unset bit-identical),
   landed as opt-in infrastructure.  Screen (default seed + seeds 1–3,
   attribution evidence, not store-recorded effect claims): 6s167 ~1.0×,
   FmlaEquivChain **1.3× worse at every seed** (the default-seed 0.55× was
   luck), mrpp wash-to-worse, worker 0.27–0.49× at two of three seeds (the
   third compared against a 2.4 k-conflict off-fluke).  No file class
   benefits consistently → the retention-*shape* lever joins the
   retention-*signal* nulls: the usage residue is not closed by keep-rule
   geometry. What remains untried for it: candidate-selection differences
   in what gets *learned* (kissat's focused-mode watcher/burning policy) —
   search-side, not retention-side.
