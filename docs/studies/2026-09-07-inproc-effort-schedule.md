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

(to be filled from the recorded runs; store: suite `sc24f-effort` at this sha)
