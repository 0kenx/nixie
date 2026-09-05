# Study B (pre-registered): walk warmup — closing the cadical parity gap

Part of the 2026-09 SAT-core campaign (O3/KR3). Pre-registration written
**before** any A/B measurement.

## Background

CaDiCaL's `walk.cpp` runs a propagation-based **warmup** before every walk
round (`options.hpp`: `OPTION(warmup, 1, 0, 1, ...)`, default **on** —
"warmup before walk using propagation"): decide + propagate to a full
assignment *ignoring conflicts*, seed the saved phases with it, then let
the ProbSAT round start from a propagation-consistent assignment. Nixie's
walk port implements the mechanism (`solver/walk.rs::warmup`, wired to
`config.walk_warmup`) but ships it **default-off** (env `NIXIE_WARMUP`
opt-in). This is a straight parity gap with the parity source.

The walk's value shows on the corpus's sat-side and near-cap files (the
2026-09-05 memory study's standing runs have 4 walk rounds on worker_550
finding a model in round 1). Local search seeded from
propagation-consistent phases should reach fewer-broken assignments faster
on chain-like structure (the warmup's claim to work).

## Hypothesis

Warmup-on (cadical parity) reduces conflicts-to-verdict on walk-active
files at equal or better solved-at-cap, versus both the default (off) and
a matched null that runs the identical warmup pass but **scrambles the
semantic content** of what it writes (every written phase bit inverted —
same pass, same work, same schedule, same RNG stream, information
destroyed).

## Arms (all CaDiCaL preset, `stats_solve`)

| arm | role | env |
|---|---|---|
| off | baseline | (defaults) |
| warmup | treatment | `NIXIE_WARMUP=1` |
| warmup-null | null | `NIXIE_WARMUP=1 NIXIE_WARMUP_NULL=1` |

The null needs one flag-gated line in `warmup()` (invert the phase bits
the pass just wrote); the treatment needs none (knob exists). Neither
changes the RNG stream (warmup consumes no draws; inversion consumes none).

## Metrics and decision rule (pre-registered)

- Primary: paired geomean `conflicts_to_verdict`, treatment/null over
  files decisive in both arms. **Win = T/N ≤ 0.95 AND solved-at-cap
  (treatment) ≥ baseline's.** Neutral = T/N ∈ [0.95, 1.05] → document,
  keep default off (or flip only if also cadical-parity-motivated and
  solved-at-cap is strictly not worse *and* T/N ≤ 1.0). Loss = T/N > 1.05
  or solved regression → document, keep off.
- Secondary: walk counters (rounds, flips, minimum), solved-at-cap,
  seed-0..9 (10 seeds), 54 corpus files, 60 s cap. Counters primary; wall
  sanity only.
- Falsification: if warmup shows no effect at all at seed 0 on every file
  (identical conflicts), the wiring is dead — fix or close.

## Rung 0 (telemetry, before A/B)

1. Seed-0 `NIXIE_WARMUP=1` vs default: conflicts + walk counters per file.
2. Confirm the warmup actually runs (walk_counters warmups > 0) and changes
   trajectories where it fires.

## Result: null — the semantic content provably does nothing (T/N = 1.0000×)

Rung 0 (seed 0, 54 files, 60 s cap): warmup ran on 20 files (walk rounds
present) and changed trajectories on 25 files — the wiring is live. But
the treatment and the matched null produced **bit-identical conflict
counts on 53/54 files** (the 54th: `j3037_10_mdd_b`, where the treatment
TO'd and the null solved — TO-censoring, not a content effect).

Full pre-registered A/B (10 seeds × 54 files × 4 arms, counters only;
sweep on 11 pinned cores, load-safe metrics):

| arm | solved / 540 runs | per-seed solved (min–max) |
|---|---|---|
| off (baseline) | 391 | 37–41 |
| warmup (treatment) | 395 | 35–41 |
| warmup-null (null) | 394 | 38–41 |
| els (reference arm, see study A) | 396 | 36–43 |

- **Geomean null/treatment over 250 both-solved pairs: 1.0000×** — the
  inverted-phase null is the treatment, bit-for-bit, wherever both decide.
- Geomean warmup/off over 219 pairs: 0.9687× (inside the ±5 % neutrality
  band) — and since the null shows the phase content carries nothing, this
  3 % is the pass's *schedule* side effects (the warmup's ignored-conflict
  propagation bumps counters/scores — a tick-accounting change, BENCHMARKING
  §10.4), not the claimed mechanism.
- The seed-0 ±9 verdict-move split (frb65/64_25/FmlaEquiv/shuffling win,
  mp1/Timetable/stable-300 lose) is textbook trajectory reshuffle: frb65
  wins at seeds {0,6,9} and *loses* at {1,2,4,5}; af-synthesis wins at 5
  seeds and loses at 2; mp1 splits 2/2. No file's move is seed-robust in
  either direction.

**Verdict: documented null. The pre-registered win condition (T/N ≤ 0.95
with no solved-at-cap regression) fails at T/N = 1.0000. The walk-warmup
default stays OFF** — cadical-parity alone does not justify a knob whose
measured information content is zero on this corpus; the pass is available
as `NIXIE_WARMUP=1` for any corpus where propagation-seeded phases plausibly
matter.

### Incidental: the ELS reference arm, seed-robustified

The same sweep's `ELS=1` arm re-tests the 2026-09-05 single-seed screen
(then: −9 files at cap): across 10 seeds ELS-on measures **396 vs 391
solved** (means 39.6 vs 39.1, per-seed ranges 36–43 vs 37–41 — inside
seed noise) with conflicts geomean **0.9525×** over 244 pairs. The −9
loss does not replicate; `64_25` is the one consistent ELS loser
(Sat→TO at all five decisive seeds). ELS stays default-off: the corpus-level
trade-off is neutral-to-slightly-positive on conflicts, well inside the
reshuffle envelope, and study A's gate thread is closed.
