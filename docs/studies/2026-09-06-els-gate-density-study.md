# Study A (pre-registered): ELS one-shot gated by congruence-gate density

Part of the 2026-09 SAT-core campaign (O3/KR3). Pre-registration written
**before** any A/B measurement; the telemetry rung below is the screen the
ladder requires before a flag-gated A/B is allowed.

## Background

The 2026-09-05 no-gate study fixed the scheduled-ELS bug and measured the
pass enabled-by-default: **6s167-opt 118 191 → 41 280 conflicts (0.349×)**
(the congruence closure finds 4 526 AND gates there), but solved-at-cap
dropped 50 → 41 (nine near-cap files TO). The three seed-robust winners of
the inprocessing bundle (mrpp, FmlaEquivChain, 6s167) are all UNSAT and
yield-heavy; the losers' list is dominated by trajectory reshuffle (mp1,
the 15× "destroyed" file at seed 0, solves *better* under the bundle at
seeds 1–10). Kissat's tail win on 6s167 is the probe-fixpoint structural
collapse (70 % of variables eliminated).

The no-gate study closed the *mid-search round* gate thread (no online
signal separates winners from losers there). It did **not** test static
formula observables for the **ELS one-shot** — specifically the
congruence-gate density, the same signal that carries the 6s167 win.

## Hypothesis

The ELS one-shot is net-positive on instances whose formula is rich in
congruent AND/XOR gate structure (the fold collapses real equivalences)
and net-neutral-to-negative elsewhere (pure reshuffle). The gate count
after parse (`detected_gate_count()`, deterministic, seed-invariant)
separates the two classes well enough that

**treatment = "ELS fires iff gates ≥ K"** beats
**null = "ELS fires iff a content-scrambled scalar crosses the same
threshold, firing on the same number of corpus files"**

on conflicts-to-verdict geomean with no solved-at-cap regression.

## Arms (all CaDiCaL preset, `stats_solve`)

| arm | role | env |
|---|---|---|
| baseline | baseline | (defaults; ELS off) |
| els-all | reference | `ELS=1` |
| gate-K | treatment | `ELS=1 ELS_GATE_SRC=gates ELS_GATE_K=<K>` |
| gate-null | null | `ELS=1 ELS_GATE_SRC=hash ELS_GATE_K=<K'>` |

`ELS_GATE_K` is chosen at the telemetry rung so treatment and null fire on
the **same number of corpus files** (`K'` = the hash-scalar rank that
matches). Both arms run identical code (the harness computes one scalar per
file and a threshold; only the scalar's source differs). The hash scalar is
`sha256(instance)[:8]` as u32 — deterministic, content-derived, carrying no
structural information.

## Metrics and decision rule (pre-registered)

- Primary: paired geomean of `conflicts_to_verdict`, treatment/null over
  files decisive in both arms. **Win = T/N ≤ 0.95 AND solved-at-cap
  (60 s, treatment) ≥ baseline's 50.** Null result = T/N in [0.95, 1.05] or
  solved regression. Loss = T/N > 1.05 → do not land.
- Secondary: solved-at-cap per arm; per-file T/N table for the three
  seed-robust tails (6s167-opt, FmlaEquivChain, mrpp must all fire ELS
  under the treatment gate — if the gate does not fire on them, the gate is
  wrong by construction and the study closes as a telemetry null).
- Seeds: 0–9 (SEED env; CRN where the firing set matches, seed-variance
  elsewhere). 54 corpus files. Counters only (conflicts); wall is sanity.
- Falsification: if the telemetry rung shows no separation (the gate-count
  distribution of ELS winners overlaps the losers'), the study closes as a
  documented null without the A/B — recording that the last plausible
  static observable fails, consistent with the round-gate closure.

## Rung 0 (telemetry, before A/B)

1. `GATE_COUNT=1` per corpus file (one line each).
2. Seed-0 `ELS=1` vs default: conflicts per file, decisive set.
3. Overlap check: gate counts of winners vs losers.

## Result: closed at rung 0 — the observable does not separate (falsified)

Rung 0 ran 2026-09-06, corpus `/tmp/sc24f` (54 files), `GATE_COUNT=1`
(deterministic, seed-invariant):

| class | file | gates |
|---|---|---|
| ELS seed-robust winner | 6s167-opt | 4 507 |
| ELS seed-robust winner | FmlaEquivChain_4_6_6 | **0** |
| ELS seed-robust winner | mrpp_4x4 | **0** |
| ELS loser (TO at 900 s under the bundle) | 64_25 | **4 073 145** |
| ELS loser | mp1-klieber2017s | 30 563 |
| near-cap losers/noise | g2-ak128 (×2), g2-slp, summle (×3), shuffling-2, j3037 (×2), simon (×3) | 764–571 244 |

The pre-registered secondary criterion — "the gate must fire on the three
seed-robust tails (6s167-opt, FmlaEquivChain, mrpp); if not, the gate is
wrong by construction" — **fails for any threshold**: two of the three
winners have **zero** congruence gates (their equivalences live in the
binary-implication SCC structure the ELS itself computes — FmlaEquivChain
is an equivalence chain by construction), while the biggest loser has the
corpus's highest gate count (4 M). The gate-density distribution of
winners and losers is not merely overlapping, it is inverted.

**Verdict: null, closed at the telemetry rung per the pre-registered
falsification criterion.** The A/B (treatment `gates ≥ K` vs matched null
`hash ≥ K'`) was not run: the registered go condition (observable
separation) does not hold, and running an A/B on a gate that provably
excludes two of three winners and includes the largest loser would only
measure a known-wrong policy. This closes the last *static* observable
candidate for ELS gating, consistent with the 2026-09-05 no-gate study's
closure of the *online* observables: ELS's win/loss split is not
predictable from formula shape, congruence density, round cost, yield, or
DB shape. Any future ELS work must either accept the corpus-level
trade-off (−9 files at cap) or find a *different mechanism* (e.g.
preserving the search state across the round), not a gate.

The study's incidental contribution: the `ELS_GATE_SRC`/`ELS_GATE_K`
harness knobs and `set_enable_equiv_substitution` accessor remain for
future gating candidates; the gate-count telemetry is one `GATE_COUNT=1`
run away.
