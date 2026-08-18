# Probe scheduling (cadical root/rank selection): infrastructure landed, ranking signal rejected (2026-08-18)

## Question

Our pre-search failed-literal probing (behind `INPROCESS`) walked every
variable by index and probed both polarities. CaDiCaL probes binary-
implication-graph **roots**, ranked by negated-occurrence count, with
`propfixed` memoization and mid-search interleaving on a conflict budget
(`probe.cpp`). Does adopting the cadical selection discipline improve
instructions-to-verdict?

## What was implemented (kept, off by default — sound infrastructure)

`solver/probe.rs`: `probe_round` schedules roots exactly as cadical's
`generate_probes` (one-polarity-only binary occurrences; probe the
polarity occurring negatively; rank by `noccs(¬probe)` descending), with
`propfixed` memoization (skip re-probing until new level-0 facts), failed
literals forced to units, and hyper-binary derivation on success. Wired as
`inprobing()` into the conflict handler before elimination (cadical loop
order), re-arming on the `25·interval·log10(rounds+9)` schedule. The old
brute-force `failed_literal_probing`/`probe_hyper_binary` remain (pre-search
path, flag-gated as before).

A matched-null switch ships with it: `OXIZ_PROBE_NULL=1` reverses the rank
order (same roots, same schedule, same budgets — only the semantic content
under test, best-first ordering, is destroyed).

## Experiment

54 files (cadical<5s corpus minus Simon-family instant solves) × 8 seeds ×
2 arms, CRN-paired, metric instructions-to-verdict (wall-clock invalid:
foreign load 5-18 during the window). 429 valid cells.

**Result: geomean(treatment/null) = 1.0091** — the treatment *loses* to its
own null by 0.9%, despite winning 325/429 cells (wins small, losses large —
the noise signature). Per-file: one real win (ak128booth 0.767), one real
loss (ITC2021_Early_3 1.529), everything else within ±7%.

Verdict per docs/BENCHMARKING.md §2: **ratio > 1 ⇒ nothing**. The
best-first root ranking carries no detectable signal on this corpus at this
power. Do not tune parameters against this measurement.

## What the controls caught along the way (recorded so they are not repeated)

1. **Phantom false-UNSAT from a stale binary**: an early single-file sweep
   reported `noL-11-14` UNSAT under the treatment (SAT per CaDiCaL). It did
   not reproduce on the freshly-built binary (5× timeout, no verdict) and
   6k differential-fuzz iterations across the probing variants were clean.
   Root cause: a `grep -cE "^error"` whose zero-match exit code short-
   circuited `&&` and masked a failed rebuild — the same trap noted twice
   before in this repo's history. `touch src/main.rs && cargo build 2>&1 |
   tail -1` before any verdict-bearing run.
2. **`env` cannot appear as an argv element under `perf stat`** (perf execs
   it as a path): the paired-harness reported `rc1/<not counted>` until env
   was threaded via `subprocess(env=...)`.
3. Fixed-conflict and wall metrics remain invalid for trajectory-diverging
   changes (re-confirmed: +53% phantom at 100k fixed conflicts).

## What is still open (the actual decisions/conflict term)

The 4.5× decisions-per-conflict gap vs cadical is *not* closed by probe
selection. Remaining hypotheses, in order of expected leverage:

1. **Elimination-as-default re-measure**: the treatment's per-file wins
   concentrate exactly where elimination pays (6s167-family). With probing
   infrastructure in place, re-run the elimination-as-default suite
   experiment (was net-negative pre-probing: 53/94 above 1.5×).
2. **Hyper-binary quality**: our HBR derives ≤64 binaries/probe with a
   fresh-clause cap; cadical's dominator/LCA analysis derives the *backbone*
   implications. This is a different lever than ranking.
3. **Equivalent-literal interleaving** (`decompose`/`sweep`-class passes):
   cadical's ELS runs inside `inprobe`; ours is pre-search-only.
