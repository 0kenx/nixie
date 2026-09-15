# 3-way perf benchmark: nixie vs kissat vs z3 on SATCOMP 2025 (2026-09-15)

One-off cross-solver standing measurement (not a heuristic A/B — no matched
null required; verdict parity is the soundness canary here).

## Corpus

SAT Competition 2025 Main Track (non-incremental), re-downloaded from the
Global Benchmark Database (`benchmark-database.de`, `track=main_2025`) —
400 CNF instances, 5.1 GB `.cnf.xz`, decompressed to 53 GB under
`satcomp2025/main_2025/` (see its `PROVENANCE.md`). The historical
`main_easy_mid` slice had been deleted; this is the full superset.

## Selection

Seed-42 Fisher–Yates shuffle of the 400 files; kissat 4.0.4 prescreen at a
30 s wall cap (6-way, pinned to P-cores) until 30 solved. **138 files were
scanned to yield the first 30 kissat-solvable instances** (14 SAT / 16 UNSAT,
kissat CPU 0.00–26 s). Picked list: `picked.txt` in the result store.

## Runs

All 30 × 3 solver runs **sequential**, pinned to P-cores 0–7, 60 s wall cap
(`timeout -k 5`), `perf stat` cycles/instructions/task-clock + `/usr/bin/time -v`
(user/sys CPU, peak RSS). Harness: `bench.py` in the result store.

- kissat 4.0.4 (`../temp/kissat/build/kissat`)
- z3 4.16.0 (`/run/current-system/sw/bin/z3`)
- nixie @ `5bf4d1a1` (`precompile/5bf4d1a1/nixie --dimacs`, shipped CLI
  default SAT config: `SolverConfig::default()` + `enable_inprocessing: true`)

Machine: Intel Core Ultra 7 265K (8P+12E), load ≈ 19 from other agents —
wall-clock is contaminated; cycles/task-clock are the load-independent
numbers. Machine was also 84% disk-full with active I/O.

## Results

| | kissat | z3 | nixie |
|---|---|---|---|
| solved / 30 (60 s cap) | **30** | 18 | 16 |
| solved / 30 (30 s) | 30 | 17 | 14 |
| verdict mismatches vs kissat | — | **0** | **0** |
| Σ cycles on 14 common-solved (G) | **51.9** | 136.2 | 403.9 |
| geomean wall on 14 common-solved (s) | 0.16 | 0.28 | 0.42 |
| peak RSS on solved runs (MB) | 5019 | 2667 | 7062 |

On the 14 instances all three solve, cost ratios vs kissat: **z3 2.6×,
nixie 7.8×** total cycles. Per-instance nixie/kissat wall spread 0.15×–181×
(nixie wins exactly one instance, `Carry_Bits_Fast_19`, 0.18 s vs 1.18 s —
pre-search/lucky-phase hit). The arles_thres10 family is trivial for all
three (< 0.05 s) and drags the geomean down; the cycle totals are the more
honest aggregate.

The 60 s-cap losses are the known standing-gap profile (studies/
2026-08-satcomp-standing-gap.md): uniform search-power deficit, no
mismatch anywhere — every solved verdict agrees with kissat.

## Two nixie CLI defects found while setting this up — FIXED in `cd544511`

1. **`--preset` silently ignored unknown names.** `apply_preset`
   (nixie-cli/src/main.rs) had `_ => { // Unknown preset, ignore }` —
   `nixie --dimacs --preset bogus` ran happily. Now rejected at startup
   with the valid names listed.
2. **`--preset` was not wired into the CNF fast path at all.** The DIMACS
   path (processor.rs) built `SolverConfig::default() + inprocessing`
   regardless of `--preset`, so `--preset cadical` was a no-op on CNF
   input. `cd544511` wires SAT-core preset names to their `ConfigPreset`
   config verbatim, rejects cross-domain presets per-file (no silent
   no-ops), and makes per-file errors visible on stderr. The stale
   "BVE disabled in every preset" comment was corrected (BVE is on in the
   CaDiCaL preset since `0ed8543`, after the 2026-08-17 fix); the
   `summle_X4044` false-UNSAT reproducer is guarded through the CLI path
   (`sat` in 46 s under `--preset cadical`).

## Follow-up: nixie `--preset cadical` arm (post-fix, `cd544511`)

Same 30 instances, same protocol (sequential, P-cores, 60 s cap, perf
stat), nixie now actually running the CaDiCaL preset — the configuration
the standing table measures. Result store:
`precompile/cd544511/benchmark/satcomp2025-cadical-arm/`.

| | nixie default (`5bf4d1a1`) | nixie `--preset cadical` (`cd544511`) |
|---|---|---|
| solved / 30 (60 s) | 16 | **17** (strict superset) |
| solved / 30 (30 s) | 14 | 14 |
| verdict mismatches | 0 | **0** |
| Σ cycles, 16 common-solved | 568.0 G | **489.3 G** (0.86×) |
| geomean wall, 16 common-solved | 0.74 s | 0.90 s (load-19 wall; cycles preferred) |

`--preset cadical` gains `Break_12_30.xml` (56.9 s, default TOs) and loses
nothing; on the commonly solved set it burns ~14 % fewer cycles. The 30 s
bar is unchanged — the win is tail-side, consistent with the preset's
inprocessing schedule paying off on longer runs.

## Verdict

kissat ≫ z3 > nixie on SATCOMP 2025 main-track easy/mid slice; nixie is
~3× z3 in cycles on the common set and solves 16/30 (default) / 17/30
(`--preset cadical`, now reachable from the CLI) vs kissat's 30/30.
Result store: `precompile/5bf4d1a1/benchmark/satcomp2025-3way/`
(results.tsv, prescreen.tsv, per-run logs, harness scripts); cadical arm:
`precompile/cd544511/benchmark/satcomp2025-cadical-arm/`.
