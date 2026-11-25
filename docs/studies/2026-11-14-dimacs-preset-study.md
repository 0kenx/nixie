# DIMACS preset study: `default` vs `aggressive` (2026-11-14, HEAD `992d81e7`)

Scan #4 item 3.  **Pre-registered** (script `/tmp/preset_study.sh`, protocol
in chat log): 23 jointly-solvable CNF instances (satcomp2024/2025 + SATLIB
uuf250, pre-filtered at 15 s), 2 presets × 10 fixed seeds (`NIXIE_SAT_SEED`
1..10), serialized CPU 18, one rep per cell, 20 s cap.  GO bar: geomean
aggressive/default wall ≤ 0.95 with ≥ 8/23 instances better and none worse
than 1.10×.  Falsification: any verdict disagreement.

## Result: NO-GO (default stands)

- **Geomean aggressive/default = 1.265×** (aggressive WORSE).
- 9/23 instances worse than 1.10× (worst 6.71×: `6s299b685_Iter22`),
  7/23 better than 0.95×.  Zero verdict disagreements.
- The scan-4 trigger was single-trajectory noise: `x9-07092.sat`'s own
  seed spread at the DEFAULT preset is **27×** (0.12 .. 3.22 s) – the
  observed 1.8× "win" of aggressive on one seed is indistinguishable from
  reseeding, exactly the failure mode `docs/BENCHMARKING.md` documents
  (seed-only moves aggregate cost 7.31× on this repo's benchmarks).
- Counters were not captured (the DIMACS fast path prints stats only under
  the `--stats` flag, not the `STATS` env); wall medians over 10 seeds are
  the recorded metric – sufficient for a NO-GO at this effect size.

Raw cells: `docs/studies/data/preset-study/cells.tsv`.
