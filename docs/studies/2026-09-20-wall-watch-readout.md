# Wall-watch readout: the third snapshot's time dimension (fragile solves, hidden regressions, noise)

**Date:** 2026-09-20 (fourth continuation, by explicit directive: watch
wall, not only solved counts).  Method note per `docs/BENCHMARKING.md`:
wall here is a *secondary observation* over the calm-load snapshot's own
pairwise-sequential runs (both solvers ran in one table pass, same box),
cross-checked against the deterministic conflict counters before any
conclusion is drawn — counters decide "real vs noise", wall decides
"fragile vs solid".

## The health datum

**Both-solved median wall ratio nixie/z3 = 0.64** (n=78) — on cells both
solvers decide, nixie is typically *faster*.  The gap lives entirely in
the unsolved tail, not in per-solve slowness.

## Fragile solves (nixie wall > 4 s under the 10 s cap)

| cell | wall | conflicts | z3 |
|---|---|---|---|
| `Sage2/bench_16217` | 9 941 ms | 39 860 | unsat, 1 067 ms, **0 conflicts** |
| `Sage2/bench_11463` | 6 462 ms | 11 398 | timeout |
| `Sage2/bench_3238` | 4 128 ms | 93 517 | timeout |

`bench_16217` is one load spike from re-timing-out.  Its residual was
dumped (`NIXIE_BV_DUMP_PRE`): 1 242 assertions of deeply nested
`bvadd`/`bvmul` chains over concat-wrapped terms — **z3's own plain
`simplify` also leaves ~159 atoms there**; the 0-conflict closer is its
full qfbv cascade (`solve-eqs` + `propagate-values` + `elim-uncnstr` +
blast), i.e. a *tactic-pipeline* gap, not a single missing rewrite rule.
Owning route: port the cascade's pre-blast stages (the biggest single
lever is `solve-eqs`-style Gaussian elimination over the `T4@k = concat
(T1@k+3..k)` definition equalities the SAGE family asserts by the
thousand).  This cell and `bench_2780` (~4.4 s user, load-borderline)
are that route's pins.

## Hidden regressions inside "solved" cells (snapshot 2 → 3)

Worst wall shifts, counter-checked:

- `bench_6722` 569→1 790 ms — conflicts **0→0: load noise**, not real.
- `convert-jpg2gif-1145` 338→626 ms — conflicts 274→274: noise.
- `Example_11` 2 011→2 550 ms — conflicts 7 667→**14 106**: a REAL
  trajectory shift (+84 %, still solves comfortably; watch it at the
  next snapshot — if it doubles again, bisect).
- Median stayed-solved shift **0.86×** — the slice got collectively
  FASTER (the SAT-core landings), so the two noise cells and one real
  shift sit on an improving base.

## The worst both-solved wall ratios (the z3-folds-at-0-conflicts class)

`prp-3-18` 47× (938 ms vs 20 ms), `problem_2__014` 42×, `bench_604`
11×, `FISCHER10-7-fair` 9.5×, `bench_16217` 9.3× — every one a cell
where z3's preprocessor decides and nixie searches (the nec-smt /
ctx-simplify fold gap already named in the 2026-09-19 attribution
study).  These are wall-visible *because* they solve; the same mechanism
also owns unsolved cells, so the fold route's payoff is double-counted
in the solved column.

## Readout for the map

No new item.  The wall dimension re-ranks nothing but sharpens two:
the tactic-cascade port (owns the fragile BV cells above) and the
branch channel (owns the LIA tail).  At the next snapshot, keep this
readout's three checks: fragile-solve inventory, counter-checked
per-cell wall deltas, both-solved median ratio.
