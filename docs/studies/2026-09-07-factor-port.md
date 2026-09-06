# Full kissat factor.c port — quotient chains (worker-class lever)

**Date:** 2026-09-07
**Handover:** `docs/handovers/2026-09-07-factor-port.md`
**Reference:** kissat 4.0.4 `src/factor.c` (instrumented `-l` build used for
ground truth)
**Landed:** `nixie-sat/src/solver/factor.rs` (full rewrite of the 2026-09-05
binary-only first slice), `BinaryImplicationGraph::compact_dead`,
`VMTF::enqueue_oldest_and_restamp`, mid-search wiring in `inprocess()`.
Default **off** (`SolverConfig::enable_factoring` / `NIXIE_FACTOR=1` /
stats_solve `FACTOR=1`).

## What was ported (all of it)

- Quotient chains: `first_factor` / `next_factor` / `factorize_next` /
  `best_quotient` / `apply_factoring` — one pivot at a time, matched
  subsets only, prefix-cut selection by reduction `n·(p+1) − n − (p+1)`,
  kissat's tie-breaks (max count, `watches_score`, first-seen-wins).
- Large clauses: `factorsize=5`, the dense-mode candidate filter (every
  literal binary+large occurrence ≥ 2, `factorcandrounds=2` fixed point)
  as an explicit CSR occurrence index with mid-pass overflow.
- Dirty-literal gating (`flags.factor` semantics on our
  `mark_subsume_lit` sites), watermark skip, tick budget
  (`factoriniticks=700` M first pass, `factoreffort=50‰` of window after,
  `mineffort=10` M floor), `factordelay=4` log10 gate.
- The early cascade is **bit-identical to kissat** on worker_550: first
  pivot quotient[0]=345 clauses, diagonal n-decay (345→344→…), first
  apply `quotient[172] reduction 29583` — same numbers kissat's `-l` log
  prints. The chain machinery is a faithful port.

## The three real bugs found on the way (all fixed + regression-pinned)

1. **`compact_dead` read later codes' edges at the *compacted* span
   offsets** instead of their original ones — after the first dropped
   edge every subsequent literal read the wrong span, silently emptying
   the BIG mid-pass. Quality-only damage (the rewrite is equisatisfiable
   on whatever clause set it sees; BCP uses the post-pass rebuild), but
   it collapsed the pass to 3,130 applies. Fixed with separate
   read/write cursors + `big_compact_dead_drops_exactly_dead_edges`.
2. **Hub self-factoring**: our first version pushed the fresh hub `t`
   into the in-pass schedule (kissat's `update_factored` never does).
   Hubs then factored against each other, building mega-clusters with
   avg_lbd ≈ 1100. Excluding `t` restored kissat-shaped chains.
3. **The handover's VMTF reading is inverted**: kissat's
   `adjust_scores_and_phases_of_fresh_variables` links fresh variables
   at `queue->first` — the **oldest** end, decided **last** — and zeroes
   their VSIDS score. The handover claims "front of the queue, making it
   the next decision". The source is unambiguous (`kissat_decide` scans
   from `queue->last` via `prev`). Empirically the handover's *effect* is
   the right one **for our search**:

   | `NIXIE_FACTOR_SCHED` | semantics | worker_550 conflicts (complete pass) |
   |---|---|---|
   | `back` (kissat source) | hubs decided last, score 0 | **472,908** |
   | `leave` | `new_var` default (tail) | 30,696 |
   | `front` (default) | hubs bumped to tail = next decisions | **10,004–23,383*** |

   *deterministic per binary; the spread is trajectory chaos across
   tick-accounting deltas (identical pass counters 48,990 intros /
   142,703 processed — the chain *sets* differ).

## worker_550 screen (the handover's calibration target)

| arm | conflicts | wall | notes |
|---|---|---|---|
| kissat 4.0.4 | 2,003 | 7.9 s | 51,466 intros, 283 M factor ticks, 227 dec/conflict |
| nixie off | 25,532 | 16 s | baseline |
| nixie FACTOR=1 (700 M budget, incomplete pass) | 14.5 k intros; conflicts 24 k–284 k | 2.5 min | pass burns the budget; search outcome is chaos across trajectories |
| nixie FACTOR=1 unbounded (complete pass) | **48,990 intros**, conflicts **10,004–23,383** | 48–64 s | 1.30 G ticks (4.6× kissat); dec/conflict ≈ 29 vs kissat 227 |
| nixie FACTOR=1 + mid-search rounds | 40,728 | 95 s | incremental delivery **hurts** — kissat's `factorizations: 1` is the winning shape |

**Verdict vs the handover's bar** (median ≤ 5,000): **not met** — the
complete pass lands at 10–24 k (2.5× better than off, 5–12× worse than
kissat). The introductions match kissat's (48,990 vs 51,466) and the
chains are kissat-shaped; the residue is the *search's* exploitation of
the restructured formula (kissat descends 227 decisions per conflict;
we descend 29 with avg_lbd ≈ 550–880). That is a search-paradigm gap
(phase/restart/bump discipline on hub-heavy formulas), not a rewrite
gap. The handover's fallback clause applies: documented with per-seed
data; the remaining worker gap requires work beyond the factor port.

## Cost model (why default-off stands)

Our pass runs at ~4.6× kissat's ticks per introduction (scan lengths
between periodic BIG compactions + per-pop dirty-gate churn on a lazy
heap — kissat's eager O(1) watch removal keeps its lists exact). The
complete worker pass costs ~1.3 G ticks ≈ 30–50 s — acceptable only on
instances that actually profit. The 700 M default budget bounds the
pre-search cost; `NIXIE_FACTOR_BUDGET` overrides.

## Soundness

- The rewrite is equisatisfiable and model-preserving downward (module
  doc proof); no reconstruction records.
- 20 k-CNF differential fuzz (chain-dense generator, mid-search rounds
  forced at interval 5) + 2 k pre-search verdict checks:
  `nixie-sat/tests/mid_factor_soundness.rs` — 0 mismatches.
- Chain/large fixtures + the `compact_dead` regression pinned in
  `solver/tests.rs`; full workspace suite green (10,603 tests).

## Corpus A/B (54-file sc24f, 5 seeds, 60 s cap, conflicts primary)

Cells recorded under `precompile/1ba99bb/benchmark/runs/sc24f/`
(`FACTOR=1 INPROCESS=0` vs env-unset, both with explicit
`INPROCESS=0`; stats_solve harness; machine under external load —
wall is sanity-only). **Results: see the addendum table below — filled
after the run completed.**

| metric | off | factor | ratio |
|---|---|---|---|
| solved / 54 (@60 s, any seed) | **50** | **48** | −2 files |
| conflicts geomean (both-decisive pairs, n=133) | 1.0 | — | **1.060×** |
| — sat subset (n=92) | | | 1.146× |
| — unsat subset (n=41) | | | 0.890× |

**Go/no-go (pre-registered in the handover): NO-GO on both prongs** —
conflicts geomean 1.060× (bar ≤ 0.95×) and solved-at-cap lower
(50 → 48: lost `Timetable_C_392…`, `frb45-21-2`; gained none).

Worker_550 under the 60 s cap: the factor arm's pass alone costs
30–50 s, so it times out 4/5 seeds while the off arm solves 5/5 —
with the off arm's own seed spread 2.4 k–106 k conflicts (worker-class
chaos, the standing-corpus studies' 203× spread in miniature).  The
complete-pass improvement measured above (10–24 k vs 25.5 k off-median)
cannot express itself inside a cap that must also pay the pass.

Bright spots (median conflicts, ≥3 decisive seeds): `stable-300` 0.31×,
`x9-09054` 0.51×, `j3037_10_mdd_b` 0.61×, `barman-pfile06` 0.62×,
`pb_300_09_lb_07` 0.65×, `worker_20_40_20` 0.75× (the *smaller* worker
instance — the class does respond where the pass fits the budget);
regressions: `shuffling-2` 6.4×, `Break_08_24` 3.4×, `ITC2021_Early_3`
2.8×.  The unsat class is net-positive (0.89×), the sat class
net-negative (1.15×).

**Disposition:** default stays off.  The port is complete and
kissat-faithful (bit-identical early cascades, matching introduction
counts and chain shapes on worker_550); the negative corpus verdict is
therefore attributable to the *search interaction* (hub-heavy formulas
under our VMTF/phase/restart dynamics: 29 decisions per conflict vs
kissat's 227 after the same rewrite), not to a port defect.  Closing
the worker-class gap needs the search-paradigm work (phase saving,
restart discipline, bump policy on restructured formulas), for which
this port is the enabling infrastructure — `FACTOR=1` +
`NIXIE_FACTOR_BUDGET` + `NIXIE_FACTOR_SCHED` are the experiment knobs.

## Divergences kept (recorded in the module doc)

`factorstructural`/`factorhops` (off in kissat) not ported; eliminate
bound escalation not ported (bound = 0); tombstone + periodic
compaction instead of eager watch removal; the `next == initial`
boundary literal excluded (one literal per pass); external termination
not ported.
