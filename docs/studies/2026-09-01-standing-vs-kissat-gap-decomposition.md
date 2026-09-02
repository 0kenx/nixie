# The real gap vs kissat/cadical: standing table, decomposition, and the structural program (2026-09-01)

The measurement `docs/BENCHMARKING.md` §12 said must exist before any
competition-language claim: the first standing table with a **kissat
column**, plus a decomposition of the gap into its actual factors, plus
the memory- footprint quantification (user-observed 2–5× vs cadical,
4–10× vs kissat — confirmed and root-caused below).

## Setup

54-file corpus (`/tmp/sc24f`, the surviving satcomp2024 selection), 60 s
wall cap, serial per file with the three arms concurrent on dedicated
pinned P-cores (oxiz=3, cadical=4, kissat=5; machine otherwise idle).
Arms: `oxiz` = `precompile/7e644a7/stats_solve` (CaDiCaL preset),
cadical 3.0.1, kissat 4.0.4. Score = solved-at-cap; wall-clock is the
scoring objective (standing-table tradition), with the
three-arms-on-three-cores layout noted as a caveat (each core private;
memory-bandwidth shared — ±few % on wall at most, verdicts unaffected).

## The standing table

| arm | solved / 54 @ 60 s | wall geomean (both-solved vs oxiz) |
|---|---|---|
| oxiz (`7e644a7`) | 50 | 1.00× |
| cadical 3.0.1 | **51** | oxiz/cadical = **1.27×** |
| kissat 4.0.4 | 50 | oxiz/kissat = **1.50×** |

0 verdict mismatches anywhere. **On this corpus there is no
order-of-magnitude gap — there is solved-parity and a 1.3–1.5× wall
gap.** The order of magnitude the project keeps feeling lives in the
tail and in memory:

### Decomposition (34 both-solved files with counters on both sides)

| factor | oxiz vs kissat | meaning |
|---|---|---|
| conflicts-to-verdict | **1.33×** | our search path is 33 % longer |
| conflicts-per-second | **0.82×** | kissat's per-conflict cost is 1.22× ours |
| product | 1.62× | ≈ the measured 1.50× wall gap — the decomposition closes |

Neither factor alone is 10×. The tail is where 10× lives:

| file | oxiz wall | kissat wall | conflicts ox→kissat | driver |
|---|---|---|---|---|
| frb65-12-2 | 36.0 s | 3.3 s | 1 062 k → 167 k (6.4×) | search path |
| 6s167-opt | 3.7 s | 0.5 s | 118 k → 19 k (6.2×) | search path |
| shuffling-2-s25 | 23.6 s | 3.6 s | 23 k → 0.8 k (**29×**) | search path |
| FmlaEquivChain | 57.7 s | 11.1 s | 2 148 k → 378 k (5.7×) | search path |
| mrpp_4x4 | 18.4 s | 3.7 s | 249 k → 179 k (1.4×) | throughput |

And oxiz **wins** the summle class 6.7×, worker_20 4×, af-synthesis
2.4× — the tail cuts both ways.

## Memory: confirmed and root-caused

Peak RSS (full solves, 65 s cap, per-run fresh measurement):

| file | oxiz | cadical | kissat | oxiz/kissat |
|---|---|---|---|---|
| noL-11-14 (1.4 k vars!) | **269 MB** | 15 MB | 20 MB | **13.5×** |
| frb65-874 | 147 MB | 17 MB | 13 MB | 11.3× |
| FmlaEquivChain | 350 MB | 97 MB | 52 MB | 6.7× |
| mrpp_4x4 | 38 MB | 13 MB | 13 MB | 2.9× |
| g2-slp | 231 MB | 113 MB | 71 MB | 3.3× |
| worker_550 | 1 601 MB | 1 874 MB | 282 MB | 5.7× (but **0.85× cadical**) |
| si2-b03m | 120 MB | 172 MB | 103 MB | 1.2× (0.7× cadical) |
| shuffling-2 | 752 MB | 906 MB | 269 MB | 2.8× (0.8× cadical) |

**Root cause for the small-instance blowups: `ClauseArena::compact()`
is an empty stub** (`clause.rs:698`, "deleted slots are never reclaimed,
so this is a no-op") — and `learn.rs:952` calls it on every reduction.
The arena is append-only; ids are never reused or relocated; every
learned clause ever allocated retains its bytes until the Solver dies.
noL-11-14 runs ~1.5 M conflicts ≈ 1.5 M × ~120 B ≈ the measured
269 MB on a 1.4 k-variable instance. This also degrades cache locality
(a component of the 0.82× throughput factor) and is an unbounded-growth
hazard under any long cap (SATComp main-track and SMT-COMP memory
limits included).

The files where oxiz is *under* cadical (worker, si2, shuffling) show
the bloat is not uniform per-clause-size — cadical's own footprint
scales with binary-heavy inputs there while ours does not; kissat stays
smallest everywhere via its tiered retention.

## The program (ranked; structural, no more 1.03× slices)

1. **Clause-arena reclamation** — implement real compaction in
   `reduce`: move live clauses into a fresh arena region in id order,
   rewrite the id→ref slot table, and rewrite each watcher's arena ref
   **in place** (never rebuild watch lists — visit order is
   trajectory-observable). Path-preserving by construction; Gate 1
   (54-file identity) applies verbatim. Attacks: the 10–13× memory
   ratio on small instances, unbounded growth, cache locality.
   cadical's reduce/arena relocation is the reference shape.
2. **Tiered learned-DB retention** (kissat core/tier1/tier2 with
   promotion-by-glue and targeted reduction): the worker-class memory
   gap (5.7× vs kissat) and part of the tail's conflict counts.
   Heuristic class — matched-null study required.
3. **Search-path tail study** (frb65/6s167/shuffling classes, 5–29×
   conflicts): the standing-gap deep study — learned-clause quality
   levers and the remaining phase-policy openings. (Correction
   2026-09-02: this item originally listed "target phases, still
   absent" — stale; cadical-faithful target phases landed 2026-08-15 in
   `7cb81f5` and are wired through `decision_polarity` /
   `update_target_and_best` / `copy_phases(PhaseArray::Target)`. The
   tail gap therefore lives elsewhere.) Heuristic class — matched-null
   study required.
4. Throughput residuals beyond 1.22× after 1–2 land: per-conflict
   profile re-rank at that point.

The addendum's strategic note stands unchanged: SMT-COMP's
thinly-populated correctness tracks remain the best medal-per-effort
target; the SAT-side goal is structural parity (memory bounded, tail
closed), not micro-throughput.

## Artifacts

`/tmp/standing3.csv` (54×3 runs, verdict/wall/conflicts/cps) and
`/tmp/standing3.py` (the runner) on this machine; memory numbers from
fresh-child `getrusage(RUSAGE_CHILDREN)` peaks.

## Lever 1 landed: arena compaction (2026-09-01, same day)

Implemented as designed in shape, with two deviations the implementation
itself forced — both improvements:

1. **No word-indexed remap table.** Every watcher carries its `ClauseId`
   next to its `.r`, and the database's `refs` table *is* the id→slot map
   the compaction rewrites anyway — so watchers are rewritten from `refs`
   in place (O(1) per holder, zero transient memory). The planned
   u32-per-word table (old_pos/2 transient bytes, a 400 MB spike on a
   worker-class arena) is unnecessary.
2. **In-place kissat-style sweep, not a fresh buffer.** The tombstone sits
   at the *end* of the compacted region, so every live clause's new offset
   ≤ its old offset — clauses `memmove` down inside the existing buffer
   (kissat `collect.c`'s src/dst shape) and the tail is returned with
   `shrink_to_fit`. The fresh-buffer version was built first; its
   transient old+new peak measurably *raised* peak RSS on si2-b03m
   (120→150 MB, 1.25×) before being replaced. In-place never exceeds the
   pre-compaction footprint.

Trigger: every reduce round (both the legacy tiered path and the
cadical-reduce port), gated on garbage ≥ 64 KiB and ≥ live/3 — total copy
work bounded at ~3× the bytes ever collected. `OXIZ_NO_ARENA_COMPACT=1`
is the A/B switch.

**The bug the gates caught:** slot physical extents cannot be read off
list neighbours — after the first compaction, tombstone entries (dead ids)
interleave with live refs, so `refs[i+1]` can sit *before* `refs[i]`'s
slot. The first end-to-end run tripped the debug assert on
`crn_11_99_u.cnf` (BVE garbage → first real compaction). Validation now
uses the same region bound every arena read uses (`get`/`read_header`).

**Gates (all green):**

- **Identity (Gate 1): 54/54 files, verdicts and conflict counts
  bit-identical** old (`7e644a7`) vs new — compaction is
  trajectory-neutral by construction, and measured so.
- **Peak RSS** (fresh child per run — `RUSAGE_CHILDREN.ru_maxrss` is a
  cumulative max across children; measuring several runs in one parent
  silently reports the first run's peak forever):

  | file | before | after | ratio | (kissat) |
  |---|---|---|---|---|
  | noL-11-14 | 269 MB | **32 MB** | 8.4× | 20 MB |
  | frb65-874 | 146 MB | **26 MB** | 5.6× | 13 MB |
  | FmlaEquivChain | 350 MB | **101 MB** | 3.5× | 52 MB |
  | worker_550 | 1601 MB | 1425 MB | 1.12× | 282 MB |
  | g2-slp | 231 MB | 166 MB | 1.39× | 71 MB |
  | si2-b03m | 120 MB | 120 MB | 1.00× | 103 MB |

  The small-instance blowups (10–13× vs kissat) are gone; the worst
  remaining ratio vs kissat is ~2× on noL/frb65 (residue: the never-
  shrunk `refs` id table and inter-compaction live data) and worker-class
  (1.12× — non-arena structures dominate there; lever 2 territory).
- **Wall** (serial, same core, 60 s cap): geomean old/new = **1.048×**
  over the 50 both-solved files (new is 4.8 % faster — the dense live
  region's locality), solved 50/50.
- Full battery (10 427 tests), clippy/fmt/doc clean, Z3 parity suite
  **0 mismatches** (169/170 decisive-agreed; 1 Z3-Unknown inconclusive,
  Z3 4.16.0 — not the 4.15.4 baseline, verdicts unaffected).

Next per the program: lever 2 (tiered retention, matched-null study) and
lever 3 (search-path tail study).
