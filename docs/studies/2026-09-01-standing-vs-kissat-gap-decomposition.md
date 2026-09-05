# The real gap vs kissat/cadical: standing table, decomposition, and the structural program (2026-09-01)

The measurement `docs/BENCHMARKING.md` §12 said must exist before any
competition-language claim: the first standing table with a **kissat
column**, plus a decomposition of the gap into its actual factors, plus
the memory- footprint quantification (user-observed 2–5× vs cadical,
4–10× vs kissat — confirmed and root-caused below).

## Setup

54-file corpus (`/tmp/sc24f`, the surviving satcomp2024 selection), 60 s
wall cap, serial per file with the three arms concurrent on dedicated
pinned P-cores (nixie=3, cadical=4, kissat=5; machine otherwise idle).
Arms: `nixie` = `precompile/7e644a7/stats_solve` (CaDiCaL preset),
cadical 3.0.1, kissat 4.0.4. Score = solved-at-cap; wall-clock is the
scoring objective (standing-table tradition), with the
three-arms-on-three-cores layout noted as a caveat (each core private;
memory-bandwidth shared — ±few % on wall at most, verdicts unaffected).

## The standing table

| arm | solved / 54 @ 60 s | wall geomean (both-solved vs nixie) |
|---|---|---|
| nixie (`7e644a7`) | 50 | 1.00× |
| cadical 3.0.1 | **51** | nixie/cadical = **1.27×** |
| kissat 4.0.4 | 50 | nixie/kissat = **1.50×** |

0 verdict mismatches anywhere. **On this corpus there is no
order-of-magnitude gap — there is solved-parity and a 1.3–1.5× wall
gap.** The order of magnitude the project keeps feeling lives in the
tail and in memory:

### Decomposition (34 both-solved files with counters on both sides)

| factor | nixie vs kissat | meaning |
|---|---|---|
| conflicts-to-verdict | **1.33×** | our search path is 33 % longer |
| conflicts-per-second | **0.82×** | kissat's per-conflict cost is 1.22× ours |
| product | 1.62× | ≈ the measured 1.50× wall gap — the decomposition closes |

Neither factor alone is 10×. The tail is where 10× lives:

| file | nixie wall | kissat wall | conflicts ox→kissat | driver |
|---|---|---|---|---|
| frb65-12-2 | 36.0 s | 3.3 s | 1 062 k → 167 k (6.4×) | search path |
| 6s167-opt | 3.7 s | 0.5 s | 118 k → 19 k (6.2×) | search path |
| shuffling-2-s25 | 23.6 s | 3.6 s | 23 k → 0.8 k (**29×**) | search path |
| FmlaEquivChain | 57.7 s | 11.1 s | 2 148 k → 378 k (5.7×) | search path |
| mrpp_4x4 | 18.4 s | 3.7 s | 249 k → 179 k (1.4×) | throughput |

And nixie **wins** the summle class 6.7×, worker_20 4×, af-synthesis
2.4× — the tail cuts both ways.

## Memory: confirmed and root-caused

Peak RSS (full solves, 65 s cap, per-run fresh measurement):

| file | nixie | cadical | kissat | nixie/kissat |
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

The files where nixie is *under* cadical (worker, si2, shuffling) show
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
work bounded at ~3× the bytes ever collected. `NIXIE_NO_ARENA_COMPACT=1`
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

## Addendum 2 (2026-09-02): the tail table's seed-selection bias, corrected

The tail table above conditions on the default RNG seed. 10-seed
distributions (mixed via `set_random_seed`, conflicts-to-verdict, 60 s
cap, `01dab25` binary) revise it:

| file | default seed | min | median | max | kissat | gap at median |
|---|---|---|---|---|---|---|
| shuffling-2-s25 | 23 130 (**max**) | 185 | 1 246 | 23 130 | 784 | **1.6×** (was "29×") |
| frb65-12-2 | 1 062 010 (near max) | 28 274 | 728 634 | 1 679 062 | 167 k | 4.4× (59× spread!) |
| FmlaEquivChain | 2 147 581 (**max**) | 811 117 | 1 306 887 | 2 147 581 | 378 k | 3.5× (was 5.7×) |
| 6s167-opt | 118 191 (median) | 115 371 | 123 801 | 149 261 | 19 k | **6.5×, tight** |
| mrpp_4x4 | 249 027 | 151 891 | 275 267 | 346 674 | 179 k | 1.5× |

The default seed sat at/near the 10-seed max on 3 of 5 tail files — not a
degenerate RNG (seed 0 mixes to the historical default xorshift state) but
pure selection bias: the tail was *read off* the files where the default
trajectory happened to be unlucky. Lessons:

* **Single-seed tail tables are seed-luck tales.** Any future tail entry
  must carry a seed distribution (the doc's own §1 chaos warning,
  quantified: 59× spread on frb65).
* **The high-variance SAT files (frb65, shuffling, x9/rbsat/crypto1 from
  the seed-portfolio study) are portfolio territory** — the `SEEDS=`
  chain in `cnf_solve` already exists and its arithmetic is measured
  (`2026-08-seed-portfolio-restarts.md`). A default-first chain at ~60 %
  per-arm budgets converts these classes at bounded caps; competition
  presets are the consumer.
* **The genuinely structural residue is 6s167-opt** (6.5×, 1.3× seed
  spread) and FmlaEquivChain-at-median (3.5×). On 6s167 the shape matches
  kissat everywhere shallow — restart cadence identical (13
  conflicts/restart both), decisions/conflict similar (3.5 vs 4.3),
  rephases/walks comparable — but kissat propagates 3.3× deeper per
  decision (93 vs 35 propagations/decision) and refutes in 6× fewer
  conflicts: diffuse per-conflict search quality (branch/clause quality),
  not a schedule parameter. This is the honest scope of lever 3.
* Kissat's rephase schedule walks every 3rd round (2/6) with
  `rephaseint×nlog³n` growth; ours (cadical shape) also walks every 3rd in
  both modes with `rephaseint×(n+1)` — the walk-frequency hypothesis for
  the tail is **dead** (kissat solved shuffling-2 with 0 rephases and 0
  walks; our single walk there found a model in 159 flips at ~conflict
  21 k — the mechanism exists but is not the gap).

## Addendum 3 (2026-09-02): reduce-percentage surface probed and closed

Single-seed screen of the legacy tier percentages
(`NIXIE_REDUCE_PCT_{LOCAL,MID,CORE}`, defaults 75/30/10), conflicts-to-verdict:

| knobs | mrpp_4x4 | 6s167-opt |
|---|---|---|
| 75/30/10 (default) | 249 027 | 118 191 |
| 60/20/5 (softer) | 282 920 | 127 523 |
| 50/15/5 (softer) | 286 612 | — |
| 90/50/20 (harder) | 451 754 | 136 247 |
| 95/60/25 (harder) | 1 234 203 | — |

The defaults are a local optimum in both directions on both files — the
"smaller DB → fewer watch visits wins" idea (mrpp runs ~40 visits/prop at
avg list ~93) is dead at this granularity: the DB earns its retention.
Consistent with the cadical-reduce port's null result. The open retention
question remains the *signal* (usage vs glue — where random deletion beat
glue-ranked 2× on stable-300 in the 2026-08-22 study), not the amount.

## Addendum 4 (2026-09-02): worker-class memory composition, measured

`NIXIE_MEM_STATS=1` (`Solver::memory_composition`) on worker_550
(10.3 M originals, avg 2.7 lits — 97 %+ binary), same values at conflict
1 and 40 000 (standing structures do not grow during search):

| structure | live | capacity |
|---|---|---|
| clause arena | 247.6 MB | 268.4 MB |
| BIG (2×8 B edges/binary) | 164.7 MB | **250.0 MB** |
| refs (4 B/allocated clause) | 41.2 MB | — |
| watch lists (≥3-lit clauses) | **14 KB** | 107 KB |
| arena compactions | 0 (gate correct: waste ≪ live/3) | |

Peak RSS: **814 MB before the first conflict**, 1387 MB during search.
So: (a) the standing footprint is ~540 MB of *original formula* —
~44 B per binary (24 B arena slot + 16 B BIG edges + 4 B refs) vs
kissat's watch-resident binaries (`binary_tagged_literal` — no arena
slot, no clause header, ~16–24 B), the structural ~2×; (b) pre-search
adds ~270 MB of transients (packed lucky snapshot ~190 MB + probe/BVE
occurrence lists); (c) search adds ~570 MB of *recurring transients* —
the scheduled elimination/probe rounds rebuild occurrence lists over the
whole 10 M-clause DB every round (cadical suffers the same: its measured
worker_550 peak is 1874 MB). My earlier "watch lists ≈ 250 MB" guess was
wrong by four orders of magnitude — worker is a BIG-only instance.

Levers, ranked: (1) **binary representation density** (kissat-style
watch-resident binaries) — major architecture work, made conceivable by
BIG-authoritative BCP existing, but binary *reasons* currently need
clause ids; (2) **elimination-transient budgeting** (stream or DB-size-
gate the occurrence lists) — targeted, pre-registerable; (3) binary
retention/reduction — heuristic class, retention-signal thread measured
dead at this granularity.

## Addendum 5 (2026-09-02): the search-time climb was the walk; packed, −431 MB

A/B of the suspected transients on worker_550 (peak RSS, 40 k conflicts):
base 1387 MB; scheduled elimination off 1331; probe off 1387; **walk off
814** — the ProbSAT walk's per-round structures owned the *entire*
search-time climb. `walk_round` built `slots: Vec<Vec<Lit>>` (one heap
Vec per original clause — ~40 B header+block overhead each, ~500 MB on a
10 M-clause formula) plus `occ: Vec<Vec<u32>>` occurrence lists. Both are
read-only after construction, so they now pack CSR-style into two flat
buffers with cumulative end offsets — identical contents and per-literal
order, RNG stream untouched, **trajectory-identical (54/54 corpus gate)**.
Worker peak: **1387 → 956 MB** (search-time climb now 814→956 MB, i.e.
~140 MB of packed round data + slack, down from ~570 MB). The remaining
956 MB is the formula itself (~540 MB standing) plus pre-search
transients (lucky snapshot ~190 MB packed, pre-search elim/probe
occurrences) — the binary-representation lever of Addendum 4 is what is
left.


## Addendum 6 (2026-09-05): lever-2 first slice landed; re-baseline at `cb9f05c`/`a29927c`

Standing table re-measured at the campaign's start commit `cb9f05c` (54-file corpus,
60 s cap, 3-arm pinned layout, benchstore suite `satcomp24-standing54-cap60`, 162
records): nixie **50/54**, cadical 51, kissat 50; 0 mismatches; wall geomeans
nixie/kissat **1.421x**, nixie/cadical **1.250x**; decomposition conflicts-to-verdict
1.332x x per-conflict-wall 1.093x.

Then the first trajectory-neutral memory slice of lever 2 landed
(`2026-09-05-worker-class-memory-landing.md`: lucky >=3-only snapshot, BIG
shrink-to-fit, walk arena-referencing + bitset, compaction gate live/8, eliminator
CSR occurrences, streamed DIMACS parse): worker_550 peak **965 -> 810 MB**
(-16%), shuffling-2 665 -> 498 MB, worst nixie/kissat ratio 3.42x -> **2.87x** —
with 54/54 bit-identical trajectories (verdicts + conflict counts) and a paired
4-arm wall of **0.991x** (50/54 solved on both arms, 0 mismatches; suite
`satcomp24-standing54-4arm`, 216 records). The KR2 targets (-25% worker peak,
<=2.5x worst ratio) are NOT yet met: the remaining blockers are the ~170 MB
post-parse floor above live composition (unattributed heap) and the walk round's
per-round occurrence CSR + true-count arrays (~120 MB on worker) — the structural
fix is a walk over the BIG itself. mimalloc in the harness measured WORSE
(1453 MB) and is recorded as a negative.
