# Kitten Sweep Port — Calibration and First Screen (2026-09-07/08)

**Arm under test:** `NIXIE_SWEEP=1` — the kissat `kitten.c` + `sweep.c`
port (`nixie-sat/src/kitten.rs`, `nixie-sat/src/solver/sweep.rs`),
default OFF. Commit `47d090c` (+ the two memory-bug fixes it carries).

**Mandate:** `docs/handovers/2026-09-07-kitten-sweep-port.md` — build the
missing *equivalence-content* (sweep) rather than another gate, route
application through the existing substitution path, and clear the
standing screen or land effort-gated below the regression threshold.

## What was ported

- **`kitten.rs`** — the embedded CDCL solver, full `kitten.h` API:
  import/export literal mapping, flat klauses arena
  (`[aux,size,flags,lits..,ants..]`), stamped-VMTF decision queue,
  assumption solving with failed-literal analysis, **tick budget**
  (deterministic counter; `solve` → Unknown when exhausted), antecedent
  tracking, clausal-core extraction, in-model literal flips, phase
  control (randomize/flip/shuffle). All walks iterative.
- **`solver/sweep.rs`** — the sweeper: depth-≤2 cone environments over
  live **original** clauses (BIG edges + watch lists, value-filtered
  copies), occurrence-ranked candidate ring (kissat's intrusive list,
  reschedule/incomplete/completed bookkeeping), backbone units (assume
  ¬l → UNSAT → core → level-0 assign+propagate), equivalence pairs (two
  implication tests → two entailed binaries via `add_clause`), flip
  rounds, per-round tick budget = `sweepeffort`‰ (100) of the effort
  window with the `mineffort` floor.
- **Application** rides the existing hardened substitution round
  (`solver/equiv.rs`) — the added binaries expose the classes to the SCC
  fold; per the handover, `substitute.c`'s rewrite layer is NOT
  reimplemented. Deviations recorded in the module doc (deferred vs
  per-pair application; no `BUMP_DELAY`; larger core lemmas dropped,
  proof-side-only in kissat).
- **Integration:** pre-search slot (kissat `preprocesssweep=1` analog)
  + budgeted inprocessing-round component. Knobs: `NIXIE_SWEEP`,
  `NIXIE_SWEEP_NULL` (matched null: ranking scrambled by a
  deterministic hash — same candidate set, same machinery),
  `NIXIE_SWEEP_EFFORT`, `NIXIE_SWEEP_TRACE`.

## Calibration bugs found on the anchors (and their shape)

Two memory-path bugs, both found via 6s167-opt (thanks to a reviewer
nudge to look for a leak when the binary died):

1. **Scheduling-ring corruption → unbounded growth.** The ring's unlink
   wrote `next[next'] = prev` where kissat writes `prev[next'] = prev`
   (`schedule_inner`). Stale back-pointers made the ring cyclic, so
   `unschedule_sweeping` walked forever pushing into `sweep_schedule`:
   RSS ~2 GB/s, killed. Fixed exactly to the C shape; `schedule_outer`
   also now sets `prev[idx] = INVALID` explicitly.
2. **Partition sentinel leak → gigabyte transients.** The pair-class
   squash in `sweep_partition_remove` drained the two literals but left
   the trailing `INVALID` separator, so a later pair-pop handed the
   sentinel (`u32::MAX`) to `kitten.assume`, whose import table then
   resized by 2³¹ entries: a repeating ~7 GB RSS sawtooth. Fixed the
   drain to include the separator; added a layout guard before the pair
   test and a `MAX_VARS`-style sanity rejection in kitten's import path
   (defensive; a rejected literal weakens a clause, never strengthens
   it).

After the fixes: 6s167-opt max RSS **14.7 MB** (base 15.6 MB), user
time 1.11 s.

Also fixed during bring-up: the sweeper's scratch clause was restored
un-emptied after encoding (every environment clause became a cumulative
super-clause of the previous — silently destroying the equivalence
structure; 0 equivalences proved until found), and the budget-boundary
deadlock (kitten aborts at `ticks >= limit` while the outer loops
needed `>`; at exactly the limit every solve returns Unknown consuming
no ticks → infinite partition loop; outer checks now `>=`).

## Anchor calibration (current head, 60 s cap, counters only)

| file | base | sweep | note |
|---|---|---|---|
| 6s167-opt | 62 241 conflicts / 1.60 s | **42 003** / 1.20 s | 0.67× — the ELS-arm level (42 681) *inside the default config*; cadical's 16 654 remains the span target |
| FmlaEquivChain_4_6_6 | 49.3 s (solves) | **23.3 s** | 2.1× — the equivalence-chain class the gates could not isolate |
| x9-09054 | TO at 70 s | **solves** (67 s) | base TO, sweep converts |
| stable-300 | 2.87 s | 2.93 s | neutral |

Sweep's own price on 6s167-opt: 10 rounds, 996 vars swept, 8 964 kitten
solves, 948 k kitten ticks, 53 equivalences, 0 units — vs kissat's own
3 rounds / 34.7 k solves / 3.5 M ticks / 162 equivalences on its 19 k
conflict run. Price is inside the reference envelope.

### Matched null (the mandated reporting form)

6s167-opt, deterministic (no seed):

| arm | conflicts | kitten solves | kitten ticks | equivalences |
|---|---|---|---|---|
| base | 62 241 | 0 | 0 | 0 |
| **treatment** | 42 003 | 8 964 | 948 k | 53 |
| **null** (scrambled ranking) | 45 858 | 8 656 | 1 063 k | 116 |

The null **fires** (same-magnitude machinery: solves 8 964 vs 8 656,
ticks within 12%) — this is the fired-null check the handover mandates
before trusting ratios. **Treatment/null = 0.92×**: the cone-ranking's
semantic content is worth ~8 % over the same-cost scrambled order; the
equivalence *content* itself (present in both arms) carries the bulk of
the base-relative 0.67×. (The null proving *more* equivalences while
losing on conflicts is consistent with per-file bimodality: which pairs
get proved first, not how many, sets the trajectory.)

## Standing corpus screen

54 files × 5 seeds × 3 arms × 60 s cap, pinned cores 10–19 (the screen
shared the box with the parity build for part of its run — absolute
numbers carry that contention; **within-screen arm deltas are paired**
and meaningful). Raw cells + runner:
`precompile/47d090c/benchmark/sweep_screen/`.

| arm | solved-at-cap (of 270) |
|---|---|
| base | 161 |
| sweep (treatment) | **159** (+3 files: summle ×3; −7: circuit_48in64out −2, j3037, frb65, qwh, worker_550, x9-08075, 64_25) |
| null (scrambled ranking) | **170** (+6, −4) |

**Zero verdict disagreements** across every both-decided cell — the
soundness gate is clean at 810 cells.

### Anchor gate (conflicts-to-verdict geomean, 5 seeds, 60 s cap)

| anchor | base | treatment | null | treatment/null |
|---|---|---|---|---|
| 6s167-opt (5/5 all arms) | 64 349 | 42 179 | **34 712** | **1.22×** (null better) |
| FmlaEquivChain (5/5) | 525 810 | **415 665** | 473 257 | **0.88×** (treatment better) |
| x9-09054 (solved-at-cap) | 1/5 | 1/5 | 2/5 | mixed |
| stable-300 (4/5) | 239 350 | 239 350 | 239 350 | inert (no equivalences there) |

Raw: `precompile/47d090c/benchmark/anchor_gate.json`.

## Verdict (pre-registered kill criteria, evaluated)

The treatment at kissat's budget (100 ‰) measures **corpus-negative
(−2 standing) while tail-bimodal** — the exact pre-registered kill
shape. Per the handover: **record and stop; the default stays OFF**
(the arm was landed default-off, so nothing to retract).

The screen adds one finding the kill criteria did not anticipate: the
**null is corpus-positive (+9 cells)** with the same machinery, budget
and candidate set — so the corpus-negative part is not *substitution
content* per se, it is the faithful **cone-occurrence ranking**. Both
orderings have anchor wins (faithful: FmlaEquivChain 0.88×; scrambled:
6s167 1.22×), which sharpens the bimodality conclusion: *any* fixed
sweep ordering wins one class and loses another; corpus standing is
decided by which class dominates the corpus mix. The follow-up this
teases — a pre-registered ranking-variant study (its own nulls: a
different-seed scramble vs identity-at-same-budget) — is out of scope
here and left on record.

**Landed:** the port (default-off, env-gated), its tests, the fixed
memory bugs, this calibration record, and the anchor/screen evidence.
Tail conversion remains a per-class-config / portfolio question, as the
handover anticipated.

## Soundness verification shipped with this change

- kitten unit tests (12) + sweep integration tests (8): chain folding
  with model-reconstruction checks over every folded var, backbone
  extraction, UNSAT env → empty clause, null-fires, default-off
  inertness, push/pop base-scope safety.
- Full `nixie-sat` suite (959 tests) green; clippy `-D warnings`; fmt.
- Z3 differential parity: **169/170 decisive, 0 disagreements** (the
  one non-match is Z3-side Unknown → inconclusive, not a disagreement;
  z3 on PATH is 4.16.0 vs the 4.15.4 baseline snapshot — recorded in
  the run metadata, per the suite's caveat).

---

# Part 2: Main-loop wiring + performance characterization (2026-09-08)

**Wiring completed** (`19692a2`): the armed sweep now runs as a first-class
conflict-scheduled component on every preset — when the inprocessing
bundle is off, the conflict handler runs `sweep_round` on the shared
interval + effort-window bookkeeping (19 rounds on 6s167-opt under
`PRESET=default`; SMT path fires it too: QF_AUFBV 12 rounds, verdicts
unchanged). Default trajectory untouched (inert unless armed).

## Pre-registration (written before the runs)

- **P1 (price)**: corpus-wide sweep cost at the port budget (100 ‰):
  kitten ticks per run, and the end-to-end instruction delta
  (`perf stat`, pinned, 3 anchor files, treatment vs base).
- **P2 (content)**: paired conflicts-to-verdict, treatment vs matched
  null (scrambled ranking — same machinery, budget, candidate set),
  CRN pairing, 10 seeds, per family and SAT/UNSAT split.
- **Go bar**: treatment/null geomean ≤ **0.95** AND sweep solved-at-cap ≥
  null solved-at-cap. [0.95, 1.05] = neutral (no corpus-level ranking
  signal). > 1.05 = the faithful ranking is corpus-harmful.
- **Falsification**: if the null's +9 solved-at-cap lead (5 seeds) holds
  at 10 seeds, the cone-occurrence ranking is corpus-harmful and the
  ranking-variant follow-up is the only live path to a default.
- **Null-fires check**: `kitten_solved(base)=0`; treatment and null both
  `kitten_solved>0` on the same files.
- Cells: 54 files × seeds 1–10 × {base, sweep, null}, 60 s cap, cores
  10–19, recorded once in the benchstore under
  `precompile/19692a2/benchmark/`.
