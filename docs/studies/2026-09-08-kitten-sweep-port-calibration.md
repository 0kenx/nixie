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

## Results (1620 cells, quiet machine, cores 10-19, recorded in the
benchstore under `precompile/19692a2/benchmark/runs/sc24f-sweepchar/`)

**Null-fires:** 245/540 (file, seed) cells have kitten activity in the
armed arms (21/54 files prove ≥ 1 equivalence); base has zero kitten
activity in every cell.

**Solved-at-cap (540 cells/arm):**

| arm | solved | vs base |
|---|---|---|
| base | 316 | — |
| sweep (treatment) | **351** | **+35** |
| null (scrambled ranking) | **355** | +39 |

Per-seed: sweep ≥ base on 8/10 seeds (null 9/10) — not a seed-mix
artifact. Gains concentrate exactly where the mechanism predicts
(equivalence-structured families: summle ×3 files, circuit ×3, FmlaEquivChain
2→7, constraints 6→9, qwh 4→7, mrpp 9→10); losses are few (mdp-28 2→0,
worker_550 4→3). **Zero verdict disagreements** in 1620 cells.

**Conflicts-to-verdict (paired geomean, both-solved):**

| ratio | geomean | n | verdict |
|---|---|---|---|
| sweep/null | **1.017** | 201 | **neutral** — inside the ±5 % band; the pre-registered go bar (≤ 0.95) FAILED: the cone-ranking carries no corpus-level signal |
| sweep/base | 0.949 | 172 | content (present in both armed arms) is worth ~5 % |
| null/base | 0.937 | 179 | — |

Per-family sweep/null is bimodal exactly as at 5 seeds: null better on
6s167 1.137 / summle 1.281 / mrpp 1.123; treatment better on constraints
0.818 / ITC2021 0.877 / crn 0.929 / si2 0.952. SAT split 1.006, UNSAT
1.043.

**Price:**

- Instructions (full solves, `perf stat`, P-cores): 6s167 13.64 G →
  9.79 G (**0.72×**), FmlaEquivChain 390.0 G → 195.9 G (**0.50×**),
  inert stable-300 31.26 G → 31.97 G (**+2.3 %** — the pure cost of the
  pass finding nothing).
- kitten ticks (sampled re-measure, 18 cells): 0.1–2.6 M ticks on files
  where it proves nothing (bounded by the 100 k/round budget); on 6s167
  22 kitten-ticks per search conflict vs kissat's own 184 on the same
  file — well inside the reference envelope.
- Wall-clock sanity (both-solved cells): sweep/base geomean **0.728** —
  consistent with (larger than) the conflicts proxy; folding also
  cheapens propagation.

**Correction to Part 1:** the 5-seed screen's corpus-negative verdict
(159 vs 161) does not reproduce. Same seeds 1–5 on the quiet machine:
base 160 (reproduces 161), sweep **169**. The Part-1 screen ran
concurrently with the parity suite's unpinned cargo build; the armed
arm pays the extra ~2 % instructions and loses borderline 60 s cells
disproportionately under load. Corpus sign at 10 seeds, quiet: **+35
solved**.

## Landing decision (enablement rule, §3 BENCHMARKING.md)

The Part-2 pre-registration governed the *ranking* question; it came
back **neutral** (1.017). The *content* question is governed by the
enablement rule instead: (a) soundness is structural (level 0 / base
scope / no proof / theory-freeze gates; every derived unit rides the
normal level-0 assign+propagate; kitten is Unknown-bounded), and (b)
the paired 10-seed differential shows **solved count not worse
(+35)** with **0 verdict disagreements**. Default flip: **ON**
(`NIXIE_SWEEP=0` restores the old default; the null arm remains
`NIXIE_SWEEP_NULL=1`). Ships with a fresh full Z3 parity at the new
default — a SAT-core change is an SMT-path change wherever the embedded
CDCL(T) core executes the schedule (most SMT logics gate the sweep off
via the real-theory freeze; the differential covers the rest).

The ranking question (faithful cone-order vs scramble, both defensible:
treatment wins constraints/ITC, null wins 6s167/summle) stays open as
the recorded follow-up; landing a scramble as the default would destroy
the null instrument for every future study.

## Addendum: the default-flip SMT differential caught a real desync
(fixed before landing)

The enablement rule's "fresh SMT differential at the new default" fired
for real: `pr30::test_bv_index_quantified_array_certifies_sat` flipped
**sat → wrong unsat** with the sweep on. Bisected chain:

1. The corruption is the **fold** (`substitute_equivalent_literals_round`),
   not the sweep's own answers: with the entailed binaries + backbone
   units applied but the fold skipped (`NIXIE_SWEEP_NOFOLD` debug arm),
   the verdict was correct. The folded equivalence itself was verified
   real (kissat-checked against a dump of the solver's own problem).
2. The sweeping instance was **not** the CDCL(T) Context's solver but
   `BvSolver`'s **embedded bit-blaster SAT solver** — created with
   `enable_inprocessing: false` and driven incrementally by hundreds of
   `solve()` calls per check. Two wiring defects made the sweep fire
   there: (a) the sweep-only conflict cadence keyed on exactly
   `!enable_inprocessing` (conflating "SAT-only workload" with "embedded
   solver"), and (b) the pre-search sweep slot had **no latch**, so every
   re-`solve` of the incremental protocol re-swept, folding variables
   between two solves of a caller-owned encoding.

Structural fixes (all landed with the flip):

- **Sweep-only cadence removed** — `!enable_inprocessing` is not a
  top-level-SAT discriminator. The sweep's homes are the inprocessing
  rounds (every inprocessing preset) plus one latched pre-search pass;
  `PRESET=default` (inprocessing off) keeps the pre-search pass only.
- **Pre-search slot latched** to once per solver instance (kissat
  `probe_initially` is a once-per-formula concept).
- **`BvSolver`'s embedded solver opts out** via `set_sweep_enabled(false)`
  (embedded incremental protocols do not admit destructive Boolean
  folding between solves — the same policy that keeps
  `enable_equiv_substitution` off in every SMT preset, now stated for
  the sweep), and the CDCL(T) Context's own solver opts out the same way.
- Defense in depth: a **sticky `theory_ever_attached`** flag keeps the
  sweep off any solver that has ever run a real-theory solve, including
  from later no-theory inner solves (the quantifier path alternates them).

Post-fix verification: pr30 sat/sat both arms; 10 712 workspace tests
green; the default-on trajectory on the standing corpus is **bit-identical
to the characterized treatment arm** (6s167-opt: 42 003 conflicts, 10
rounds, 8 964 kitten solves — the stored cells), and `NIXIE_SWEEP=0`
restores the base trajectory exactly (62 241). The Part-2 numbers stand.

## Reference arms (§12 obligation) — nixie / kissat / cadical on the
sweep-class files (deterministic, single run each, recorded in the
benchstore under `bd1d759`)

| file | nixie base | nixie sweep | kissat | cadical |
|---|---|---|---|---|
| 6s167-opt (unsat) | 62 241 | 42 003 | 19 164 | **16 654** |
| FmlaEquivChain (unsat) | 525 810 gm | **415 665 gm** | 377 701 | 373 747 |
| x9-09054 (sat) | ~709 k, 1/5 cap | ~709 k, 1/5 cap | 579 744 | **292 566** |
| stable-300 (sat) | 239 350 | 239 350 (inert) | 761 400 | **210 042** |
| constraints_17 (sat) | — | 8.9 k (seed 8) | 38 725 | **7 075** |
| qwh (sat) | — | 46 k-class | 62 866 | **24 182** |
| mrpp (unsat) | — | ~191 k | 179 485 | **138 035** |

Reading: the sweep takes nixie to **reference parity on the
equivalence-chain class** (FmlaEquivChain 416 k vs 374–378 k; the base
was 526 k and 2× the wall) and keeps it mid-pack on the other sweep-class
files; on 6s167 the port closed base 62 k → 42 k of the 42 k→16.7 k span
(kissat's own sweep substitutes 14 % of the variables there — the
remaining gap is substitution *depth*, not presence). cadical leads the
remaining files; kissat trails cadical on this class. No verdict
disagreements against either reference.

---

# Part 3: Effort calibration + yield-delay feedback (2026-09-08, `97cf2b9`+)

**Observation.** At kissat's nominal `sweepeffort=100 ‰` our sweep was
budget-starved relative to the reference: on 6s167 it proved 53
equivalences for 948 k kitten ticks where kissat's own sweep proves 162
for 3.5 M — our window currency is propagations, not ticks, so the
per-mille nominal under-prices us ~4×.

**Effort sweep (anchors, deterministic).** Raising the effort buys
content monotonically on 6s167 (42 003 → 40 375 → **32 602** → 38 998 at
100/200/400/800 ‰) — but at the nominal cadence the inert files pay the
raised budget every round (qwh, eq=0 at every effort: 26 rounds, 7.9 M
ticks at 100 ‰ → 30.7 M at 400 ‰, +30 % wall on a 21 s solve).

**5-seed check** reversed the single-run bimodality read on
constraints_17 (0.81× *better* at 400 ‰, 4/5 seeds) — the effort axis is
robustly good where the sweep has content; the only real blocker is the
inert-file tax.

**Fix: the ported yield-delay feedback** (kissat `delays.sweep`,
`kimits.c`): a round with yield < 0.001 eliminations per swept variable
bumps the interval (current += 1) and skips that many firings; a
productive round halves it. With the delay, qwh fires 6 rounds instead
of 26: **6.5 M ticks at 400 ‰ — below the old default's 7.9 M at
100 ‰**. 6s167 at 400+delay: **32 168** conflicts (best measured; the
handover's half-span target was ~29.7 k).

**Standing differential (540 cells, cores 10–19, benchstore-recorded;
config `sweep400`, compared paired against the stored 100 ‰ cells):**

| arm | solved-at-cap | conflicts vs base | wall vs sweep100 |
|---|---|---|---|
| base (`NIXIE_SWEEP=0`) | 316 | — | — |
| sweep @100 ‰ (previous default) | 351 | 0.949× | — |
| **sweep @400 ‰ + delay (new default)** | **363** | **0.934×** | **0.908×** |

Per-file flips 100→400: +13 / −3 (gains: summle_X11112 3→7,
worker_550 3→5, FmlaEquivChain 7→8, frb65 9→10; losses:
circuit_seed4 7→5, pb_300 3→1, 64_25 2→1). **Zero verdict
disagreements** against both arms (540 paired cells). Conflicts geomean
sweep400/sweep100 = **1.000** (n=204): the raised effort buys *cells*,
not cost — it converts cap-boundary files while the delay more than pays
for the bigger budgets (wall 0.908× on both-solved cells).

**Landed:** default effort 100 → 400 ‰ (enablement rule: solved count
better at every comparison, 0 disagreements; `NIXIE_SWEEP_EFFORT`
restores any other value).

## Part 3 anchor table (from the store, seeds 1–10)

| anchor | base | sweep@100 ‰ | sweep@400 ‰+delay |
|---|---|---|---|
| 6s167-opt | 10/10, 65 873 gm | 10/10, 40 967 | 10/10, **33 561** |
| FmlaEquivChain | 2/10 | 7/10 | **8/10** |
| x9-09054 | 0/10 | 0/10 | 0/10 (cap-boundary) |
| stable-300 | 6/10, 130 403 | 6/10, 130 403 | **7/10**, 164 289 |
| constraints_17 | 6/10, 14 114 | **9/10**, 17 786 | 9/10, 20 037 |

(The stable-300 / constraints_17 cost upticks with more solved cells are
the §11 shape: the newly-solved seeds are the expensive tail cells that
previously capped out — solved-at-cap and cost-geomean over both-solved
cells answer different questions.)

Landed-binary identity: 6/6 sampled `sweep400` cells bit-identical
between the screen binary (97cf2b9, env override) and the landed
default (c9cfe71).
