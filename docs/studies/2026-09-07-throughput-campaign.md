# Per-conflict throughput campaign: measured verdicts on the four targets, one sub-bar landing (2026-09-07)

Executed against [`docs/handovers/2026-09-07-throughput-campaign.md`](../handovers/2026-09-07-throughput-campaign.md).
The handover pre-registered four targets and ordered "profile first"; the
profile refuted the root-cause decomposition behind three of the four before
any of them was built. This file records the measurements, the one arm that
was worth building (and its honest sub-bar verdict), and the anatomy
instrumentation that is now permanent.

## Headline

| target | premise (handover) | measured verdict |
|---|---|---|
| 1. arena locality (size-sorted compaction) | "20–40% of arena cache misses" | **refuted** — LLC-load-misses are 0.06–0.37 per propagation; the loop is instruction/branch-bound |
| 2. watcher compression (8-byte) | "10–20% watch-scan cost" | **already closed** by [`2026-08-watcher-8byte.md`](2026-08-watcher-8byte.md) (+0.7%, reverted); the handover's variant is strictly worse (adds a ref→id lookup) |
| 3. BIG/watch single pass | "15–25% per-prop cost" | **refuted by anatomy** — BIG traffic is 1.37 edges/prop on 6s167, 0.07 on crypto1, vs 17.4 watch visits/prop; the merge adds a branch to 100% of visits |
| 4. `propagate_step_limit` hoist | — | landed earlier (`7fc47eb`), below noise — confirmed |
| *(new)* BIG probe fold + `assign` cold split | found by disassembly | **landed** — 22/22 files faster, geomean 1.0104 instructions (capped) / −1.56% (6s167 full solve), bit-identical trajectories; sub-bar, landed under the zero-complexity rule below |

## The profile that decided everything (step 2 of the handover)

`stats_solve` (CaDiCaL preset), `perf stat` pinned to E-core 10, whole run,
6s167-opt full solve (62 241 conflicts, 7.41 M propagations — the handover's
anchor):

| | nixie (HEAD `ad375d1`) | cadical 4.02 | ratio |
|---|---|---|---|
| cycles | 9.75 G | 1.48 G | 6.6× (3.7× is conflicts) |
| instructions | 13.94 G | 2.74 G | 5.1× |
| **instr / propagation** | **1 883** | **1 187** | **1.59×** |
| branches / prop | 389 | 189 | 2.06× |
| branch-misses / prop | 18.2 | 9.6 | 1.9× |
| IPC | 1.43 | 1.86 | 0.77× |
| **LLC-load-misses / prop** | **0.37** | 0.024 | — |

The handover's cost model ("8 entries × 3 cache accesses × ~30 cycles ≈
720 ≈ the measured 770 cycles/prop") requires ~24 LLC/L3 accesses per
propagation. Measured: **0.37 per propagation** — under 2 % of the cycle
budget at E-core LLC latency. The same holds on crypto1 (0.06/prop). This
independently reproduces the 2026-09-02 closure study's finding on
`mrpp_4x4` ("not memory-bound; instruction-count and branch-mispredict
cost") on both campaign anchors. `perf record`: `propagate` = 51–55 % of
samples; nothing else exceeds 7 %.

**Consequence**: any change whose mechanism is "fewer arena/watch memory
misses" attacks ≤2 % of the cost. The gap is ~700 instructions per
propagation of *retired work*, half of it branches.

## The BCP anatomy (now a permanent instrument)

Landed: `nixie_sat::diag_bcp` — process-global counters printed by
`stats_solve` under `NIXIE_BCP_STATS=1` (requires `--features bcp-stats`;
see the harness note at the end for why it is a feature).

6s167-opt (full solve) and crypto1 (`MAXC=40000`):

| per propagated literal | 6s167 | crypto1 |
|---|---|---|
| watch visits | **17.4** | **17.9** |
| — blocker hits | 70.0 % | 45.2 % |
| — miss visits (arena deref) | 30.0 % | **54.8 %** |
| — deleted skips | 0.008 % | 0.0001 % |
| of miss visits: watch **moved** | 47.6 % | **72.4 %** |
| — satisfied first watch | 10.8 % | 3.2 % |
| — parked on satisfied repl | 29.4 % | 12.3 % |
| — unit propagation | 12.1 % | 11.8 % |
| — conflict | 0.14 % | 0.14 % |
| replacement-scan steps / miss | 1.95 | 1.49 |
| 0/1 normalize swaps / miss | 39.8 % | 33.6 % |
| BIG edges | **1.37** | **0.073** |
| BIG propagations | 0.40 | 0.041 |

(The replacement-scan counter was measured with the throwaway per-step form
and dropped from the landed set — it is the only counter that needs a branch
on an inner scan step.)

Reading: the loop's workload is ~17–18 watcher visits per propagated
literal with 30–55 % miss rate, plus a per-literal BIG pass that is *small*
(≤8 % of entry traffic on 6s167, ~0.4 % on crypto1). Against cadical's
~430 cycles/prop, our ~1 317 (E-core, whole-run) is spread across the whole
loop body — per-visit instruction count and data-dependent branches — not
concentrated in any one structure. That is the closure study's conclusion
again, now with exact numerators.

## Target verdicts in detail

### Target 1 — arena size-sort at compaction: premise refuted, not built

1. *The memory argument*: measured LLC misses above. Even attributing every
   L1-miss→L2 hit (~19/prop) full E-core L2 latency, exposure is bounded
   well below the branch-miss term (18.2/prop × ~17 c).
2. *The reference argument*: the handover's mechanism claim about cadical is
   wrong. `opts.arenasort` (`collect.cpp:427`) sorts the *clause pointer
   vector* for iteration determinism, not the arena; cadical's locality
   comes from `arenatype == 3` — a **copying** GC whose 'to'-space order is
   decision-queue × watch lists ("clauses watched by the same literal are
   allocated consecutively", `arena.hpp`). kissat's `collect.c` is an
   in-place **order-preserving** sweep (plus a stable
   irredundant/redundant boundary). Neither sorts by size.
3. *The engineering argument*: reordering variable-size records in place is
   not achievable below ~O(live) scratch (cycle-chasing degenerates to
   stashing ~everything for any real permutation — inversions are cycles),
   so any reorder is a copying GC. That directly reverses the RSS property
   the arena was rebuilt to have ("peak RSS never exceeds the
   pre-compaction footprint"; the fresh-buffer copy measured +25 % peak on
   si2-b03m, `memory.rs` module docs). Paying that for a ≤2 % mechanism is
   not a trade, it is a loss.

Verdict: **not built; do not retry** unless a future profile shows LLC
misses/prop above ~5 on some instance class (worker-class instances with
multi-hundred-MB arenas are the only plausible candidate, and the
worker-class memory studies own that domain).

### Target 2 — 8-byte watcher: closed by prior measurement

[`2026-08-watcher-8byte.md`](2026-08-watcher-8byte.md): 12→8 B watchers
were built, measured +0.7 % instructions (70/72 cells faster, none
significantly), reverted at the ≥1.02 bar. The handover's variant (drop
`clause`, keep `r`) has the *same* density effect plus a new ref→id reverse
lookup on every unit-propagation reason assignment, conflict, and watch
move — strictly more work than the measured variant. Not re-run; the prior
verdict stands.

### Target 3 — BIG/watch single pass: refuted by anatomy, not built

The BIG pass is 1.37 edges/propagated literal on the BIG-heaviest anchor
(6s167) and 0.073 on crypto1 — against 17.4/17.9 watch visits. A merged
structure replaces two loop setups with one, but adds a per-entry binary
tag branch to **every** watch visit (129 M on 6s167) to save a per-literal
probe (7.4 M). The 15–25 % estimate cannot survive those denominators.
It would also reverse the BIG-authoritative BCP design (a measured 2026-09
landing) and require reworking transitive reduction, ELS equivalence
detection and AND-gate factoring off the CSR. Verdict: **do not build**;
the per-literal BIG overhead that *is* real was attacked by the landed
probe fold below.

### Target 4 — step-limit hoist

Landed at `7fc47eb` before this session; structurally correct, below noise.
Confirmed, nothing to do.

## What was actually worth building (landed)

Disassembly of the propagate loop (perf-profile build) showed two pure
codegen defects, both trajectory-identical by construction:

1. **BIG probe fold** (`propagate.rs`): the per-literal emptiness probe
   `!self.binary_graph.get(lit).is_empty()` was a real (non-inlined) `call`
   — the `BigList` view construction is too big for LLVM's cost model —
   followed by post-call register restores and a re-derivation of the same
   `span_of`/`extra_len` reads the loop needs. Folded to: read `span_of` +
   `extra_len` once, probe `plen + xlen != 0` (exactly `BigList::is_empty`:
   both are `primary.is_empty() && extra.is_empty()`).
2. **`Trail::assign` cold split** (`trail.rs`): assignment was a real `call`
   at the BIG-edge propagation site (3.0 M on 6s167) because the rarely-taken
   standalone-test resize path sat inside it. The grow path moved to
   `#[cold] assign_grow`, `assign` made `#[inline]` — the hot core (2 value
   stores + VarInfo write + trail push) now inlines into both BCP paths.

### Measurements (PMU `instructions`, pinned E-core 10, paired binaries)

Isolated pair (identical naive instrumentation in both arms):

| anchor | base | fold+split | Δ |
|---|---|---|---|
| 6s167 full solve | 14.660 G | 14.359 G | **−2.05 %** |
| crypto1 @40k | 7.670 G | 7.571 G | **−1.29 %** |

Landed state (feature off — counters compiled out) vs HEAD `ad375d1`:

| | HEAD | landed | Δ |
|---|---|---|---|
| 6s167 full solve | 13.938 G | 13.713 G | **−1.56 %** |
| crypto1 @40k | 7.259 G | 7.216 G | **−0.60 %** |
| 22-file corpus sample, `MAXC=40000` | — | — | geomean **−1.04 %**, 22/22 non-negative (max −6.0 %) |

Trajectory identity: every file in both tables (plus the two full-solve
anchors) reports **bit-identical** `conflicts=/decisions=/propagations=`
counters and verdicts. Full workspace suite 10 597/10 597, clippy/fmt/doc
clean, Z3 differential parity **169 correct / 0 mismatches / 1 z3-Unknown**.

### Verdict against the bars, honestly

The effect is **inside the ±5 % neutrality band and below the 2 %
pre-registered bar** used by the four prior BCP experiments. It is landed
anyway under the narrow rationale the band allows: the change is
*strictly negative complexity* (removes a call site, splits a cold path;
adds no structure, no policy, no semantic surface), measured uniformly
non-negative across 24 files, and the paired determinism is ±0.01 %
run-to-run. The cost side of the band's trade (maintenance surface,
soundness-adjacent risk) is absent. If a later A/B disagrees, the revert is
one commit with no entanglement.

## What remains of the throughput gap, and what class it is

Per-propagation instruction parity with cadical needs ~−700 retired
instructions inside a loop the closure study already showed compiles
near-optimally for its shape. The anatomy above says the remaining levers
are:

* **visit count** (17.4/prop) — blocker quality and watch-move policy:
  *heuristic class*, matched-null discipline required (the handover's
  expected-outcome framing of "pure engineering" does not survive contact
  with these numbers);
* **per-visit body cost** — register pressure around the take/put watch
  list and the reason-id plumbing; the remaining items (per-literal Vec
  header traffic ~2 %, bounds-check elision on the write-back index ~1 %)
  are individually sub-noise and were deliberately not chased;
* **the other half of the run** — conflict analysis + search glue are ~45 %
  of samples; nobody has profiled `minimize_literal_plain` /
  `shrink_and_minimize_clause` against cadical's the way BCP now has been.

## Addendum (same session, second half): the analysis side

The study's closing map named the non-BCP half (~45 % of samples) as
unexplored. It was decomposed the same way — 55 k-sample `perf record` on
6s167 (single-sample percentages before that were noise: at ~110 samples,
one sample ≈ 0.9 %, which had inflated `minimize` to "18 %" in one capture):

| share of samples (6s167) | |
|---|---|
| `propagate` | 48 % |
| `solve_with_theory` (search glue) | 9.5 % |
| `shrink_and_minimize_clause` + `minimize_literal_plain` + `classify` + `mark_antecedent` | ~10 % |
| allocator traffic (`_int_malloc`+`cfree`+`unlink_chunk`+`memmove`) | ~3 % |
| `memset` (per-conflict full-width `seen` reset) | 1.35 % |
| sorts (bump-order driftsort) | 2.3 % |

The anatomy counters landed with this addendum (`diag_bcp::analysis`, same
`bcp-stats` feature) measure the volumes: **3.65 M bump-sort elements**
across 62 k conflicts (27 % of sorts over the 64-element insertion limit,
max 1 304), 1.91 M shrink-sorted literals, 4.14 M `minimize_classify`
calls, 2.78 M minimizer child steps.

### The persistent-scratch arm (cadical `analyzed`-member port): measured, REVERTED

The obvious candidate was the cadical-faithful restructuring: `analyzed` /
`unit_analyzed` as persistent member vectors (capacity survives across
conflicts), sort-key scratch as members, and `clear_analyzed_literals`-
style exact seen-reset instead of the entry memset. Built in full
(bit-identical trajectories on all 22 corpus files + both anchors — the
exact-coverage reset carries a debug-mode full-scan assert replacing the
silent scrub).

**Verdict: neutral-to-negative, reverted.** Instructions (paired, pinned):

* 22-file corpus (`MAXC=40000`): geomean **+0.24 %**, 13 files improved
  (≤ +0.9 %), 9 small files regressed (−0.07 % each);
* 6s167 full solve −0.87 %, crypto1@40k −0.59 %;
* **worker_550@30k (550 k vars — the design's target case for the memset
  cut): +0.13 % slower.** The full-width `seen` reset is bandwidth-cheap
  relative to even this file's per-conflict work, and glibc's fast-path
  malloc/free of the spilled SmallVecs costs about what the persistent
  buffers' extra clear bookkeeping does.

With one measured regression and a geomean deep inside the band, the arm
fails every landing rule (it also adds a real invariant — exact coverage
of `seen` writers — where the BCP arm added none). Reverted wholesale;
the instrumentation extension alone lands.

### Where this leaves the constant-factor program

Six measured closures now bracket the per-conflict cost: flat arena
(−4.5 %), 8-byte watcher (+0.7 %), word-split (+0.04 %), write-elision
(landed), BIG probe fold + assign cold-split (landed, +1.4 % geomean),
persistent analysis scratch (reverted, +0.24 %). Both halves of the run
have been decomposed to the level of "the remaining delta vs cadical is
spread across the whole loop body / analysis walk, with no lever above
~1 %". Closing the rest of the 1.4–1.6× per-propagation and per-conflict
instruction gap means *doing less work* — visit counts (blocker quality,
watch-move policy), miss-visit rates (Gent's saved-position scan — a
semantic policy), bump-set reduction (cadical's
`bumpreasonlimit`-capped reason bumping) — all heuristic-class changes
that require the matched-null machinery of `docs/BENCHMARKING.md`, or the
kissat-shape single-pass BCP (inline binary watchers), which is gated on
reworking the BIG's non-BCP consumers (transred, ELS, AND-gate factoring).

## Second addendum: the loop is stall-bound — PGO closes the question

After the analysis-side closure, two further engineering arms were built and
measured (both **negative**, both reverted):

**BIG-pass slice iteration.** Three variants (field-borrowed `BigList` with
deferred conflict tail; the same with the conflict tail inlined at field
level; two plain slice loops with a shared body macro replacing the
`Chain` iterator's per-edge branch). The disassembly showed the index form
paying two bounds checks + two base reloads per edge; the slice forms
remove them. Measured (properly rebuilt, md5-verified binaries): best
variant **−0.36 % on 6s167, +0.29 % on crypto1** — mixed, sub-bar.
LLVM's index-loop codegen beats all three hand-restructures; the watch-write
bounds-check elision (unchecked stores under the documented-invariant
pattern) never got a clean isolated measurement after the build-fingerprint
trap below, and is not worth pursuing at that effect size.

**PGO** (`-Cprofile-generate`/`-profile-use`, trained on 6s167 + crypto1 +
3 corpus files, the recipe from `nixie-sat/Cargo.toml` that nothing had
ever exercised):

| 6s167 | base | PGO |
|---|---|---|
| instructions | 13.71 G | **12.78 G (−6.8 %)** |
| **cycles** | 8.73 G | **8.62 G (−1.3 %)** |
| IPC | 1.57 | 1.48 |
| branch-misses | 134 M | 136 M |
| crypto1@40k | instr −7.0 %, **cycles +0.0 %** | |

This is the decisive experiment for the whole campaign's premise. PGO
removes 7 % of retired instructions — more than every landed source change
of this campaign combined — and the wall does not move, because **the
propagate loop's cycle cost is not instructions: it is the 18.1
data-dependent branch misses and ~19 L1→L2 loads per propagation**, which
no inlining, layout or instruction-count change removes. (PGO is therefore
*not* proposed for the standing builds: −7 % instructions at 0 % cycles
buys nothing but build complexity.)

**PEBS load-source attribution** (`perf mem`, ldlat 30, 52 k sampled
propagate loads) closes Target 1 at every cache level, not just LLC: the
long-latency loads are **27 % L1 hits / 13 % L2 hits / 3 % L3 hits /
0.2 % L2 misses**. They are slow because they sit on dependent
pointer-chains (watcher → arena header → literals), not because data is
far — no arena reordering, prefetching or layout change shortens a chain
that already hits in L1. The 2026-08-22 studies' conclusion ("density is
not where the propagate cost lives") is confirmed at the cycle level.

### Where the instruction ratio actually lives (asked: "Rust codegen?")

Correct the denominator first: **per-propagations is inflated**. cadical
runs 138.5 props per conflict against our 119.0, so the honest same-work
comparison is **per-conflict: 220.3 k vs 164.8 k instructions = 1.34×**
(per-prop reads 1.56×). Inside the loop, per entry-event (visit or BIG
edge): ours **40 instr** (5.59 G propagate instructions, the
instruction-sampled share, over 140 M events) vs cadical **~24** (their
entry count derived from `ticks = 1 + ceil(16n/64)` → n ≈ 22/prop; their
share is cycle-sampled, so treat as ±20 %). ≈ **1.6× per entry**.

Attribution of the extra ~15 instructions per entry, from the session's
disassembly pass:

* **Rust safety/codegen, ≈ 7–9**: the bounds-check pair on every
  `watches[write]` store; the values-array base reload after each `&mut`
  arena call (aliasing — C++ caches `vals` in a register across the
  loop); `read`/`write` as `usize` indices with `lea` math vs C++
  pointer post-increment; capacity checks on every watch-move push;
  SmallVec inline/heap machinery.
* **Deliberate structure, ≈ 6–8**: the 12-byte watcher carries BOTH the
  clause id and the arena ref (3 loads + 3 stores per copy vs their
  2+2 — the 8-byte variant was measured +0.7 % and reverted at the bar);
  the `write != read` elision branch (our measured win; cadical copies
  unconditionally); the BIG two-pass with phantom-tick accounting and the
  bounded-check branch chain; the LRAT/step-limit branch chain.

**The twist that matters**: the codegen half is real instructions but not
real wall time. Measured three ways — PGO removed 7 % of instructions
(exactly the removable codegen class) for **0 % cycles**; the slice
rewrites removed the bounds checks and base reloads and measured
neutral-to-negative; and the branch-miss *rates* are the same in both
solvers (4.7 % vs 5.1 %) — we pay 2× the misses per propagation because
we execute 2× the branches per entry, which is the structural half. The
IPC term (1.57 vs 1.86) is the same story: their loop holds fewer live
values (16-byte watcher in two registers, pointers not indices), so each
stall overlaps more work. Conclusion: Rust codegen accounts for roughly
half the instruction gap, ~none of the cycle gap; the cycle gap scales
with the branch/visit structure.

### The final decomposition (6s167-opt, E-core)

| factor | ratio | class |
|---|---|---|
| wall | **5.8×** | |
| = conflicts | 3.74× | heuristic (search quality; corpus-wide standing is 0.88× — this anchor is a tail case) |
| × instructions/prop | ~1.45× | measured floor: restructures ±0.4 %, PGO −7 % (no cycle effect) |
| × stall efficiency (IPC) | ~1.25× | branch-miss/L1-latency bound; immune to codegen |

Everything that remains above ~1 % is one of:

1. **visit count** (17.4/prop) and **miss-visit structure** (30–55 % miss
   rate, 48–72 % of misses move the watch, 1.95 replacement-scan steps) —
   policies like cadical's Gent saved-position scan (`clause->pos`,
   JAIR'13) or blocker-refresh strategies. *Heuristic class*: they change
   which watch moves and which clauses park where, i.e. the trajectory;
   they require the matched-null machinery of `docs/BENCHMARKING.md`, not
   trajectory identity.
2. **the conflicts factor itself** — the standing-gap program's territory
   (restart/reduce/branching policy deltas vs cadical/kissat).
3. **kissat-shape single-pass BCP** (inline tagged binary watchers, 4–8
   byte watch granularity) — the one structural rewrite left; it changes
   tick accounting and stored watch order, so it is heuristic-class too,
   and it must rework the BIG's non-BCP consumers (transred, ELS, AND-gate
   factoring).

The constant-factor program on the current architecture is closed: eight
measured source arms (four landed, four reverted) plus PGO bound the
recoverable instruction share, and the PGO cycle result shows even a full
instruction-parity rewrite would recover at most the IPC term.

## The lever catalog (what "keep chasing" should buy, ranked)

Seed-matched diagnostic first (6s167, 5 seeds each): nixie conflicts
{62.2k, 55.3k, 66.3k, 70.4k, 74.9k} vs cadical
{16.7k, 26.8k, 25.2k, 16.3k, 26.4k} — **median gap 2.6×, and cadical's
worst seed beats our best by 2×**. The single-seed 3.74× was partly luck;
the gap itself is config-systematic. That makes the conflicts program the
top lever by an order of magnitude over anything left in per-conflict
cost.

### Tier 1 — the conflicts program (search quality; matched-null class)

The corpus aggregate stands at 0.88× conflicts vs cadical, so this is a
*class/tail* problem, not a uniform one. Order of attack:

1. **Diagnose the class** (cheap, existing infrastructure): per-file
   conflicts-gap distribution over the standing corpus at ≥5 seeds
   (`benchstore.py` cells exist); tag the tail files by family. 6s167 is
   crypto — is the gap concentrated there?
2. **Search-shape diffs per tail file** vs cadical: the visible one on
   6s167 is **stable-mode share: ours 56 % vs their 36.5 %** (we
   stabilize far more); also restarts/conflict (currently ~14 vs ~13.8 —
   matched), DB size at equal conflicts, learned-LBD distribution,
   decisions/conflict (3.39 vs 3.95).
3. **Policy ports, each pre-registered with matched null:**
   - stabilization/restart schedule (EMA-driven stable switching — the
     56 %-vs-36.5 % share is the biggest unexplained shape delta);
   - reduce/retention schedule (the `NIXIE_CADICAL_REDUCE` /
     `NIXIE_KISSAT_REDUCE` arms already exist behind env gates — evaluate
     them at seeds on the tail class instead of re-porting);
   - inprocessing mix on the tail class: cadical *substituted 12.5 % of
     all variables* on 6s167 (sweep/equiv), vivified 2.84 % of clauses,
     and ran OTF clause improvement on 5.3 % of conflicts — compare our
     per-pass yields on the same files;
   - rephase/walk schedule deltas.

Gates: conflicts and solved-at-cap with matched nulls, never instructions
(the PGO result shows instructions are uninformative for wall time).

### Tier 1 executed: the class, the mechanism, and a causal test (this session)

**Class distribution** (standing corpus, both-solved files, nixie
current-default median over 5 seeds vs cadical, from stored
`conflicts_to_verdict` cells):

| tail (>1.5×) | ratio | nixie seed range | secondary (1.2–1.75×) | parity | we win |
|---|---|---|---|---|---|
| constraints_17 **5.04×** | | 9.6k–119k (**12×**) | stable-300 1.75×, x9 1.62×, crn 1.53× | circuit×3, summle×3, Break_06, si2 | worker_20 **0.10×**, Break_08 0.19×, shuffling 0.20×, j3037 0.23×, af 0.28×, frb 0.45×, barman 0.52×, ITC 0.55× |
| 6s167 **4.43×** | | 70k–82k (tight) | mrpp 1.41× | | |
| qwh.50 **4.05×** | | 27k–280k (**10×**) | | | |
| worker_550 **3.05×** | | 2.5k–55k (**22×**) | | | |

n=25, geomean 0.892 (the standing 0.88×), median 0.985 — the aggregate
hides **four files that carry the whole gap**, three of them with 10–22×
seed instability (nixie's search is *unreliable* there; cadical is
consistent).

**Mechanism found on the tail** (shape stats at matched conflict caps):

| | worker_550 | qwh | constraints_17 | 6s167 |
|---|---|---|---|---|
| our avg LBD | **517.6** | **241.2** | 27.7 | 11.7 |
| our restarts (per conflict) | **19 (1/1344)** | 772 (1/65) | 4188 (1/12) | 4107 (1/12) |
| cadical restarts (per conflict) | 226 (1/22.6) | 640 (1/37.8) | 319 (1/22.2) | 1206 (1/13.8) |
| our dec/conflict | 10.1 | 23.6 | 5.6 | 3.7 |
| cadical dec/conflict | **58.5** | 21.0 | 3.7 | 3.9 |
| our stable share | 62 % | 68 % | 57 % | 53 % |
| cadical stable share | 75 % | 48 % | 32 % | 36.5 % |

The restart scheme itself is verified ported correctly (windows 33/1e5,
glue = levels−1, 10 % focused margin, per-conflict update, mode-swap —
checked against `restart.cpp`/`averages.cpp` line by line). The stall is
an **equilibrium property**: when the glue stream is uniform-huge
(worker_550: every learned clause ~LBD 500), the fast EMA never crosses
1.10× slow → focused restarts stop firing → the search runs deep without
recovery. cadical's glue on worker_550 is also large (~126) but *noisy*
(conflict depth varies), so their EMAs cross every ~22 conflicts.

**Causal test** (`RESTART=geometric`, unconditional interval restarts,
single seed):

| | base | forced restarts | cadical |
|---|---|---|---|
| qwh | 134 113 | **63 395 (−53 %)** | 24 182 |
| constraints_17 | 87 007 | **49 893 (−43 %)** | 7 075 |
| worker_550 | 25 532 | >200 000 (**8× worse**) | 5 113 |
| 6s167 | 62 241 | >200 000 (3× worse) | 16 654 |

The restart stall IS causal on the seed-unstable tail (qwh,
constraints_17) — and blanket restart cadence splits the class 2-and-2,
because worker_550/6s167 need search depth. cadical wins all four *with*
frequent restarts: their restarts are **productive** — the worker_550
dec/conflict gap (58.5 vs 10.1) says their phases/branching make each
restart land on a different productive shallow region, while ours thrash.

**Pre-registered treatments** (all matched-null class):

* **T1 — stall-aware restart** (`NIXIE_RESTART_STALL=<k>`, landed this
  session as an env-gated arm, **default off**): fire a focused restart
  when the gap since the last restart exceeds `k`× the restart-gap EMA
  (window 8, floor 200 conflicts) — the cadical Glucose condition has no
  max-gap fallback, so a uniform-huge glue stream silences it. Inert by
  construction on healthy cadence (verified bit-identical default-off on
  6s167/crn_11 full solves and 22-file-equivalent behavior; the trigger
  cannot fire when restarts already outpace 8× their own EMA).

  **5-seed screen** (base vs `k=8`): constraints_17 geomean 45.4k →
  14.7k (3.1×), qwh 91.3k → 52.1k (1.75×), worker_550 10.5k → 16.4k
  (1.57× worse).

  **Full study** (10 seeds × {base, stall8, null8} × tail files, 60 s+
  caps, cores 10–19; 54-file × 5-seed standing safety screen):

  | file | treatment/base | null/base | treatment/null | solved@10 |
  |---|---|---|---|---|
  | constraints_17 | **2.66×** | 1.81× | **1.47×** | 8→10 |
  | qwh | **1.65×** | **1.65×** | **1.00×** | 7→9 |
  | worker_550 | 1.11× | 0.88× | 1.25× | 8→8 |
  | 6s167 | 0.95× | 0.96× | 0.99× | 10→10 |
  | tail geomean | **1.46×** | **1.26×** | **1.16×** | |

  **The null corrects the attribution.** The first null build was
  broken (its scrambled-EMA bookkeeping never ran — the arm silently
  degraded to a constant 800-conflict-gap trigger, near-inert on
  healthy-cadence files), and under that weak null the treatment looked
  uniformly null-clean. The proper null (gap-history EMA fed from
  pseudo-randomly reordered ring entries; restart-rate matched, e.g.
  cons17 seed 0: treatment 207 restarts / null 386, same magnitude
  family) shows: **qwh's entire effect is generic "add restarts of this
  magnitude"** (null/base = treatment/base = 1.65×); **drought
  alignment adds real signal only on constraints_17 (1.47× over null)
  and worker_550 (1.25×, noisy)**. Tail-wide: 1.46× total, of which
  1.26× is the generic restart rate and 1.16× the aligned trigger.

  **Max-gap follow-up** (`NIXIE_RESTART_MAXGAP=<n>`, landed env-gated):
  the null's generic-cadence finding suggested a flat floor on the restart
  gap — the MiniSAT-lineage mechanism, no EMA, no semantic signal at all.
  Matrix (10 seeds, same cells):

  | arm | tail geomean vs base | worker_550 | qwh | constraints_17 | 6s167 |
  |---|---|---|---|---|---|
  | stall8 (ref) | 1.46× | 1.11× | 1.65× | 2.66× | 0.95× |
  | maxgap 250 | 1.09× | 1.04× | 0.92× | 1.51× | 0.96× |
  | maxgap 500 | 1.27× | 1.61× | 1.40× | 1.19× | 0.99× |
  | **maxgap 1000** | **1.46×** | **2.18×** | 1.30× | 1.63× | 0.99× |
  | maxgap 2000 | 1.19× | 0.85× | 1.65× | 1.52× | 0.94× |

  maxgap=1000 equals the stall trigger's tail effect **with a better
  per-file profile** — it *fixes* worker_550 (2.18×, 10/10 solved vs
  base's 2 TOs) and is neutral on 6s167 (0.99×) — and the response is
  non-monotone in the constant (2000 collapses worker_550 to 0.85×),
  pinning the operating point at ~1000. At the right constant the
  drought-*alignment* premium is ≈ zero: the flat floor captures
  everything the EMA trigger does. 6s167 remains untouched by restart
  policy at any setting — its 4.4× is T3's (substitution) territory.

  **Default flip: NO.** Paired differential (54 files × 5 seeds, 60 s,
  fresh base arm vs maxgap=1000): solved-at-cap **157 → 154 (−3)** with
  17 gained / 20 lost boundary cells and **0 verdict disagreements**
  (both-solved). The enablement rule's "solved count not worse" bar
  fails; the corpus cost of the flat floor is small but real at the
  60 s cap, so both restart arms stay env-gated. A future flip needs
  either a cheaper constant, a class gate, or a portfolio shape (the
  `SEEDS` harness's later arms convert exactly these tail wins at zero
  risk to files the default arm already solves).

  **Safety screen** (54 files × 5 seeds, 60 s, base vs stall8):
  solved-at-cap 153 → 151 (8 files −1/−2, 6 files +1/+3, notably
  mp1-Nb7T42 +3), **0 verdict disagreements** where both arms solved.
  The enablement rule's "solved count not worse" bar fails by 2 cells:
  **no default flip at k=8.** The arm stays env-gated; the next
  iteration's axes are gentler triggers (k = 16/32, higher floors) or
  drought-gated variants that keep worker_550/6s167/summle untouched —
  and the null shows any such variant must be compared against the
  *generic-restart* control, not just base.
* **T2 — restart productivity** (phase quality): why do cadical's
  restarts help them on worker_550/6s167 and ours hurt? dec/conflict is
  the metric; targets are the rephase/walk cadence and target/best phase
  machinery. This is the lever that must land for T1 to be safe on the
  deep-search tail.
* **T3 — equivalence substitution per-class gating**: ours substitutes
  **zero variables on every file** (default off since the 2026-09-06
  corpus-negative study) while cadical substituted 12.5 % of all
  variables on 6s167 — where the disabled feature had measured 0.349×
  conflicts. The ELS=1 arm exists; the study needs a gate rule
  (instance-class or effort-scheduled) rather than a global flip.

### T2 executed: restart productivity = never entering the starvation regime

Three candidate mechanisms were checked and one confirmed:

* **Port divergences: none.** Rephase mode (1 = always) and interval
  (base 1000, growth ×(k+1) — cadical's effective ~1110 on 6s167) match;
  trail reuse, target/best phases and the walk are ported with matching
  counters.
* **H-reuse rejected** (`REUSE=0`, 5 seeds): worker_550 geomean 10.5k →
  **28.4k (2.7× worse)** — the reused trail is load-bearing for deep
  search, not the thrash mechanism. `stall8+reuse0` loses to `stall8`
  alone everywhere.
* **The bimodality is decided early** (worker_550 @ 2 000 conflicts):
  the bad seed's avg LBD is already **1 131** vs **393–473** for the
  good seeds (which then solve at 2.4–21k), and cadical has **154
  restarts** by then against our 6–9. The tail problem is not capability
  — our best seed beats cadical (2 463 vs 5 113) — it is *reliability*:
  some seeds learn fat clauses from the start and never recover.
* **Complete mechanism**: Glucose's slow glue EMA (window 1e5 ≈ the
  run-global mean) fires on *sustained degradation* (fast ≥ 1.10 ×
  slow). Instances whose glue trend is fat-early-then-improving
  (worker_550/qwh/constraints_17) never cross it — restart starvation
  from conflict ~1, self-reinforcing (no restarts → deep fat conflicts
  → flat EMA). cadical never enters the regime because its frequent
  restarts keep the glue stream shallow and noisy from the start.

T2's answer to "why are cadical's restarts productive": they *never
stop*. The remaining T2 question — why `stall8` regresses worker_550
(1.57×) when it recovers qwh/constraints_17 — is whether the forced
restarts break genuinely productive deep runs there; gentler triggers
(k = 16/32) or gap-EMA floors are the tuning axes inside the T1 study.

### T3 executed: portfolio conversion — the ELS tail wins land at +8 standing cells

The static-gate family was falsified four ways in parallel studies
(online observables, gate density, placement, SCC mass — the last two
*inverted*: every ELS anchor-winner has zero surface structure, the
biggest losers have the most). What survived is the shape this study's
max-gap section named: **a portfolio arm** — the ELS one-shot is not a
default and not a gate, but a *second trajectory* the harness rolls when
the default arm's budget exhausts.

`cnf_solve` gained an `els` arm token (`SEEDS=default,els
ARM_CONFLICTS=<n>,<rest>` — `ELS=1` semantics on a fresh solver;
example-only change, no library code). Screen (54 files × 5 seeds,
60 s cap, cores 10–19):

| config | solved-at-cap | gained | lost | verdict disagreements |
|---|---|---|---|---|
| default | 153 | — | — | — |
| **portfolio: default@100k → els** | **161 (+8)** | 13 | 5 | **0** |
| portfolio: default@250k → els | 153 (0) | 10 | 10 | 0 |

The gains are exactly the ELS-anchor class the gates could not isolate:
**FmlaEquivChain ×5** (base TOs it; the ELS arm solves — the equivalence
chain is *invisible* to every static observable but folded by the pass
itself) and worker_550 ×2. The losses are truncation (circuit_48in64out
needs >100k conflicts of default; 64_25, summle_X11112 reshuffle). The
budget constant is the trade: 100k keeps most near-cap default wins and
still buys the second trajectory; 250k truncates more than the ELS arm
recovers.

This is a **harness configuration**, not a solver default: the standing
table's invocation would carry the `SEEDS`/`ARM_CONFLICTS` prefix. The
`chrono`-arm precedent is identical (converts cadical-only standing
losses at zero risk). Both restart arms (`NIXIE_RESTART_STALL`,
`NIXIE_RESTART_MAXGAP`) are likewise portfolio-eligible — e.g.
`SEEDS=default,els,maxgap:1000` composes fresh trajectories for the
whole tail class inside one deterministic budget schedule.

### Tier 2 — miss-visit and watch-move policies (per-visit × search coupling)

- **Gent saved-position scan** (`clause->pos`, cadical/JAIR'13): starts
  the replacement scan at the last replacement site. Instruction ceiling
  small (1.95 → ~1 scan steps ≈ 1.7 %), but it changes *which* literal
  becomes the new watch → watch distribution → search; pre-register with
  matched null. Needs a header field: the 12-byte header is pinned by
  the cache-line tests — steal bits (lbd is u16 but saturates far above
  every consumer's ≤10 threshold; pos needs ~8 bits for practical
  clauses) or re-price the header.
- **Blocker-refresh policy**: miss rate is 30 % (6s167) to 55 %
  (crypto1) — every 10 pp of hit rate removes ~13 M arena visits on
  6s167 (~1–2 % instructions plus their stall exposure). E.g. prefer
  recently-true literals as blockers when parking on satisfied
  replacements. Changes parking → trajectory → matched null.
- **Watch-move rate**: 48–72 % of miss visits move the watch; moves drive
  revisit pressure. `MOVED`/visit from the anatomy counters is the
  metric; the null must hold visit counts fixed while scrambling the
  move choice.

### Tier 3 — the structural rewrite (kissat-shape single-pass BCP)

Downgraded by this campaign's anatomy relative to the handover's 15–25 %
estimate: BIG traffic is 8 % of entry events on 6s167 and 0.4 % on
crypto1, and merging the passes does not touch the large-clause visit
cost. The real content is the per-entry *shape*: inline tagged binary
watchers, 4–8 byte watch granularity, word-indexed arena — attacking the
measured 21 branches/entry and the IPC term. Cost: tick accounting (=
restart schedule = trajectory), the 12-byte-header pin, and reworking the
BIG's non-BCP consumers (transred, ELS, AND-gate factoring). Only as a
deliberate kissat-convergence program; per-entry instruction gains of
30–40 % *if* the shape converges, cycle gains uncertain (stall-bound
evidence).

### Measured dead — do not retry

Arena locality (dead at LLC *and* L2/L1 by PEBS), watcher density (8-byte
+0.7 %, word-split +0.04 %), PGO for wall time (−7 % instructions, 0
cycles), BIG-pass restructures (slice/index variants ±0.4 %), persistent
analysis scratch (+0.24 % geomean, worker_550 regression), reverting the
write-elision branch (it is a measured win).

## Harness notes (all bitten this session)

* **Pin *outside* perf**: `taskset -c 10 perf stat …`. With `perf stat
  taskset …` the run migrates across clusters and summing both cluster
  counters double-counts (~2× totals). Pinned instruction counts repeat to
  ±0.01 %.
* **Cargo fingerprints example binaries per feature set** and hardlinks
  them into `target/*/examples/`; after alternating `--features` builds the
  plain name may point at the last-built variant. Verify which one answered
  (e.g. `NIXIE_BCP_STATS=1` must print counters) before trusting a number.
* **Worktrees lack untracked corpora**: `nixie-testcorpus` resolves from the
  workspace root, so `satcomp2024/`/`smt-lib/` must be symlinked into any
  worktree running the suite (else corpus tests panic `[corpus-missing]`,
  which looks exactly like a soundness failure in the summary line).
* `nixie-cli interpolate::tests::test_temp_proof_log_is_cleaned_up` flakes
  once per ~10k tests under heavy parallel load (temp-file collision);
  passes in isolation on both arms. Pre-existing.
* **Worktrees can vanish mid-session** (shared box; /tmp hygiene or
  another agent's sweep): the max-gap arm's verified code was lost
  uncommitted once and re-applied. Commit early in the worktree even for
  study arms, or keep the patches outside /tmp.
* **A silently-degraded null arm is worse than no null**: the broken
  null (never-updated EMA → constant threshold) produced a *plausible,
  clean-looking* result table that mis-attributed qwh's effect to
  drought alignment. The repair: verify the null actually fires (compare
  restart counts across arms at a fixed conflict cap) before trusting
  any treatment/null ratio.
* **`cnf_solve`'s `RESTART=luby` token is not recognized** (falls through
  to the CaDiCaL preset silently — trajectories identical to base), and
  `INTERVAL=N` does not change the geometric arm's trajectory (geo22 ≡
  geo200): verify a knob actually moves counters before using it as an
  arm. `RESTART=geometric` does switch strategies.
* **Worktree builds go stale silently after RUSTFLAGS/feature flips**: two
  variant measurements this session were of stale binaries (`Finished in
  0.1 s` after an edit, no `Compiling` line). Protocol that fixed it:
  `touch` the edited file, require a real rebuild, and `md5sum` the binary
  before trusting any A/B number.
* **Feature-build analysis counters run unconditionally**: the
  `bcp-stats`-gated counter blocks in `conflict.rs` have no runtime env
  check (the propagate-side ones do). A feature build pays full counter
  cost regardless of `NIXIE_BCP_STATS`; never benchmark one.
* Instrumentation cost, for the record: naive per-event counter branches
  measured **+5.2 %/+5.7 %** whole-run instructions *disabled* (register
  pressure, not the branches themselves). The landed form is compile-time
  gated (`bcp-stats` feature); with the feature off the binary is
  measurably indistinguishable from pre-instrumentation HEAD, and with it
  on, the derived-count design reproduces the naive counters exactly
  (verified number-for-number on 6s167).
