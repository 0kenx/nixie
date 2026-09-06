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
* Instrumentation cost, for the record: naive per-event counter branches
  measured **+5.2 %/+5.7 %** whole-run instructions *disabled* (register
  pressure, not the branches themselves). The landed form is compile-time
  gated (`bcp-stats` feature); with the feature off the binary is
  measurably indistinguishable from pre-instrumentation HEAD, and with it
  on, the derived-count design reproduces the naive counters exactly
  (verified number-for-number on 6s167).
