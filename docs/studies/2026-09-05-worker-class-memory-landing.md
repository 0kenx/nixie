# Worker-class memory: trajectory-neutral reductions (2026-09-05)

Standing-gap lever 2 (worker-class memory, `2026-09-01-standing-vs-kissat-gap-decomposition.md`
Addendum 4/5): after the arena compaction and packed-walk landings, worker_550 peaked at
**965 MB** (kissat: 282 MB → 3.4x) with a search-time floor of ~690 MB over ~511 MB of live
structures. This study lands five trajectory-neutral memory changes and re-measures.

## The changes (all identity-gated, see below)

| # | change | where | mechanism |
|---|---|---|---|
| A | lucky snapshot restricted to `len >= 3` clauses | `solver/lucky.rs` | binaries are BIG-authoritative (no watch entries) and the BIG scan never permutes clause bytes, so restoring a binary's literals with their own bytes was a no-op. On worker_550 only 550 of 10.3 M clauses qualify — the ~190 MB snapshot transient collapses to ~0.4 MB |
| B | BIG `shrink_to_fit` after every full rebuild + before lucky | `solver/mod.rs`, `solver/equiv.rs` | the BIG's per-literal Vecs held elimination-churn capacity: 250 MB capacity vs 164.7 MB live. Exact-capacity after rebuild keeps it at live (binary clauses only shrink downstream) |
| C | walk objective arena-referencing + broken bitset | `solver/walk.rs` | the default-path walk slot IS the clause id: literals are read from the arena (stable for the whole round) instead of being copied into a packed CSR; `in_broken` becomes a bitset. Per-round transient on worker: ~230 MB → ~120 MB (occ CSR + true-count remain). RNG stream and every decision are unchanged (slot values only feed membership/occurrence/literal reads) |
| D | arena compaction gate `live/3` → `live/8` | `memory.rs` (`COMPACT_WASTE_DIV`) | compaction ends in `shrink_to_fit`, so a tighter gate keeps arena capacity near live; copy work bounded at 8x collected bytes (was 3x). Compaction is id-preserving, hence cadence is trajectory-free |
| E | eliminator occurrences as CSR + overflow (`RoundOccs`) with exact presize | `solver/eliminate.rs` | the historical `Vec<Vec<ClauseId>>` paid ~111 MB live in glibc heap bins per round, never returned; the CSR primary is one exact mmap-backed Vec (returned on drop) and mid-round resolvent additions go to lazily allocated per-literal overflow Vecs. A reference differential test (`round_occs_matches_vec_semantics`) pins the combined-view semantics (connect/push/rewrite/swap_remove/clear) to `Vec::swap_remove` semantics — the test caught a real swap_remove bug (primary-vs-overflow hole fill) before the corpus gate did |
| F | DIMACS parse streamed in 1 MiB windows | `dimacs.rs` | the whole-file read buffer, once freed, raised glibc's dynamic mmap threshold to the file size, so every later sub-file-size transient allocated from the main heap and stayed resident after free. Line-complete chunk scanning preserves the token stream exactly |

Negative result included: switching the harness allocator to **mimalloc** (matching the shipped
`nixie` CLI) measured **worse** on this workload — 1453 MB peak vs 810 MB (lazy purging keeps
freed pages resident). Reverted; recorded here so it is not retried.

## Identity gate (the trajectory-neutrality proof)

54-file `/tmp/sc24f` corpus, 62 s cap, old (`cb9f05c`) vs new binary, verdict **and** conflict
count must match bit-exactly: **54/54 identical, 0 diffs** (`/tmp/identity_gate.log` on the
measurement host). Every spot-check during development (crn_11_99_u, mrpp_4x4, 6s167-opt,
si2-b03m, shuffling-2: conflicts/decisions/propagations/restarts all bit-identical). The
`RoundOccs` reference differential test in `eliminate.rs` is the unit-level guard for the
occurrence-list refactor (it caught a real `swap_remove` hole-fill bug pre-landing).

## Memory result (fresh child per run, VmHWM-sampled, 65 s cap, all four arms)

| file | old | new | Δ | cadical | kissat | new/kissat | old/kissat |
|---|---|---|---|---|---|---|---|
| noL-11-14 | 29 | 33 | +14% | 15 | 21 | 1.57x | 1.38x |
| frb65-12-2 | 22 | 22 | 0 | 17 | 12 | 1.83x | 1.83x |
| FmlaEquivChain | 94 | 85 | −10% | 97 | 52 | 1.63x | 1.81x |
| mrpp_4x4 | 15 | 16 | +7% | 13 | 12 | 1.33x | 1.25x |
| g2-slp | 166 | 159 | −4% | 113 | 72 | 2.21x | 2.31x |
| **worker_550** | **965** | **810** | **−16%** | 1874 | 282 | **2.87x** | 3.42x |
| si2-b03m | 120 | 108 | −10% | 172 | 103 | 1.05x | 1.17x |
| shuffling-2 | 665 | 498 | **−25%** | 906 | 269 | 1.85x | 2.47x |

Worst nixie/kissat ratio across the set: **2.87x** (worker_550), down from 3.42x.
The two small-file +4 MB regressions (noL, mrpp) are the CSR/dimacs windows' fixed
overhead on instances whose entire footprint is ~15-30 MB — absolutely small, and
the ratio movement there is within the set's noise.

**Honest scorecard vs the goal's KRs:** worker_550 −16% (target was ≥25%);
worst ratio 2.87x (target ≤2.5x). Both missed but materially moved, and every
change is strictly trajectory-neutral (54/54 identity), so the landing carries no
correctness or search-path risk. The measured blockers for the remaining ~85 MB:

- worker_550's post-parse floor sits ~170 MB above the live composition
  (arena 235 + BIG 157 + refs 39 = 451 MB vs 630 MB RSS; smaps shows the gap
  inside the main anonymous heap, not any single named structure we could
  attribute — needs malloc-level attribution next).
- Each walk round still allocates the occurrence CSR (~80 MB) plus a
  per-clause-id true-count array (~41 MB) on worker; the structural fix is a
  walk over the BIG itself (the BIG already is the binary occurrence
  structure), eliminating both — a bigger port, to be pre-registered
  separately.

## Wall neutrality: the paired 4-arm table (and a measurement lesson)

A first 3-arm re-run of the standing table with the new binary read as 48/54 solved
and +9.4% paired wall — which the identity gate (bit-identical conflict counts on
all 54 files) ruled out as a code effect: identical trajectories cannot cost search
work. Serial re-timing of the "regressed" files matched the old binary exactly, and
the machine's load average had sat at 4-10 during the contaminated run. The honest
instrument is a **paired 4-arm layout** — old, new, cadical, kissat on four pinned
cores in one pass, so both nixie arms see identical machine state:

| arm | solved / 54 @ 60 s | paired wall vs old |
|---|---|---|
| old (`cb9f05c`) | 50 | 1.000x |
| **new (`a820a31` + churn fixes)** | **50** | **0.991x** |
| cadical 3.0.1 | 51 | — |
| kissat 4.0.4 | 50 | — |

0 verdict mismatches; nixie/kissat 1.436x → 1.411x, nixie/cadical 1.245x → 1.239x
(both within the both-solved set churn). Conclusion: **wall-neutral (0.991x,
inside the ±5% band), no solved-at-cap movement** — the memory is free.

Three micro-fixes landed after the first measurement to keep it that way (all
trajectory-neutral, re-verified 54/54 identity + full battery):

- BIG `shrink` gated on slack ≥ 25% of capacity and ≥ 4 Mi — rebuilding lists
  that are already tight paid a full reallocation per elimination round on
  BVE-heavy instances for no memory gain;
- the walk's per-flip literal scratch hoisted out of the flip loop (one
  SmallVec init per flip on walk-dominated instances);
- the eliminator's flush keep-list reuses a round-scratch `Vec` instead of a
  per-flush allocation.

## What remains (next iteration)

- The post-parse floor still carries ~170 MB above the live composition (arena 235 + BIG 157 +
  refs 39 = 451 MB vs 630 MB RSS at post-parse; smaps shows the gap inside the main anon heap,
  not a single allocation we could attribute). Needs malloc-level attribution.
- The walk round still allocates occ CSR (80 MB) + true-count (41 MB) per round on worker —
  the structural fix is a walk over the BIG itself (the BIG already *is* the binary occurrence
  structure), eliminating both. Bigger port; pre-register separately.
- Binary representation density (44 B/binary vs kissat's ~16-24 B) remains the structural 2x.
