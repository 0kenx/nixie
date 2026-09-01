# Shrink-next reap port (cadical `shrinkreap`, default-on): pre-registration (2026-09-01)

Next slice of the perf arc after the write-elision landing (`d3261a6`).
Target picked from a fresh instruction profile on the surviving corpus
(`/tmp/sc24f`, `MAXC=20000`, no-LTO symbols build):

| file | top self-cost symbol | share |
|---|---|---|
| worker_550 | `shrink_and_minimize_clause` | 27.5 % |
| circuit_64in | `propagate` | 30.0 % |
| g2-slp | `eliminate_phase` | 59.3 % |

Inside `shrink_and_minimize_clause` on worker_550, the dominant hot
loop is the **block trail scan** (`conflict.rs:1691`): the linear
backward walk that pops the newest shrinkable literal by testing
`MF_SHRINKABLE` on every trail entry it passes. worker_550 runs at
13.6 decisions/conflict with ~945 propagations/decision, so each block's
scan crosses enormous trail stretches to find a handful of flagged vars.

**Port-fidelity gap, not a new heuristic**: CaDiCaL 3.0.1 solves exactly
this with `opts.shrinkreap` — **default 1 (on)** (`options.hpp:206`,
"use a reap for shrinking"): `shrink_literal` pushes
`dist = max_trail − v.trail` into a monotone radix heap
(`src/reap.{cpp,hpp}`, 33 buckets) at marking time, and `shrink_next`
pops the minimum distance — `pos = max_trail − dist` — never scanning
unflagged trail entries. Our port's own comment says "without the reap".
This restores reference behavior.

Identity argument (Gate 1 must confirm): every `MF_SHRINKABLE` var of a
block is pushed exactly once at marking (block literals in the marking
pass, walk-discovered ones in `shrink_literal`); the flags are fully
reset between blocks (success path converts to `MF_REMOVABLE`, failure
path unsets), so the linear scan's popped sequence — newest flagged
trail position first — is exactly the reap's min-dist sequence. The scan
and the marking sites have no side effects beyond the flags/reap.

Not taken (measured or closed already):
* reason-`SmallVec` scratch pooling for the block walk — the
  minimize-scratch-pool study closed this class at ~1 % neutral;
* zero-copy reason iteration — blocked by `deny(unsafe_code)` and the
  recursive minimizer's `&mut self` reach;
* eliminate round-2+ economics (g2-slp lever) — heuristic class,
  needs its own matched-null study.

## The change

1. New `oxiz-sat/src/reap.rs`: faithful safe-Rust port of CaDiCaL's
   `Reap` (monotone radix heap, 33 buckets, `last_deleted` bucket-0
   protocol). `pop() -> Option<u32>`; `None` (precondition violation,
   cannot happen given the invariants) degrades the block walk to
   `failed` — the sound plain-minimization fallback — instead of
   panicking.
2. `Solver.shrink_reap: Reap`; `shrink_block` gains a max-trail
   pre-pass (cadical computes it while finding the block bounds), the
   marking pass pushes `max_trail − trail_index` per block literal,
   `shrink_literal(lit, blevel, max_trail)` pushes walk-discovered
   distances, and the scan loop is replaced by
   `pos = max_trail − reap.pop()`. `reap.clear()` at both block exits,
   exactly like CaDiCaL's `shrink_block` epilogue.

## Go / no-go (pre-registered BEFORE measuring)

1. **Gate 1 — trajectory identity**: 54-file `/tmp/sc24f`, `stats_solve`,
   `MAXC=60000`, default seed vs `precompile/d3261a6`: counters + verdict
   bit-identical on every file.
2. **Gate 2 — instructions** (`cpu_core/instructions`, pinned, 3 reps,
   private target dir): `MAXC=40000` on the shrink-class target
   {worker_550} — **≥ 1.02**; controls {circuit_64in, si2-b03m, noL-11-14,
   frb45-21-2} in **0.99–1.01**; 54-file both-solve corpus geomean ≥ 1.00.
   1.00–1.02 on the target class = neutral → revert and record.
3. **Gate 3 — soundness** (if landed): workspace suite, clippy/fmt/doc,
   `diff_equiv` ≥ 100 k, corpus verdict sweep 0 mismatches, SMT
   differential 0 disagreements, z3 parity clean.

## Results — REVERTED (corpus bar failed at every configuration; the trail-scale hypothesis is falsified)

**Gate 1 — trajectory identity: PASSED at every configuration tried**
(54/54 files bit-identical vs `precompile/d3261a6`, `MAXC=60000`) —
the pop-sequence identity argument held everywhere, including both
hybrid thresholds. The mechanism is sound; only its cost is wrong.

**Gate 2 — instructions** (`cpu_core/instructions/`, P-core pinned, 3
reps, `MAXC=40000`; reps repeat to ~1e-5 relative):

*Pure reap (first implementation):* worker_550 **1.0738** ✓, but
noL-11-14 0.9879 ✗ and frb45-21-2 0.9762 ✗ — the reap's per-literal
constant loses to the 2–7-skip scan on small-trail instances.

*Hot-path fast paths* (single-element bucket, bucket-0 direct pop):
worker 1.0819, frb45 0.9814 — improved but still out of band.

*Scan/reap hybrid, threshold 4096 (scan below, reap above; pop sequence
provably identical either way):* all class bars green —

| file | old/new | band | |
|---|---|---|---|
| worker_550 | **1.0718** | ≥ 1.02 | pass |
| circuit_64in | 0.9997 | 0.99–1.01 | pass |
| si2-b03m | 0.9997 | 0.99–1.01 | pass |
| noL-11-14 | 0.9975 | 0.99–1.01 | pass |
| frb45-21-2 | 0.9952 | 0.99–1.01 | pass |

— but the **54-file corpus geomean = 0.9992 < 1.00** (bar failed):
mid-size dense-flag instances pay: qwh.50.1250 **0.9715**, summle ×3
0.9858–0.9887, pb_300_09 0.9917, rbsat 0.9943.

**Threshold sweep — the falsification:** if the reap's benefit were a
function of trail scale, some threshold would win worker while sparing
the corpus. Measured (worker/qwh/summle old=163.69 G/42.32 G/37.62 G):

| threshold | worker | qwh | summle |
|---|---|---|---|
| 4096 | 1.0718 | 0.9715 | 0.9858 |
| 8192 | 1.0718 | 0.9715 | 0.9858 |
| 32768 | 1.0718 | 0.9932 | 0.9931 |
| 131072 | **0.9834** | — | — |

Worker's response is **non-monotone**: its 32 k–131 k-trail blocks save
13.7 G under the reap (going scan at 131072 *costs* that back and more),
while its >131 k-trail blocks *lose* 2.8 G under the reap. Flag density
varies within a single instance — a dense-flag block with a million-entry
trail scans cheaply; a sparse block with a 50 k trail needs the reap. No
static threshold, and no cheap per-block predictor short of running the
scan itself, separates them. (The adaptive alternative — always push,
scan until a miss budget trips, then pop from the reap — preserves the
sequence too, but its unconditional push tax is most of the cost the
dense instances are already losing at 4096, so it cannot clear the
corpus bar either.)

**Score check (§11.1 landing path)**: full solves, 3 reps, pinned —
worker_550 37.8 → 34.4 s (−9.5 % wall, real), qwh 17.8 → 18.1 s,
summle 7.0 → 7.1 s. **Zero solved-at-cap flips** at any competition-like
cap on these files — the class win is cost-only, so the cost-neutral-
but-score-positive landing clause does not apply.

### Verdict

Reverted per the pre-registered corpus bar (best corpus geomean 0.9992,
bar ≥ 1.00), matching the repo's precedents for sub-bar neutral results
(minimize-scratch-pool 0.9994, eliminator-persistence 1.0008 — both
reverted). The kept knowledge:

1. **The pop-sequence identity holds** — a reap, a linear scan, or any
   mix pops the identical newest-flagged-first sequence, and Gate 1
   verified it at every configuration. Any future retry inherits this
   soundness argument.
2. **Trail scale does not predict reap benefit; flag density does, and
   density is intra-instance.** cadical's default-on `shrinkreap` does
   not transfer to this engine at our Rust constants (~2× the C++
   constant: bounds-checked `Vec` buckets, no inline bucket arrays).
3. The worker-class win (7.2 % instructions, 9.5 % wall) is real and
   still on the table for a mechanism that can find the sparse blocks
   cheaply — e.g. a per-var "recently flagged" epoch bitmap that the
   scan consults, or a cheaper push structure. Nothing here is landed.
4. The `Reap` port itself (radix heap, 33 buckets, monotone, safe Rust,
   oracle-tested vs a sorted-vector model, incl. duplicate keys and all
   bucket boundaries) was correct — the unit tests live in the reverted
   patch preserved in this study's git history if anyone retries.

Artifacts: `/tmp/reap.patch` on the session's machine held the full
reversible diff; the experiment was reverted from the shared tree with
`git apply -R` of exactly that diff (no other agent's changes touched).

