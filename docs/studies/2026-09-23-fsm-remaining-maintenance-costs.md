# The FSM arc's remaining maintenance costs: live-memo lists and witness bitmaps

**Date:** 2026-09-23 · **Nixie:** `161704e4` (live-memo lists, bitset
witnesses, once-only CSRs) + `769c3fe3` (bitmap cut witnesses, packed
endpoint scans, boxed journal entries; with `1e1c2ca6` the release-clippy
fix and `bd56cd00` the doc drift) · **Z3:** 4.16.0 ·
**Tooling:** `bench/fsm_perf/` (pinned-instruction methodology),
`bench/graph_differential/` (GNF corpora, bit-identity A/B), the new
`STATS=1`/`--stats` counter output.

## Question

The FSM-arc handover (`docs/handovers/2026-09-22-fsm-theory-arc-handoff.md`)
ranked "propagator per-event O(V+E) scans" as the next FSM perf slice and
sketched incremental (Ramalingam–Reps) reachability plus prefix-layer
sharing. Where does the time actually go after the witness-certificate
landing (`f667e809`), and which fixes pay?

## Method

Symbolized profile (`[profile.perf]`, `perf record -e cpu_core/instructions/u`,
pinned `taskset`, sampling period 0.5–2 M) of `fsm_s64_w80_r0` (the study's
worst instance), plus new deterministic maintenance counters
(`TraceKind`: pops/invalidations/re-reads/true+false events/witness+cycle
drops/closure rebuilds/per-rule emissions), printed by `STATS=1` or
`--stats` (the CLI flag existed but was never wired — it silently did
nothing). Every change verified **trajectory-inert**: GNF corpus A/B
bit-identical `s`-line + conflicts/decisions/propagations + counters
(80/80 at n∈{25..150}, 18/18 at n∈{200,300,500}), same FSM verdicts.

## Findings

1. **The handover's absolute numbers were partly PMU-noise.** Pinned, the
   pre-change `fsm_s64_w80_r0` costs **21.7 G** instructions (the study's
   "≈2.0 G" absolute came from the inflated first campaign; its *ratios*
   were pinned and remain right).
2. **62% of the pinned profile sat on one instruction**: the discriminant
   probe of the `backward_searches` **slot sweep** that every false edge
   event ran — O(vertices) per event over 5184 mostly-`None` slots per
   product graph (`if let Some(backward) = memo && witness-match`). The
   same shape existed for `forced_searches` in `merge_new_edge`.
3. **18%**: per-consequence cut-certificate checks (O(edges) scans with
   hash-set membership per edge). **16%**: `add_vertex`'s pristine test
   scanning both per-vertex tables per added vertex — **O(V²)** per
   product graph at registration. Smaller: per-emission O(V) cut-set
   collection, per-epoch CSR rebuilds, closure rebuilds after witness
   drops.
4. **Pops are not the ceiling here.** `pops=6764` but `reread=116` (and
   `reread=2` at GNF scale): most backtracks never trigger a re-read
   before the next one, so the trail-undo/Ramalingam–Reps deletion
   machinery the handover sketched would buy little on these corpora —
   the *event-driven* maintenance was the cost, not the pop path.
5. **Prefix-layer sharing is worthless for random-word corpora** (the
   expected shared prefix of two random binary words is ~1 layer of 81);
   it would only pay on structured, prefix-heavy example sets.

## Changes (all trajectory-inert by construction or verified so)

- **Live memo lists** (`forced_live`/`backward_live`): event handling and
  memo drops visit exactly the memoized structures, never the slot
  arrays. This alone took `fsm_s64_w80_r0` from 21.7 G to 5.7 G.
- **O(1) `add_vertex` pristine test** through the live lists (was O(V)
  per vertex ⇒ O(V²) per product graph).
- **Cut witnesses as shared membership bitmaps**: the emitting closure
  packs the complement of its `seen` array once per memo lifetime; the
  per-consequence check runs pure bit tests (no set build, no fill). Cut
  and NoCycleThrough rules carry `Arc<[u64]>` bitmaps; the statement
  carries packed `(from, to)` endpoints so the check's edge scan touches
  half the cache footprint.
- **All-edges CSRs built once ever** (their contents are
  value-independent; the per-epoch rebuild was pure waste).
- Cut-reason collection (`cut_negations`) keeps its edge-index order —
  the emitted sequence feeds learned clauses, so reordering would
  perturb the search trajectory. A false-edge-list variant with
  per-emission sort was measured **slower** and reverted; a by-tail
  statement index visiting only the closed set's leaving edges was also
  measured **slower** (FSM product cuts put most vertices on the closed
  side; the row indirection loses the linear scan's locality) and
  reverted. Both negative results are recorded here so they are not
  retried.

## Results (pinned instruction counts)

| instance | before | after | |
|---|---:|---:|---|
| fsm_s64_w80_r0 | 21.7 G | 5.6 G | 3.9× |
| fsm_s64_w40_r0 | 7.5 G | 2.6 G | 2.9× |
| fsm_s32_w80_r0 | 4.5 G | 1.4 G | 3.3× |
| fsm_s16_w80_r0 | 1.3 G | 0.45 G | 2.9× |

`bench/fsm_perf` total geomean nixie/z3: **0.123 → 0.055** (unsat
canaries ~40× under z3; 41/42 verdicts agree, the remainder a z3 60 s-cap
timeout on a load-50+ machine with no verdict disagreement). GNF corpora:
bit-identical A/B everywhere including n=500. The perf landing gate
against the pre-change binary: conflicts/decisions ratios **1.000**
(PASS). Z3 parity suite: 177/177 decisive agreement, 0 wrong.

## What remains (ranked by the new profile)

1. **The certificate crossing scan** (~a third of the worst instance):
   per-emission O(edges) — the bitmap made each test cheap, but the
   iteration count is inherent unless the check is indexed by side
   (measured slower — see above) or memoized across the pop-driven
   re-emissions (a content-keyed verified-cache on the certified path;
   soundness surface, not attempted).
2. **Closure rebuilds after witness drops** (~14%): 1834 drops ×
   O(V+E) rebuilds on the worst instance — a better repair rate
   (full Italiano/RR decremental reachability) is the genuine next
   algorithmic slice.
3. **The model-gate replay** (`check_model` ~6%): re-validated
   statements per final check.

None of these is worth a risky rewrite today: at 0.055 vs z3 the lazy
reduction is 18× cheaper in aggregate, and every landed change is
bit-identical on the search trajectory.
