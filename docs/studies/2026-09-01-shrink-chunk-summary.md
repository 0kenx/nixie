# Shrink scan chunk-summary acceleration: pre-registration (2026-09-01)

Direct follow-up to the reverted reap port
([`2026-09-01-shrink-reap-port.md`](2026-09-01-shrink-reap-port.md)), taking
its recorded retry lever #3: a cheap position-indexed summary the scan
consults, instead of the per-literal push structure that cost the corpus
bar. The reap study established:

* the scan's cost lives in skipped entries (worker 52.5/pop, dense files
  2–7/pop), and flag density is **intra-instance** — no static threshold
  separates winner from loser blocks, so any always-on per-literal
  bookkeeping (~7 instr) loses the corpus (0.9992);
* the pop sequence (newest flagged first) is mechanism-independent —
  Gate 1 verified identity for scan/reap mixes, and the argument carries
  to any exact accelerator.

## The change

**Epoch-stamped chunk summary of `MF_SHRINKABLE` over trail positions,
lazily activated.**  Two iterations were built; the landed one is the
second.

*Iteration 1 (eager, corpus bar failed at 0.9996):* every `MF_SHRINKABLE`
marking site ORs the position into a 64-position chunk word
(`{epoch: u64, bits: u64}` per chunk, epoch bumped per block so stale
entries read as empty without a clearing pass), and the scan consults it
after 8 consecutive misses.  Trajectory identity held (54/54), worker
1.0704, class controls in band — but the ~3-instruction marking tax on
dense blocks cost mid-size files up to 1.2 % (Break_08_24 0.9881, qwh
0.9881) and the 54-file geomean landed at 0.9996 < 1.00: the same
disease as the reap, halved.

*Iteration 2 (landed — lazy activation, zero dense-block tax):* the
summary is **not maintained at marking time at all**.  The scan runs the
original per-position descent in probe groups of 8; only when a whole
group misses — the signature of a sparse stretch — does the block
(b) bump the epoch once, size the summary for the trail, **bulk-mark
the complete flagged set** (`shrinkable` + `walk_marked` are exactly
that set), and (c) from then on mark walk-discovered literals
incrementally and descend by summary jumps (masked `leading_zeros` to
the highest candidate in the chunk, whole empty chunks skipped).
Dense blocks (2–7 misses per pop) never activate and pay only the probe
group-loop induction (~1 instruction per position) — no epoch bump, no
sizing, no marking, no summary reads.

**Soundness and identity**: within a block the flagged set only grows
(no assignments, no flag resets), positions are immutable, and the
activated summary is exact (bulk-marked from the complete flagged set,
then extended at the one remaining marking site under the same epoch).
Positions already popped may stay set — harmless, the cursor never
revisits them.  **`mf_get` remains authoritative for every popped
literal**: the summary only decides where to look next, never what pops
— sound by construction, and a wrong summary could not mis-pop, only
waste work (a phantom-bit liveness guard clears any such bit to keep
the descent progressing).  The pop sequence (newest flagged first) is
the original scan's in every mix, so Gate 1 trajectory identity must
hold.

## Go / no-go (pre-registered BEFORE measuring; same bars as the reap study)

1. **Gate 1 — trajectory identity**: 54-file `/tmp/sc24f`, `stats_solve`,
   `MAXC=60000`, default seed vs `precompile/d3261a6`: counters + verdict
   bit-identical.
2. **Gate 2 — instructions** (`cpu_core/instructions/`, P-core pinned, 3
   reps, `MAXC=40000`): worker_550 **≥ 1.02**; controls {circuit_64in,
   si2-b03m, noL-11-14, frb45-21-2} in **0.99–1.01**; **54-file corpus
   geomean ≥ 1.00** — the bar the reap failed at 0.9992. Class 1.00–1.02
   or corpus < 1.00 → revert and record.
3. **Gate 3 — soundness** (if landed): workspace suite, clippy/fmt/doc,
   `diff_equiv` ≥ 100 k, corpus verdict sweep 0 mismatches, SMT
   differential 0 disagreements, z3 parity clean.

## Results — LANDED (all gates green; the corpus bar the reap failed now passes)

**Gate 1 — trajectory identity: PASSED** — 54/54 files bit-identical vs
`precompile/d3261a6` (`MAXC=60000`, `stats_solve`), for the eager
iteration and the landed lazy one.  The pop-sequence argument held in
both designs.

**Gate 2 — instructions** (`cpu_core/instructions/`, P-core pinned, 3
reps, `MAXC=40000`; reps repeat to ~1e-5 relative):

| file | old | new | old/new | bar | |
|---|---|---|---|---|---|
| worker_550 | 163.692 G | 151.361 G | **1.0815** | ≥ 1.02 | pass |
| circuit_64in | 16.356 G | 16.359 G | 0.9998 | 0.99–1.01 | pass |
| si2-b03m | 15.650 G | 15.652 G | 0.9999 | 0.99–1.01 | pass |
| noL-11-14 | 4.935 G | 4.941 G | 0.9986 | 0.99–1.01 | pass |
| frb45-21-2 | 8.831 G | 8.882 G | 0.9943 | 0.99–1.01 | pass |
| **54-file corpus geomean** | | | **1.0008** | ≥ 1.00 | pass |

0 verdict mismatches over the corpus run (every file, both arms).
Worker's class win (8.15 % instructions) even exceeds the pure reap's
(1.0738–1.0819): the summary jumps are at least as good as radix-heap
pops on the sparse stretches, and the probe groups waste less on the
dense ones.  The worst corpus files (Break_08_24 0.9912, qwh 0.9920,
rbsat 0.9923, stable-300 0.9925) are mid-size instances whose blocks
sit on the activation boundary — they activate on sparse stretches and
pay the bulk-mark, netting ~−0.9 % each, well inside the corpus-level
budget.

**Wall-clock sanity** (full solve, pinned, 2 reps): worker_550
37.4/36.6 s → 33.8/35.0 s (−6..−10 %), consistent with the instruction
ratio.

**Gate 3 — soundness (all green)**:

- workspace `cargo nextest run --workspace --all-features`:
  **10 418 / 10 418** passed;
- clippy `-D warnings` clean; `cargo fmt --check` clean; `cargo doc
  -D warnings` clean;
- `diff_equiv` **100 000** iterations (66 993 sat): **0 mismatches,
  0 invalid models**;
- corpus verdict sweep: 54/54 identical verdicts (Gate 1 runs);
- SMT differential (`bench/differential`, 270-instance pinned sample):
  **solved 160, agree_z3 160, 0 disagreements**, par2 2312.90;
- z3 parity (`bench/z3_parity`): **169 Correct / 1 Inconclusive /
  0 disagreements** — identical to the recorded baseline verdict set.

### What the two-study arc establishes

The reap study falsified "trail scale predicts the win"; this one
isolates the actual predictor — **skip density per pop** — and exploits
it at runtime with a probe-triggered accelerator instead of a static
threshold.  The load-bearing design property is that the dense-class
cost had to go to ~zero (lazy activation), not merely get halved;
eager marking at half the reap's constant still lost the corpus
(0.9996).  The `mf_get`-authoritative-pop structure makes the summary
a pure accelerator — the same argument would hold for any future scan
accelerator.

Residual (not taken): the activation bulk-mark walks `shrinkable +
walk_marked` — O(open) once per sparse block; on worker this is noise,
and no corpus file showed it as a cost.
