# 8-byte clause header (activity off-slot): pre-registration + results (2026-09-01)

Executed `docs/HANDOVER_ARENA_LAYOUT.md` — approach **A**. Approaches B
(bit-packed header) and C (kissat `lits[3]` inline overlap) stayed
out of scope: A measured neutral, so "only if A leaves the bar unmet but
is close" did not trigger (A was not close).

## What was built (and reverted)

`ClauseHeader` (`nixie-sat/src/memory.rs`) lost `activity: f32`:
12 bytes → **8 bytes** (`len: u32, lbd: u16, flags_tier: u8, usage: u8`).
Activity moved to a dense side table `Vec<f32>` keyed by `ClauseId` on
`ClauseDatabase`; the arena lost `set/add/scale_activity`; `ClauseView`
lost the `activity` field; the three read sites
(`reduce_clause_database` sorts, `clause_maintenance` demotion + deletion
scoring) fetched `ClauseDatabase::activity_of`. Semantics preserved
bit-exactly (same f32 values, same op order, same sort keys — Gate 1
proves it). New slot geometry: binary 16 B (4 per line), 3- and 4-lit
24 B, 5- and 6-lit 32 B (two 6-lit clauses per line, was 1).

Pre-registered gates (written before any measurement, per
`docs/BENCHMARKING.md`):

1. **Gate 1 — trajectory identity**: all 54 `/tmp/sc24f` files,
   `stats_solve` (CaDiCaL preset), `MAXC=60000`, default seed, vs
   `precompile/5f3ae49`: counters + verdict bit-identical.
2. **Gate 2 — instructions**: `cpu_core/instructions`, pinned cores,
   private `CARGO_TARGET_DIR`, binary shas recorded. (a) fixed
   `MAXC=40000` on `circuit_64in64out…` / `frb45-21-2` / `si2-b03m` with
   `noL-11-14` as control; (b) symmetric both-solve selection at a 12 s
   wall cap, geomean(base/new) ≥ **1.02×**; 1.00–1.05 = neutral, below
   the bar → revert and record. No wall-clock claims.
3. **Soundness**: `nixie-sat` suite (876 passed on the experimental tree),
   clippy/fmt clean, workspace battery on landing.

Arms: old = `precompile/5f3ae49/cnf_solve`/`stats_solve`
(sha256 `b88cbd78…`), new = private-target build of the experimental
tree (sha256 `6e0b32dd…`). Host load ~6/20; instruction counters are
load-independent.

## Results

**Verdict: REVERTED — Gate 2 failed at 0.9980** (threshold ≥ 1.02), with
Gate 1 clean (54/54 bit-identical: result, conflicts, decisions,
propagations, restarts, learned — the refactor was semantically correct).

**Gate 2a** (fixed `MAXC=40000`, 3 reps, rep spread 1.0000 — deterministic):

| file | old | new | old/new |
|---|---|---|---|
| circuit_64in64out | 17.247 G | 17.250 G | 0.9998 |
| frb45-21-2 | 9.802 G | 9.807 G | 0.9995 |
| si2-b03m | 16.019 G | 16.040 G | 0.9987 |
| noL-11-14 (control) | 5.034 G | 5.039 G | 0.9990 |

geomean **0.9992** — neutral.

**Gate 2b** (both-solve at 12 s cap, 22 cells of 54, zero verdict
mismatches): geomean **0.9980** (per-cell ratios 0.9948–1.0003; the
`simon-*` family sits uniformly at ~0.997, `mrpp_4x4` 1.0003).

**Diagnostics** (post-gate, explanatory only — pinned core, 3 reps):
`cpu_core/cycles` geomean 1.0034 (circuit +1.2 %, frb45 +1.0 %, si2
+0.4 %, control noL **−1.1 %**); `LLC-load-misses` −5.3 % on circuit,
−14 % on si2 (frb45 ratio meaningless at 1e5 absolute). The density
mechanism is *real but small*.

## Root cause of the smallness (why the arena layout lever is dead here)

The propagate scan reads `len`/`flags`/`literals` — in the **old**
12-byte layout those all live in bytes 0–8; `activity` sat at offset 8–12
and was **never loaded by the hot scan**. So the header *load* was
already a single word before the change; shrinking to 8 bytes could only
shrink the **stride between clauses** (how many clauses share a line),
which the LLC-miss reduction confirms — and that is a modest slice of
total cycles on these files. Instruction counts cannot see any of it
(same dynamic instruction stream; the ±0.2 % is codegen noise from the
changed struct), so a layout change of this class can only ever move
cycles by the fraction of stalls the arena lines represent — measured
here at ~1 % on the most propagate-heavy file in the corpus.

This closes the handover's approach-A question the same way the two
watcher studies closed theirs, and by the same mechanism: the BCP loop's
remaining cost on the loss files is **scan volume**, not per-visit
memory density. Approach B (bit-packing `lbd`/`flags`/`usage` into the
spare upper bits of `len`) cannot beat this result — it changes the same
stride by at most as much (header would go 8→4 or stay 8; slot strides
already round to 8, so a 4-byte header only shifts the *binary*-clause
stride 16→8 and nothing else) — recorded as not worth running. Approach
C (kissat `lits[3]` overlap) likewise only re-buys density on the same
lines. The propagate lever that remains is **structural visit-count
reduction** (cadical tagged binary watchers: satisfied binaries answered
from the watcher itself, no arena touch — the pass-5 characterization
showed circuit-class visits dominated by exactly those).

## Disposition

- Code reverted (memory.rs / clause.rs / learn.rs / clause_maintenance.rs
  back to `5f3ae49` content). The experimental code was preserved
  momentarily on a side branch for zero-discard reversion, then deleted —
  this study is the artifact (same disposition as the flat-watch study);
  the plumbing shape is fully described above.
- **Kept** (this commit): the corrected stale doc lines the handover
  flagged (the "32-byte header" module-doc line in `memory.rs` and the
  "16-byte header" comment in `clause.rs` — both described widths that
  predate the 12-byte f32 header of `5f3ae49`).
- Harness scripts and the private `target-arena/` dir deleted after the
  runs (scratch, per AGENTS.md cleanup).

## Measurement notes

- `perf -x,` event names carry a `/u` suffix on this perf (7.1.8) — CSV
  parsers must match on substring, not equality.
- 6-way parallel PMU produced 12 `<not counted>`/parse-fail cells
  (~22 %) even with per-slot pinned cores; the pre-registered serial
  retry recovered all of them. Parallel PMU on this box needs the retry
  pass; the watcher study's "pin and retry serially" note is load-bearing.
- The both-solve 12 s cap selected 22 cells; the corpus's heavier half
  times out in both arms symmetrically (selection-on-speed, valid for an
  instructions-to-verdict geomean, as the flat-watch study established).
