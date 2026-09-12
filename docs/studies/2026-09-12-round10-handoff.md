# SAT performance program — round-10 handoff (2026-09-12 close)

> Entry point for the next agent. Full detail in the 14 studies dated
> 2026-09-12 under `docs/studies/` (start with
> `2026-09-12-program-close.md`, then this file's deltas). Everything
> below assumes the discipline of `AGENTS.md` + `docs/BENCHMARKING.md`.

continue sat perf work. Based on the measured state, in priority order:

## 1. Portfolio at wider caps — the only open route to the circuit-class conversions

Measured state: the amplitude arms are done and sound — `NIXIE_OTFS` +
`NIXIE_EAGER_SUB` together give **0.9645× conflicts (super-additive;
singles are 1.016×/0.9932×), circuit_64in64out 0/5→5/5, mp1-Nb7T42 4→5**,
0 verdict disagreements ever — but corpus-neutral in aggregate, and every
route to *adaptive* arming is now measured dead (seven static features +
early-window online probe all non-predictive:
`2026-09-12-class-signature-exhaustion.md`). The 60 s mini-bench
portfolio died on budget arithmetic (Phase-3, 2026-09-11); **300 s+
is untested**. First step: the 13-file 0/5-at-60 s class, seeds 0–4,
default@300 s vs default@X→comb@(300−X) for X ∈ {60,120} (~3 h wall at
5 workers; runners exist as assets — see below). If the comb arm
converts ≥3 files, the `SEEDS=` portfolio token already accepts it as a
late arm.

## 2. A different elimination schedule for the Timetable class

The residual amplitude gap (cadical eliminates 147 k vars = 52 %, we
stop at 81 k) is now precisely scoped by elimination, not by the
candidates we already have: mass economics match (erratum), phase-entry
subsume fixpoint is dead (`NIXIE_ELIM_SUBFIX`: bve unchanged, 0.990×
conflicts, −3 cells), AND-gates add ~900 vars, search-side feeders are
the arms of item 1. What is *not* tried: restructuring when elimination
phases fire (our conflict-clock `elim_interval × (phases+1)` with
2 rounds vs cadical's pre-search fixpoint + event interleave), or
elimination under a saturated-occurrence schedule. Read
`2026-09-12-and-gate-elimination.md` (anatomy tables) +
`2026-09-12-elim-ballast-erratum.md` first; the `NIXIE_LOG_ELIM` round
line now prints `added= bw_retired= otf_shrunk= live_orig=` so every
hypothesis is measurable before you build it.

## 3. CSR watch lists (architecture)

The ELS rewatching study (`2026-09-12-els-rewatching.md`) proved local
watch surgery is architecturally unprofitable at the current
`Vec<Vec<Watcher>>` structure (entry-major random arena access loses to
the rebuild's sequential sweep by 9.7 %). CSR/arena watch lists make
rebuild = memcpy and surgery = sorted splice. Multi-session; touches
every BCP hot path; needs the same bit-identity + screen bar.

## Standing items

- **Re-baseline before any new claim.** The 8082e335 cells (270 +
  10-seed tails, all verdict-verified) were re-validated
  bit-identical at the 2026-09-12 close. If any nixie-sat default-path
  commit lands, re-verify with paired counter runs before reusing them.
- **The workspace is shared.** Other agents' in-flight edits have twice
  broken the workspace build mid-session. If `cargo build -p
  nixie-solver` fails with their WIP, run parity from a clean worktree
  at HEAD with only your diff applied (the recipe is in
  `2026-09-12-elim-subfix.md`).
- The tla-syntax crate has had failing tests all day (another agent's);
  exclude it from your verification math and say so.

## Infrastructure you inherit

- **Binaries**: `precompile/{8082e335,303771ef,7c7c4623,4f51efd7,
  6cdaea11,7c7c4623,67b02c80,6c769850,e0cc947e,81192b11}/stats_solve`.
- **Cells**: same trees under `benchmark/runs/sc24f/` — baseline
  (`default`), tiered, otfs, eager-sub, otfs-plus-eager-sub, gent-off,
  elim-subfix; all verdict-verified (SAT model-checked, UNSAT
  cadical-agreed). Reuse, never re-run.
- **Screen runners** (config-hash-aware skip — see the bug history in
  the first gent/comb attempts): `docs/studies/assets/
  inproc-amplitude-2026-09-12/sc24f-*-screen-runner.py`. The record's
  `config.flags` content-hash is the cell identity; the runner's `OUT`
  variable does NOT control where benchstore files records.
- **Arms available** (all default-off = bit-identical, all with
  differential tests): `NIXIE_OTFS`, `NIXIE_EAGER_SUB`,
  `NIXIE_AND_GATES`, `NIXIE_TIERED`, `NIXIE_ELIM_SUBFIX`, plus the
  earlier restart-family arms (`NIXIE_FOCUSED_*`, drought, stall).

## Traps that cost real time today

1. `clauses.num_original()` **never decrements** on
   `mark_deleted_raw` retirements (elim/vivify/OTFS paths) — it is not
   a live-DB measure; use `live_orig` from the elim trace. This
   manufactured a false 580 k "ballast" narrative for a day.
2. The default `RandomSlice` subsume mode **re-rolls the dirty set at
   every round's end** — any extra `subsume_round()` call (even
   zero-yield) re-places the scheduled literals and diverges
   trajectories. Nulls for schedule changes must control for this.
3. The OTFS false-unsat (caught by the screen's verification gate, fixed
   in `7c7c4623`): trigger conditions must be exactly cadical's
   absorption condition, not a size heuristic. The corpus screen with
   model-checked SAT cells is the net that catches this class — never
   screen without it.
4. The screen runner's skip glob must match the config hash exactly
   (a bare `*` glob matches other arms' cells and silently skips them).
