# Kitten/Sweep Audit — Gaps Found and Closed (2026-09-09)

A line-by-line audit of the kissat `kitten.c`/`kitten.h` port
(`nixie-sat/src/kitten.rs`) and its sweeper consumer
(`nixie-sat/src/solver/sweep.rs`, kissat `sweep.c`) against the reference
sources in `../temp/kissat/src/`. This document records every gap found
and the fix that closed it, so the next reader can verify the port's
claims without re-deriving them.

**Verification gate for this landing**: full workspace suite
(10 743 tests), clippy `-D warnings`, fmt, doc, and the Z3 differential
parity suite — **169/170 decisive-matched, 0 disagreements** (the single
unresolved cell is a Z3 `Unknown`, inconclusive by methodology).

## Gaps closed

### 1. Per-solve tick budget disarmed after the first swept variable (budget overrun)

`kitten.clear()` resets `ticks_limit` to unlimited (kitten.c
`initialize_kitten` — same in both). kissat's `clear_sweeper` re-arms it
to the *remaining* round budget (`set_kitten_ticks_limit`, sweep.c:196);
the port called `set_ticks_limit_delta` exactly once per round
(`Sweeper::new`), so **from the second swept variable on, every kitten
solve ran unbounded** — one hard environment (up to 8 192 vars /
32 768 clauses) could blow the round budget arbitrarily inside a single
solve, since round checks only fire *between* solves.

**Fix**: re-arm after each per-variable `kitten.clear()` in
`sweep_one_variable` (`set_ticks_limit_delta(limit.ticks − kitten.ticks)`),
restoring the absolute round limit exactly like the reference.
Regression: `sweep::tests::sweep_ticks_limit_rearmed_after_clear`.

### 2. Environments walked sparse watch lists, not dense occurrence lists (yield gap)

kissat enters dense mode and connects **every literal** of every live
irredundant large clause (`kissat_connect_irredundant_large_clauses`,
watch.c:169 + `kissat_inlined_connect_clause`); its environment builder
iterates those full occurrence lists. The port walked its **propagation**
watch lists (two literals per clause), silently missing every clause
where the swept literal sat un-watched: smaller environments (fewer
equivalences provable), a truncated depth-cone, divergent
"cone fully copied"/`sweep_completed` accounting, and occurrence-ranking
counts that could exclude variables kissat sweeps.

**Fix**: the sweeper now builds a per-round `OccurrenceList` (dense,
every literal of every live original clause with ≥ 3 literals — binaries
stay BIG-authoritative, exactly the dense-mode split) in `Sweeper::new`;
the environment walk and `sweep_occurrences` (scheduling rank + both-
polarity filter) read it. Liveness is re-checked on visit
(`sweep_reference` retires satisfied clauses lazily, kissat's
`mark_clause_as_garbage` analog). This also corrected an inverted
polarity label in the BIG counting (occurrences of `l` live under key
`¬l`; the old code queried `l` under a "pos" name — totals identical,
labels wrong).
Regression: `sweep::tests::sweep_dense_occurrences_cover_all_clause_positions`.

### 3. `completely_backtrack_to_root_level` omitted the units-unassign loop

kissat's `flush_trail` (in `decide`) empties the root trail **keeping
values assigned**; root facts then live only in `values[]` + the `units`
list (every level-0 assignment — unit or wrapped propagation — has its
unit klause there). The C's complete-backtrack unassigns those units
after draining the trail (kitten.c:1272-1282); the port drained only the
trail, so **root-level values persisted across solves within a round**
(a hot start, where kissat cold-starts every solve). Sound — klauses are
monotone between clears — but every post-first candidate solve took a
different trajectory and tick profile than the reference, and the
`Kitten` contract quietly differed for any incremental caller.

**Fix**: port the loop verbatim (unassign every unit whose literal is
still true). Regression: `kitten::audit_tests::completely_backtrack_clears_flushed_root_units`.

### 4. Missing API entries: `traverse_core_ids`, `shrink_to_clausal_core`

The port lacked both entries; their only kissat consumer is
`definition.c` (gate/definition extraction feeding definition-based
elimination — itself unported; `eliminate.c` keeps a persistent embedded
kitten for it). The port now carries both, so a future `definition.c`
port has its full `kitten.h` surface:

- `traverse_core_ids` — original core klauses' caller-tagged ids, in
  arena order (the id↔gate-watch mapping the definition extractor uses);
- `shrink_to_clausal_core` — compact the arena to core originals,
  rebuild units/watches at new offsets, reset to unsolved (the
  standalone `-O` shrinking round). Port note: the C's
  `if (!kitten->inconsistent)` sentinel test is an upstream quirk
  (true only for ref 0); the port uses the intended `== INVALID`
  semantics and no-ops honestly when no `inconsistent` ref exists.
Regression: `kitten::audit_tests::core_ids_and_shrink_to_clausal_core_round`.

### 5. No interrupt/termination path

kissat checks `TERMINATED(sweep_terminated_*)` at 8 sweep points and —
crucially — **inside kitten's `decide`** (`TERMINATED(kitten_terminated_1)`),
so even a single sub-solve is cancellable. The port's `sweep_round`
never looked at the solver's cooperative `interrupt` flag and `Kitten`
had no hook: a Ctrl-C during a long round was ignored (compounded by
gap 1).

**Fix**: `Kitten::set_termination(Arc<AtomicBool>)` checked in `decide`
at the reference's granularity (between decisions, not propagations);
the sweeper shares the solver's flag; `sweep_round`, the round loop, the
backbone/partition loops and both flip loops check
`sweep_interrupted()` at the kissat `TERMINATED` positions.
Regressions: `kitten::audit_tests::termination_flag_aborts_solve_as_unknown`,
`sweep::tests::sweep_respects_interrupt`.

### 6. Randomness parity (bit-exactness with kissat)

- `randomize_phases` assigned `phase[i] = bit i` of each 64-bit draw;
  the C's word trick writes `phase[64k + 8m + j] = bit_k(k + 8j)` — an
  8×8 transposition. Same generator stream, same uniform distribution,
  but not bit-identical. **Fix**: exact transposed mapping.
  Regressions: `kitten::audit_tests::randomize_phases_*` (golden, replaying
  the LCG).
- `shuffle_clauses` drew `j ∈ [0, i]` (Fisher–Yates); the C's
  `pick_random(0, i)` is **exclusive** (`j ∈ [0, i−1]`, no-op only at
  `i == 0`) — a different shuffle *and* draw mapping. **Fix**: exclusive
  draws. Regression: `kitten::audit_tests::shuffle_clauses_matches_kissat_draws`
  (full draw-sequence replay).

### 7. Robustness hardening (release-mode honesty)

- `new_reference` now latches an `exhausted` flag at `≥ INVALID` arena
  words instead of silently wrapping refs (kissat fatals). Producers
  refuse: original klauses are dropped (a *weaker* environment — sound,
  kitten clauses are entailed restrictions), learned klauses return
  `INVALID` and `analyze`/`failing`/`register_inconsistent` bail with
  the solve reported `Unknown` — never a fabricated answer; the
  level-0 wrap in `assign` is skipped (loses a core hop, not soundness);
  `register_inconsistent` falls back to the root conflict klause (still
  a true UNSAT). `clear` resets the flag.
  Regression: `kitten::audit_tests::exhausted_ref_space_is_unknown_until_clear`.
- All `REQUIRE_STATUS`/`INVALID_API_USAGE` aborts (`value`, `failed`,
  `flip_literal`, `compute_clausal_core`, `track_antecedents`,
  `shuffle_clauses`, traversals, shrink) are now `debug_assert!` plus an
  honest neutral result (0 / false / no-op) in release — the C aborts;
  a library must neither abort the process nor fabricate.
  Regression: `kitten::audit_tests::contract_guards_are_honest_noops_in_release`.

### 8. Performance divergences (semantics equal)

- `propagate_literal`/`flip_internal` used `Vec::remove` per moved watch
  (O(n²) worst case); now the C's in-place two-pointer compaction
  (O(n)), with the conflicting watch kept and the tail flushed exactly
  like the reference.
- `analyze`/`failing`/`register_inconsistent`/`assign` allocated
  `klause_lits(reason).to_vec()` per reason clause; now direct index
  reads (no allocation on the conflict path).

## What remains open (recorded, not gaps in the port)

- **`definition.c` (definition-based elimination) is unported** — the
  only consumer of the two API entries added in gap 4. Porting it is a
  feature decision (persistent elimination-phase kitten, gate
  extraction via core ids), not a port defect.
- **Deferred equivalence application** (end-of-round ELS fold instead of
  per-equivalence `substitute_connected_clauses`) — deliberate,
  documented in `sweep.rs`, rides the soundness-hardened rewrite.
- **`sweeprand`** (randomized frontier) unported; kissat default 0.
- **Trajectory evaluation**: dense environments + per-solve caps change
  search paths. Correctness is gated (tests + parity, above); a
  performance claim would need the matched-null protocol
  (`NIXIE_SWEEP_NULL=1`, ≥ 10 seeds) per `docs/BENCHMARKING.md` — not
  attempted here; no performance claim is made for this landing.

## Audit-verified-equal core (no action needed)

Import/export mapping; klause arena layout & flags; VMTF stamped ring
incl. `search` maintenance; `assign` incl. level-0 learned-unit wrapping
with antecedents; `propagate` (tick formula `len/16+1`, blit refresh,
replacement scan, binary shortcut); 1UIP `analyze` incl. jump/swap-at-1;
`failing` (unit/clashing/first-failed priority, two-phase BFS, core
reuse); `register_inconsistent`; `propagate_units`; `decide`
(assumption walk, pseudo-levels, `unassigned == 0 → SAT` before the
tick check); `solve`/status lifecycle & resets; `value`/`fixed`/
`failed`; `flip_literal`; `compute_clausal_core` (post-order DFS,
sentinel protocol); `clear`. Sweep-side: scheduling ring, limit schedule
(256/1024/2 doubling with `sweep_completed ≤ 32`), backbone & partition
loops, refine functions, the two-implication equivalence protocol with
both cores, repr path compression, incomplete/completed bookkeeping,
yield-delay analog, effort budget analog (400‰ calibrated default).

## Follow-up increment (same day): the `definition.c` consumer ported

The largest "remains open" item — definition-based elimination — is now
ported too, closing the audit's finding-4 consumer gap end to end:

- **`elim_find_definition`** (`solver/eliminate.rs`, kissat
  `kissat_find_definition`): exports both polarity occurrence clauses of
  an elimination candidate into a fresh kitten with the pivot-polarity
  occurrence erased (`clause_with_id_and_exception`, ids = export
  indices), solves under `definitionticks` = 1e6; on UNSAT extracts the
  core, runs the `definitioncores = 2` shrink round
  (`shrink_to_clausal_core` + `shuffle_clauses` + re-solve, Unknown
  aborts the extraction exactly like kissat's `ABORT`), and maps core
  ids back to clauses via the export table (`traverse_core_ids`).
- **Gate-aware elimination** (kissat resolve.c's `gates` branch): on a
  two-sided definition the pivot is eliminated with the three products
  gates0×a1, a0×gates1, gates0×gates1 under the usual
  `pos + neg + elimbound` bound — the antecedent×antecedent cross
  product is skipped (entailed by the proved definition; the
  completeness argument is recorded in the source). One-sided cores
  force a unit (`definition_units`, assigned through the hardened
  `elim_assign_unit`). Retirement + SatELite model reconstruction ride
  the existing `elim_retire_pivot_clauses`/`bve_def` machinery
  unchanged (the reconstruction invariant holds for gate resolvents).
- **Gating**: `NIXIE_DEFINITIONS` (kissat `definitions`, default 1
  there) — nixie default **off** until characterized per
  `docs/BENCHMARKING.md`; proof-attached runs keep it off (the core's
  resolution proof has no cheap LRAT provenance here — weaker, sound).
  Per-phase safety valve of 64 M kitten ticks (no kissat analog;
  documented) since the structural gate detectors that front-run the
  kitten in kissat are not ported.
- **`sweeprand`** (kissat option, default 0) is now ported as
  `NIXIE_SWEEP_RAND` — randomized frontier swap in the sweep's
  environment loop (per-round LCG seeded 0; kissat draws from the
  persistent solver generator).

Tests: `definition_gate_elimination_beats_cross_product` (a variable the
full cross product cannot eliminate falls to the gate products),
`one_sided_definition_forces_unit`, and a 150-case seeded verdict
differential (armed vs base). Gate: 10 749 workspace tests, clippy/fmt/
doc clean, z3 parity 169/170 decisive-matched, 0 disagreements.

**Still open by design**: the structural gate detectors
(`equivalences.c`/`ands.c`/`ifthenelse.c`) that run before the kitten in
kissat — the definition path subsumes them semantically at one bounded
kitten solve per candidate; porting them is a pure speed optimization.
And the standing note: a performance claim for either the sweep fixes or
definitions needs the matched-null protocol, not correctness gates.

## Pre-registered screen (written before the runs)

The audit fixes changed the **default-on** sweep path (dense
environments, per-solve tick caps, cold-start solves). Per the
enablement rule (`docs/BENCHMARKING.md` §3), a default-path change
ships with a differential screen at the new default; the definitions
arm gets its first cost/verdict measurement. Standing corpus
(`precompile/corpus-sc24f/`, 54 files), 60 s cap, 5 repetitions per
cell (the solver is deterministic — repetitions sample the load margin
at the wall cap only), cores 10–19, arms interleaved within each
repetition round so load drift hits all arms equally:

| arm | binary | env |
|---|---|---|
| base | `precompile/66166ed` (pre-audit parent) | — |
| treat | `precompile/825f24e` (current default) | — |
| defs | `precompile/825f24e` | `NIXIE_DEFINITIONS=1` |

- **S1 (default screen, treat vs base)**: verdict agreement on every
  both-decided cell must be **100% (0 disagreements)**, and treat
  solved-at-cap **not lower** than base. Within ±3 files is a reshuffle
  (§11.1) — judged on the flip list vs the mechanism, not the count.
- **S2 (cost)**: paired conflicts-to-verdict geomean, treat vs base,
  both-decided cells only. [0.95, 1.05] = neutral. No win language
  without a matched null — this screen cannot produce one.
- **S3 (defs arm)**: verdicts must agree with treat on both-decided
  cells (soundness of the gate path under real corpora); solved-at-cap
  and cost reported descriptively. **No enablement decision from this
  screen**: a merit claim needs an extract-and-discard matched null
  first (§2); if S3 shows any disagreement or a corpus-negative
  solved-at-cap, the arm stays default-off with that recorded verdict.
- **Falsification**: a single S1 verdict disagreement is a soundness
  bug (report + fix before anything else, AGENTS.md); S1 solved-at-cap
  more than ~3 files below base = the fixes regressed the default →
  investigate the flip list before keeping them default-on.

## Screen results (S1/S2/S3) and the dense-environment verdict

Standing corpus, 54 files × seeds 1–5 × 60 s cap (`stats_solve`,
`SEED=N` seeds the solver PRNG — verified to fire: 33 804 vs 34 613
conflicts on 6s167-opt s1/s2), cores 10–19 under normal box load, arms
interleaved per seed round. Raw cells: `precompile/825f24e/benchmark/
audit_screen/cells.jsonl` (base/treat/sparse) + `decomp/cells.jsonl`.

| arm | solved-at-cap (270) | verdict disagreements | conflicts geomean vs base |
|---|---|---|---|
| base = `66166ed` (pre-audit) | 173 | — | 1.000 |
| treat = `825f24e` (all fixes) | 166 | **0** | 0.960 |
| sparse = treat minus dense envs | **177** | **0** | 1.062 |

**S1 failed for treat** (−7 cells, past the ±3 bar) and the flip list
is structural, not load: `si2-b03m-m800-03` 5/5→2/5 (base solves in
5–9 s), `constraints_17` 4/5→1/5, `FmlaEquivChain` 5/5→2/5. Trace
(`NIXIE_SWEEP_TRACE=1`, si2 seed 1) pins the mechanism: dense
environments are ~5× clause-denser → 767 vs 391 kitten ticks/solve and
a 4.5× larger schedule (9 912 vs 2 221 scheduled — dense counting makes
far more variables schedulable), so the fixed 400 k-tick round budget
swept 55 vs 144 variables and proved ~103 vs ~179 equivalences in five
rounds. kissat's dense-mode construction is paired with kissat-scale
budgets; at our calibrated 400 ‰ it buys less sweep per tick.

A decomposition screen (6 files: the three regressed + mrpp/summle/
mdp, 0 disagreements) showed reverting only the dense change recovers
`si2` (5/5) and `constraints_17` (5/5, ≥ base) while `FmlaEquivChain`/
`summle` stay down 2 cells — within reshuffle scale for a
distribution-identical change (the bit-parity `randomize_phases` fix
redraws every witness; the 2026-09-08 null moved ±9 cells on this
corpus). The full-corpus sparse screen then passed S1: **+4 solved,
0 disagreements**, flips spread over 11 files (no file worse than −2,
gains on g2-slp/circuits/j3037/worker/af-synthesis — the sweep's
classes). Cost 1.062 vs base is marginally above the ±5 % band;
reported as such — no cost claim in either direction, the flip list
decides (§11.1: cheap-to-score are different objectives).

**Verdict**: dense-mode occurrence environments are **reverted** on
main (environments and occurrence counting walk the sparse propagation
watch lists + BIG again — a strictly smaller, sound environment
source). Everything else from the audit closure stands: per-solve tick
re-arm, cold-start backtracking, termination wiring, overflow/contract
hardening, bit-exact randomness, API entries, perf compaction — and
the landed tree was verified **bit-identical** to the screened `sparse`
binary (same conflicts at same seeds on two anchors). The dense yield
gap vs kissat is recorded as **open, budget-bound**: a follow-up
effort-scale study (dense environments × a kissat-scale absolute
budget) is the live path, in the footsteps of the 2026-09-09 effort
study that found 1600 ‰ reaches kissat-parity equivalence counts but
splits the anchors.

**S3 (definitions arm)**: 0 disagreements vs treat and base, and
solved-at-cap **176 vs treat's 166** (+10 cells) at cost 1.017
(neutral band) — but per the pre-registration no enablement follows
from a screen: an extract-and-discard matched null is required before
any merit language, and the flip list (summle swings ±4.5× both ways)
is the known bimodal class. `NIXIE_DEFINITIONS` stays default-off with
this positive screen recorded.
