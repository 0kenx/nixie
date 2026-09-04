# Restart-EMA input + block-UIP clause shrinking (cadical `shrink=3` port)

Date: 2026-08-19
Verdict: **Landed as cadical-parity defaults.** Headline (94-file tracking, canonical
seed) improved 23 → 17 files above 1.5× of CaDiCaL (geomean 1.129× → 0.952×), 0 verdict
disagreements. The 5-seed null study is *completion-biased positive, instruction-noisy* —
recorded below without inflation. One soundness bug in the new shrink port was found and
fixed before landing (with two regression tests); it was ours, not pre-existing.

## Item-1 background: where the 4.5× decisions/conflict term actually lives

The handover's search-quality term decomposed (stable-300, fixed 100k conflicts,
traced via `NIXIE_TRACE_DECISIONS` + a temporary bump trace):

| metric                      | Nixie (before) | CaDiCaL (log replay) |
|-----------------------------|---------------|----------------------|
| decisions / conflict        | 4.97          | 1.27                 |
| propagation-cascade / decision | ~8 (med 12) | ~24 (first-after-restart: ~96) |
| restarts                    | 5313          | 4996 (not fewer!)    |
| levels kept per restart     | ~2 (27% of restarts reuse) | 60% (98% reuse) |
| trail shape                 | 266 lits / 41 levels | 245 lits / 8–12 levels |
| final learned clause        | 61 literals   | ~21 (shrunken 68%)   |
| raw 1-UIP clause            | 89 (med)      | ~66                  |

Key structural finding (replayed from `cadical --log`): at every restart CaDiCaL's trail
decision bump-stamps are *perfectly consecutive descending* —
`[905562, 905561, …, 905554]` — i.e. the trail's decisions are literally the N most
recently bumped variables in exact order. That is what makes `reuse_trail`'s
first-cold-stamp walk keep 60% of levels. Our stamps zigzagged (conflicts don't re-bump
the whole trail) because our learned clauses were 3× fatter and conflicts landed shallow.
CaDiCaL **without inprocessing** (`--elim=false --probe=false …`) still shows
1.26 dec/conf and 97.8% reuse — the search core, not preprocessing, holds the regime.

## Change 1: restart EMAs now eat the analysis-walk glue (cadical parity)

`analyze.cpp:1281` feeds the restart EMAs with `levels.size() - 1` — the number of
decision levels touched by the *whole 1-UIP resolution walk* — not the stored clause's
LBD. We fed the clause LBD. Distribution consequences (stable-300, traced):
our fast/slow ratio sat at median **0.82**, crossing the 1.10 margin on 12% of checks;
first restart fired at conflict **1132** vs CaDiCaL's **73**. The walk-glue statistic is
larger and noisier, which is exactly what makes the Glucose condition cross early.

After the port (single-seed observations, not the study): stable-300 242.9s → 21.1s
(11.5×), first restarts at ~70–110 conflicts. `NIXIE_GLUE_LEGACY=1` restores the old
input for A/B; `NIXIE_GLUE_NULL=1` feeds the previous conflict's walk glue (matched null).

## Change 2: block-UIP clause shrinking (`shrink.cpp`, cadical default `shrink=3`)

Port of `shrink_and_minimize_clause`: per decision-level *block* of the raw 1-UIP
clause, run a mini 1-UIP restricted to that level and replace the block by its block-UIP
literal; plain recursive minimization remains the in-block fallback and the LRAT path.
On stable-300 this takes avg stored-clause LBD from 28.6 to 12.9 and dec/conf from 4.97
to 1.68 (Cadical 1.27), with 99.5% of restarts now reusing a prefix. `enable_shrink`
(default true, cadical parity); `NIXIE_SHRINK_NULL=1` runs the full walk and discards the
result (matched null).

### The bug the port surfaced (fixed before landing)

`shrink_block`'s backward trail scan recomputed the popped literal's trail index as
`cursor + 1` *after* the pop loop. With `cursor.saturating_sub(1)`, a block-UIP at trail
index 0 leaves the cursor at 0, so `cursor + 1` is the *next* literal above — the block
was replaced by the wrong literal's negation. End-to-end symptom: 194 incremental
model-blocking clauses over an 8-Boolean tautology answered `unsat` in the SMT layer
(nixie-cli model-counter test; certified-mode independently rejected the verdict, Z3 says
sat). Minimized to a standalone 194-clause CNF reproducing at the SAT core
(`focused_vmtf=false` + shrink); first unentailed clause `[3,4,5,-7,6,-8]` at conflict
33 (block `{-8,-1}` at level 1; UIP = the level-1 *decision* `-1`, replaced by `-8`).
Fix: capture `uip_pos = pos` at pop time. Tests:
`nixie-sat/tests/shrink_trail_index_regression.rs` (minimal CNF + brute-force oracle;
every clause load-bearing) and `nixie-solver/tests/shrink_tautology_regression.rs`
(end-to-end 194-block script).

## Measurements (the honest part)

**94-file tracking metric** (instructions-to-verdict, `perf stat -e instructions`,
verdicts cross-checked vs CaDiCaL; deterministic canonical seed):

| arm | geomean cad/nixie | files > 1.5× | disagreements |
|-----|------------------|--------------|---------------|
| legacy (pre-change semantics) | 1.129× | 23 | 0 |
| walk-glue + shrink (new default) | **0.952×** | **17** | 0 |

Paired speedup new/legacy on the 79 commonly-completed files: geomean **1.166×**;
per-file highly bimodal — qwh.50.1250 27.8×, mp1-Nb7T42 20.6×, summle_X4044 7.2×,
stable-300 5.0× vs frb65 0.03× (frb65 is seed-chaotic: 5–40s within a single config),
mdp-28 0.06×, constraints_17 0.23×. Known-fragile files (ITC2021_Early_3, worker_550)
did not regress.

**Null study** (6 dev files × 5 seeds × 60s cap, CRN pairing on file+seed):

| arm | completions | med instr | paired geomean default/null |
|-----|-------------|-----------|------------------------------|
| default    | 26/30 | 162.9G | — |
| gluenull   | 23/30 | 147.9G | 0.822 (default faster on 10/21 pairs) |
| shrinknull | 16/30 | 197.5G | 0.690 (default faster on 10/16 pairs) |

Read: the nulls time out more (completion gap is real signal — the null arms *do not
finish* where the default does), but the instruction ratios at n≤21 are mixed and cannot
support a strong aggregate claim. Per-file, the effect is large and bimodal in both
directions. The honest conclusion: this is cadical-parity semantics with a clear
headline-metric win at the canonical seed, a real completion-rate win at 5 seeds, and
per-file chaos of the usual CDCL kind. A ≥10-seed ≥30-file study is the follow-up if a
publication-grade number is needed; the 5-seed study here would not survive review as
proof of a tuned win.

## What was ruled out along the way (do not retry)

- **Forced earlier restarts** (margin 1.10 → 1.00/0.90): monotonically worse
  (496k → 795k/861k decisions at fixed 100k conflicts). At our (pre-shrink) reuse
  quality, more restarts just multiply the 67-decision re-descent cost. Cadical can
  restart every ~3 conflicts because each is nearly free.
- **Reuse-keep-top-fraction probe** (`NIXIE_REUSE_KEEP`, non-semantic): keeping ~50% of
  levels at restart cut decisions 466k → 298k — confirms restart *cost* is the lever,
  but is not a cadical semantic and was not pursued further once shrink delivered the
  same equilibrium shift semantically.
- **Propagation completeness**: `NIXIE_CHECK_FIXPOINT` sweep (hanging-unit invariant at
  decision points, 8k conflicts) — zero violations. BCP is not missing cascades.
- **Restart frequency as cause**: cadical restarts *as often as we do* (4996 vs 5313);
  the difference is entirely cost-per-restart.
- **Inprocessing as cause**: cadical with all inprocessing disabled still shows the good
  regime (1.26 dec/conf, 97.8% reuse); it is 4.6× slower end-to-end but the search
  shape survives. Our stack's net-negative verdict (1.74×) is unchanged by this result.

## Files

- `nixie-sat/src/solver/conflict.rs` — walk-glue snapshot, `improve_learnt_clause`
  dispatcher, `shrink_and_minimize_clause` / `shrink_block` / `shrink_literal` port,
  bump-block reordering (shrink adds block-UIP vars to the bump set where cadical adds
  them to `analyzed`).
- `nixie-sat/src/solver/learn.rs` — `note_learned_lbd` EMA input switch (+ nulls).
- `nixie-sat/src/solver/decide.rs` — restart diagnostics (`restarts_stable`,
  `reused_trails`, `reused_levels`), `nixie-restart` trace line.
- `nixie-sat/src/solver/{mod,search_ext,tests}.rs`, `config_presets.rs`, `lib.rs` —
  config/stats/flag plumbing, fixpoint diagnostic, updated EMA-contract test.


## Follow-up: shrink × inprocessing produces a false `unsat` (gated; root cause open)

While re-measuring the inprocessing stack against the new default (Item 2), the
full-stack arm answered `unsat` on **SATISFIABLE**
`satcomp2024/bench/303480ca7e8322d771c94caf4ebd4e95-circuit_48in64out_with_700gates_4in4out_dist128_seed1.sanitized.cnf`
(CaDiCaL: `sat` with model; certified mode: `unknown`).  Regression window:
`3fdcd38` answers `sat` under the same env; the shrink landing answers `unsat`.

**Deterministic reproducer** (every run, ~67 s): `INPROCESS=1` with the
standalone pre-search vivify and the periodic inprocess round disabled
(diagnostic gates since removed) – i.e. *pre-search `inprocess()` alone* plus
shrink.  `SHRINK=0` on the identical arm answers `sat`.  With the whole stack
on, the verdict is trajectory-dependent (the LBD-recompute fix below flips some
arms) – only the reduced arm is stable.

**What the corruption looks like** (all diagnostics temporary, removed):

- The final refutation is a *learned* clause falsified by level-0 facts.
  That clause is entailed (CaDiCaL: input ∧ ¬clause = UNSAT).
- The level-0 trail has 775 units; **286 are not entailed by the input**
  (per-unit CaDiCaL satisfiability witnesses), starting abruptly at trail
  index 237 — one poisoned propagation cascade.
- Every learned unit/binary/ternary is RUP-entailed over the live database at
  learn time, and every level-0-pinning learned clause (unit, or
  all-other-literals-false-at-0) is RUP over the then-current DB; every
  in-place rewrite of an original clause by vivify/subsume (5000 + 35 checked)
  is entailed by the pristine input.
- The first poison unit is pinned via `assign_unit_fact` (a learned unit whose
  RUP witness resolves through previously learned clauses — the chain bottoms
  out somewhere after the pre-search round; the exact hand-off inside
  `inprocess()` {pure-literal, subsume+strengthen, vivify, transred} is **not
  yet isolated**: disabling subsume or the internal vivify individually makes
  the arm time out (no verdict), the others still answer `unsat`).

**Also fixed en route** (real, pre-existing): in-place clause strengthening
(vivify, subsume, elimination) shrank clauses without recomputing the stored
LBD, tripping `check_learned_clause_lbd` (`lbd > len`) in debug builds on both
sides of the landing.  All three rewrite sites now recompute LBD (and re-tier).

**Divergence found and fixed after gating** (cadical parity, affects the
default path too): `shrink_block` reset the `MF_SHRINKABLE` flag only for the
*block* literals after each block, while cadical's `shrinkable` vector collects
the walk-discovered literals as well and `reset_shrinkable` /
`mark_shrinkable_as_removable` clear **all** of them.  A stale
`MF_SHRINKABLE` from one block's reason walk leaking into a later block's
backward trail scan within the same clause makes that scan pop a foreign
literal — the same mis-derivation category as the `uip_pos` bug fixed before
landing (and caught then by the `si2-b03` replacement-level assert).  The
reset now covers `block ∪ walk-marked` on both outcomes.  With the fix, the
deterministic arm no longer produces the false `unsat` — it stops producing
*any* verdict within 900 s (the trajectory moved from "wrong answer in 67 s"
to "no answer"), so the fix is proven correct-by-parity but not proven curative
on this file; the gate below stays until a clean refutation or a root-cause
isolation lands.

**Gate removed after the flag-reset fix** (see next section): the
mechanistic fix plus the following evidence replaced the refusal gate —
- both reproducer files answer `sat` under every previously-failing arm
  (`INPROCESS=1` 71 s / 48 s; full stack 19 s — also *faster* than the
  gated build's 25 s);
- corpus soundness sweep, combo enabled: 40 files at the default seed plus
  20 satcomp files × 2 extra seeds — 117 verdicts, 0 disagreements with
  CaDiCaL;
- differential fuzzer, 2000 iterations — 0 failures (with the gate gone,
  the full-stack arm carries the combo automatically);
- regression test `nixie-sat/tests/shrink_inprocessing_regression.rs`
  (never-UNSAT-under-budget on the seed1 circuit, gated behind
  `NIXIE_SLOW_REGRESSIONS=1`, ~51 s debug).

The exact unentailed-clause chain on the circuit file was never captured
end-to-end (unlike the `uip_pos` bug, where the offending clause was
isolated); the flag-leak is established by cadical parity plus the empirical
disappearance of every false verdict.  If the combination ever misfires
again, the per-unit witness method above (286-unentailed-units signature)
reproduces the diagnostic in one ~70 s run.

The 94-file tracking numbers in this document were measured with inprocessing
off and are unaffected.


## Follow-up 2: root cause of the false `sat` found and fixed (`len()` used as a slot bound)

Re-measuring Item 2 with the (now ungated) combo surfaced a **false `sat`**:
`j3037_10_mdd_bm1` answered `sat` under BVE+ELS+inprocessing (CaDiCaL and Z3:
`unsat`; our default config: `unsat`).  The returned model falsified **134
input clauses**.  Pre-existing — the parent commit `3fdcd38` reproduces it —
and historically invisible because the stack was off in default sweeps and
this file timed out elsewhere.

**Root cause** (`nixie-sat/src/preprocessing_core.rs`):
`ClauseDatabase::len()` returns the number of *live* clauses
(`num_original + num_learned`) — it shrinks with every deletion — while
clause IDs index the full slot space.  All five `for i in 0..clauses.len()`
slot walks in that file (occurrence building, pure-literal, subsumption ×2,
watch rebuild) therefore stopped early once anything had been deleted,
making every clause stored at a slot ≥ the live count **invisible**.
Concretely: BVE deleted clauses and added resolvents (moving the live count
*below* the highest input-clause slot); the pure-literal pass then ran on the
torn occurrence view, saw a variable with only negative occurrences (its one
positive occurrence lived in the invisible tail), pinned it to the wrong
polarity in `pure_literal_reconstruction`; the search later assigned it the
opposite (correct) value, and `save_model`'s pure-literal overwrite turned
the final model into one that violates live input clauses.  Fix: all five
walks use `num_slots()` (the dense id upper bound), with the mechanism
documented at `build_occurrences`.

Regression tests (`nixie-sat/tests/preprocessor_slot_bound_regression.rs`):
- `len_is_not_a_slot_bound_pure_pin_minimal` — unit-level: delete a clause,
  build occurrences, assert the tail clause is visible (verified to FAIL on
  the bug and PASS on the fix).
- `j3037_stack_is_unsat` — end-to-end verdict pin under the full
  BVE+ELS+inprocessing combination (`NIXIE_SLOW_REGRESSIONS`, ~57 s release).

Post-fix: the stack sweep over all 92 CaDiCaL-solvable corpus files produced
77 verdicts with **0 disagreements**; differential fuzz 2000 iterations, 0
failures; z3_parity 0 wrong; workspace 10046 green.

**Item 2 consequence**: with soundness restored, the stack's earlier
"1.74× net-negative" verdict is obsolete — on the 17-file dev corpus the
stack now completes 16/17 vs default 10/15 (0 disagreements), solving the
two `circuit_48in64` files and `mdp-28`/`noL` where the default times out.
Whether the stack (or a schedule variant) should become the default is the
pre-registered factorial study the handover describes — now unblocked, next
session, with matched nulls per docs/BENCHMARKING.md.


## Follow-up 3: the ≥10-seed null study (measurement debt paid; one claim revised)

The headline (23→17 files >1.5×, canonical seed) and the 5-seed screening
below were the evidence at landing time.  This addendum adds the bounded
10-seed CRN-paired study the methodology requires: 6 dev files × 10 seeds ×
3 arms (T = landed default; GN = `NIXIE_GLUE_NULL` lagged-glue null;
SN = `NIXIE_SHRINK_NULL` shrink-discarding null), 60 s cap, paired
instructions per file×seed, exact two-sided binomial sign test.

| comparison | T-only comp | null-only comp | paired n | T faster | geomean | sign p |
|---|---|---|---|---|---|---|
| T vs **shrink null** | 8 | 7 | 35 | 25/35 | **1.59×** | **0.0167** |
| T vs **glue null**   | 2 | 12 | 41 | 22/41 | 1.03× | 0.755 |

Verdicts: 0 disagreements in 138 completed runs.

**Shrink (block-UIP clause shrinking) is supported**: significantly faster
than its null (p≈0.017, 1.6× paired geomean, completions even).  The
component with the cadical-parity port and the two fixed soundness bugs is
also the component with statistical evidence.

**Walk-glue (restart-EMA input) is NOT supported as a performance claim at
this sample size**: dead-even instructions, p=0.76, and the null completes
10 more cells — concentrated in one file (`summle_X4053`: T 2/10 vs null
9/10; all other files within ±2).  This *revises the 5-seed screening*
below, which had the default ahead on completions (26 vs 23) — that ordering
was seed luck.  What survives for walk-glue is the *faithfulness* argument:
cadical feeds its restart EMAs the analysis-walk glue (`analyze.cpp:1281`)
and we fed the stored clause LBD — a genuine porting divergence, fixed to
match the reference, with documented single-file wins (stable-300 11.5×)
and losses in both directions.  Keeping parity is the landed decision;
**reverting would also be defensible on measurement alone** (the null is
indistinguishable), and the resolver is a full-corpus multi-seed study,
recorded as open.

The single-seed tracking metric (23→17) stands as what it is — one seed of
a chaotic system — and the study's original framing ("recorded without
inflation") is why this addendum can revise rather than contradict it.
