# Restart-EMA input + block-UIP clause shrinking (cadical `shrink=3` port)

Date: 2026-08-19
Verdict: **Landed as cadical-parity defaults.** Headline (94-file tracking, canonical
seed) improved 23 → 17 files above 1.5× of CaDiCaL (geomean 1.129× → 0.952×), 0 verdict
disagreements. The 5-seed null study is *completion-biased positive, instruction-noisy* —
recorded below without inflation. One soundness bug in the new shrink port was found and
fixed before landing (with two regression tests); it was ours, not pre-existing.

## Item-1 background: where the 4.5× decisions/conflict term actually lives

The handover's search-quality term decomposed (stable-300, fixed 100k conflicts,
traced via `OXIZ_TRACE_DECISIONS` + a temporary bump trace):

| metric                      | OxiZ (before) | CaDiCaL (log replay) |
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
(11.5×), first restarts at ~70–110 conflicts. `OXIZ_GLUE_LEGACY=1` restores the old
input for A/B; `OXIZ_GLUE_NULL=1` feeds the previous conflict's walk glue (matched null).

## Change 2: block-UIP clause shrinking (`shrink.cpp`, cadical default `shrink=3`)

Port of `shrink_and_minimize_clause`: per decision-level *block* of the raw 1-UIP
clause, run a mini 1-UIP restricted to that level and replace the block by its block-UIP
literal; plain recursive minimization remains the in-block fallback and the LRAT path.
On stable-300 this takes avg stored-clause LBD from 28.6 to 12.9 and dec/conf from 4.97
to 1.68 (Cadical 1.27), with 99.5% of restarts now reusing a prefix. `enable_shrink`
(default true, cadical parity); `OXIZ_SHRINK_NULL=1` runs the full walk and discards the
result (matched null).

### The bug the port surfaced (fixed before landing)

`shrink_block`'s backward trail scan recomputed the popped literal's trail index as
`cursor + 1` *after* the pop loop. With `cursor.saturating_sub(1)`, a block-UIP at trail
index 0 leaves the cursor at 0, so `cursor + 1` is the *next* literal above — the block
was replaced by the wrong literal's negation. End-to-end symptom: 194 incremental
model-blocking clauses over an 8-Boolean tautology answered `unsat` in the SMT layer
(oxiz-cli model-counter test; certified-mode independently rejected the verdict, Z3 says
sat). Minimized to a standalone 194-clause CNF reproducing at the SAT core
(`focused_vmtf=false` + shrink); first unentailed clause `[3,4,5,-7,6,-8]` at conflict
33 (block `{-8,-1}` at level 1; UIP = the level-1 *decision* `-1`, replaced by `-8`).
Fix: capture `uip_pos = pos` at pop time. Tests:
`oxiz-sat/tests/shrink_trail_index_regression.rs` (minimal CNF + brute-force oracle;
every clause load-bearing) and `oxiz-solver/tests/shrink_tautology_regression.rs`
(end-to-end 194-block script).

## Measurements (the honest part)

**94-file tracking metric** (instructions-to-verdict, `perf stat -e instructions`,
verdicts cross-checked vs CaDiCaL; deterministic canonical seed):

| arm | geomean cad/oxiz | files > 1.5× | disagreements |
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
- **Reuse-keep-top-fraction probe** (`OXIZ_REUSE_KEEP`, non-semantic): keeping ~50% of
  levels at restart cut decisions 466k → 298k — confirms restart *cost* is the lever,
  but is not a cadical semantic and was not pursued further once shrink delivered the
  same equilibrium shift semantically.
- **Propagation completeness**: `OXIZ_CHECK_FIXPOINT` sweep (hanging-unit invariant at
  decision points, 8k conflicts) — zero violations. BCP is not missing cascades.
- **Restart frequency as cause**: cadical restarts *as often as we do* (4996 vs 5313);
  the difference is entirely cost-per-restart.
- **Inprocessing as cause**: cadical with all inprocessing disabled still shows the good
  regime (1.26 dec/conf, 97.8% reuse); it is 4.6× slower end-to-end but the search
  shape survives. Our stack's net-negative verdict (1.74×) is unchanged by this result.

## Files

- `oxiz-sat/src/solver/conflict.rs` — walk-glue snapshot, `improve_learnt_clause`
  dispatcher, `shrink_and_minimize_clause` / `shrink_block` / `shrink_literal` port,
  bump-block reordering (shrink adds block-UIP vars to the bump set where cadical adds
  them to `analyzed`).
- `oxiz-sat/src/solver/learn.rs` — `note_learned_lbd` EMA input switch (+ nulls).
- `oxiz-sat/src/solver/decide.rs` — restart diagnostics (`restarts_stable`,
  `reused_trails`, `reused_levels`), `oxiz-restart` trace line.
- `oxiz-sat/src/solver/{mod,search_ext,tests}.rs`, `config_presets.rs`, `lib.rs` —
  config/stats/flag plumbing, fixpoint diagnostic, updated EMA-contract test.
