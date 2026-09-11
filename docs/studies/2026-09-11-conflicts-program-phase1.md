# Conflicts program Phase 1-3: corpus gap map, shape diffs, two failed conversions (2026-09-11)

Continues the 2026-09-07 campaign's lever catalog (`Tier 1 — the conflicts
program`). All cells recorded via benchstore (suite `sc24f`, sha `75650d99`
worktree): nixie × seeds 0-4 (378-cell phase-1 sweep) + the portfolio and
tail-probe arms below. Harness: the merged `cnf_solve` (`9f8221e4`).

## Phase 1 — the corpus gap map has inverted

Standing corpus, 54 files, 60 s cap, conflicts-to-verdict (nixie median of
5 seeds; references single-shot):

| | both-decided geomean |
|---|---|
| nixie / cadical 3.0.1 (n=37) | **0.781×** |
| nixie / kissat 4.0.4 (n=37) | **0.848×** |

The campaign-era 2.6×-median gap is gone — the aggregate conflicts program
succeeded via the intervening landings (inprocessing default-on, SSR+probe,
sweep, level-0 seeding). What remains is a *tail* problem. Worst
both-decided cells vs kissat: **worker_550 7.8×** (3/5 solved; med 15.7k vs
2.0k), frb65-12-2 2.76× (spread 30× — chaos class), **x9-08075 1.90×
(spread 1.09 — systematic)**, summle_X4044/X4053 1.77× (the Gent-chaos
losses, re-confirmed), Break_unsat_06_07 1.41×. The user-table files are
milder vs kissat: j3037 1.24×, constraints 1.03×, crn 1.08×, noL 1.08×
(noL is throughput-bound at its 1.2 M conflicts, not conflict-bound).
Measurement traps carried forward: cadical/kissat cells under parallel load
are wall-censored (64_25's "1332" was a load artifact; solo it solves at
5,026 conflicts / ~90 s).

## Phase 2 — shape diffs at equal conflicts (MAXC-capped, seed 0)

| file (at cadical's total) | nixie dec/conf | cadical dec/conf | nixie restarts/conf | cadical | signal |
|---|---|---|---|---|---|
| x9-08075 @329k | 2.26 | 1.36 | 0.056 | 0.030 | decisions/conflict ~1.7× |
| summle_X4044 @46k | 9.5 | 5.04 | 0.091 | 0.098 | dec/conf 1.9× |
| frb65-12-2 @167k | 2.29 | 1.48 | 0.056 | 0.038 | dec/conf 1.5× |
| worker_550 @2003 | 108.9 | 58.5 | **0.0045** | 0.044 | **avg_lbd 1873, restart drought** |

worker_550 re-confirms the 2026-09-07 T1 diagnosis on current HEAD: the
focused Glucose condition (fast ≥ 1.10× slow glue EMA) never fires on the
uniform-huge-glue stream — 9 restarts in 2,003 conflicts, learned clauses
averaging LBD ≈ 1900. cadical restarts 10× as often and spends 75 % of
conflicts stabilizing. The systematic residual across the other tails is
**decisions/conflict 1.5-1.9×** — a decision-quality / phase-policy gap,
not a restart-cadence one.

## Phase 3 — both studied conversions re-screened and failed

1. **Portfolio** (`SEEDS=default,chrono,maxgap-1000 ARM_CONFLICTS=400000,400000,`):
   solved-at-cap **203 → 197 (−6)**, 0 verdict disagreements. The budget
   arithmetic is structurally mismatched at a 60 s cap: on
   slow-throughput files the early arms never exhaust before the cap (the
   maxgap fallback never fires — worker_550 stayed 3/5), while on files
   whose default trajectory needs 300-600 k conflicts (x9-08075 3/5 → 0/5,
   FmlaEquivChain 5/5 → 3/5) the budget truncates the winning arm.
2. **maxgap-1000 as the default** (the campaign's −3 flip, re-screened at
   90 s on the previous winners *and* losers): worker/constraints/qwh/6s167
   hold 5/5, but **noL 1/5 → 0/5, mdp-28-14 2/5 → 0/5, rbsat 4/5 → 2/5**.
   The flat floor still costs verdicts on the long-healthy-gap class.

Both exits from the 2026-09-07 study ("portfolio shape" / "class gate")
are dead ends in their simple forms on current HEAD. What would remain:
a *signature-gated* floor (fire only when the glue stream is uniform-huge
*and* the gap dwarfs its own EMA — i.e. stall8's gate with maxgap's
constant), or the kissat-native route (stable/focused phase schedule with
tiered restarts rather than any floor).

## Landed: the `maxgap-<n>` portfolio arm

`SolverConfig::restart_maxgap` (config-level form of
`NIXIE_RESTART_MAXGAP`, env as fallback, both unset = bit-identical
default — verified on crn/break/si2/mrpp full solves) plus the
`maxgap-<n>[:<seed>]` harness arm token, joining `chrono`/`els` as A/B
infrastructure. Single-arm evidence: worker_550 maxgap-1000 solves **5/5**
seeds (6.8k-92k conflicts) where default solves 3/5 with two timeouts.

## Where the program goes next

The aggregate is won; the tails decompose into (a) worker-class restart
drought — needs the signature gate or kissat-shaped phase schedule, both
matched-null class; (b) the **dec/conf 1.5-1.9× systematic** on
x9/summle/frb65/Break — decision-quality territory (branching score,
phase saving, learnt-clause quality), the largest unexplained shape delta;
(c) chaos tails (frb65 30× spread, mdp 17×) where only ≥10-seed tails
campaigns can claim anything. Seeds move the search (verified: crn s0
93,638 vs s1 89,536).

Gates: workspace nextest 10,931/10,931; clippy/fmt/rustdoc clean; Z3
parity 4.16.0 — 175 files, 0 wrong.
