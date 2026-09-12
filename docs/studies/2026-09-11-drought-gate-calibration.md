# Drought-gated max-gap floor: the calibration matrix and why it parks (2026-09-11)

Follow-up to [`2026-09-11-conflicts-program-phase1.md`](2026-09-11-conflicts-program-phase1.md).
The ungated `maxgap-1000` floor fixes the worker-class restart drought
(worker_550: 5/5 seeds, 6.8k-92k conflicts) but costs verdicts on
noL/mdp/rbsat; this round built the class gate the 2026-09-07 study called
for and measured it out of a default.

## The gate

`NIXIE_RESTART_DROUGHT_MAXGAP=<n>` / `SolverConfig::restart_drought_maxgap`
(default off = bit-identical, verified on crn/si2/worker full solves): the
flat floor at `n` fires only while `glue_current.fast.value() >
DROUGHT_GLUE_GATE` after `DROUGHT_WARMUP` conflicts — the
uniform-huge-glue signature of the drought class.

## Measured separation and its failure

The cumulative-average separation is real (worker 762, qwh 224 vs noL 21,
mdp 15, rbsat 10, 6s167 11) but does not survive as a *fast-EMA* gate:

| (gate, warmup) | worker | qwh | mp1-Nb7T42 | rbsat/frb45 | others |
|---|---|---|---|---|---|
| (100, 0) — round 1 | fires, good | fires, **mixed-negative** | fires, mixed | **leaks via early-glue transients** (rbsat 4/5→2/5) | inert |
| (300, 1000) — round 2 | fires, good (med 15k vs 28k) | fires, mixed | fires, **worse** (seed 325k→TO) | inert | inert |
| (500, 1000) — round 3 | fires, weaker (med 45k) | **still fires, mixed** | inert | inert | inert |

The mechanism of the failure: **qwh's glue stream is bimodal** — its fast
EMA crosses *every* workable threshold during its huge-glue phases, and in
those phases the floor hurts it (seed 0: 32k→183k). mp1 sneaks through at
300. There is no single point that keeps worker_550 (needs the floor)
while excluding qwh/mp1 (floor-negative): worker and qwh both live above
the gate wherever the gate does anything at all.

Corpus flip screen at (100, 0): solved-at-cap 209→215 (+6), 0 verdict
disagreements — but the per-file conflicts probe showed the gains were
dominated by transient-leak trajectory changes (pb_300/stable-300) that
vanish at (300, 1000); the honest refined-gate corpus effect is
worker-only (~+2 cells) against qwh/mp1 collateral. Not landable as a
default; the arm stays env-gated/config-gated infrastructure.

## What did land

- `SolverConfig::restart_drought_maxgap` + `NIXIE_RESTART_DROUGHT_MAXGAP`
  + `DROUGHT_GLUE_GATE = 500` / `DROUGHT_WARMUP = 1000` constants, default
  off, bit-identical (crn/si2/worker verified; workspace nextest
  10 937/10 937; clippy/fmt/rustdoc clean; Z3 parity 4.16.0 175 files,
  0 wrong).
- The calibration matrix above, so the next attempt starts from the
  measured map instead of re-deriving it.

## Where this leaves the restart-drought tail

Three exits are now measured dead: flat default (costs noL/mdp/rbsat),
portfolio (budget arithmetic), single-threshold glue gate (qwh/mp1
collateral). What remains untried and promising:

1. **Per-restart drought accounting instead of glue**: arm the floor only
   when *this search's own* restart-gap distribution has collapsed (gap
   EMA stagnation — `restart_gap_ema` already exists) *and* the trail is
   deep — qwh's bad phases have healthy gap EMAs, worker's drought does
   not; this separates on the drought axis rather than the glue axis.
2. **kissat-shaped tiered schedule** (stable/focused phases with
   per-mode restart policies) — the structural fix rather than a floor.

The bigger systematic from Phase 2 — decisions/conflict 1.5-1.9× across
x9/summle/frb65/Break — remains the program's largest open target.

## Round 4: gap-stagnation conjunction — isolates the collateral, indicts the medicine

`NIXIE_RESTART_DROUGHT_MAXGAP` now also requires `gap >= 8 x restart_gap_ema`
(`DROUGHT_GAP_K = 8.0`; the gap EMA freezes during a drought because it is
updated only at restarts, so this is the drought axis itself). 12-file
probe, 5 seeds:

| file | effect |
|---|---|
| mp1, rbsat, frb45, noL, mdp, 6s167, pb_300, stable-300, x9, summle | **fully inert** (bit-identical) |
| worker_550 | fires — but the changed seeds get *worse* (10k→47k, 28k→29k, 59k→80k conflicts) |
| qwh.50 | seeds 1/3 still fire — *worse* (132k→207k, 115k→313k) |

The conjunction achieves the separation every earlier point missed, and the
separated outcome shows the floor itself is the problem: where the arming
is strict enough to be safe, the forced gap-1000 restart no longer helps
even worker_550, and qwh's genuine drought phases are floor-negative at
every arming.  Across four rounds the only configuration that beat
worker_550 decisively was the *ungated* floor (and the `maxgap-1000`
portfolio arm remains that tool: worker 5/5 at 6.8k-92k conflicts, 2026-09
studies + this round's probes).  The restart-drought family is closed:

1. flat floor — corpus-negative (noL/mdp/rbsat);
2. glue gate — no separable threshold (qwh bimodal);
3. glue + warmup — mp1 leak at 300, qwh always;
4. glue + warmup + gap-stagnation — safe, and thereby revealed ineffective.

What would actually close the worker-class tail is the structural
difference the shape data points at: cadence plus phase policy (kissat's
tiered stable/focused schedule with per-mode restart policies), not a
floor.  The landed arm keeps the round-4 conjunction (safest arming) and
stays off by default.

## Round 5: the dec/conf mechanism is causal — focused-restart margin ladder

Phase 2's systematic (nixie dec/conf 1.5-2x cadical on the tails) tracks
our focused restart rate: 99.5% of our restarts are focused-mode Glucose
fires, at ~2x cadical's cadence with identical EMA constants
(emagluefast 33 / emaglueslow 1e5 / margin 1.10; j3037: restart every ~12
conflicts vs cadical's ~22, stable shares 51.5% vs 43.0%, stable-phase
restarts 109 vs cadical's reluctant-doubling few).

`NIXIE_FOCUSED_MARGIN` (env arm, default 1.10 = bit-identical; OnceLock,
no per-conflict cost) raises the fire margin. 5-seed medians (120 s cap,
all cells decisive):

| file | 1.10 | 1.25 | 1.40 |
|---|---|---|---|
| Break_unsat_06_07 | 35,959 | 36,237 | **21,749 (−40 %)** |
| summle_X4044 | 81,294 | 61,015 | **54,006 (−34 %)** |
| j3037_10_mdd_bm1 | 348,577 | 405,499 | 426,884 (+22 %) |
| x9-08075 | 628,266 | 666,912 | 704,821 (+12 %) |
| frb65-12-2 | 461,240 | 970,938 | 727,933 (+58 %, non-monotone) |

dec/conf collapses to cadical level (1.2-1.5) at 1.40 everywhere — the
mechanism is confirmed causal — but the conflicts response is split:
the two Break/summle-family tails win 34-40%, j3037/x9/frb65 lose 12-58%.
That split is the matched-null question: is the Break/summle win the
*semantic* content of slower Glucose firing (deeper focused phases) or
just restart-rate reshuffle? Null design (pre-registered): fire the 1.10
trigger but only every k-th evaluation with k tuned to reproduce 1.40's
restart count per file — same rate reduction, no EMA information — then
the full 54x5 corpus screen for whichever margin (or per-class gate)
survives. The Break/summle class would close 1.4-1.8x of the remaining
kissat gap on two user-table files.

## Round 6: the margin arm's matched null — attribution settled

Null v1 (scrambled glue reference) was **magnitude-broken and is recorded
as a trap**: a full-variance reference makes `fast >= 1.4x rand-past-glue`
fire at the *base* rate (j3037 null: 33,045 restarts vs the treatment's
1,366), so it is not a null at all — the same failure class as the
campaign's first stall-null build.  Removed.

Null v2 (`NIXIE_FOCUSED_MARGIN_NULL=1` + `NIXIE_FOCUSED_FIRE_EVERY=k`,
default 20): fire every k-th pass of the untouched 1.10-margin condition —
same restart-count reduction family as the margin treatment (counts match
within ~2x on every probe file), no EMA information in which passes fire.
5-seed medians, conflicts/restarts:

| file | base | treat 1.40 | null k=20 | T/N | N/B |
|---|---|---|---|---|---|
| Break_unsat_06_07 | 35,959/2,954 | **21,749/25** | 34,002/83 | **0.64x** | 0.95x |
| summle_X4044 | 81,294/9,069 | **54,006/849** | 62,947/435 | **0.86x** | 0.77x |
| j3037_10_mdd_bm1 | 348,577/29,192 | 426,884/1,366 | 437,657/2,083 | 0.98x | 1.26x |
| x9-08075 | 628,266/33,180 | 704,821/646 | 721,437/2,507 | 0.98x | 1.15x |
| frb65-12-2 | 461,240/27,288 | 727,933/2,389 | 386,950/1,674 | **1.88x** | **0.84x** |

**Attribution**: Break_06_07's -40 % is real EMA-informed content (T/N
0.64 at a null that itself does nothing); summle's -34 % is roughly half
semantic, half generic rate; j3037/x9's losses are pure rate effects; and
frb65 is *anti*-semantic — at the same reduced rate, EMA-blind firing
beats the margin (0.84x vs base while the treatment sits at 1.58x).
Restarts on this corpus are a per-family sign, not a monotone good.

The class signature is visible in the base shapes: the two semantic
winners have the highest base dec/conf (summle 9.5, Break ~5.5 vs j3037
2.8, x9 2.1, frb65 2.2).  The designed follow-up (pre-registered):
**dec/conf-adaptive margin** — margin ramps 1.10 → 1.40 as a decisions-
per-conflict EMA crosses ~4 → ~8, targeting the decision-bloated class
while leaving the tight-search class at today's cadence; then the 54x5
corpus screen and this same null for the gate itself.
