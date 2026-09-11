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
