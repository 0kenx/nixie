# The per-class arming signature: five static features, no separation (2026-09-12)

The recorded endgame question for the amplitude/restart program: five
intervention families (margin ladder, adaptive margin, tiered schedule,
OTFS, eager-sub, plus their combination) all land on the **same
winner/loser split** — so an adaptive gate on a measurable class
signature would arm the mechanisms only where they pay.  This study
exhausted the cheap static observable set against the combination
screen's per-file ratios (the most complete effect measurement).

## The features, against the combination's conflict ratios

Classes from `2026-09-12-amplitude-combination.md` (ratio < 0.9 = winner,
> 1.2 = loser):

| feature | winners span | losers span | verdict |
|---|---|---|---|
| decisions / conflict | 1.5 – 34.6 | 2.3 – 32.4 | interleaved |
| average LBD | 7.2 – 762 | 9.7 – 221 | interleaved |
| restarts / conflict | 0.001 – 0.099 | 0.022 – 0.055 | interleaved |
| clause / var ratio | 3.6, 4.0, 4.5, 8, 21.7, 58.5, 110, 1323 | 4.3, 5.5, 11.3, 19.8, 31.7, 33.8, 57.4 | interleaved |
| binary-subsumption mass | ~0 everywhere | ~0 everywhere | no signal |

Spot checks that kill each candidate: ITC (4.3 clause/var, loser) sits
between Break_08_24 (3.6, winner) and mp1-Nb7T42 (4.0, winner); rbsat
(57.4, loser) next to stable-300 (58.5, winner); worker_550 (LBD 762,
winner) vs qwh (221, loser) vs circuit64 (8.7, winner).  The
dec/conf-EMA gate was already measured dead in round 7 (adaptive
margin); glue gates in the drought study; this closes the rest of the
cheap set.

## What this establishes

The winner/loser classes are **not separable on any static search-shape
observable** — the effect of an amplitude perturbation is not a function
of the macroscopic search statistics.  This is consistent with the
chaos-band finding (7.31× seed spread): the classes are trajectory
facts, not profile facts.  Every gate design that reads these counters
is dead on arrival; five families of landing data now say so.

## The remaining shapes (recorded, untried)

1. **Online A/B probing** (the tiered study's pre-registered idea): run
   k conflicts with the arm, k without, compare a *within-run* signal
   (conflict rate at matched propagation budgets), arm accordingly.
   The signature is the response to the perturbation itself, not a
   static profile.  Costly to design soundly (the probe perturbs what it
   measures — needs the null discipline), multi-session.
2. **Structural (pre-search) features beyond the cheap set**:
   occurrence-distribution shape, measured redundancy density (an actual
   bounded subsume probe's yield/clause), clause-width entropy.  These
   are formula facts, not search facts — computable once, cheap to gate
   on.  Untested; the redundancy-mass theory of the circuit class
   predicts *some* separation here (circuit64's 1323 ratio is unique,
   but the mid-band interleaving suggests it will not generalize).
3. **Portfolio budget arithmetic** (measured dead once at the 60 s cap —
   the Phase-3 finding; revivable only at wider caps).

The combination itself stays available as two env flags
(`NIXIE_OTFS=1 NIXIE_EAGER_SUB=1`, 0.9645× conflicts, circuit class
fully converted) — arming it per-class is what needs the signature this
study rules out of the cheap observable set.

## Postscript (same day): the structural set fails too

Exact-duplicate fraction and clause-width statistics (mean/σ over the
first 600 k clauses) join the exhausted set — the interleaving is total:

- `dup%`: winners at 0.00 / 0.35 / 2.53 / 5.13, losers at 0.00 / 2.69 /
  4.85 / 7.82 — Break_08_24 (winner, 5.13 %) sits *between* rbsat
  (loser, 4.85 %) and ITC (loser, 7.82 %).
- Width: FmlaEquivChain (W, μ 2.8 σ 0.6) vs mp1-klieber (L, 2.3/0.5) vs
  mp1-Nb7T42 (W, 2.7/0.7) vs qwh (L, 2.1/1.2) — indistinguishable.

**Seven features, zero separation.**  The winner/loser classes are
trajectory facts, full stop — every cheap gate (search-shape or
formula-structure) is dead.  The remaining shapes are the online A/B
probe and the portfolio, as recorded above.
