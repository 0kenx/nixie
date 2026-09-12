# The amplitude arms compound: OTFS + eager-sub combination screen (2026-09-12)

The amplitude program's closing experiment for the day: circuit_64in64out
(the diagnosis's #1 target, 0/5 at the cap where cadical solves @ 373 k)
had converted under three *different* single arms — tiered 0→2, OTFS
0→1, eager-sub 0→4 — via three distinct mechanisms.  The obvious
question: do they compound?

## Screen

`NIXIE_OTFS=1 NIXIE_EAGER_SUB=1` (both individually landed, sound,
default-off), 54 × 5 seeds, 60 s cap, vs the 8082e335 baseline.
270 cells filed under `precompile/4f51efd7/benchmark/runs/sc24f/`
(config `otfs-plus-eager-sub`), **0 verdict disagreements, 0 rejected
cells** (every SAT model-checked, every UNSAT cadical-agreed).

| metric | base | OTFS only | eager-sub only | **combination** |
|---|---|---|---|---|
| solved (seeds 0–4) | 180 | 180 | 180 | **182** |
| conflicts geomean (n≈102–107) | 1.000 | 1.0160 | 0.9932 | **0.9645** |

The product of the single-arm effects is ≈ 1.009; the measured
combination is **0.9645 — super-additive** (−3.6 %).  The mechanisms
reinforce: OTFS's antecedent rewrites populate the subsumer side that
eager-sub's retirements keep small, and both feed the subsume rounds.

| class | outcome |
|---|---|
| **circuit_64in64out** | **0/5 → 5/5** — full conversion of the #1 diagnosis target |
| mp1-Nb7T42 | 4/5 → 5/5 |
| x9-09054 / frb45 / shuffling | +1 each |
| rbsat | 4/5 → 1/5 |
| mdp | 2/5 → 0/5 |
| pb_300 / 700gates | −1 each |

## Verdict

Not default-on material (−3.6 % conflicts + 2 cells is far short of the
sched-vivon 0.83× bar; the loser set — rbsat/mdp/mp1/pb_300/ITC — pays
more than the circuit class gains).  The combination stays available as
documented infrastructure (`NIXIE_OTFS=1 NIXIE_EAGER_SUB=1`).

**The finding that matters**: the amplitude thesis is confirmed — the
inprocessing mechanisms are *reinforcing*, not independent perturbations.
The circuit class is fully reachable today via two env flags.  The
endgame options recorded for the next session:

1. **Per-class arming** (the five-family demand split, now measured on
   this combination too): arm the amplitude pair only on the
   circuit/structured signature.  The signature question is the same
   one the restart program left (what separates rbsat/mdp from
   circuit/x9 — both measured, no gate yet).
2. **Portfolio arm**: `otfs+eager-sub` as a late arm converts circuit64
   at zero risk to files the default solves — the Phase-3 budget
   arithmetic (60 s cap) is the recorded obstacle.
3. **The eliminator phase-feeder** (Timetable class, still open): the
   combination does not move Timetable (its elim starvation needs
   original-clause removal between phases — the cadical-side absorption
   of originals).

Runner asset: `sc24f-comb-screen-runner.py`.
