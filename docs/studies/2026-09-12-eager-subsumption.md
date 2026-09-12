# Eager subsumption: landed, screened — corpus-neutral, circuit-class conversion (2026-09-12)

The amplitude diagnosis's lever #3 (`docs/studies/
2026-09-12-inproc-amplitude-diagnosis.md`): cadical's
`eagerly_subsume_recently_learned_clauses` (default ON there, 51 672
retirements on Timetable_C = 48 % of its total subsumed).  Ported as
`NIXIE_EAGER_SUB=1` (`4f51efd7`, default off = bit-identical).

## The port

After each conflict's driving clause is installed, walk the learned
clauses **newest-first** for at most `eagersubsumelim = 20` candidates
(every visit consumes budget — garbage and self included — so the walk
is exactly the newest ≤ 20 entries, snapshotted before the mutable
retirements) and retire any clause subsuming-contained by the fresh one.
Learned-by-learned only: both are formula consequences and the subsumer
is strictly stronger — sound by construction; `retire_clause` handles
the watch/BIG purges and re-points live trail reasons to `Decision`.

This is **not** the removed unbounded `check_subsumption` scan (the crn
lesson: ~30 % of instructions in an O(learned) walk) — a constant ≤
20-probe walk, cadical's exact shape, which is why the old NOTE's
cadical-parity claim was subtly wrong: cadical *does* subsume per
learned clause, just budgeted.

## Screen (54 × 5 seeds, 60 s cap, vs the 8082e335 baseline)

- Solved-at-cap **180 = 180**, **0 verdict disagreements** (every SAT
  model-checked, every UNSAT cadical-agreed), 0 rejected cells.
- Both-decided conflicts geomean **0.9932 (−0.7 %, n = 103)**.
- Yields: 11 495 retirements on circuit_64in64out @ 15 k (3.8 % hit
  rate), 3 790 on Timetable @ 20 k.

| winners | | losers | |
|---|---|---|---|
| **circuit_64in64out 0/5 → 4/5** | — | mp1-Nb7T42 | 1.98× |
| 170058440 0/5 → 1/5 | — | FmlaEquivChain | 1.42× |
| x9-09054 3/5 → 4/5 | ~1.0× | ITC2021 | 1.40× |
| shuffling-2 4/5 → 5/5 | ~1.0× | constraints_17 | 1.33× |
| rbsat (conflicts) | **0.48×** | rbsat (solved) 4/5 → 2/5 | — |
| stable-300 | 0.67× | mp1-klieber 3/5 → 1/5 | — |
| qwh.50 | 0.69× | af-synthesis 3/5 → 1/5 | — |
| worker_550 | 0.80× | frb45 1/5 → 0/5, pb_300 −1 | — |

## Verdict

**Default stays off** (aggregate −0.7 % is inside the chaos band; the
repo's default-on bar is the sched-vivon class of 0.83×).  The arm joins
the documented-negative-as-default infrastructure with a real
winner-class conversion.

The circuit-class result is the session's signal: **circuit_64in64out
(0/5, cadical solves @ 373 k) now converts under three different arms —
tiered (0→2), OTFS (0→1), eager-sub (0→4)** — three different
mechanisms (schedule, antecedent rewriting, learned-DB hygiene), the
same winner.  The restart-hungry loser set is equally constant
(mp1/rbsat/af-synthesis/ITC).  Combined with the four-family record,
the corpus genuinely factors into two demand classes, and the circuit
class is reachable by *any* sufficiently strong perturbation of the DB
state — consistent with its diagnosis profile (99.7 % of its mass is
redundant and removable; whichever arm starts removing it, compounds).

## The remaining eliminator item (unchanged)

Eager-sub does not feed the elimination marked sets (learned-only
retirements mark nothing) — the Timetable phase-yield starvation
(anatomy in `2026-09-12-and-gate-elimination.md`) needs original-clause
removal between phases: cadical's elim-side absorption (backward
subsumption of *originals* during elimination, `elimotfstr`-class
strengthening inside the resolvent loop) or stronger interleaved subsume
phases.  Recorded as the next eliminator item.

Cells: `precompile/4f51efd7/benchmark/runs/sc24f/` (270, all verified).
