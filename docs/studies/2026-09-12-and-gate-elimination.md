# AND-gate elimination: the recognizer lands; the compounding blocker is the resolvent ballast (2026-09-12)

> **ERRATUM (same day)**: the "resolvent ballast" below was a counter
> artifact — `num_original` does not decrement on elim retirements, so
> the "+580 k growth" missed ~660 k removals.  Live masses match cadical
> (1,648,558 vs 1,626,226).  See
> [`2026-09-12-elim-ballast-erratum.md`](2026-09-12-elim-ballast-erratum.md)
> for the corrected anatomy (the phase-yield starvation stands; the mass
> narrative does not).

The amplitude diagnosis's #2 lever: cadical eliminates **147,478 of
282,525 variables** on Timetable_C (52 %, solving at 184,851 conflicts
where we time out) with 17,009 AND-gates recognized and gate-aware
resolution.  This session ported the recognizer, measured it honestly,
and root-caused why gates alone do not compound.

## The port (`NIXIE_AND_GATES=1`, `e0cc947e`, default off)

cadical `gates.cpp::find_and_gate` (SATeLite SAT'05): `g ↔ x1∧…∧xk` is
recognized exactly when the occurrence lists contain the sides
`(¬g ∨ xi)` and the base `(g ∨ ¬x1 ∨ … ∨ ¬xk)` (false literals dropped —
actual-binary semantics).  Both orientations are tried, because
`elim_round` flips the pivot to its less-occurring polarity and the same
clauses then present as the OR-shape mirror `¬g ↔ ¬x1∨…∨¬xk`.  A hit
feeds the existing `elim_definition_resolvents_bounded` — the g×a + g×g
restricted products (a×a entailed), the same machinery the sub-solver
`NIXIE_DEFINITIONS` path uses, now reached by pure pattern matching.

Soundness: the equivalence sides ∧ base ⊨ g ↔ x1∧…∧xk is elementary;
two differential suites pin it (240 paired random AND-gate circuits —
verdict agreement, model validity, non-vacuous eliminations — plus 60
broken-gate circuits where one side clause is removed and the recognizer
must not fire).  A subtle test-infrastructure finding: the tiny circuits
solve before the conflict-scheduled eliminator (`lim_elim` = 2 000)
ever fires — the tests run under `presearch_collapse`, which is also why
the arm's corpus-reachable surface is the mid-search schedule.

## Measured: gates alone add ~1 % of the gap

| horizon | base vars eliminated | + gates |
|---|---|---|
| 8 k conflicts | 76,844 | 77,695 (+851) |
| 60 k conflicts | 80,734 | 81,612 (+878) |

The +878 does not grow with the horizon — no compounding.

## The real blocker: the phase-yield collapse and the resolvent ballast

`NIXIE_LOG_ELIM` anatomy over 60 k conflicts (7 phases, every round
`complete=true`, bound growing 0→16 on schedule):

| phase | conflicts | eliminated | DB size |
|---|---|---|---|
| 1 | 2,000 | 74,533 + 198 | 1.75 M → 2.33 M |
| 2 | 6,003 | 1,732 + 379 | 2.33 M |
| 3 | 12,166 | 3,596 + 28 | 2.33 M |
| 4 | 20,263 | 120 + 19 | 2.34 M |
| 5–7 | 31k–59k | 60 → 28 → 21 | 2.34 M |

Our elimination **balloons the database by +580 k clauses** in phase 1
(resolvent ballast); every later phase operates on the bloated formula
where occurrence lists exceed the limits and nothing shrinks again.
cadical runs the same resolution counts (52.8 M) on the same file and
its formula *shrinks* — because its eliminator absorbs its own
resolvents as they are added: **elim-side backward subsumption
(`elimbwsub` 21,891) and elimination-time OTF strengthening
(`elimotfstr` 60,492)**, plus interleaved subsume phases (7 phases,
13 rounds, 107 k subsumed total).

We have `elim_backward_clauses` (the backward pass runs) — but its yield
on Timetable is negligible against the ballast.  The recorded next
eliminator item is that absorption system: resolvent-time
self-subsumption/strengthening against the occurrence lists (cadical
`elim.cpp`'s `elim_backward_clause` OTF arm), which is what converts
one-shot elimination mass into the compounding 52 %-of-variables
amplitude.  Multi-session, soundness-sensitive (in-place strengthening
inside the eliminator), and now precisely scoped by the anatomy above.

## Status

`NIXIE_AND_GATES` stays env-gated default-off infrastructure (its
measured effect is 1 % of the target gap; flipping it on buys nothing
until the absorption system exists).  Committed: recognizer + both
orientations + stats + differential tests + this anatomy.
