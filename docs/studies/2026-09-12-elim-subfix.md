# The elim phase-feeder, cheapest form: measured dead (2026-09-12)

The corrected Timetable anatomy (`2026-09-12-elim-ballast-erratum.md`)
left one recorded item: candidate starvation between elimination phases,
hypothesized to be fed by cadical's denser subsume interleave.  The
cheapest form of that lever — **a subsume fixpoint at the elimination
phase entry** (`NIXIE_ELIM_SUBFIX`, rounds until zero yield, bounded at
8) — is landed and measured.

## Screen (54 × 5, vs the 8082e335 baseline, 0 verdict disagreements)

- conflicts geomean **0.9900** (−1.0 %, n = 103); solved **180 → 177**
  (−3).
- x9-09054 3→5, circuit_64in64out 0→2 (the **fourth** independent arm
  converting the circuit class), shuffling 4→5; rbsat 4→2,
  pb_300/stable-300 −1, frb45/700gates/mdp/mp1-klieber −1 each.
- Default stays off.

## The amplitude verdict (the point of the experiment)

**Timetable's `bve_eliminated` is unchanged** (80,614 at 30 k conflicts
vs the baseline's 80,734): the pre-phase subsume rounds were never the
elimination bottleneck.  The phase-2 pre-phase round already yields
9.8 k in both configurations; iterating to the fixpoint adds rounds
whose yields collapse immediately — the dirty set is exhausted, and the
starvation in phases 3+ comes from the *search-side* feeding (learned
clauses marking dirty literals at a rate the schedule cannot compound),
not from too few rounds at the phase entry.

## Mechanism note (why the trajectory moved at all)

The arm's divergence path is instructive: the default `RandomSlice`
subsume mode **re-places the dirty set uniformly at each round's end**
(a fixed-count deterministic re-roll).  Every extra round — even at
zero yield — re-rolls which literals the *next mid-search round* will
schedule.  The arm is therefore fixpoint-mining **plus a dirty-lottery
reshuffle**, and the −1 % aggregate / per-file split is consistent with
the reshuffle dominating.  Any future interleave experiment must
separate these (e.g., a null that only re-rolls).

## Where the feeder item stands

Both forms of "more subsumption between elim phases" are now measured:
the fixpoint at the phase entry (this study — dead for amplitude) and
the search-side feeders (OTFS + eager-sub, landed as arms — they feed
the dirty set directly and super-additively convert the circuit class
but are corpus-neutral in aggregate).  The remaining amplitude gap on
the Timetable class is not reachable by scheduling subsumption
differently; it needs either the arms as defaults (barred by the
aggregate) or a different elimination schedule entirely.

Cells: `precompile/6c769850/benchmark/runs/sc24f/` (config
`elim-subfix`, 270, all verified).  Parity from a clean worktree
(another agent's in-flight nixie-solver edits break the shared tree's
workspace build): 175 files, 0 wrong.
