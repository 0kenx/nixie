# The amplitude→trajectory translation, answered: the one-sided arm removes the region the carried phase state exploits (2026-09-14)

Round-11 handoff item 2 — the program's closing open question:
*why does a 17 k-variable-richer elimination (NIXIE_ELIM_ONESIDED,
Timetable round 1: 74 755 → 91 808, cadical parity) slow the solve so
much that Timetable times out at 300 s (0/5) while the default solves
5/5 — and cadical, eliminating the same 91 k, solves in 33.6 s?*

The answer, measured: **the richer elimination does not make the
formula harder — it makes the *carried search state* worthless, and our
search's Timetable performance is almost entirely carried state.**  The
one-sided retirement removes the formula's shallow-conflict region (the
pure-side clauses), which is exactly the structure the phase tables
have encoded and continue to exploit.

## The decomposition (new tooling: `NIXIE_DUMP_ELIM_PHASE=<n>`)

`NIXIE_DUMP_ELIM_PHASE=2` dumps the formula at the second elimination
phase's entry (live originals + level-0 units — the post-round-1 state;
same dump format as `NIXIE_DUMP_ELIM_ENTRY`, now factored into
`dump_elim_state`).  Dumps taken under both arms, SEED=2, then solved
by a **fresh default search** (no arm):

| fresh default search on | clauses | conflicts to Sat |
|---|---|---|
| default's phase-2 formula | 1 659 286 | 489 k (seed 2); seeds {0,1,3}: TO@500 s / 1 206 k / 392 k |
| onesided's phase-2 formula | 1 648 123 | 478 k (seed 2); seeds {0,1,3}: 580 k / 978 k / 506 k |

**The arm's formula is consistently easier-or-equal for a stateless
search** (median ~540 k vs ~700 k+, one default-formula seed times out
at 500 s where all arm-formula seeds solve).  The formula shape is
exonerated; richer elimination leaves a *better* formula.

## The carried state is the performance (new probe:
`NIXIE_ELIM_RESET_PHASES=<min-retired>`)

The probe resets `phase`/`best_phase`/`target_phase` (and their
counters) at the end of any elimination phase that retires ≥ N vars —
activities, learned DB, restart state untouched.  Timetable:

| configuration | conflicts to Sat |
|---|---|
| default carried | 6–32 k per seed (5/5 ≤ 300 s; seed 2: 32 423) |
| **default + phase-reset** | 314 k (seed 2); seeds {0,1,3}: 909 k / 834 k / 851 k |
| onesided carried | **0/5 at 300 s** (665 k+ and climbing at the cap) |
| onesided + phase-reset | 793 k (seed 2); seeds {0,1,3}: 1 113 k / 874 k / 971 k |

Two reads:

1. **The default's 20–100× edge is phase state.**  Every stateless-ish
   configuration — fresh on either formula, either arm with phases
   reset — lands in the 300 k–1.2 M conflicts band, one to two orders
   above the carried default.  The phase tables built over the
   *pre-elimination* formula remain valid guidance for the default's
   post-elimination formula because two-sided elimination (resolve,
   add resolvents) preserves the pure-side clause mass the phases
   encode.
2. **The arm doesn't merely lose that value — removing the region
   invalidates it.**  With the region retired, the carried phases steer
   the search into structure that no longer exists: within 2 k
   conflicts of the resume, learned clauses average LBD 48.6 vs the
   default's 24.0 (identical phases at resume, near-empty learned DB in
   both arms — 26 %+ of vars eliminated means every learned clause
   mentions one and is retired), and decisions/conflict lock at ~74
   where the default improves to ~60.  The walk is exonerated
   (`WALK=0` changes nothing; the gap persists), the empty learned DB
   is symmetric across arms, and a phase reset that would *help* a
   merely-confused search does not recover the arm (793–1 113 k —
   still around-or-above its own fresh band): the residual poison is
   carried *activities* pointing at removed structure, documented as
   the open residue of this study.

## Why cadical solves the same elimination at 185 k conflicts

cadical never leans on cross-elimination phase carry the way our
co-adapted search does: its rephase machinery reset polarities 18× and
walked 5× over the solve (cadical Timetable statistics), so its search
is always near its "stateless band" — and its stateless band (185 k)
is 3–6× better than ours (~540 k–1.2 M) on this family.  Our
flat-2k-clock co-adaptation bought the 20–100× carried-state miracle
on the old elimination shape (the clock-matrix studies' local optimum)
at the price of fragility to elimination amplitude: any arm that
retires the pure region collapses the search to its stateless band,
which 300 s cannot pay on Timetable's clause mass.

**The translation, stated once**: elimination amplitude and search-state
carry are coupled levers.  The default's amplitude leaves the formula's
easy region in place, so carried state compounds (6–32 k).  The one-sided
arm's amplitude converts that region into upfront simplification
(fewer clauses, fewer vars — a strictly better formula), and the search,
built to carry state across the boundary, cannot re-derive in 300 s
what the fresh-search band pays 500–1 200 k conflicts to find.  The
aggregate-conflicts improvement (0.974 geomean) is real because most
corpus files don't have a Timetable-scale carried-state investment to
lose; the 60 s / 300 s losses concentrate where they do.

## What this closes, and the next lever it names

- The handoff's candidate angles: (a) restart/phase-saving co-adaptation
  — **confirmed, primary**; (b) occurrence-list mass — not needed to
  explain the effect (the fresh-search band shows the reduced formula
  is fine); (c) learned-clause quality — a symptom (LBD 2× at resume),
  not a cause.
- The actionable corollary for any future amplitude arm: it must ship
  with a state cadence our search tolerates — e.g. cadical-style
  aggressive rephasing after high-amplitude phases, or phase-state
  preservation aware of retired regions.  The clock-matrix result
  (each single-step cadence change loses) says this is a *joint*
  schedule redesign, now with the mechanism identified: the design
  target is maintaining the validity of carried phases across the
  elimination boundary, not the elimination itself.
- Handoff item 3 (the metric question) gets its sharpest datum yet:
  the 60 s cap and the 300 s cap agree on this arm (both reject), and
  both misjudge the *mechanism* — the arm's losses are not search
  weakness but carried-state collapse, which no wall-cap metric can
  distinguish from cost.  The conflicts-geomean vs cap-cells split
  (0.974 vs −8/−5-file) is exactly what a carried-state story predicts.

## Tools landed (default-off diagnostics)

- `NIXIE_DUMP_ELIM_PHASE=<n>` — dump the formula at phase-n entry
  (`dump_elim_state` factored out of the phase-1 dump; byte-identical
  `NIXIE_DUMP_ELIM_ENTRY` behavior).
- `NIXIE_ELIM_RESET_PHASES=<min-retired>` — reset the phase tables at
  the elimination boundary (the ghost-attractor probe).
- Runner: `outputs/amp_traj_multiseed.py` (the four-cell × multi-seed
  harness behind the tables above).

All measurements: binary built at `0e005231` + these diagnostics,
Timetable (`2a15a301…Timetable_C_392…`), seeds as marked; single-seed
cells are marked and only 10×-scale reads are drawn from them.
