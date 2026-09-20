# Correction: the standing table's z3-conflict column was a parser artifact — re-attributing the fragile BV cells

**Date:** 2026-09-20 (late; the solve-eqs probe session).
**Landed with this:** the `run_perf.sh` z3-counter fix (grep
`:sat-conflicts` first, `:conflicts` as fallback).

## The bug

`run_perf.sh`'s `run_z3` grepped `:conflicts N` from z3's `-st` output.
On the bit-blasted QF_BV path z3 prints **`:sat-conflicts`** and never
`:conflicts` — so **every z3 conflict count in every recorded snapshot
is `0`**.  Verdicts and wall columns were always real; only the z3
conflict columns were junk (the snapshot aggregates "z3 89 504" etc.
were also artifacts — parsed from the SMT-core counter on LIA families
where it exists, and 0 on BV).

## What survives (re-verified against z3 -st directly)

- `counterexample.dump.ia32_Mul_*` (BuchwaldFried): **`sat-mk-var 1`,
  no conflicts line at all** — a genuine preprocessing-only decision.
  The extract-window rules' timeout→unsat-at-25 ms stands on real
  evidence (nixie's own 0 conflicts).
- `prp-3-18` / `problem_2__014` (the 47×/42× wall-watch cells): the
  2026-09-19 attribution study verified those by direct
  `(apply simplify)` probes folding to `false` — tactic-level evidence,
  not the counter column.  Stands.

## What changes

- **`Sage2/bench_16217`**: z3 decides it with **2 371 SAT conflicts /
  6 675 decisions / 2.9 M propagations in 1 067 ms**; nixie's 39 860
  conflicts ≈ **17× z3's** — the gap is **SAT-core capacity on the
  bit-blasted instance**, not preprocessing.  The wall-watch study's
  "tactic-cascade owns it" attribution is retracted; the SAT arc owns
  this cell (conflict-count ratio vs z3 is the metric).
- **`sage/app12/bench_2780`**: z3 uses **329 conflicts** — same class.
- The solve-eqs route probe that started this: the SAGE family's
  definition variables (`|T4@k| = byte-concat(|T1@…|)`, asserted via
  let-wrapped equalities) have **~500 uses each** — substitution is
  explosive and z3's own `solve_eqs_max_occs=2` would refuse them.
  Solve-eqs is *not* the closer for this family; withdrawn as a route.

## Consequences for the map

- The fragile-BV cells (16217 at 9.9 s, 11463 at 6.5 s) are
  **SAT-capacity cells** — the SAT arc's territory (their CSR/surgery
  campaign is exactly that surface).
- The BV-preprocessing routes that remain real: the BuchwaldFried-class
  identities (landed), the prp/nec ctx-simplify class (own-session,
  unchanged).
- Future tables record honest z3 counters — the wall-watch readout's
  "both-solved conflict ratio" column becomes meaningful from the next
  calm snapshot on.
