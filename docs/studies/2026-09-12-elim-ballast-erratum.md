# ERRATUM: the resolvent-ballast narrative was a counter artifact (2026-09-12)

`2026-09-12-and-gate-elimination.md` root-caused the Timetable
elimination-amplitude gap as "our elimination balloons the database by
+580 k resolvent clauses while cadical's shrinks".  **That was wrong**:
the `orig=` counter in the `NIXIE_LOG_ELIM` phase line is
`clauses.num_original()`, which increments on every
`add_original` (resolvents) but is **never decremented by the
elimination's retirement path** (`elim_retire` → `retire_clause` →
`mark_deleted_raw` — only the separate `remove` path decrements).  The
"+579 k growth" counted the additions and missed ~660 k retirements.

## The corrected anatomy (measured, `live_orig` now in the phase line)

| | nixie (phase-1 end) | cadical (its big elim event, t = 3.6 s) |
|---|---|---|
| live original clauses | **1,648,558** | **1,626,226** |
| resolvents added | 577,633 (7.75 / eliminated var) | ~600 k (inferred: −108,691 net with ~728 k pivot-clause removals) |
| vars eliminated | 74,535 + 198 | 91,067 |
| backward-pass retirements | 4,799 | `elimbwsub` 21,891 (whole run) |
| OTF antecedent shrinks | 10,738 | `elimotfstr` 60,492 (whole run) |

The elimination **masses match** (1.4 % apart).  cadical's elimination
adds resolvents at the same rate we do and removes the same pivot-clause
mass — the SATeLite economics are identical.

## What the gap actually is

The residual amplitude difference (cadical 147,478 vars = 52 % vs our
~81 k = 29 %) is the **phase-yield collapse with candidate starvation**:
our phases 3+ eliminate hundreds where cadical's events keep eliminating
tens of thousands.  With matched algorithms (bound, limits, OTF shrink,
backward pass all verified identical), the difference is the **feeding
between elim events** — cadical's inprocessing interleave is denser
(subsume phases removing 5.5 k–20 k clauses between elim events,
transred −12.8 k, probing), each removal re-marking variables for the
elimination schedule.  Our one budgeted pre-phase `subsume_round` yields
~500–1,500 on this file.

So the "eliminator absorption system" item reshapes into what the
morning diagnosis originally said: **subsume-phase strength** (the
round hit-rate / candidate-generation gap) plus interleave density.
The OTFS + eager-sub arms (landed, default-off) feed exactly this when
armed — the combination screen's super-additivity on the circuit class
is the same mechanism family.

## Landed alongside this erratum

- `NIXIE_LOG_ELIM` round lines now carry `added= bw_retired=
  otf_shrunk=` and phase lines carry `live_orig=` (a direct live-count,
  O(live) per phase under the flag only) — the ballast anatomy is now
  measurable, not inferable.
- The counters are stats-field-class writes (same as `subsumed_removed`)
  and were verified trajectory-identical (Timetable @ 8 k and
  circuit_64in64out @ 15 k bit-exact).
