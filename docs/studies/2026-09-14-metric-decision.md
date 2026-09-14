# The metric question settled: the 60 s cap was right, the "aggregate favors amplitude" was survivorship bias (2026-09-14)

Round-11 handoff item 3.  The recorded tension: *the 60 s mini-bench cap
anti-correlates with elimination amplitude five independent ways
(indexed schedule −20 cells, scaled clock −24, combo −15, live occ-gate,
one-sided −8) while the aggregate-conflicts direction favors every
amplitude arm (0.968–0.974 geomean)* — so which metric should gate
defaults, the standing 60 s screen or a 120/300 s standard?

## The re-analysis (stored cells only — run-once rule)

Every recorded "conflicts geomean" was computed over **both-decided
cells**: cells where one arm timed out at the cap contribute nothing.
The arms' 60 s losses are timeout cells by definition — the aggregate
excludes exactly the cells the cap metric counts.  Recomputed from
`precompile/<sha>/benchmark/runs/sc24f` (joined on file × seed vs
default `107b7868`), with a censoring-aware score: per-cell
`ln(arm/def)` on both-solved cells, `±L` when exactly one side solved
(win/loss), `0` on both-timeout, mean over all cells, L-sensitivity at
ln 3 / ln 10 / ln 30.  Negative = arm cheaper.

| arm | solved cells | recorded gm (recomputed) | decided-by-one cells | censored mean log-ratio |
|---|---|---|---|---|
| indexed (`281de4c0`, 261 joined) | 220 → 200 | 1.032 | 3 arm-wins / **23 arm-losses** | **+0.108 / +0.201 / +0.285 — costlier at every L** |
| scaled (`93703871`, 270 joined) | 229 → 205 | **0.978** | 6 / **30** | **+0.082 / +0.189 / +0.286 — costlier at every L** |
| combo (`06011ff4`, 270 joined) | 229 → 214 | 1.042 | 6 / **21** | **+0.093 / +0.159 / +0.220 — costlier at every L** |

(The recomputed gms differ from the studies' 1.049/0.968/1.061 only by
join subsets; direction and conclusion are identical.  The one-sided
arm's cells were never filed — the bogus-tag trap — but its 0.974 has
the same structure: its −8 cap losses are timeout exclusions, so its
censored direction is costlier a fortiori.)

**Every amplitude arm is costlier under fair aggregation — including
scaled, the only one whose both-decided geomean looked favorable.**
The "five independent ways the cap anti-correlates with amplitude"
dissolves into one consistent finding: the cap metric was measuring
real cost (default solves mdp-28-14 s2 in 1.6 s where the scaled arm
burns the full 60 s; 23–30 such cells per arm against 3–6 arm-wins)
that the both-decided geomean is structurally blind to.  The wide-cap
re-runs agree rather than contradict: the 9-file 300 s check
(2026-09-13 widecap study) shows the 60 s losses partly convert
(genuine cap artifacts exist) but **no arm recovers** — cell-equal
everywhere with mostly worse conflicts, and the Timetable
carried-state collapse (see
`2026-09-14-amplitude-trajectory-answer.md`) is invisible to *any*
conflicts metric that excludes timeouts.

## The decision

1. **The 60 s solved-cells gate stays the primary acceptance metric
   for default-config changes.**  Its verdicts agree with 300 s re-runs
   and with censoring-aware aggregation; nothing in the five-way
   "anti-correlation" survives as evidence against it.
2. **The both-decided conflicts geomean is retired as an
   "the aggregate favors X" claim.**  It may be reported only with its
   exclusion accounting (decided-by-one wins/losses).  Its replacement
   is the censored mean log-ratio with L-sensitivity —
   `docs/studies/assets/amp-traj-2026-09-14/sc24f_censored_reanalysis.py`
   is the reference implementation over the store.
3. **300 s wide-cap re-runs are the tie-breaker for borderline cells,
   not a standing gate.**  They convert cap artifacts (the widecap
   study's 12/13 finding) at 5× the cost of a 60 s cell; use them when
   a candidate's losses concentrate in near-cap cells, per the widecap
   protocol.
4. A structural note for any future metric: killed processes print no
   counters (conflicts −1 in the store), so cap-time cost signals must
   be verdict-based — solved cells is exactly that.

With this, the round-11 handoff's three items are all closed: the CSR
dual-write scan landed (`0e005231`), the amplitude→trajectory question
answered (carried-phase-state collapse), and the metric question
settled (keep the cap, fix the aggregate, wide-cap as tie-breaker).
