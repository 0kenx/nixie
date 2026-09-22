# The unified wide driver reverted — the mis-attribution corrected, the preserve pair and the cadence kept

**Date:** 2026-09-22 (third session).  **Entry:** the CAV audit
(`2026-09-22-cav-regression-attribution.md`) + its piece-level bisect
(S1 innocent / S2 owns the damage), and this session's completion of
that matrix.  **Tree:** `1cccf71b` + this landing.

## The correction this study owns

The unified-driver campaign
(`2026-09-22-simplex-unified-feasibility-driver.md`) measured its
"4 z3-validated recoveries" against a STALE BASE (`ef572fc1`, the
session's entry tip) while main raced four times underneath it.  The
parallel session's integer-tableau landings (`c5e8026a`…`795abb8f`)
had ALREADY recovered every one of those members on the pre-driver
tree.  Measured now, back-to-back, calm:

| member | `7687dc39` (pre-driver, cached binary) | + preserve (S1) | driver `2a7dc324` | + cadence `9a114017` | **this revert** |
|---|---|---|---|---|---|
| i129 / i144 / i492 / i361 | sat | sat | sat | sat | **sat (9–32 ms)** |
| i202 | sat | sat | timeout | sat (11 s) | **sat (12 ms)** |
| i445 | sat | sat | timeout | unknown (7 s) | **sat (7.5 ms)** |
| CAV 011 | sat ≤27 s | sat 13.9 s | no verdict @120 s | no verdict @60 s | **sat 12.4 s** |
| CAV 025 | sat ≤20 s | sat 23.0 s | TO @60 s | sat 17.0 s | **sat 22.5 s** |
| CAV 034 | sat ≤7 s | sat 5.1 s | TO @60 s | TO @60 s | **sat 4.7 s** |
| CAV 026 (control) | sat | sat | sat | sat | **sat 0.6 s** |

The driver did not recover the survey family — the tableau work did —
and the driver REGRESSED `i202`/`i445` (sat → timeout/unknown) and the
CAV cells (the audit's S2 finding, confirmed here on every cell).  The
cadence landing's own i202 "recovery" was re-fixing what the driver
broke.  (The cadence landing's COST win is real and survives the
revert — below.)

## What this landing changes

`simplex/mod.rs` (+132/−108): the three driver pieces are REVERTED to
the pre-driver shapes, verbatim from `7687dc39` —

* `find_violating` narrows again (the wide-store scan is gone);
* `make_feasible`'s wide-leaving branch and its no-column
  refutation-or-decline arm are gone (the historical
  `explain_conflict` arm restored);
* `check`'s interleaved one-wide-repair-then-re-feasibilization loop is
  restored (with its `MAX_WIDE_REPAIRS` budget and the exact-violated-
  side read).

KEPT (both measured valuable independent of the driver):

* **The preserve pair** (`nonbasic_rests_at_bound` + the two `continue`
  guards in `crash_basis`/`update_assignment`): S1 proved it innocent
  on CAV; the `rederivation_preserves_*` pins hold; and the position
  contract is Z3's.
* **The request cadence** (`LIA_REQUEST_NODES = 64`): the walk-vs-
  request dose was re-measured ON THE REVERTED ARCHITECTURE —
  walk@20k: 231s corpus / 32 >1s / 13 timeouts vs **request@64: 80s /
  11 / 3**.  The ray-walk class exists on the old driver too (it is
  what the ORIGINAL survey family decayed into before the tableau
  landings); the cadence win is architectural, not driver-specific.

## Measured (the battery)

* Suite: 12,142 run, **12,138 passed, 0 failed** (the three
  `known_unsound` corpus cells pass again on this tree — the driver's
  trajectory had been their state too), 4 scope_rebase timeouts = the
  documented load-artifact class (9/9 pass isolated).
* clippy/fmt/rustdoc clean.  Parity **176/177 Correct, 0 wrong**
  (z3 4.16.0).  Perf gate PASS (counters 1.000/1.000).  Differentials
  clean (mixed 20262750, wide 20262752).
* 10-seed corpus distribution (20263000–09 × 600): median seed 43.3s
  (21–69), 13 timeouts — vs the driver+cadence tree's 36.7s (20–73),
  15: overlapping ranges (the 3-seed "+30%" was noise), and the
  decisive surfaces (CAV, members) are verdict differences, not
  preferences.
* Surveys: fixed 3 members (i284, i123, i428 — all the conflict-limit
  class), fresh 2 members (i161 conflict-limit, i551 J5-`Undecided`).
  The residual map is unchanged in kind: **conflict-limit (dominant) +
  J5**.
* Named members: i142 sat, i116 sat, i129 sat, i393 sat, i504 sat,
  i566 sat — all z3-agreeing.

## The regeneration trap (recorded for every future survey)

A member-regeneration script that iterates a seed LIST must contain
every seed of every (seed, index) pair it writes — a missing seed
leaves a STALE file at the target name and the run reports a phantom
verdict flip (this session's five-minute false-`unsat` scare: the
"i566 unsat" was a stale file from an earlier script; the true
(20261001, 566) regenerates `sat`/`sat`).  Always md5-verify a
regenerated member against a fresh single-seed generation before
believing a verdict change.

## Where this leaves the arc

* The simplex family (the original campaign target): solved by the
  tableau landings + the cadence; the driver is gone; the preserve
  contract and the pins remain as its sound residue.
* The residual map: the conflict-limit class and the J5-`Undecided`
  certificate class — both search-level, both with recorded
  instruments.

The one-sentence version: **the driver's recoveries were the tableau
session's, measured against a stale base — the piece-level bisect
pointed at the driver, the member matrix confirmed it regressed more
than it fixed, and the revert (keeping the innocent preserve pair and
the architectural cadence win) restores every cell to its best
recorded state.**
