# Handoff: the simplex family retired — the unified feasibility driver landed; the residual map is search-level (2026-09-22)

**Read `AGENTS.md` first — it is canonical.**  This handoff executes
`docs/handovers/2026-09-21-arithmetic-arc-simplex-family-handoff.md`'s
open item 1 to completion.  The campaign's full record — classification,
the three-layer root cause, the fix, the measurements — is
`docs/studies/2026-09-22-simplex-unified-feasibility-driver.md` (the
study wins where they disagree).

## What landed (`2a7dc324`, binary at `precompile/2a7dc324/nixie`)

The simplex pivot-cap / resource-limit family is **retired**: zero
`smx-rl` attributions remain anywhere in the survey.

* **One feasibility driver** over both stores: `find_violating` scans
  the wide rows too (the same smallest-index leaving rule — Z3's
  `one_iteration_tableau_rows` shape); `make_feasible` pivots wide
  leaving basics through the exact entering rule, with the interval
  refutation (Farkas) or the honest decline on the no-column arm;
  `check`'s classification keeps refutation/undecidable only.
* **Position preservation**: `crash_basis` AND `update_assignment`
  (the layer-3 site, one call deeper) keep nonbasics already resting at
  a current bound.  The historical lower-preferred re-snaps silently
  relocated every repair parked at an upper bound — the period-1 and
  period-2 limit cycles of the stall class.
* **Recovered (models z3-validated by binding+negation, ledger empty):**
  i129 (0.36s), i144, i492 (the pivot-cap class, instant), i361.
  Aggregate fixed-seed corpus cost **−21%** (262s → 206s), timeouts
  18 → 11, median unchanged; p90 28→46ms (the exact wide-row scan per
  driver iteration — recorded, accepted).
* Battery: suite 15 failures = the documented pre-existing class
  (verified identical on clean); clippy/fmt/rustdoc clean (main's
  Phase-3 test shipped clippy-dirty — its unused `skipped` is now
  reported in the mass assertion, a mechanical fix); parity 176/177
  Correct **0 wrong** (z3 4.16.0); perf gate PASS (1.000/1.000);
  3×400 mixed + 3×300 wide differentials clean.

## The residual map (in priority order)

1. **`i202` / `i445` (timeout class, fresh seeds):** the simplex no
   longer cycles, but the SEARCH thrashes — decoded on i445: a 3-phase
   rotation (`13↔8`, `0↔13`, `8↔0`) at the CHECK level across B&B dive
   nodes (~18k one-pivot `make_feasible` calls, 25+ branch requests,
   node budget burned repeatedly).  Item 89's dive-leaf/branch-channel
   territory: the dive's per-node bound pushes recreate the same
   violated slack each round.
2. **`i133` / `i285` / `i566` (conflict-limit class):** all attribute
   to `check_core_solving`'s "a real theory conflict was dropped at the
   conflict limit" arm — the search-capacity tail, reshuffled in by the
   trajectory change (as every landing reshuffles; the wrong-verdict
   ledger stayed empty).
3. **`i551`:** the J5-`Undecided` class (the certificate declines
   without refuting — not block-and-retried).  The predecessor
   handoff's open item 2, unchanged.

## Survey state (measure before believing)

Fixed seeds 20261000–02 × 600: **1 member** (i129 recovered; the
reshuffled `i285`, conflict-limit).  Fresh seeds 20262600–02 × 600:
**3 members** (i133/i566 conflict-limit, i551 J5) + the timeout tail
(8 fresh / 12 fixed — i202/i445 migrated here from unknown-members).

## The instrument set (recipes in the study's closing section)

The probe inserter (auto `fn:line` tags at Unknown returns and
`resource_limit` writes), the write-site trace (`assignment[x]`/
`wide_points` mutations for a cycling pair — the tool that found
layer 3), the `[[MF-CALL]]`/per-pivot trace, the corrected model
validator (the `(model` wrapper must be included; assert bodies are
already balanced — do not re-parenthesize), and the corpus-timing
script (the theory-path cost gate the perf gate does not cover).

## Traps that fired this session (do not repeat)

* **Stash-pop silently drops a parallel session's hunks.**  Rebasing
  over the integer-tableau landings, the stash 3-way merge resolved
  tests.rs to MY version — wiping Phase 3's 55 lines of pins.  Caught
  by diffing against main (`+117` only, no deletions).  After ANY
  raced rebase: `git diff <main> --stat` must show ONLY your hunks.
* **A parallel session's clippy-dirty landing rides your gate.**
  Verify clippy failures on clean main before owning them.
* **Backgrounded output redirects are unreliable in this harness**
  (surveys/parity logs vanished; a `pkill -f` pattern matched its own
  command line and killed the cleanup mid-chain).  Run long jobs in
  the foreground, or check the log file exists before `wait`ing.
* **/media/data AND / can both hit 100%**: the two cargo targets
  (127G + 100G) filled the root disk mid-battery.  Keep exactly one
  target dir, on the disk with room, and `rm -rf` it the moment the
  battery ends (binaries live in `precompile/`, never `/tmp`).
* The `p90` cost of the unified driver is real (28→46ms) — the wide
  scan evaluates exact rows per iteration.  If a future campaign
  needs the tail back, the fix direction is incremental wide-row
  violation caching keyed on `rows_ver`, NOT re-splitting the driver.

## For the parse-arc / FSM session (your tree)

Your primary-tree edits (the FSM module, user_propagation, graph
tests — mid-flight when I landed) are preserved **verbatim** on the
branch `parse-arc-wip-snapshot` (commit `e0bfaf7d`, nothing
discarded, never stashed).  The primary checkout is sitting on that
branch with your files in place.  Rebase onto `main` (`2a7dc324` or
later) at your leisure; my landing does not touch your files (the
simplex driver + tests only, plus one test-file assertion message).

The one-sentence version: **the simplex family was three stacked
value-continuity breaks — a split driver and two re-snap loops, the
second hiding one call inside `crash_basis` — and one unified driver
plus a position-preservation rule retires the class outright, with
every recovery z3-validated, the ledger empty, and the residual map
now pointing entirely at the search layer.**
