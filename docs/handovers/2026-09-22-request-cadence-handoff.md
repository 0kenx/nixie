# Handoff: the request-cadence campaign — the ray-walk class dissolved (Z3's one-case-split shape, dosed and null-decomposed); the CAV 011/034 driver regression is the open item (2026-09-22, later session)

**Read `AGENTS.md` first — it is canonical.**  This executes the
predecessor handoff's residual item 1 (`i202`/`i445`) plus the CAV
audit's Route-A option.  Studies:
`docs/studies/2026-09-22-lia-request-cadence.md` (this campaign — the
study wins where they disagree) and
`docs/studies/2026-09-22-cav-regression-attribution.md` (the parallel
session's audit + piece-level bisect).

## What landed (`9a114017`, binary at `precompile/9a114017/nixie`)

**`LIA_REQUEST_NODES = 64`** — with the branch channel ARMED (the
default), the CDCL-visible branch request fires after a 64-node walk
instead of 20,000; the `NIXIE_LIA_BRANCH_LEMMA=0` opt-out keeps the
full walk.  One constant and one channel-gated budget check in
`bnb_search` (+30/−1 in `nixie-theories/src/arithmetic/solver.rs`).

* **The decode**: `i445`'s B&B burned 46,848 node bodies per 10s as a
  4,000-deep linear chain whose branch bounds WALK (`+1`/`+3` per node
  along an LP ray) — item 96's ray class, directly measured.  Z3's
  `branch_infeasible_int_var` is the reference shape: one case-split
  lemma per fractional vertex, exploration in CDCL.
* **The dose curve** (1/8/64/1024/20k): flat cost at ≤64 (61–63s vs
  200s on the fixed-seed corpus); `i202` recovers `sat` at ≤64 with a
  **z3-validated model**.
* **The matched null** (same cadence, branch point `k+7`): reproduces
  the ENTIRE −70% cost (the CADENCE) and recovers nothing (the CONTENT
  recovers `i202`).  Both mechanisms separately attributed.
* **10 fresh seeds × 600**: walk 77.5s median / 39 timeouts →
  request@64 36.7s / 15; every request seed beats the walk's best seed.
* **Also cured**: `i116`'s 23s trajectory reshuffle (0.71s), `i445`
  migrated from 30s timeouts to a 7s honest `unknown` (65 branch
  rounds), **CAV `problem__025` recovered** (sat 17s from TO@60s).
* Battery: suite 3 pre-existing failures (a subset of the documented
  class; the other twelve pass on this base from parallel sessions'
  landings); clippy/fmt/rustdoc clean; parity 176/177 Correct 0 wrong
  (z3 4.16.0); perf gate PASS (1.000/1.000, wall 0.88); differentials
  clean (mixed 20262730/20262740, wide 20262732).
* Named members: i142 sat 0.10s, i393 unsat, i504 sat, i566 sat, i116
  sat 0.71s, i129 sat 0.37s.

## The open items, in priority order

1. **CAV `problem__011` / `problem__034`** (the driver regression the
   piece-level bisect attributes to the unified wide-driver rewrite —
   S2; the preserve pair is innocent — S1).  Route-A (this landing)
   recovers only 025 of the three.  The remaining fix options (per the
   audit's addendum): restore the interleaved one-wide-repair-then-
   narrow-re-feasibilization shape for wide-heavy trajectories, or the
   dive-level landing that makes the internal trajectory difference
   stop deciding these cells.  **The calm-load LIA standing table is
   the prerequisite baseline** — run it before any fix lands.
2. **The conflict-limit class** (`check_core_solving`'s dropped-conflict
   arm): now the DOMINANT survey family (`i0`, `i133`, `i161`, `i258`,
   `i496`, `i445`).  Search capacity.
3. **`i551`:** the J5-`Undecided` certificate class (the arc's standing
   open item 2).

## Survey state at this landing

Fixed seeds: 2 members (`i0`, `i496` — conflict-limit), 1 timeout.
Fresh seeds: 5 members (`i133`, `i161`, `i258`, `i445` conflict-limit;
`i551` J5), 2 timeouts.  Zero `smx-rl`, zero ray-walk, zero
repair-orbit attributions anywhere.

## Traps this session (do not repeat)

* **Surveys must re-run after the default lands** — a survey launched
  against a pre-landing binary measures the old default (caught: the
  first fixed/fresh pair measured the 20k walk).
* **Backgrounded `nohup ... > log` launches fail intermittently in this
  harness** — verify the log file exists before `wait`ing; prefer
  foreground for one-shot long jobs.
* **The probe strip after attribution**: the auto-inserter's tags and
  the hand probes must all be gone before `git diff` is the landing —
  verify with `grep -c NIXIE_GAP_PROBE` = 0 in every touched file, and
  `cargo fmt --check` catches the leftovers.
* `git checkout -- <file>` can fail transiently with "unable to write"
  (the FS flicker) — re-run it and verify the byte count before
  continuing.

The one-sentence version: **the ray walk was the internal B&B
re-optimizing along an LP ray one integer at a time, and Z3's
one-case-split-per-vertex shape — dosed at 64 nodes, with the cost win
null-attributed to the cadence and the recovery to the branch content —
dissolves it, leaving the CAV 011/034 driver regression as the named
open item with its baseline prerequisite recorded.**
