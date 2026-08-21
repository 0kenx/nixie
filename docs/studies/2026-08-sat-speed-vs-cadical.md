# SAT-core speed vs CaDiCaL: constant-factor pass, and why the remaining gap is not constant-factor

Date: 2026-08-21. Trigger: the 94-file tracking suite (`/tmp` harness, 25 s cap)
showed oxiz up to **20.7× slower than CaDiCaL** on `6s167-opt.cnf`, 2–6× on
several structured instances, with a suite geomean of ~0.91.

## What was measured first (and what it said)

Instrumented run of `6s167-opt` (UNSAT, both solvers):

| metric | oxiz | cadical | ratio |
|---|---|---|---|
| conflicts | 170,039 | 16,654 | **10.2×** |
| propagations | 19.37 M | 2.31 M | 8.4× |
| props/conflict | 113.9 | 138.6 | ≈ equal |
| props/sec (wall) | 1.2–3.5 M | 6.3 M | ~2–5× |

Two independent multipliers: a per-propagation cost gap (~2–5×) *and* a
search-trajectory gap (10× more conflicts). Props/conflict being roughly equal
means the propagation machinery is not wasting work — the search just visits
far more of it. Any fix that only speeds up BCP scales the whole picture down
by a small constant; it cannot close a 10× conflict gap.

## Landed this pass (commit `2b55658`) — trajectory-preserving

All changes verified **bit-identical** conflict/decision/propagation counts
against clean-HEAD binaries on `6s167-opt`, `constraints_17_0.4_1`,
`crn_11_99_u`:

1. `Watcher` carries its clause's arena slot (`ClauseRef`) next to its id;
   BCP dereferences clauses directly instead of walking `refs[id]` (one
   dependent load saved per visited watcher). Slots are append-only
   (`memory.rs`), so slot and id stay bound to the same clause; deletion
   remains visible through the deleted flag.
2. Binary-implication edge lists scanned via take/put-back of the owned
   `Vec` (was: two bounds-checked loads per implication). Guarded by an
   `is_empty` probe (most literals have no binary edges). The conflict path
   restores the list before returning — losing it would silently drop every
   implication keyed under that literal. Thread-safety note: the solver is
   thread-local (portfolio workers each own one), so nothing here is shared.
3. Byte-level DIMACS token scanner replacing `lines()` + `str::parse::<i32>`
   per token. Semantics preserved exactly (line directives, CRLF, `+`
   literals, error text); regression tests added next to the parser.
4. One decorated stable insertion sort for the per-conflict VMTF bump order
   (identical output to `sort_by_key`; O(n) key reads).

Measured effect (perf counters, identical trajectories): cycles −4.8 %
(`6s167-opt`), −2.7 % (`constraints_17`), −0.9 % (`crn_11`); parse-dominated
files (uf100/simon families) 1.2–2.3× wall. Zero verdict changes across the
94-file suite; Z3 parity 168/168 correct (0 wrong, 1 Z3-Unknown inconclusive);
full workspace suite + clippy + fmt + doc clean.

### Negative results worth recording

* **The −34 %-cycles reading was a measurement artifact.** An intermediate
  perf-stat showed 29.2 B → 19.3 B cycles. Controlled rebuilds in throwaway
  worktrees reproduced only −4 %. The transient coincided with mixed
  stale/partially-rebuilt example binaries in the shared `target/`; do not
  chase it.
* **Undecorated insertion sorts are slower than std.** Replacing
  `sort_by_key` on trail-index orders with a plain insertion sweep made the
  key closure O(n²) bounds-checked lookups and *lost* to driftsort. Only the
  decorated (pre-extracted keys) variant won; the others were reverted.
* **SmallVec snapshotting of binary edges traded loads for memmove** and
  measured net-negative (+2.4 B instructions); take/put-back of the owned
  vector is the correct pattern.
* Tick accounting was deliberately left at 8 bytes/watcher although our
  watcher is now 12: ticks drive restart/mode-switch schedules, and the one
  time it was "corrected" mid-session the trajectory moved immediately
  (170 k → 131 k conflicts on `6s167-opt`). Correcting it is a heuristic
  change and needs the matched-null treatment below.

## Where the remaining 2–20× actually lives

The dominant term is the **conflict-count gap**, i.e. CDCL heuristics, not
constant factors. Candidate deltas vs CaDiCaL (`src/restart.cpp`,
`reduce.cpp`, `analyze.cpp`, `vivify.cpp`), in the order I would attack:

1. **Reduction schedule**: oxiz reduces every fixed 12 000 conflicts with
   fixed tier percentages; CaDiCaL schedules by *ticks*, starts far earlier,
   grows geometrically, and protects glue ≤ 2 / recently-used clauses via
   `used` flags rather than activity sorts.
2. **Mid-search vivification/OTFS cadence** — CaDiCaL re-vivifies learned
   clauses on a tick budget between reductions.
3. **Tick accounting correction** (above) once its trajectory effect can be
   attributed properly.
4. VSIDS/VMTF double-maintenance: oxiz bumps *both* structures every
   conflict; CaDiCaL bumps scores only in stable mode and the queue only in
   focused mode (`analyze.cpp: bump_variable`). Removing the dead structure's
   cost is also a trajectory change (stale scores after mode switches) and
   must be studied as such.

Every one of these alters the path the search takes, so per
`docs/BENCHMARKING.md` each ships with: ≥10 seeds per cell, a matched null
(same physical perturbation, semantics removed), replay at fresh seeds, and
tick counters rather than wall-clock — this box is shared and wall-clock
moved >30 % between consecutive runs of identical binaries during this
study. A pragmatic intermediate: since these changes are all *CaDiCaL-parity*
ports, differential-vs-CaDiCaL conflict counts on a fixed corpus give a much
more sensitive signal than time.

## Harness notes for whoever continues this

* Build stats harness: an example printing `conflicts/decisions/
  propagations` after `solve()` is the fastest way to check
  trajectory-preservation after any core edit (compare against recorded
  values above). It was used throughout but intentionally not committed;
  recreate from `Solver::stats()` if needed.
* `perf stat -e cycles,instructions` is load-independent on this machine;
  wall-clock is not (load average ranged 14–46 during this study).
* Worktree hygiene followed: baselines built in throwaway worktrees, only
  binaries copied out, worktrees deleted.
