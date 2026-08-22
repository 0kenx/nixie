# 8-byte watcher (kissat density): pre-registration (2026-08-22)

Follow-up to [`2026-08-flat-watch-arena.md`](2026-08-flat-watch-arena.md),
whose Gate-2 failure pointed at watcher **density** as the dominant term:
our `Watcher` is 12 bytes (clause id + arena slot + blocker) and kissat's
watch granularity is 4–8 bytes.  The flat-arena study pre-named this
experiment.

## What

Shrink `Watcher` to 8 bytes — `{ clause: ClauseId, blocker: Lit }` — in the
**existing per-list layout** (`Vec<Vec<Watcher>>`, reverted arena).  The
arena slot is no longer carried; the (rare) visit that needs the clause
literals resolves `ClauseRef` through the existing `refs` table
(`ClauseDatabase::ref_of`), i.e. the pre-direct-addressing indirection.

Rationale: the documented blocker-hit rate is ~55%+, and a blocker hit
touches only the watcher bytes — for that majority, scan cost is pure
watcher-list density (8B → 1.5× more watchers per cache line vs 12B).  The
`refs` indirection is paid only on non-blocker-hit visits.  Adding a
clause-id field to the clause header instead (to keep direct slot
addressing) would grow the pinned 12-byte header and break the 5-literal
32-byte slot property globally — rejected.

## Change class

Path-preserving data-layout refactor.  The null is trajectory identity
itself (as in the arena study): any counter divergence means the refactor
is semantically wrong, regardless of speed.

## Go / no-go (pre-registered)

* **Gate 1 — trajectory identity**: 94-file corpus (40× uf100, 54×
  satcomp2024), `PRESET=cadical`, default seed: decisions / propagations /
  conflicts / restarts / learnt and the verdict identical to the baseline
  binary on every comparable file.  A file that solves in one arm and
  times out in the other is re-run at a longer cap to confirm identical
  counters (faster/slower is fine; *different* is not).
* **Gate 2 — instructions-to-verdict**: symmetric both-solve selection at a
  12 s cap, geomean(base/8B) over ≥50 cells must be **≥ 1.02**.  Below →
  revert and record (the direct-addressing `r` field keeps its measured
  win).
* Metric: PMU `cpu_core/instructions`, serial pinned to one core, harness
  kills the **whole process group** on timeout (three orphan incidents
  this session; `subprocess.run(timeout=…)` only reaps the direct child
  `perf`, leaving `cnf_solve` grandchildren running).
* Soundness: full `oxiz-sat` suite + workspace suite; `diff_equiv` 200k
  iterations (watcher construction is shared with the BVE/ELS stack).

## Results

**Verdict: REVERTED — Gate 2 failed at 1.0068** (threshold ≥ 1.02), with
Gate 1 clean (0 diffs, 0 unresolved: every comparable trajectory
bit-identical in counters and verdict).

The shape of the result is the information: **70/72 cells faster, none
significantly slower, geomean only +0.7%**.  A near-uniform small gain is
the signature of a real-but-minor effect — watcher-list density is NOT
where the remaining propagate cost lives.  Combined with the flat-arena
result (−4.5% for strictly more machinery), this maps the BCP hot loop:
the blocker-hit majority already touches so few lines that 12→8 bytes buys
~1%, and the visits that do dereference clauses are bounded by the clause
arena and trail-value loads, not by the watcher entry.  kissat's 4-byte
watch granularity would compound the same ~1%-class effect — not worth a
port.

Disposition: code reverted (worktree deleted); the direct-addressing
`r` field keeps its place.  The `refs`-indirection concern that motivated
carrying the slot is now *measured*: removing it costs nothing measurable,
but keeping it costs nothing either — layout stays as-is on the pre-change
side of a sub-threshold effect.

Item-2 sub-item also closed by reasoning: conflict-analysis scratch
pooling (`minimize_literal_plain` / shrink reason collection) allocates
`SmallVec<[Lit; 8]>` — inline storage, no heap alloc for the ≤8-literal
reasons that dominate; pooling would churn for no measurable win.

The two watcher experiments together close the "path-preserving constant
factors" thread on the propagate side: remaining item-2-class levers are
the clause-arena layout itself (header density, slot packing) and the
trail-value load path (blocked by `#![deny(unsafe_code)]` on the raw
pointer cache — would need a documented exception decision, not a
shortcut).

Harness note: this study's `gates.py` kills the whole process group on
timeout (`start_new_session` + `killpg`); zero orphan incidents, unlike
the three that preceded it.
