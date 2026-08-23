# Flat watch arena (kissat parity): pre-registration + results (2026-08-22)

## Change class

**Path-preserving data-structure refactor**, not a heuristic change. No
search-policy input changes, no schedule changes. The equivalent of a
matched null here is *trajectory identity itself* (below); if trajectories
diverge, the refactor changed semantics and is invalid regardless of speed.

## What

Replace `WatchLists { watches: Vec<Vec<Watcher>> }` with kissat's scheme
(`../temp/kissat/src/watch.h`, `vector.{h,c}`, `proplit.h`):

* one flat `pool: Vec<Watcher>` arena;
* per-literal-code spans `{start, len, cap}` — contiguous, geometric slack;
* propagation scans its own span by index with two-pointer in-place
  compaction (never moves the span);
* **cross-list pushes during a scan are buffered in a `delayed` queue and
  flushed after the span is closed** (kissat `kissat_delay_watching_large` /
  `kissat_watch_large_delayed` in `proplit.h`) — this is the property that
  makes arena shifts safe mid-scan, ported verbatim;
* periodic defrag compacts accumulated span slack (kissat
  `vectors.usable` + defrag).

Expected effect: removes per-list allocator traffic (push growth) and
per-Vec heap headers; improves pool locality. Claimed 5–7% from earlier
profiles (propagate-dominated files).

## Go / no-go (pre-registered BEFORE running)

* **Gate 1 (correctness of the refactor): trajectory identity.** On the full
  94-file corpus (40× uf100, 54× satcomp2024) with `PRESET=cadical`, default
  seed: decisions, propagations, conflicts, restarts, learned counts and the
  verdict must be **identical** to the pre-change binary on every file.
  Divergence anywhere = the visit order changed = fix before proceeding.
* **Gate 2 (the point of the work): instructions-to-verdict.** Geomean over
  the both-solve corpus files must improve by **≥ 2%**. Below that the
  added structural complexity is not justified → revert, record as negative.
* Metric: PMU `cpu_core/instructions` (deterministic, load-independent,
  covers all work the change affects — it is a whole-process counter).
* Record every run into the result store (`benchstore.py record`), cells
  content-addressed by config flags; never re-run a stored cell.
* Soundness: full workspace suite + clippy/fmt/doc; fuzz `diff_equiv`
  200k iterations (watch invariants under BVE/ELS stack); the SAT core has
  no verdict path outside the corpus check (SAT-only change).

## Results

**Verdict: REVERTED — Gate 2 failed** (0.9554–0.9647, i.e. the arena is
4–4.5% *slower*; pre-registered threshold was >= 1.02). Gate 1 passed: the
final port is behaviour-identical (75/75 comparable trajectories
bit-identical in decisions/propagations/conflicts/restarts/learnt; the 76th
file, `64_25.sanitized`, was baseline-timeout at the 30 s cap and solved
with *identical* counters at 31.8 s — faster, not divergent).

### The defect chain the hang exposed (8 layers, all fixed, all worth keeping in the record for any retry)

The first port livelocked `si2-b03m` at 100% `__memmove` (perf profile,
symbolized build). Following the chain downward, in symptom order:

1. **Phantom slack**: the fast-path `add` (write into reservation) never
   decremented `slack`, so defrag fired constantly.
2. **Defrag collapsed spans**: the rebuild set `cap = len`, making the very
   next add to every distinct span a middle-growth shift → quadratic churn
   (shuffling-2: no progress in 60 s, baseline solved in 0.9 s).
3. **Middle-growth insert loop**: reserving `grow` slots via `grow`
   separate `Vec::insert` calls paid `grow` full-pool memmoves; fixed to
   one resize + one `copy_within`… which then panicked: `copy_within(from..,
   to)` expands the source range to the *post-resize* length — must bound
   at the pre-resize tail (`from..old_len`).
4. **The real structural fix** (kissat `kissat_enlarge_vector`, which the
   first port under-read): a full span is **relocated to the arena tail**
   with doubled capacity; the old region becomes dead space; *no other
   span's data or `start` changes*; O(cap) copy, never O(pool).
5. **Dead-space accounting**: the exact delta from the invariant
   `slack = pool - live` is `new_cap - 1` per relocation. Adding `+len` for
   the moved old slots *overcounts* and underflows `pool.len() - slack`
   (lucky_random fuzz caught it). The earlier "pool ballooning" symptom was
   actually bug 6, not missing `+len`.
6. **Unpadded rebuild**: rebuilding with `cap = 2*len` headroom without
   padding the pool to each reserved extent left `start+cap > pool.len()`
   → OOB panic on the first post-defrag fast-path write. Every span's
   reserved extent must lie inside the pool.
7. **Sticky threshold**: a pool-fraction defrag threshold can be *permanently*
   exceeded by tiny-span headroom (slack == live after every rebuild), giving
   defrag-per-add thrash. The non-sticky form is dead-vs-live
   (`slack <= 2*live + 64`), which the rebuild itself restores.
8. **Scan indirection**: `slot()`/`set_slot()` method calls with unprovable
   bounds in the hot loop cost ~4% (0.9647 → recovered by taking the whole
   pool out for the scan, the arena analogue of the old per-list
   `mem::take`); even with that fix the arena measured 0.9554.

### Why it is slower (hypothesis, for the next attempt)

Our `Watcher` is 12 bytes (id + arena slot + blocker); kissat's is 8 (a
31-bit ref + blocking lit in two 4-byte words — no stable clause id at
all). The flat arena makes every cache line cover fewer *distinct-literal*
watchers than the per-list layout did for a single scan, so the locality
win from removing allocator traffic is eaten by density. The retry that
could actually pay: shrink the watcher to 8 bytes (drop the id from the
hot struct, recover it via the slot's clause header only when a reason is
needed) — a different, pre-registrable experiment.

### Measurement lessons (third orphan incident)

- The outer `timeout` on a *python harness* orphans the solver children
  (their `start_new_session` survives the parent's death). Third incident
  this session; load hit 75 again. Any harness must install a SIGTERM trap
  that kills its process group.
- `perf stat` under 8-way parallel *without* per-job CPU pinning produces
  `<not counted>` PMU cells — pin each job to a distinct core, and retry
  failed cells serially pinned.
- Wall-caps under external load corrupt "solved/TO" splits; the final
  Gate-2 used a 12 s symmetric cap with both-solve cell selection, which
  is selection-on-speed, not on outcome (valid for a geomean of
  instructions-to-verdict).

### Disposition

Code reverted on main (the worktree branch is deleted); this study is the
artifact. Precompile entries for the touched commits retained.

## Erratum (2026-08-23): classification under the ±5% neutrality band

`docs/BENCHMARKING.md` §3 now defines a ±5% neutrality band for geomean
effects.  The measured 0.9554–0.9647 (−3.5 to −4.5%) falls **inside** it:
this study's Arena result is therefore **neutral**, not "4.5% slower" as
the prose above says.  The verdict is unchanged — the pre-registered bar
was ≥ 1.02× and was not met — but under the band rule the correct wording
is "neutral, below the pre-registered bar".  The 8-bug defect chain and
the density hypothesis remain the study's content.