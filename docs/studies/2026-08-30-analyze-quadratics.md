# Conflict-analysis quadratics: the worker-class per-conflict cost was a sort, not the search

Date: 2026-08-30. Trigger: fresh standing table (54-file satcomp2024 extract,
serial-quiet oxiz 43 vs cadical 48, 0 mismatches) decomposed the 9 one-sided
losses into conflicts-to-model vs per-conflict instruction cost at a fixed
conflict cap, pinned to the `cpu_core` PMU (this box is hybrid; bare
`-e instructions` reads the atom PMU first and yields garbage lines).

## The decomposition (both solvers, cap 40 000 conflicts)

| file | oxiz instr/conflict | cadical instr/conflict | ratio |
|---|---|---|---|
| worker_550 | **18.2 M** | 1.81 M | **10.1×** |
| timetable | 3.18 M | 2.38 M | 1.34 |
| g2-slp | 1.72 M | 0.79 M | 2.18 |
| summle53 | 1.21 M | 0.95 M | 1.27 |
| summle11 | 1.15 M | 0.82 M | 1.39 |
| circuit | 0.57 M | 0.30 M | 1.87 |
| rbsat | 0.26 M | 0.17 M | 1.48 |
| mdp-28 | 0.25 M | 0.23 M | 1.06 |
| crypto1 | 0.17 M | 0.15 M | 1.15 |

(An earlier reading of "5.5× on summle" was a measurement artifact: cadical
solves several files *below* the cap, so its total instructions covered a full
solve, not the cap. Cap below every solve point before dividing.)

worker_550 is the outlier: 10× per-conflict cost at equal search shape.
Its counters explain why the clauses are giant: `avg_lbd = 543`,
810 shrunken literals per conflict — and cadical on the same file *also*
learns ~2 677-literal clauses (13.36 M learned literals / 4 989 clauses),
so the giant-clause regime is legitimate, not a divergence.

## Root cause 1 (the big one): quadratic insertion sort of the bump set

Stack-walk profile (no-LTO symbols build — the LTO blob attributes 82.8 %
to `solve_with_theory`, a phantom; the real split): **75.8 % of all
instructions in `analyze`**, dominated by an element-shifting loop.

`analyze` sorts the per-conflict VMTF bump set
(`vars_to_bump` = every literal marked seen during the 1-UIP walk) with
`insertion_sort_by_key_stable`, justified by a comment promising "typically
≤ 40 analyzed variables". On worker-class conflicts the set is ~1 900
entries; the sweep is O(n²) ≈ 3.6 M element moves per conflict ≈ millions of
instructions — exactly the profile's hot loop.

CaDiCaL sorts the same array with `MSORT` (`radix.hpp`): `std::sort` below
`radixsortlim` (default 800), radix sort above. It never insertion-sorts a
large bump set.

**Fix**: hybrid — insertion sort up to `BUMP_SORT_INSERTION_LIMIT = 64`
(keeps the measured small-array win over driftsort), stable
`sort_by_key` (O(n log n)) above. Both branches are stable, so the output
order — and therefore the entire search trajectory — is bit-identical.

## Root cause 2: O(n·levels) LBD scan

`compute_lbd_from_literals` counted distinct levels with
`levels.contains(&level)` over a SmallVec: ~1 900 literals × 543 levels ≈
1 M comparisons per conflict (5.9 % of instructions on worker). The solver
already had a stamped O(n) form (`Solver::compute_lbd`, `lbd_mark`
generation counter) — but the analyze path used the quadratic free function
because it needs only `&Trail`.

**Fix**: `compute_lbd_stamped` sharing the `lbd_mark` stream, growing
`level_marks` on demand so a literal at decision level == num_vars is
counted, not skipped (the reference has no bound; neither does the new
path). A property test pins stamped ≡ reference over 200 randomized
trail/clause shapes, duplicates and repeated calls included.

The wraparound test caught a real latent defect: generation 0 collides with
virgin slots (`level_marks` initial zeros), undercounting LBD once per 2³²
analyses (heuristic-only impact). Both `compute_lbd_stamped` *and* the
pre-existing `Solver::compute_lbd` now reset the table on wrap. The old
`compute_lbd` would also have panicked in debug on u32 overflow.

## Root cause 3: per-reason literal snapshot

The 1-UIP walk copied every reason clause into a heap-allocating
`SmallVec<[Lit; 8]>` to work around a borrow conflict ("snapshot the
literals so the shared marking helper may take `&mut self`"). One allocation
plus a full literal copy per non-inline reason — linear, but ~30–60 allocs
and ~300 KB of copying per worker-class conflict.

**Fix**: `AnalysisMark` split-borrow bundle (`seen`, `trail`, `learnt`, the
three level tables) so the walk iterates the reason clause **in the arena**
with the immutable borrow held across the loop. The LRAT level-0 unit ids
are deferred to a post-loop flush (walk order preserved — nothing else
appends to `unit_chain` inside the loop).

## Verification

- **Trajectory identity**: bit-identical `conflicts/decisions/propagations/
  restarts` counters AND verdicts on 8 stratified instances (worker, noL,
  circuit_48, constraints_17, si2-b03m, frb65, Timetable, mdp-28) at a 60 k
  cap, pre-fix vs post-fix binaries. This is the matched null for a
  pure-perf change: the null is identity itself.
- **Instruction win** (`cpu_core/instructions`, same caps, same trajectories):

  | file | pre | post | ratio |
  |---|---|---|---|
  | worker_550 (40 k) | 729.7 G | 187.2 G | **3.90×** |
  | summle11 (40 k) | 45.9 G | 40.1 G | 1.15× |
  | summle53 (40 k) | 48.7 G | 43.5 G | 1.12× |
  | mdp-28 (40 k) | 9.8 G | 9.2 G | 1.07× |
  | timetable (40 k) | 127.3 G | 120.6 G | 1.06× |
  | noL (40 k) | 5.3 G | 5.1 G | 1.05× |
  | frb65 (40 k) | 11.0 G | 10.5 G | 1.05× |
  | circuit (40 k) | 7.7 G | 7.7 G | 1.00× |

- **Post-fix worker profile**: `analyze` 75.8 % → 1.9 %; the map is now
  balanced (shrink 13 %, parse 10 %, elim 7 %, propagate 2.8 %) — i.e. the
  analysis path is no longer the outlier; worker's remaining 2.6× vs
  cadical per-conflict lives in propagate/shrink over giant clauses plus
  the 10.3 M-clause DB.
- **End-to-end (serial, quiet-ish)**: worker_550 63.8 s → **42.5 s**
  (1.50×; the conflict-to-model count is unchanged — this instance is now
  throughput-bounded, not sort-bounded). j3037/FmlaEquiv/summle53 within
  noise (they are search-bound, not analysis-bound).
- **Gates**: workspace 10 415/10 415; clippy/fmt/doc clean; wisas xs_8_13
  canary `unsat` fast; z3 parity **169 correct / 1 inconclusive / 0 wrong**
  (Z3 4.16.0, not the 4.15.4 baseline — recorded, not directly comparable
  to older snapshots); differential **159 solved / 0 disagreements**
  (par2 2 325 under load; the wisas timeouts in the QF_UFLIA tail are the
  10 s cap under load-6+ conditions, canary itself solves in seconds).

## Standing table effect

None at the 40 s / 6-way cap beyond load noise: the losses are
conflicts-to-model-bound (the emergent search gap the deep study already
catalogued), and worker_550's 42.5 s sits at the cap boundary (flaps in
place of a 63.8 s certain TO — a strict improvement of the worst loss).
The durable artifact is ~4–15 % off every SAT search (5 % on noL-class,
11–15 % on summle-class, ~4× on worker-class) at identical trajectories,
plus the SMT-side CDCL(T) core which executes the same analyze path.

## Follow-ups recorded

- worker's residual 2.6× per-conflict vs cadical: propagate/shrink over
  ~1 900-literal clauses and the 10.3 M-clause watch lists. A watcher or
  arena-layout slice, same scale as the flat-watch-arena study.
- The 9 losses remain search-efficiency-bound; the conflict-count gap
  (4× on summle53, 100× on worker) is the standing deep-study item.
