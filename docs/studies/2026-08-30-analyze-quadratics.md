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

## Follow-up slice (same day): elimination-phase costs

g2-slp-synthesis (60 % of variables eliminable) profiles at **44.7 %
`eliminate_phase` + ~14 % malloc-family** — the remaining 2.1× per-conflict
excess vs cadical on that file is entirely elimination cost. Two fixes:

1. **`elim_resolve_clauses` arena iteration** — both antecedents were
   snapshot-copied into heap SmallVecs per resolution (the same borrow-
   checker-appeasement shape as `analyze`). Rewritten as a pure marking
   phase (immutable arena borrows only) + effect phase (deferred
   retire/shrink). En route this exposed and fixed a **mark-leak parity
   divergence**: the c-side satisfied-antecedent path returned without
   clearing `ctx.mark` (the d-side path and cadical's `unmark(c)` both
   clear); stale ±1 marks could misclassify shared literals in later
   resolutions.
   The first cut of this rewrite also introduced (and the
   trajectory-identity gate caught) a **wrong-UNSAT**: the
   "antecedent missing" breaks fell through to the size checks with a
   partial resolvent, fabricating `trivially_unsat` from an empty c-side
   on `circuit_48in64…seed1` (CaDiCaL: `sat`, model verified). Fixed with
   an explicit `missing` skip before any size logic. Lesson re-confirmed:
   every phase-restructure needs the counter-identity check against the
   pre-change binary *and* a verdict cross-check on any divergence.

2. **`elim_flush_sort_occs` decorated sort** — the occurrence-list sort
   (twice per scheduled variable per round) keyed on an arena lookup
   *inside the comparator*: O(n log n) dependent-load pointer chases per
   list. Keys are now pre-extracted (`(len, cid)` pairs, stable sort).
   Equal-size tie groups now keep occurrence-list order instead of
   driftsort's internal permutation — an arbitrary-tie reordering, so
   this slice's trajectories legitimately diverge; verified by verdicts
   instead of counter identity: 54-file corpus sweep vs cadical
   **0 mismatches**, **1 800 differential-CNF fuzz iterations 0
   mismatches** (stratified generator: 2/3/k-SAT families), workspace
   10 415/10 415, differential 160/0, parity 169/0/1, wisas canary
   `unsat` fast.

Cumulative instruction ratios vs the pre-study binary (fixed 40 k caps):

| file | pre | post | ratio |
|---|---|---|---|
| worker_550 | 729.7 G | 187.4 G | 3.89× |
| timetable | 127.3 G | 104.7 G | **1.22×** |
| g2-slp | 68.8 G | 63.6 G | 1.08× |
| mdp-28 | 9.8 G | 9.2 G | 1.07× |
| frb65 | 11.0 G | 10.3 G | 1.06× |

(One 3.5 %-of-total residual in `eliminate` is counter increments inside
the resolution loops — cadical pays the same per-resolution count. The
elim schedule itself — which variables, how often — is heuristic
territory and untouched here.)

## Negative result (same day): cadical `rsort` radix port — neutral, not landed

Ported cadical's `radix.hpp` `rsort` (stable byte-wise LSD radix with
constant-byte pass skipping and sortedness detection) and wired it into the
two per-conflict decorated sorts (bump-order timestamps; the shrink
`(level<<32|trail_index)` order via the order-reversing complement key),
switching above cadical's own `radixsortlim` (800). Keys are unique per
element at both call sites (VMTF stamps for bumped vars, trail indices for
literals), so the output order — and the trajectory — is bit-identical;
verified directly.

En route the small-branch comparison briefly sorted the complement key
with `Reverse`, silently *ascending* the original order — the
trajectory-identity gate flagged it instantly (every file diverged; worker
"got lucky" and solved). The corrected port measured:

| file | comparison sort | radix | ratio |
|---|---|---|---|
| worker_550 (40 k) | 187.2 G | 184.6 G | 1.015× |
| summle53/11, timetable, g2-slp, mdp-28 | — | — | ≈ 1.000× |

Bump sets exceed 800 elements only on giant-clause conflicts, which the
first slice already made rare. Well inside the ±5 % neutrality band →
**reverted, not landed** (the port lives in this study's history and in
cadical's `radix.hpp` if the clause-length gap is ever closed and the
bump sets grow again). The `Reverse(complement)` inversion is recorded as
the kind of off-by-one the identity gate exists to catch.

## Session close: standing table after the three landed slices

54-file table (40 s, 6-way, load ~4–6): **oxiz 43 / cadical 48, 0
mismatches, 5 ox-only wins** — headline unchanged (the losses are
conflicts-to-model-bound, as the deep study catalogue says), but the
composition moved exactly where a pure throughput win predicts:

- **summle_X4053 and summle_X11112 now solve under the cap** (were certain
  losses; serial 36.8 s → 35.7 s and capped-run instructions −12/15 %).
- **worker_550 solves serially in 42.5 s** (was 63.8 s) — sits at the
  cap edge and flaps under parallel load.
- `shuff`/`FmlaEqu`/`frb45` (34–39 s solves) flap with load margin, as
  they always have.

Per-conflict instruction state vs cadical after the three slices
(cap 40 k, `cpu_core` PMU): worker 4.7 M vs 1.8 M (was 18.2 M), timetable
2.6 M vs 2.4 M (was 3.2 M), g2-slp 1.6 M vs 0.8 M (was 1.7 M), summle
1.05 M vs 0.95 M, mdp/crypto at parity. The remaining excess concentrates
in (a) the shrink/minimize walk over giant clauses (worker: 34 % of
instructions), (b) elimination phases (g2-slp: 45 %), (c) propagate watch
layout — each a further data-structure slice, none a missing mechanism.

SMT-side paired check over the 270-instance differential sample:
geomean 1.007 (neutral — the sample is easy-instance-dominated; the
differential's 0-disagreement is the load-bearing gate there).

## Second follow-up slice: the elimination connect pass + a reverted take/put-back

Setup-subtracted search-cost ratios (instructions at cap 40 k minus
instructions at cap 1, both solvers) after the landed slices put five of
the nine standing losses at ≤ 1.23× (mdp 0.98, crypto 1.09, summle53
1.11, timetable 1.10, summle11 1.23) with worker 3.3×, circuit 2.2×,
g2-slp 2.1×, rbsat 1.4× left. The elimination-heavy outliers' profiles
pinpointed `elim_round`'s connect pass (a fresh `Vec` of all clause ids
per round + a heap SmallVec copy of every original clause's literals)
and the per-variable occurrence-list clones.

**Landed** (bit-identical trajectories on 6 instances incl. the fragile
`circuit_48in64…seed1`): the connect pass now defers retire/mark effects
to after the scan and iterates every clause's literals in the arena.
circuit_64in 1.094×, circuit_48 1.045×, timetable 1.027×, g2-slp 1.015×
instructions at fixed caps.

**Reverted with prejudice**: replacing the `ps`/`ns` occurrence clones in
`elim_resolvents_bounded` with take/put-back diverged circuit_48's
trajectory. Root cause: the clones are **load-bearing** — the pair loop
mutates the live lists underneath them (`elim_shrink_clause`'s
self-subsumption path `swap_remove`s the shrunken clause from the
dropped literal's occurrence list; with the lists taken the removal
no-ops and the restore reintroduces a stale entry — exactly the
false-SAT hazard class the swap_remove's comment documents). A warning
comment now guards the clone site. Third time this session the
trajectory-identity gate caught a wrong-direction change before landing;
the fourth candidate (radix) was caught by measurement instead.

Gates: workspace 10 415/10 415, clippy/fmt clean, differential 160/0
(par2 2 320), z3 parity 169/0/1, 800 differential-CNF fuzz iterations
0 mismatches, wisas canary `unsat` fast.

## Third follow-up slice: iterative `minimize_literal_plain`

The last snapshot-copy site in the conflict path (and the repo's
recursion-policy target): the recursive removable check copied every
node's reason clause into a heap SmallVec (`others`, filtered by value)
and burned a native frame per node (depth-capped at 100, so no overflow
risk – but the cap itself silently *weakened* minimization on deep
reason graphs, and the per-node allocation dominated its cost).

Rewritten as an explicit heap stack (`Frame { var, cid, cursor, depth,
failed }`) that re-reads literals from the arena on demand (the clause
set is not mutated during analysis, so this equals the recursive form's
per-node snapshot; a missing reason clause reads as "no children",
matching the old `unwrap_or_default`). The short-circuit is preserved
exactly: a child's `false` stops the parent's remaining children before
they are ever classified, and poisons it. The pre-children checks moved
to a shared `minimize_classify` (early exits mark nothing and record
nothing, as before; the depth-0 counter/Knuth gating is unchanged).

**Bit-identical trajectories on 8 instances** (worker, noL, summle53,
g2-slp, circuit_48 – the fragile one – si2-b03m, Timetable, j3037) at a
60 k cap, pre/post binaries.

| file | recursive | iterative | ratio |
|---|---|---|---|
| worker_550 (40 k) | 184.5 G | 172.2 G | **1.071×** |
| noL (40 k) | 5.15 G | 5.05 G | 1.019× |
| summle53 / timetable / g2-slp / circuit64 | — | — | ≈ 1.000× |

Gates: workspace 10 415/10 415, clippy/fmt/doc clean, differential
160/0 (par2 2 311), z3 parity 169/0/1, 1 200 differential-CNF fuzz
iterations 0 mismatches, wisas canary `unsat` fast.

## Session totals (2026-08-30, both continuation passes)

Cumulative instruction ratios vs the session-start binary (fixed 40 k
caps, `cpu_core` PMU; baselines recorded above): **worker_550 4.24×**
(729.7 G → 172.2 G), timetable 1.25×, summle53 1.16×, summle11 1.14×,
g2-slp 1.10×, circuit 1.09×, mdp-28 1.08×, noL 1.06×; five further
corpus files measured 1.00–1.05× in the per-slice tables. End-to-end:
worker_550 63.8 s → 42.5 s serial (now cap-edge), summle ×2 moved from
certain standing-losses to solving under the 40 s / 6-way cap.

Setup-subtracted search cost vs cadical is now: mdp 0.98×, crypto 1.09×,
summle53 1.11×, timetable 1.10× (parity class), rbsat 1.43×, g2-slp
2.07×, circuit 2.22×, worker 3.3× (was 10.1×). What remains in the
outliers, per profile: worker's shrink block-walk + pivot trail scans
over ~1 900-literal clauses; g2-slp/circuit's eliminate/subsume rounds
(occurrence-list churn — the `ps`/`ns` clones are now documented as
load-bearing); and the propagate watch layout (the named next
data-structure slice). None is a missing mechanism; all are constant
factors on files whose *losses* are conflicts-to-model-bound.

Final 54-file table (40 s, 6-way, load 3–16): oxiz 43 / cadical 49,
0 mismatches, 10 one-sided losses (summle ×2 solved; shuff / FmlaEqu /
frb45 flap at the cap edge with load as they always have).

Landed this session: `1d9de4d` (analyze quadratics), `b382263` (theory
walk arena iteration), `218355c` (elim resolution + decorated occs
sort), `2b1495e` (elim connect pass), `d4820fb` (iterative minimizer) —
plus three documented negative results / near-misses (rsort radix
neutral-reverted; missing-antecedent wrong-UNSAT caught pre-landing;
take/put-back stale-entry hazard caught and reverted with a warning at
the clone site).

## Fourth follow-up slice: occurrence-flush scratch reuse + cadical gate order

`elim_flush_sort_occs`'s decorated sort collected into a fresh
`Vec<(usize, ClauseId)>` per call — twice per scheduled variable, and
6.2 % of circuit-class instructions. Now collected into a round-scoped
scratch buffer on the `Eliminator` (trajectory-identical: pure
allocation reuse, verified bit-identical on 5 instances).

On top of it, the **gate order** now matches cadical's
`try_to_eliminate_variable`: the raw (uncompacted) occurrence-list
lengths gate `pos == 0 || neg == 0` and the occ-limit **before** any
flush+sort work (cadical reads `ps.size()`/`ns.size()` and rejects
before `elim_resolvents_are_bounded` flushes). The previous order
flushed+sorted both lists for every scheduled variable only to throw
the work away for the majority that fail these gates in later rounds.
Raw lengths only over-estimate live counts, so the occ-limit gate can
newly skip a variable whose compacted count would have fit – a
heuristic-order divergence (verified by verdicts: 54-file corpus sweep
0 mismatches, 1 000 differential-CNF fuzz iterations 0 mismatches, not
by trajectory identity).

**Deterministic effect**: the collect is gone by construction; circuit
files −3.6…−9 % instructions at fixed caps.

**Search effect (single-draw, multi-seed honest)**: Timetable now
solves at *every* completed seed (32.8 k–470 k conflicts; previously
never) and rbsat/g2-slp solve at the canonical seed. rbsat and
FmlaEquivChain swap wins/losses across seeds 0–3 (rbsat: NEW solves
seed0/PRE solves seed2; FmlaEqu: PRE solves seed0/NEW solves seed3) –
per-file chaos redistribution, not attributable merit. FmlaEqu at the
canonical seed regresses reproducibly (36.8 s → 62 s) and is recorded
as such. No aggregate solve-count claim is made from this.

Gates: workspace 10 415/10 415, clippy/fmt clean, differential 160/0
(par2 2 315), z3 parity 169/0/1, wisas canary `unsat` fast.

## Final session ledger (all continuation passes, 2026-08-30)

Landed: `1d9de4d` (analyze quadratics: bump-sort hybrid, stamped LBD,
arena reason iteration, LBD-wraparound fix), `b382263` (theory-walk
arena iteration), `218355c` (elim resolution arena iteration +
decorated occurrence sort + mark-leak parity fix), `2b1495e` (elim
connect pass arena iteration + load-bearing-clone warning),
`d4820fb` (iterative minimizer), `b8fdc0f` (flush scratch reuse +
cadical gate order).

Cumulative per-conflict instructions vs the session-start binary:
worker **4.27×**, timetable 1.24×, summle53 1.16×, circuit64 1.19×,
g2-slp 1.09×, mdp 1.08×, noL 1.06×. Serial solve flips: Timetable
never→always (multi-seed consistent), rbsat/g2-slp/summle ×2 at the
canonical seed, worker 63.8 s→42.5 s. Recorded regressions: FmlaEqu
36.8 s→62 s at the canonical seed (chaos-class, swaps across seeds).

Negative results / near-misses recorded for the next agent: rsort
radix (neutral, reverted); missing-antecedent wrong-UNSAT (caught by
identity gate, fixed pre-landing); take/put-back stale-entry hazard
(caught, reverted, clone site now warned); the `Reverse(complement)`
sort inversion (caught by identity gate).

Remaining after this session, in recorded priority: (1) the
conflicts-to-model gap on the standing losses (the deep multi-seed
study; every single-policy port remains null-beaten); (2) worker's
shrink block-walk (~26 % of its remaining profile) and the propagate
watch layout – constant-factor data-structure slices; (3) g2-slp's
eliminate/subsume residue (~2×, occurrence churn beyond the
load-bearing clones).

## Fifth follow-up slice: resolution scratch buffers (the 21.5 % push)

The call-graph under `eliminate_phase` on g2-slp finally attributed the
elimination excess: **`SmallVec::push` and its grow/spill path measured
21.5 % of the entire process** inside `elim_resolve_clauses` – the
per-resolution `marked` and `resolvent` SmallVecs spilled to the heap on
long-antecedent resolutions (g2-slp phase 1 alone runs **6.2 M
resolutions**; CaDiCaL's whole elimination takes **0.56 s / 1.79 %** on
the identical instance for the same 61 k eliminated variables – it
reuses member `clause`/`marked` vectors across every resolution).

Both buffers are now Eliminator-scoped scratch (`res_marked`,
`res_resolvent`), cleared per resolution, capacity retained across the
round; the single owned allocation left is the `Resolvent` outcome's
clone (only ~6 % of resolutions produce a non-tautological resolvent).
The unmark moved inline over the disjoint ctx fields (the shared helper
takes `&mut ctx` and cannot borrow the scratch).

**Bit-identical trajectories** on 6 instances (g2-slp, both circuits,
Timetable, constraints_17, j3037) vs the previous binary.

| file | before | after | ratio |
|---|---|---|---|
| g2-slp (40 k) | 63.1 G | 48.2 G | **1.311×** |
| timetable (40 k) | 102.3 G | 88.7 G | **1.154×** |
| worker / circuits / mdp | — | — | ≈ 1.000× |

Gates: workspace 10 415/10 415, clippy/fmt clean, differential 160/0
(par2 2 310), z3 parity 169/0/1, 800 differential-CNF fuzz iterations
0 mismatches, wisas canary `unsat` fast.

Session cumulative vs the start binary: worker 4.27×, timetable 1.43×,
g2-slp 1.43×, circuit64 1.19×, summle53 1.16×.

## Standing table at low load after all six slices

54-file table (40 s, 6-way, load 2.1): **oxiz 45 / cadical 49,
0 mismatches** – up from 43/48 at the same load at session start
(cadical's own count stable at 48–49 across the day). Losses reduced to
8: mdp-28 (45 s serial, cap-edge), j3037 (37 s), worker (43 s),
circuit_64in (deeper search gap), g2-slp (35.7 s serial – flaps under
parallel load), combined-crypto1, FmlaEqu (the recorded canonical-seed
regression), frb45 (cap-edge). Timetable, rbsat, summle ×2, shuffli and
x9-08075 now solve under the cap.

The throughput program has now taken every profiled outlier down to
either parity (mdp/crypto/summle/timetable-class) or structural work
(worker's shrink walk, circuit's propagate layout, g2-slp's remaining
resolution machinery). The standing losses that remain are
conflicts-to-model-bound – unchanged in kind from the deep study's
catalogue.

## Sixth follow-up slice: the watch rebuild's hidden collections

`rebuild_watches_and_binary_graph` (the eliminate/ELS/BVE epilogue,
rebuilt whole whenever a phase dirtied the database) collected every
clause id into a fresh `Vec` and copied every clause's literals into a
heap SmallVec before re-attaching – on worker's 10.3 M clauses that is a
~40 MB Vec plus 10.3 M copies per rebuild. Rewritten to iterate ids
directly and read each clause's first two literals in the arena through
split-borrowed fields (same shape as all the other arena-iteration
fixes; the debug-missing-ref assert is preserved).

Bit-identical trajectories on 6 instances. Instructions at fixed 40 k
caps: circuit_64in **1.090×**, circuit_48 1.037×, timetable 1.025×,
worker 1.016×, g2-slp 1.006×, constraints 1.003×.

Gates: workspace 10 415/10 415, clippy/fmt clean, differential 160/0
(par2 2 311), z3 parity 169/0/1, 800 differential-CNF fuzz iterations
0 mismatches, wisas canary `unsat` fast.

### Loss-file classification after all seven slices (setup-subtracted
### search cost vs cadical, cap 40 k)

mdp-28 0.97×, FmlaEqu 0.67×, crypto1 1.06×, j3037 1.07× (parity or
better – their losses are purely conflicts-to-model), frb45 1.36×,
g2-slp 1.55×, circuit64 1.79×, worker 2.98×. A counterfactual on
g2-slp is instructive: `--elim=false` costs cadical 13 % there but
costs us 2× – our bare search is the residual gap, and BVE rescues us
disproportionately; the resolvent bloat (323 k → 789 k originals) is
not the problem.

## Pass-3 close

Landed `cf12e5f` (watch-rebuild arena iteration). Standing table holds
at **45/49** (load 3.3; 7 losses this draw – mdp-28 flapped in, the
cap-edge files continue trading with load). Session cumulative
instructions vs the start binary at fixed caps: worker 4.34×, g2-slp
1.44×, timetable 1.47×, circuit64 1.30×, summle53 1.16×, mdp 1.08×,
noL 1.06×.

Eight code commits this session, every one gated on trajectory identity
(where semantics-preserving) or full verdict batteries (where
heuristic-ordered), with the workspace suite, clippy/fmt, the z3 parity
suite and the SMT differential clean at every landing, and ~7 000
differential-CNF fuzz iterations in total across the passes.

## Negative result: unshadowing zero-broken walks — the shadowing is protective

The session-opening mystery (a walk reaching `minimum == 0` on
`summle_X4053` at conflict 21 006 while the search ground on to 90 909)
root-caused to **stable-mode target-phase shadowing**: the walk writes
the completed assignment into the saved phases, but stable-mode
decisions read the target array (`target > 1 || (stable && target)`),
so the write-back is invisible for the ~70 % of conflicts spent in
stable mode. Trace evidence: walks completed at conflicts 21 006 and
55 010 in stable mode (shadowed, search continued); the 78 013 walk
landed in focused mode (target inactive) and the solve closed 12 k
conflicts later.

The obvious fix — on a zero-broken walk, copy the assignment into the
target/best arrays too (phases-only, no verdict claimed; the descent
still confirms) — was implemented and **rejected on multi-seed
evidence**:

| file (conflicts to verdict, pre → post) | s0 | s1 | s2 | s3 |
|---|---|---|---|---|
| summle53 | 90.9 k→124.1 k | 58.1 k→58.1 k | 59.7 k→86.8 k | 74.8 k→167.3 k |
| summle11 | 25.0 k→25.0 k | 91.9 k→91.9 k | 246.5 k→**131.1 k** | 168.9 k→168.9 k |
| worker / timetable / rbsat / mdp | identical (no walk0 ever fires) | | | |

summle53 is consistently **worse** at every diverging seed: the
zero-broken test is computed over the walk's slot set, which excludes
clauses containing fixed literals — a completed walk is a satisfying
assignment *of the slots only*, and following it as phases leads the
descent into regions that cost more than the accidental shadowing did.
One summle11 seed improved 1.9×; the aggregate is chaos-shaped with a
negative lean. Reverted per the matched-null discipline; the shadowing
stays, deliberately, with this study as the record.

**Kept**: the `stats.walk.minimum` monotonicity fix — the update's
`== 0 ||` disjunct let every later walk's worse minimum overwrite an
earlier completion, hiding walk0 events from the counter (this exact
misdirection cost an hour of diagnosis mid-study; the search never
reads the counter, so the fix is trajectory-neutral, verified).

## Negative result 2: the walk-objective stripping port (cadical parity) — knob-gated, default off

The shadowing study's root cause pointed one level deeper: cadical
garbage-collects fixed variables before every walk with new fixed
vars, flushing them from all clauses, so its walk objective covers the
**full residual clause set** and a zero-broken completion is a true
residual model. Our port excluded fixed-literal clauses from the
objective instead, so walk0 completions satisfied only the fixed-free
subset — which is exactly why following them (the unshadowing
experiment) hurt.

The faithful port (strip fixed-false literals from participating
clauses, keep permanently-satisfied ones out, single-flippable-literal
clauses now visible to the objective) works as designed — summle53's
canonical-seed solve improves 90 909 → 56 438 conflicts, walk0 now a
genuine residual model — but the multi-seed verdict is chaos-shaped:

| file (conflicts, pre → post) | s0 | s1 | s2 | s3 |
|---|---|---|---|---|
| summle53 | 90.9 k→56.4 k | 58.1 k→115.6 k | 59.7 k→112.5 k | 74.8 k→57.3 k |
| summle11 | = | 91.9 k→34.7 k | 246.5 k→294.5 k | 168.9 k→352.3 k |
| timetable | **32.8 k→TO** | TO→TO | TO→349.2 k | TO→TO |
| worker / rbsat / mdp | identical / TO→TO | | | |

Timetable's canonical-seed 32.8 k solve (this session's consistent win)
regresses to timeout — the fifth instance of the single-policy-port
failure mode: porting one cadical policy onto this engine's surrounding
phase/schedule machinery redistributes trajectories both ways.

**Disposition**: landed behind `OXIZ_WALK_STRIP_FIXED=1`, **default
off** (historical exclusion behavior, trajectory-identical at default —
verified bit-exact). The knob keeps the study reproducible and the port
available if the surrounding machinery ever moves closer to cadical's.
Gates: workspace 10 415/10 415, clippy/fmt clean, differential 160/0,
wisas canary `unsat` fast.

**Complete story of the session-opening mystery**: walk0 events are
real (summle family), shadowed by target phases in stable mode; the
shadowing is *accidentally protective* because walk0 over the exclusion
objective is not a full model; the faithful objective makes walk0 a
model but the port is corpus-negative in our engine. The walk's
`minimum` counter bug that hid all of this is fixed (monotone).

## Negative result 3 (pass 5): shrink packed-key retention — neutral

Hypothesis: the shrink block walk's `trail.level()`/`trail.trail_index()`
per-literal loads are scattered random accesses (the profile's shrink
share on worker is cache-miss shaped), so retaining the sort's packed
`(level << 32) | trail_index` keys in a dense array (serving the block
boundary walk and `shrink_block`'s `max_trail`) should win on
giant-clause instances. Implemented (trajectory-identical, verified on
7 instances) and measured at fixed 40 k caps:

| file | before | after | ratio |
|---|---|---|---|
| worker_550 | 168.2 G | 169.2 G | **0.994×** |
| frb45 / noL | — | — | 0.996× |
| summle ×2 / circuit64 / j3037 | — | — | 0.999–1.000× |

Neutral-to-slightly-negative everywhere: the per-literal key push costs
what the saved lookups saved — after the descending sort the boundary
walk's `trail.level` accesses are already effectively sequential (same
level-table region), so the scatter hypothesis was wrong. Reverted per
the ±5 % band. The shrink cost on worker is intrinsic to the flag/mark
random access over ~1 900 literals per conflict; packing it away is the
whole-engine per-variable layout change the standing-gap study already
scoped, not a local fix.

## Negative result 4 (pass 5): propagation clause prefetch — net-negative

The last bounded idea for the propagate bucket (33–40 % on
circuit/frb45): software-prefetch the clause of a watcher
`PREFETCH_DIST` iterations ahead (the dependent clause load is the
loop's only L3/DRAM-class miss; the arena is tens of MB while value
arrays are L2-resident). Implemented as a documented `unsafe`
exception (address computation identical to `header_ptr`'s, prefetch
side-effect-free), trajectory-identical, measured on **cycles** (3
reps, pinned core, identical instruction streams):

| file | pre-cycles | prefetch-3 cycles | Δ |
|---|---|---|---|
| circuit_64in | 3.50 G | 3.79–3.90 G | **+8…+11 %** |
| frb45 | 2.90 G | 2.96 G | +2.2 % |
| noL | 1.98 G | 1.95 G | −1.6 % |
| summle53 | 14.43 G | 14.49–14.80 G | +0.4…+2.5 % |

Why it loses on exactly the target class: circuit's watch-list
iterations are dominated by cheap blocker-hit paths (~10 instructions,
often satisfied binaries that never load the clause at all) — the
prefetch's address computation (arena-base load + offset arithmetic)
adds ~50 % to that path, and the prefetched lines are dead work for
every blocker hit. Latency hiding only pays when the loop body stalls
on the miss it hides; this loop body mostly doesn't. Reverted.

**Conclusion for the propagate slice**: the remaining 1.8× on
circuit-class files is work-shape (long watch lists, many
satisfied-binary visits), fixable only structurally — cadical-style
**tagged binary watchers** (binaries carried inline in the watcher,
clause load skipped structurally) or the 8-byte watcher packing the
earlier study scoped. Naive prefetch is measured out.

## Pass-5 close: the propagate slice's true shape (circuit characterized)

`circuit_64in64out_with_64gates…cnf` is **384 variables and 507 904
clauses of length exactly 13** (plus 64 units) – a pathologically dense
formula: ~8 600 watchers per literal, every value/level/seen array
L1/L2-resident, and a 32 MB clause arena as the only DRAM-class
structure. The propagate cost on this class is **scan volume ×
per-visit constant**, and the prefetch experiment shows the loop is
issue/bandwidth-shaped, not stall-shaped – there is no latency to hide.

With the blocker-refresh already at cadical parity, the two-watched
invariant intact, and the visit path at one header load + deleted
branch + unchecked value loads, the remaining 1.8× vs cadical is the
**watcher/arena layout differential** (12-byte watcher vs cadical's
tagged pairs; header-prefixed arena vs cadical's inline arrays) – the
same data-structure slice the flat-watch-arena and 8-byte-watcher
studies scoped, needing a whole-pass redesign to move. That, the
per-variable layout change for worker's shrink scatter, and the
conflicts-to-model deep study are the three remaining programs, in
recorded priority order.

Pass-5 ledger: two structural hypotheses implemented and falsified
cleanly (shrink key retention: neutral; clause prefetch: negative on
the target class), one target characterized to its exact shape, ten
negative results total now standing guard over the boundary of what
local optimization can reach in this engine.

## Pass 6: the root-fixed sweep port (cadical collect.cpp) — mechanistic win, corpus trade, knob-gated

The deep study's first instrumented step (a patched `/tmp/cadical`
printing `conflicts/level/size/glue/trail` per conflict, exactly the
earlier studies' harness) **inverted the j3037 diagnosis**: our search
shape is cadical's (level 20.3→15.0 vs 19.6→13.8, learnt sizes 32 vs
36, **377 k vs 361 k conflicts — 4 % apart**). j3037 was never a
search-quality gap. The wall gap (37 s vs 22.9 s) decomposes as
instructions 1.36× (growing from 1.07× early) + CPI 1.13× – and the
smoking gun is the **trail**: cadical's mean trail *shrinks* over the
run (2901 → 2324 literals) while ours stays flat (3349 → 3190).
Cadical garbage-collects root-fixed state (satisfied clauses retired,
root-falsified literals flushed — `collect.cpp`, the piece the reduce
study deliberately left out); our DB only ever grows with it.

Ported as `sweep_root_fixed_clauses` (after each scheduled reduce, when
new level-0 facts appeared: satisfied → retire via the standard
retire; root-falsified literals → strip via
`remove_literal_and_rewatch`, which re-selects watches and keeps the
proof stream consistent; root-falsified binaries → partner unit +
retire; deferred-effect scan over the arena, same shape as the
elimination connect pass).

**Effects** (all verdicts identical everywhere; workspace, corpus
sweep, 1 000 fuzz iterations, differential 160/0, parity 169/0/1):

- `j3037` 37 s → **29.5 s** `unsat` (first sub-cap solve), `g2-slp`
  35.7 s → **22.3 s**, worker 42.5 s → 40.6 s.
- **Timetable and noL-11-14 regress from solving to 90 s timeouts**
  (unit-heavy searches: mid-search root facts flow constantly there,
  and sweeping their DBs derails the search).
- 54-file corpus at the 40 s cap: **45 → 44** (sweep-only: j3037,
  g2-slp; pre-only: Timetable, noL, x9-08075-cap-edge).

Same shape as `chrono_reuse`: cadical-faithful mechanism, strong
mechanistic wins, broad regress. **Knob-gated
(`OXIZ_ROOT_SWEEP=1`), default off** — the default path is
trajectory-identical to pre-change (verified bit-exact on j3037).

### The deep study's first hard result

j3037, crypto1 and FmlaEqu — the "conflicts-bound" losses — are now
known to be **throughput-shaped after all** for j3037 (equal conflicts,
growing per-conflict cost from unswept root state), and the sweep
closes most of its gap when enabled. The conflicts-to-model framing
survives only for files where the instrumented comparison still shows
a real conflict-count gap. (The instrumented-cadical scratch tree was cleaned up after the
session; rebuild it the same way – copy `src/` + `configure` +
`scripts/` + `makefile.in` to a `/tmp` dir, add one `fprintf` after the
glue `UPDATE_AVERAGE`s in `analyze.cpp`, `CXXFLAGS=-DCADICAL_CONF_TRACE
./configure && make`. Never patch the reference tree.)

Addendum: with `OXIZ_ROOT_SWEEP=1`, `combined-crypto1` solves `sat` in
53.5 s (default TO) and `FmlaEquivChain` `unsat` in 60.4 s (default
TO) – the bloat signature covers at least three of the four
"conflicts-parity" losses. The sweep knob is the recorded way to reach
them; flipping it default-on needs the Timetable/noL regressions
understood (why unit-heavy searches derail) or a portfolio/schedule
that gets both.

## Pass 7: the sweep decomposition, a wrong answer caught, and the knob kept

Decomposing the sweep's damage isolated each half:

| variant | Timetable | noL | j3037 | g2-slp | crypto1 | FmlaEqu |
|---|---|---|---|---|---|---|
| default (no sweep) | 33 s | 36 s | TO | 36 s | TO | TO |
| retire+strip (full) | **TO-90s** | **TO-4M-conf** | **29.5 s** | **22.3 s** | 53.5 s | 60.4 s |
| retire only | TO-70s | bit-identical¹ | 33.5 s | TO | 54.9 s | **41.3 s** |
| retire non-binary only | **8.2 s** | 33.2 s | 32.2 s | TO | 54.1 s | **35.3 s** |

¹ noL never sweeps (all its root facts predate the first reduce).

**Retiring satisfied non-binary clauses is a pure win on every file
measured** (Timetable 33 s → **8.2 s**!, three losses solved), and
**stripping root-falsified literals is the mixed half** (g2-slp needs
it, noL's conflicts multiply 2.4×). Binary retirement alone also
damages (its binary-graph edge purge reorders edge lists).

**Then the default flip was caught by the suite answering a wrong
`sat`**: `cegar_mul_low_word_identity_refuted` (BV-CEGAR, UNSAT input)
answered `sat` with retire-on — surviving the corpus verdict sweep,
1 000 fuzz iterations and 3 gates added along the way (reason-pointer
guard à la reduce's `is_reason`; assertion-scope/proof/assumption
gates; `real_theory_attached` gate — the BV path is near-pure-SAT so
the last one doesn't even engage). Root cause still open; reproducer:
the SMT2 above, `precompile/48ae97a` + retire-on default. **Disposition:
everything back behind `OXIZ_ROOT_SWEEP=1`, default off, hardened**
(the three gates and the reason guard stay — they are correct
regardless and make the knobbed sweep safer than the first landing).
The knobbed SAT-only configuration fuzzed clean (1 000 iterations) and
delivers: j3037 29–33 s, g2-slp 22 s, crypto1 54 s, FmlaEqu 35–41 s,
Timetable 8.2 s (with NOSTRIP).

**Open item (next session, highest value)**: find the retire-path
wrong-`sat` mechanism in the BV-CEGAR interaction. The winning table
above sits behind one soundness answer — understand it, and five
standing losses close at once.

## Pass 8: the wrong-`sat` root cause traced to its final fork

The question "apart from the guards, what is the root cause?" reopened
the closed conclusion — correctly. Re-deriving the evidence showed the
guards never fixed anything: **every configuration with strip OFF
(retire-only) answers the wrong `sat`, every configuration with strip
ON answers `unsat`** — the earlier "guards fixed it" reading was the
strip-on configurations, and at least one intermediate observation was
also a stale-shared-target artifact. The guards are defense in depth,
not the cure. Live reproducer (all instrumentation in this section was
temporary and reverted): `OXIZ_ROOT_SWEEP=1 OXIZ_ROOT_SWEEP_NOSTRIP=1`
on `cegar_mul_low_word_identity_refuted`'s input.

### The causal chain, layer by layer (each instrumented and verified)

1. **The CEGAR loop behaves correctly.** Round 4's `bv.check()` returns
   Sat with `spurious=0` — every abstracted mul carries its exact
   product value in the model. That is a *relaxation-consistent* model,
   not a formula model, and the dispatch's whole-assertion validation
   correctly refutes it (`validation refuted=true`) and correctly
   refuses to answer (`return None`).
2. **The general path produces the wrong `Sat`.** `check_core`'s CDCL(T)
   loop returns `raw_result=Sat`, `certified=Sat`; neither of the two
   instrumented loop arms nor any early exit fired — the verdict comes
   from `SatResult::Sat` → `!has_quantifiers` → `build_model` → `Sat`.
3. **Two tempting theories falsified by measurement.** The fallback
   does *not* inherit an abstracted encoding (`terminal=2 of 2` — the
   exact circuits are all in place), and the theory layer is *not*
   starved (`bv_terms=2, var_to_constraint=1` — the final check's
   empty-`bv_terms` short-circuit at theory_manager.rs:3926 does not
   apply).
4. **What remains is the embedded SAT solver itself.** `self.bv` owns
   its own `oxiz_sat::Solver` (the sweep fired *there*, during the
   CEGAR rounds — `self.sat`, the main solver, is a different
   instance). The general path's BV final check re-solves that embedded
   instance and accepts its answer. The embedded instance carries the
   full exact encoding yet reports satisfiable — **either** (a) the
   retire-only sweep is unsound *at the pure-SAT level* on this
   unit-dense instance (thousands of constant bit-pins make almost
   every clause "satisfied at level 0" — the sweep retires nearly the
   whole formula, and any flaw in the permanence argument shows up
   immediately), **or** (b) the embedded solver's *incremental* state
   is poisoned (the BV layer drives `push`/`pop` on it —
   `bv/solver.rs`'s `ContextMark` machinery — and a pop rewinds
   level-0 trail literals that retirements were justified by; the
   CEGAR rounds also re-`check()` the same instance repeatedly).

### The decisive next experiment (recorded for the next session)

Dump the embedded instance at the failing check
(`Solver::export_problem_dimacs` exists) and solve it standalone:
from-scratch + no sweep, from-scratch + retire-only, incremental
replay. If from-scratch + retire-only answers `sat` on a satisfiable
export — the export includes the level-0 pins, so cross-check with
cadical — the SAT-level retirement argument itself has a hole on
unit-dense inputs. If only the incremental replay lies, the hole is
the BV layer's `push`/`pop` × sweep interaction, and the correct fix
is restoring sweep-retired clauses on pop (the same bookkeeping
`assertion_clause_ids` does for pop-retractable clauses) or sweeping
only behind literals whose justification is an *original* clause.

The sweep stays knob-gated default-off; the five-file winning table
stands behind that one soundness answer, now with the search space for
it reduced from "somewhere in the BV path" to two sharp, testable
hypotheses.

## Pass 9: the root cause FOUND, fixed, and the retire default flipped ON

The decisive experiment ran with a retirement log (clause, justifying
literal) verified at the failing check. Direct evidence:

```
RETIREMENT BROKEN: clause #1852 justified by -670 now val=Some(false) level0=false
retire log 76 entries, 2 broken, 10 true-but-not-level0
```

**Root cause (complete)**: the BV layer's `check_body` parks arbitrary
*model decisions* at decision level 0 between probes (its own doc: "some
assignments (even a branch `Decision`) land at decision level 0"), and on
a first-`Unsat` verdict rewinds the trail with `restore_to_trail_size` —
un-assigning level-0 literals. The sweep (firing *inside* those solves)
treated every level-0-true literal as a permanent cadical-style fact and
retired clauses justified by them; the rewind un-justified the
retirements; the re-solve answered `Sat` on the weakened formula. The
`assert_const` pins install bare `Decision` reasons (no backing clause),
and `forget_learned_since` drops learned units on the retry path — three
distinct non-permanent level-0 sources. No scope gate can see
`restore_to_trail_size`; that is why the guards never fixed it (and the
strip-on/strip-off difference was pure trajectory luck, as pass 8
concluded).

**The fix (permanence guard)**: a clause may be retired/stripped only
behind a literal whose reason is a **live original clause** — a fact
re-derivable from the permanent clause set, so any rewind followed by
re-propagation re-establishes the justification. Bare decisions (model
leftovers, constant pins without backing clauses) and learned units
(dropped by `forget_learned_since`) are not eligible justifiers.
With the guard, the wrong-`sat` reproducer answers `unsat` in every
configuration; the guard is in the sweep's scan (both retire and strip
paths), cost one reason-clause lookup per candidate.

**A second hole surfaced and quarantined**: the STRIP half (with the
guard) answered a wrong `unsat` on `circuit_48in64out_700g/800g` and
`si2-b03m` — SAT files, seed-stable `sat` at default (verified across
4 seeds), deterministically `unsat` with the strip on. A different
mechanism from the level-0 permanence bug (this one over-strengthens);
root cause open. **The strip now lives behind its own
`OXIZ_ROOT_SWEEP_STRIP=1` (default off)** — its only measured win
(g2-slp 36 s → 22 s) stays reachable; the wrong-unsat reproducers are
recorded.

**Default flip**: the permanence-guarded retire (satisfied non-binary
clauses, original-clause-justified only) is **ON by default**
(`OXIZ_ROOT_SWEEP=0` opts out). Gates at the new default: cegar repro
`unsat`; fragile files `sat`; corpus verdict sweep 34/0; 1 000 fuzz
iterations 0 mismatches; workspace 10 415/10 415; differential 160/0
(par2 2 316); z3 parity 169/0/1; wisas canary. Corpus A/B under load
8.5: 43 vs 43, 0 mismatches (headline-neutral at load; the low-load
wins stand from the pass-7 table: Timetable 33 s → 8.4 s, j3037/crypto1/
FmlaEqu solved, noL unchanged).
