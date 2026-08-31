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
