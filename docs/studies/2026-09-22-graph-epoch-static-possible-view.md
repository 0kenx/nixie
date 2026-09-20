# Study: graph-constraint work parity vs MonoSAT — the epoch-static possible view, and how to measure anything on this machine

**Date:** 2026-09-22
**Base:** `38cb15d4` (main; the graph arc landed at `d2025ba0`)
**Verdict:** **LANDED** — instruction-count gap vs MonoSAT **2.25× → 0.965×
geomean** (parity), totals **7.36× → 1.22×**, worst instance **33.8× →
2.82×**, with **bit-identical `conflicts/decisions/propagations` counters**
on every corpus instance (trajectory-inert), the full validation stack
green, and two reusable methodology findings recorded below.

## Part 1: the measurement layer (read this before any future perf work here)

The handoff's headline number (1.65× geomean, wall-clock medians of 3)
could not be reproduced on first attempt — and the reason invalidates
*every* unpinned wall-clock or `perf` number taken on this box under load:

1. **Wall-clock is unusable under co-tenant load.** Load average was
   35–65 on 20 cores during this session. A corpus run measured "5.38×
   gap vs MonoSAT" and "a 2.3× regression vs the arc head commit" —
   both artifacts: the same binaries measured minutes later ran the
   flagged instances 10–100× faster. (This also *retroactively explains*
   why the arc's own numbers were noisy enough to need medians of 3.)
2. **The CPU is hybrid, and `perf` counts migrate.** Unpinned processes
   bounce between P-core and E-core clusters, and `perf stat` then
   reports *two* partially-enabled counters (`cpu_core/instructions/u`
   at e.g. 84%, `cpu_atom/instructions/u` at 16%) whose sum is not
   comparable run-to-run. Worse, when another agent holds PMU slots,
   single events get time-sliced and **scaled up by the enabled-time
   fraction** — a 25M-instruction run reported "626M". The `(25.15%)`
   field in `perf stat` output is the tell: any enabled-fraction below
   100% means the number is not a count, it is an estimate.
3. **The fix**: `taskset -c <one P-core> perf stat -x, -e instructions:u`,
   retry until a numeric line appears. Pinned to one P-core: counts are
   stable to **±0.001%** under load 56 (co-tenancy steals *time*, not
   *work*). This is the corpus metric for everything below — it is a
   *work* metric, not a time metric; wall comparisons on this box remain
   possible only in quiet windows and were deliberately **not** used to
   re-baseline the 1.65× headline (recorded limitation, not a claim).

Tooling: `bench/graph_differential/run_instructions.sh` (pinned
measurement, PMU-contention retry, geometric-mean summary; corpus
generation one-liner in its header context above). MonoSAT rebuild
recipe: see the 2026-09-19 differential study (unchanged; note
`make libmonosat_static` does not build `Main.cc.o` — compile
`src/monosat/Main.cc` directly for the CLI).

Corpus (regenerable): `n ∈ {25,50,100,150} × reach-max ∈ {4,8,16,32} ×
seeds 1..5`, generator defaults (unit + two-literal mix), 80 instances;
61 were measured at every checkpoint (the subset completed before the
first wall-clock corpus attempt was abandoned).

## Part 2: where the work actually went

Pinned instruction profile of the worst instance (`v150_r4_s3`, 9.7G
instructions, `conflicts=1 decisions=0` — pure propagation):

- **70%** `Csr::rebuild` + **15%** `backward_seen`: every false-edge
  fixation marked the possible view dirty and the next run (fires per
  event — `on_fixed` is the eager propagation channel, and `final_check`
  only runs at full assignment) rebuilt *both* possible-side CSRs from
  scratch and cleared *all* backward memos. 7k events × O(V+E) each.
- The forced side (event-driven incremental since `aa8a6cf6`) was cold.

## Part 3: the design

Three changes, all preserving the per-check **exactness contract** the
exhaustive oracles pin (eager conflict detection and determined
propagation — verified when a weaker "stale-valid" design failed the
oracles; see below):

1. **Epoch-static possible view.** The possible-side CSRs now contain
   *all* edges and are built once per epoch (a backtrack boundary), never
   on events. Queries traverse them skipping currently-false edges
   (`bfs_filter`, `find_cycle_filter`); row declaration order is
   preserved, so discovery order and emitted justifications are
   bit-identical to the rebuilt-CSR design at computation time.
2. **Precise dirty-marking with a closure-preservation probe.** Disabling
   `e = (a→b)` drops a memoized backward closure `C_t` only if `b ∈ C_t`
   **and** `a` no longer reaches `t` without `e` — that second condition
   is exactly when the closure changes: if `a` keeps a surviving path,
   every old member's path through `e` reroutes through it, so
   `C_t ⊆ C_t' ⊆ C_t`. The check is a BFS from `a` over surviving edges,
   **pruned at non-closure vertices** (provably off every surviving path)
   and exiting only at `t` itself — bounded by the closure, typically a
   few hops in dense graphs. A memoized possible cycle dies only if its
   edge list contains `e`; a memoized cycle *absence* is stable under
   shrinking.
3. **All-fixed exactness gate** (defense in depth) + **O(1) event
   routing**: the gate re-verifies every true-fixed reach atom against
   the exact forced view and re-checks the demanded-cycle case before any
   `Sat`; `UserCallback::on_assignment` routes through the existing
   `by_var` index instead of scanning the whole watch list per literal
   (quadratic once models register thousands of watches), and
   registration now rejects watch lists where two distinct terms share a
   SAT variable (a term and its negation) — that collision previously
   made `by_var` silently drop a watch, a latent soundness hazard in the
   justification-truth lookup that pre-dates this change.

**The bug the oracles caught mid-design** (kept as a regression,
`closure_probe_preserves_and_drops_exactly`): the probe's first version
exited at *any* closure member `x`, reasoning "x reaches t". But x's own
path may pass through the disabled edge — after `e` dies, a stale closure
remained and a determined `¬reach` was not propagated. The fix is the
exit-only-at-`t` rule plus closure pruning; the regression's 1↔4 cycle is
exactly the shape that fooled the first version.

## Results (deterministic instruction counts, 61-instance corpus)

| | MonoSAT | before | after |
|---|---|---|---|
| geomean | — | 2.251× | **0.965×** |
| totals | 9.84G | 72.4G (7.36×) | **12.0G (1.22×)** |
| worst (`v150_r4_s3`) | 0.29G | 9.67G (33.8×) | **0.81G (2.82×)** |
| instances below 1× | — | — | **32/61** |

Stage attribution: rebuild elimination alone (epoch-static CSRs +
per-dirty-memo recompute) → 1.53×/2.72×/11.8×; the closure-preservation
probe → 0.965×/1.22×/2.82×. The residual profile is flat (top symbol
`GraphModel::run` at ~42% on the worst instance — the per-event atom
scan itself; nothing above 3% anywhere else).

## Verification

- **Bit-identity**: `conflicts/decisions/propagations` identical to the
  pre-change build on all 61 corpus instances (STATS=1, both binaries;
  re-verified after the final fmt/clippy pass on a 12-instance subset).
- **Suites**: workspace `--all-features` 12081/12081 (the one failure,
  `si2_b03m_is_not_unsat`, and the 13 earlier ones are worktree artifacts:
  `smt-lib/non-incremental`, `satcomp2024/5`, `satlib` are git-ignored
  corpora absent from fresh worktrees — symlink them before testing in a
  worktree).
- **Oracles**: 28/28 graph oracle suite including the exhaustive
  all-completions oracles and the 200-campaign generated oracle with
  nested rollback; +3 new focused regressions (probe preserve/drop,
  all-fixed determined propagation, negated-watch rejection).
- **MonoSAT differential**: 1600/1600 agree, 0 skips (1000 mixed + 400
  `VERTICES=12` + 200 `VERTICES=20`).
- **Z3 4.16.0 parity**: 0 disagreements.
- **Perf gate**: PASS, counters exactly 1.000 (the module is inert unless
  registered; the routing change only executes with registered
  propagators).
- clippy `-D warnings`, fmt, rustdoc clean (one pre-existing
  `nixie_tla` output-filename collision warning, present at main).

## Residual and follow-ups

- The remaining totals gap (1.22×) lives in `GraphModel::run`'s per-event
  atom scan and the fixed SMT stack (interning/Tseitin/BCP), which is
  shared by every theory — not in graph-specific recomputation anymore.
- True decremental reachability (Ramalingam–Reps, MonoSAT's `dgl/`) would
  target the same remaining closure recomputes the probe cannot save
  (genuine closure shrinks); nothing in the corpus profile says it is due.
- Theory-directed decisions remain the search-shape lever; matched-null
  discipline applies (untouched here — this landing is trajectory-inert,
  which is strictly stronger).
