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

## Addendum (2026-09-22, later): the probe was the residual — witness edges close it, geomean 0.965× → 0.818×, totals 0.906×

Re-profiling the landed state at instruction level put the
closure-preservation probe itself at ~50% of the worst instance
(`v150_r4_s3`): in dense graphs every vertex is within two hops, so a
probe explores the whole closure and scans each explored vertex's full
row — O(closure × average out-degree) ≈ O(E) per disabled edge, the same
order as the recompute it tries to avoid (it wins only on constants and
by avoiding the memo-clear cascade).

**The budget trap (measured, reverted).** Capping the probe at 16
vertices to bound that cost made the worst instance **3.8× worse**
(805M → 3.07G instructions): the probes were mostly *expensive
successes* — closures genuinely preserved but provable only via long
paths — and truncation converts every one into a memo drop plus an
O(V+E) recompute, repeated per event. A cap on a preservation decision
is not a policy knob; it is a regression generator. Reverted.

**The witness design (landed).** `Backward` now stores the BFS parent
edge of every closure member: a genuine, *simple* path to the target
whose edges are all non-false (a surviving memo's witnesses can never
have been disabled — a match drops the memo). Disabling `e = (a→b)`
endangers the closure only through member `a`'s path, and a simple path
uses exactly one out-edge of `a` — so the check
`witness[a] == e` decides preserve-vs-drop in **O(1)**, with no
truncation anywhere. A witness match (~1/out-degree of disables, and
1/75 on the corpus graphs) drops the memo; the next query recomputes it
exactly. Correctness is structural rather than exploratory: preserved
and recomputed closures are both exact, so emitted answers — and hence
`conflicts/decisions/propagations` — are **bit-identical** to both the
probe design and the pre-arc propagator (verified via `STATS=1` on the
worst instances).

| | probe (morning) | witness |
|---|---|---|
| geomean | 0.965× | **0.818×** |
| totals | 1.223× | **0.906×** (8.92G vs MonoSAT 9.84G — less total work) |
| worst instance | 2.82× (`v150_r4_s3`) | **2.30×** (`v150_r16_s3`, a different outlier) |
| instances below 1× | 32/61 | **40/61** |

Validation re-run for the witness change: graph oracles 30/30 (incl. the
renamed `closure_witness_preserves_and_drops_exactly` regression, whose
1↔4-cycle shape the witness design rejects structurally), MonoSAT
differential 1600/1600, Z3 4.16.0 parity 0/354 wrong, perf gate PASS at
exactly 1.000 counters, workspace `--all-features` 12093/12093 (14
corpus-path worktree artifacts, all pass with the corpora symlinked).

**Where the remaining outliers live.** `v150_r16_s3` (2.30×, unchanged
by both the probe and the witness): its cost is not closure maintenance
— it is the per-event scan plus the fixed SMT stack, i.e. the shared
per-assertion/BCP machinery every theory pays. The corpus as a whole is
now below MonoSAT on total work; closing the outliers means the shared
stack (interning/Tseitin/EUF), not the graph propagator.

## Addendum (2026-09-22, close-out): the outlier class is the assertion pipeline; a capacity hint, and where the residual is handed off

Re-baselined at current main (the assert-fold campaign landed between the
witness measurement and now — it *improved* this corpus too: 0.818× →
0.764× geomean on the comparable 37-instance subset, totals 0.906× →
0.837×). The worst class (`v150_r16_s3`, 2.32×) was profiled at
instruction level and is a **pure assertion-pipeline instance**:
`conflicts=0 decisions=0 propagations=0` — the entire instruction mass
is minting and asserting ~22k terms. Breakdown: term interning and its
hash-table churn ~30% (three `reserve_rehash` growth storms, `intern`,
`hash_term_key`, `lasso`), kernel page-fault time ~12% (allocation
traffic), `memmove` ~11% (table-growth copies), and a long tail of
per-assert pipeline stages at 2–4% each (`contains_quantifier`,
`intern_term_for_congruence`, `arith_atoms_need_theory`,
`intern_compound_uf_args_into_arith`, `StaticFeatures::collect`). The
survey-style stages are already gated or cached (the earlier arcs' work
— `StaticFeatures` once per goal, set/bag and BV gates); nothing
dominates. This is the structural cost of the SMT API versus MonoSAT's
integer GNF loader, distributed across dozens of stages.

One surgical slice landed: **`TermManager::with_capacity`** — presizes
the terms vector, the hash-consing table, and the symbol interner
(`new()` delegates with the previous defaults; purely an allocation
hint, identical TermIds and answers), and the GNF driver estimates its
term population from the parsed instance (edges + reach + acyclic +
clause literals + clauses, ×2). Effect on the outlier: 159.6M → 155.5M
instructions (corpus subset: geomean 0.764× → 0.750×, totals 0.837× →
0.822×, worst 2.32× → 2.24×). The remaining growth-copy mass lives in
the *solver-side* maps (Tseitin/guard/constraint tables), not the
manager's — not worth chasing from the graph side.

**The corpus is closed from this side**: below MonoSAT on geomean and
totals (≈0.75×/0.82×), 40+/61 instances individually below it, and the
residual outlier class is per-assertion SMT-stack territory — the
assert-fold arc's successors own that surface (their handoff names the
load wall and the top parser symbols). The profile evidence above is
the handoff. One caveat for whoever picks it up: on the outlier class
the *wall* ratio exceeds the instruction ratio (≈3.5× vs 2.24× in a
quiet window, medians unstable) — the pipeline is pointer-chasing
(hash tables, hash-consing) where MonoSAT's loader streams arrays, so
instruction-count wins there understate wall-time wins.

Validation for the capacity slice: workspace `--all-features`
12108/12108, MonoSAT differential 300/300 (full 1600 not re-run — the
driver hint is inert for verdicts and the corpus verdicts were verified
at 300), Z3 4.16.0 parity 0/354 wrong, perf gate PASS at exactly 1.000
counters (nixie-core is upstream of the gate — verified explicitly),
clippy/fmt/rustdoc clean.

## Addendum (2026-09-22, third session): taking the outlier class — feature-gated early scans, memoized quantifier checks

The outlier class (`v150_r16_s3`, 2.24×) profiled as a pure
assertion-pipeline instance, so the slices are per-assert/per-check
pipeline stages that run regardless of what the goal contains. Five
inert fixes landed together (search counters bit-identical on every
measured instance):

1. **Feature-gated early-conflict scans.** `check()` runs four
   whole-assertion-set scans per check — string, FP, datatype, array
   early conflict detection — plus the finite-domain-enumeration bump
   walk. The goal's `StaticFeatures` (already computed once per goal
   for the router) knows whether each theory is present; the scans now
   run only when it is (`has_string/fp/dt/array_terms`, and
   `num_eqs > 0` for the bump walk, whose leaves are `Eq` terms of any
   sort). Absent-theory collection is provably empty, so the gates are
   inert by construction — but they delete a full per-check DAG sweep
   per theory for every goal that isn't using it. The FP scan's cache
   has no external readers (verified) and the string scan's ground
   evaluator already self-gates.
2. **Memoized `contains_quantifier`** (`TermManager`): the pipeline
   asks per assertion at several stages; each call re-walked the DAG
   with a fresh visited set. The manager now records every term proven
   quantifier-free (a completed negative traversal proves it for the
   whole visited DAG; term content is immutable and ids are never
   reused — the same argument the `eq_solve_cache` documents), making
   repeated queries and shared subterms set lookups. `RefCell` because
   the queries arrive through `&TermManager` (the manager is not
   `Sync`; single-threaded interner).
3. **Allocation-free BV fragment walk** (`term_in_blastable_fragment`):
   per-asserted-term walk allocated a fresh `FxHashSet`; now a flat
   `Vec` with linear membership below 256 entries (assertion-sized
   DAGs), spilling to a set above. Same reachability semantics.
4. **Incremental `add_vertex`** (graph module): the per-vertex table
   re-size was O(V²) over construction; pristine caches now grow one
   row.

Effect on the heavy half of the corpus (12 instances,
n∈{100,150}×r∈{16,32}): the worst instance 155.5M → 142.8M
instructions (**2.24× → 2.06×** vs MonoSAT), and the subset as a whole
now runs at **0.596× geomean / 0.593× totals** (1.57G vs 2.65G — 40%
less work than MonoSAT on the heavy instances).

**What remains in the outlier, and whose it is.** Re-profiling after
the gates: process teardown ≈ 19% (`drop_in_place<Solver>` +
`drop_in_place<TermKind>` + `mi_free` — the cost of destructing ~60k
hash-consed terms and the solver's maps at exit; MonoSAT's flat arrays
destruct nearly free; deliberately NOT gamed with `process::exit`),
Vec-growth copying ≈ 20% (SAT watcher lists + the per-assert
simplifier's term traffic — the simplifier is the assert-fold arc's
surface), `new_var` 4.7% + `intern_term_for_congruence` 6.9%
(structural: one SAT var and one congruence entry per encoded atom),
and `link_or_blast_bv_circuits` ≈ 12% (per-assert BV circuit walk that
no-ops on Boolean goals — skippable only by threading a "saw a BV
subterm" bit out of the encoder, a coupling change for the BV owner).
The instruction-level profile is preserved in this study's session
logs; the graph side's remaining contribution to the outlier is now
noise.

Validation: workspace `--all-features` 12113/12113, bit-identical
counters 12/12 vs the pre-change build, MonoSAT differential 300/300,
Z3 4.16.0 parity 0/354 wrong, perf gate PASS at exactly 1.000
counters, clippy/fmt/rustdoc clean.

## Addendum (2026-09-22, fourth session): the tail is flat — one more inert gate, one measured-negative skip, and the stop decision

Re-profiling the outlier at the current head showed the post-gates
tail is now genuinely flat: driver-side term minting (`mk_not` + `main`
≈ 17%), the hash-consing insert/probe mass (≈ 17%, spread across the
term→var table, the watch-registration maps, and the elim-uncnstr
occurrence bookkeeping), memory traffic (`memmove`/`memset`/mimalloc
≈ 15%), one SAT var + one congruence entry per encoded atom
(structural), and the one-per-goal feature walk. No remaining symbol
is both large and in this arc's lane.

Two slices were tried:

- **UF interface-repair gate (landed)**: `intern_compound_uf_args_
  into_arith` walked the whole encoded vocabulary (per check, whenever
  the vocabulary grew) even when the goal has no uninterpreted
  function anywhere — its candidates are `Apply` arguments, and an
  `Apply` node requires an arity>0 UF symbol, which is exactly what
  `StaticFeatures::has_uf()` counts. Gated at both call sites; the
  worst instance drops 142.8M → 141.2M instructions (−1.2%), counters
  bit-identical, full stack green.
- **BV link/blast skip while `bv_terms.is_empty()` (measured
  NEGATIVE, reverted)**: skipping the per-assertion link/blast pass
  when no BV term was ever encoded — provably a no-op walk — *added*
  3.5M instructions (~+2.4%) on the same instances. The walks it
  removed were already cheap at this head (they no longer appear in
  the top symbols), and the change's code-layout shift alone costs
  more than the walks. Reverted; recorded as a reminder that
  instruction deltas under ~2% in this pipeline can be layout noise
  in either direction — the deterministic counter is bit-identity,
  and instruction deltas at this scale need the before/after pair
  measured on the same binary layout to be meaningful.

This closes the engagement from the graph side: corpus geomean
0.75× / totals 0.82× vs MonoSAT (below parity on both), heavy half
0.60×, worst outlier ~2.0× with the residual attributed to the
structural SMT-API cost (hash-consing, one-var-per-atom, teardown)
and to the simplifier/parse surface owned by the assert-fold and
parser arcs. Further outlier work belongs to those owners with this
study's profiles as the entry point.
