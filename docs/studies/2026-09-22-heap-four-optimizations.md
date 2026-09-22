# Four heap optimizations: design and preregistration

This study implements four bounded optimizations of the existing exact-heap
fragment: directional anchor coverage, assertion-entailed integer substitution,
immutable expression templates across scopes, and guarded lazy Boolean rows.
It adds no inductive predicates, permissions, wand, proof translation, or new
syntax. See [the heap semantics](../HEAP.md).

## Correctness obligations

For a valid source heaplet with k distinct nonzero locations, equal-length
coverage of all its cells by a destination list forces k distinct matches in
that list. Every destination position participates; its validity follows.
The direction matters: coverage from an invalid duplicate destination does not
prove this. The redundant-validity control uses the same coverage direction.

Only asserted equalities and exact literal bounds reached through entailed
Boolean polarities are propagated. Union-find representatives are constants or
the earliest node, and integer rebuilding is iterative. Contradictory classes
or bounds retain the original terms for backend reasoning. Neither arbitrary
disjuncts nor an endpoint of a nonexact interval provides a substitution.
Original assertions and original-input model checking remain intact.

Cached values are immutable TermManager expressions. Keys contain the complete
ordered current operands (including stored values and coverage direction), never
scope-local equivalence classes. The arena retains IDs across backend pop.
Every private scope asserts its definitions anew; assertions, rewritten operand
maps, model guesses, and truth values are not cached across scopes.

Without an entailed positive anchor, candidate models are checked against the
original input first. A failed candidate with selected atom pi installs
`pi => Vi` and `pi => (pj <=> Eij)` for every other j. These are guarded valid
lemmas, not unconditional assumptions about the selected heap. Every failed
iteration installs a previously absent row or returns Unknown. At most n rows
are installed per private scope. Successful original-input model validation is
sufficient even when unused internal atoms have different candidate phases.
Backend conflict/decision budgets accumulate; an optional user timeout spans
refinement calls. Repeated failure after an installed row is an honest Unknown.

Reference inspection: CVC5 `theory_sep.cpp` reduction conclusions and model-based
guarded refinement; CVC5 `non_clausal_simp.cpp` literal substitution and retaining
incremental equalities; Nixie backend scope journals, model extraction, budget
accounting and TermManager ID lifetime. Exhaustive finite-map tests cover all
16 optimization combinations plus the older specialization/redundancy controls.
A second exhaustive Boolean test covers pairs of binary clauses without a forced
unit. Focused regressions protect duplicate targets, nil, value disagreement,
exact/nonexact bounds, cyclic equations, reused variable names, changed values
across scopes, template reuse, retracted assertions and alternative lazy rows.

## Preregistered experiment (before any performance cells)

The baseline library is `cb50c87ec8331659e40c9fe257bf7191f2184d47`.
Both revisions use the same new workload interpreter and independent Python
snapshot validator; the baseline adapter links the clean old library through a
separate client package. Both use release opt-level 3, LTO, one codegen unit,
abort panic, no stripping, default library features, mimalloc, no incremental
compilation. Binary/source hashes and the baseline manifest/lock are retained.

`next_experiment.py` fixes 27 cases, seeds 0–9 plus held-out 103, and six arms:
baseline, all, no_coverage, no_equalities, no_cache, eager. Total: **1,782 cells**.
The candidate's all arm explicitly enables all four options, independent of any
later default selection. Controls disable exactly the named optimization:

* no_coverage retains destination validity with identical directional coverage;
* no_equalities discovers the same substitutions but uses original operands;
* no_cache performs the same template lookup/store but recomputes expressions;
* eager installs the exact guarded row family up front instead of on demand.

The first three are exact encoding/construction transformations, not learned
search policies. The lazy control shares the lemma content; timing and row order
necessarily differ, so this tests staging and its search consequences, not a
claim about a new branching heuristic. All arms use matched seeds and budgets.

The corpus retains all five original families at sizes 4 and 16. Views and
free_views use 8, 16, 32 heaplets. Symbolic_views, offset_views, cache_scopes,
boolean_sat and boolean_unsat use 8 and 16; boolean_alias uses 16. Cache scopes
perform 24/48 checks per process and verify every Sat/Unsat/Sat restoration.

Predeclared target groups: coverage → free_views; equalities → views,
symbolic_views, offset_views; templates → cache_scopes; lazy rows → all three
boolean families. Report all/control instruction ratios on retained known pairs,
per-instance distributions, solved counts, and held-out 103 separately. A target
gain under 5% is inconclusive for enabling an option on performance grounds;
no lost solves or wrong answers are acceptable without an explicit revised
verdict. Report original-baseline results as well; control ratios alone cannot
hide common discovery/cache overhead. Report regressions and interactions.

Primary metric is whole-process `instructions:u`, CPU 2, a single counter with
at least 99.9% scheduling coverage. It includes client construction, solving,
every independent model check, subprocess startup and Python checking. Conflicts,
definitions, template hits/builds and refinement rows are diagnostics only.
Wall time is secondary and never a solver policy. Each arm has 10,000 conflicts,
100,000 decisions, no solver timeout, plus a 20-second outer cleanup cap. Cleared
NIXIE_/HEAP_PERF_ environment; PYTHONHASHSEED=0. Rotate arm order by seed.

Every cell is immutable in benchstore. Termination status is persisted before
parsing PMU output so an interrupted parse can resume without rerunning a cell.
Unknown, timeout, and unmeasured regions are explicit, excluded from solved-pair
ratios, and never counted as a match. Raw output and counter scheduling evidence
survive. Correctness calibration against CVC5 native SL and Z3 exact UF+array
precedes timing; references are not extra arms in this optimization experiment.

## Correctness calibration

All 102 small workloads completed with expected, independently checked answers
across the historical client, five candidate modes, CVC5 1.3.4 native SL and
Z3 4.16.0 exact UF+array: 150 snapshots. The full 32-cell cache-scope calibration
exceeded CVC5's 45-second outer cap; this is recorded as a reference limitation,
not agreement. That schema's two references instead checked all nine active
snapshots of a four-cell reduction, adding 18 agreeing snapshots. Its six Nixie
arms still used the full 32-cell workload. Formal performance cases remain
exactly as preregistered. Calibration performs no PMU measurements.

The Python harness has 25 passing tests, including corrupted values/duplicate
cells, wrong or missing check snapshots, missing diagnostics, unauthenticated
schemas, incomplete result matrices, and timeout recovery without fake counters.

## Verification before measurement

All-feature build, Clippy (`-D warnings`), formatting, and documentation
(`rustdocflags = ["-D", "warnings"]`) pass. The full nextest run passed 12,223
tests with 17 skipped; separate doc tests passed 114 with 31 ignored. Both
explicit CVC5 tests passed all 832 reference cases. Z3 4.16.0 parity returned
176 correct, one inconclusive, zero wrong answers. Build/test debug information
and incremental compilation were disabled to bound scratch disk use. An earlier
compile-only ENOSPC was resolved by moving this worktree's target directory to
the data volume; no failed test was hidden by that recovery.
The frozen-CLI perf landing gate passes: conflicts 1.000, decisions 1.000
(nine nontrivial pairs), secondary wall ratio 0.99, three agreeing trivial
external cases. Baseline CLI is cached `40851e3e` (cb50c87e changed only study
files); no verdict loss.

The feature was measured at `16e323ec` against the clean baseline library.
The later integration commit `fa7a2d36` also contains concurrently landed CP,
FSM and array fixes. It passed every gate again: 12,243 nextest tests, 17 skipped;
114 passing doc tests, 31 ignored; all 832 CVC5 cases; Z3 4.16.0 parity 176 correct,
one inconclusive, zero wrong; perf-gate conflicts and decisions 1.000, secondary
wall 0.99. Build, Clippy, formatting and documentation are clean. Integration
builds used CPUs 4–7 while the frozen experiment stayed on CPU 2. Its release
CLI and verification evidence are cached under `precompile/fa7a2d36/`.

Main was fast-forwarded to the checked integration with unrelated dirty files
preserved byte-for-byte. The experiment continues to use the exact frozen
`16e323ec` client and harness; it does not attribute concurrent changes to heaps.

## Results

All **1,782 cells** completed exactly once. Every arm solved **275/297**
complete workloads (187 Sat, 88 Unsat); its other 22 workloads were Unknown.
No wrong answer and no lost or gained solve occurred. All 132 Unknown cells
belong to the two cache-scope cases: 108 completed with a backend Unknown and
24 hit the outer cap. Every PMU sample was available; partial Unknown costs
are excluded from every ratio, not treated as completed work or agreement.

The all-options arm uses **52.1% fewer instructions** than the original baseline
on 250 shared pairs at seeds 0–9 (ratio 0.4794); held-out 103 gives 0.4682 over
25 pairs. The original ten cases remain neutral (0.9929, held-out 0.9927).
These aggregate baseline numbers do not replace the individual controls:

* Coverage: all/no_coverage **0.1352** on its 30 target pairs, held-out
  **0.1389** on three. This meets the benefit bar: about **86.5% less work**.
* Equality propagation: all/no_equalities **0.3802** on 70 target pairs,
  held-out **0.3537** on seven. This meets the bar: about **62.0% less work**.
* Templates: no complete target pair. Across other known pairs the ratio is
  **0.9999**, neutral. In the completed-but-Unknown `cache_scopes-8`, seed 0,
  caching builds eight templates instead of 128; both arms have the same
  5,220 conflicts and 3,970,597 propagations. This proves construction reuse,
  **not an end-to-end speedup**. Keep the finding: increasing this symbolic
  offset/scope workload under the same caps will not isolate construction cost;
  investigate backend arithmetic/scoped rechecking before retrying it.
* Lazy Boolean rows: all/eager **1.0197** on 50 target pairs, held-out
  **1.0237** on five. It saves work on the satisfiable alternatives, but loses
  on contradictory alternatives and especially the alias example (median
  290.80M versus 242.83M instructions). The overall target verdict is negative;
  a favorable satisfiable subcase does not justify enabling it globally.
  The alias case installs all 16 rows over 16 refinement rounds, ending with
  the same 256 definitions as eager encoding. It saves no definitions and pays
  for repeated solves/validation. The unsatisfiable alternatives need eight
  rounds; the satisfiable alternatives need none. Avoid retrying a global lazy
  default based only on the favorable zero-round cases; equivalent heaplets and
  repeated candidate rejection are the concrete remaining targets.

Baseline and control distributions (minimum, median, maximum), solved counts,
and diagnostics are in [the CSV](2026-09-22-heap-four-optimizations.csv).
The tables below report medians over all eleven seeds; the paired ratios keep
seeds 0–9 and held-out 103 separate. No wall time selected a solver policy.

| Case | Baseline | All | No coverage | No equalities | No cache | Eager |
|---|---:|---:|---:|---:|---:|---:|
| allocate-4 | 230.56 (11/11) | 230.66 (11/11) | 230.63 (11/11) | 230.63 (11/11) | 230.61 (11/11) | 230.60 (11/11) |
| allocate-16 | 378.31 (11/11) | 378.47 (11/11) | 378.35 (11/11) | 378.35 (11/11) | 378.45 (11/11) | 378.44 (11/11) |
| alias-4 | 227.00 (11/11) | 226.20 (11/11) | 226.19 (11/11) | 227.05 (11/11) | 226.19 (11/11) | 226.20 (11/11) |
| alias-16 | 236.40 (11/11) | 227.99 (11/11) | 228.01 (11/11) | 236.49 (11/11) | 228.02 (11/11) | 228.03 (11/11) |
| values-4 | 226.74 (11/11) | 226.76 (11/11) | 226.78 (11/11) | 226.79 (11/11) | 226.79 (11/11) | 226.80 (11/11) |
| values-16 | 233.44 (11/11) | 233.35 (11/11) | 233.43 (11/11) | 233.43 (11/11) | 233.34 (11/11) | 233.40 (11/11) |
| permutation-4 | 227.45 (11/11) | 226.79 (11/11) | 227.49 (11/11) | 226.78 (11/11) | 226.76 (11/11) | 226.79 (11/11) |
| permutation-16 | 240.08 (11/11) | 233.38 (11/11) | 240.27 (11/11) | 233.39 (11/11) | 233.38 (11/11) | 233.33 (11/11) |
| negative-4 | 226.88 (11/11) | 226.92 (11/11) | 226.93 (11/11) | 226.93 (11/11) | 226.91 (11/11) | 226.92 (11/11) |
| negative-16 | 230.99 (11/11) | 231.05 (11/11) | 231.05 (11/11) | 231.06 (11/11) | 231.03 (11/11) | 231.00 (11/11) |
| views-8 | 331.39 (11/11) | 237.29 (11/11) | 237.31 (11/11) | 264.58 (11/11) | 237.35 (11/11) | 237.32 (11/11) |
| views-16 | 698.76 (11/11) | 249.12 (11/11) | 249.16 (11/11) | 333.44 (11/11) | 249.15 (11/11) | 249.12 (11/11) |
| views-32 | 5188.79 (11/11) | 274.59 (11/11) | 274.51 (11/11) | 438.41 (11/11) | 274.68 (11/11) | 274.59 (11/11) |
| free_views-8 | 832.25 (11/11) | 253.32 (11/11) | 832.26 (11/11) | 253.29 (11/11) | 253.30 (11/11) | 253.23 (11/11) |
| free_views-16 | 2878.85 (11/11) | 316.50 (11/11) | 2879.04 (11/11) | 316.47 (11/11) | 316.33 (11/11) | 316.50 (11/11) |
| free_views-32 | 8460.76 (11/11) | 733.17 (11/11) | 8458.88 (11/11) | 733.05 (11/11) | 732.96 (11/11) | 732.98 (11/11) |
| symbolic_views-8 | 5632.55 (11/11) | 306.70 (11/11) | 308.98 (11/11) | 2212.49 (11/11) | 306.94 (11/11) | 306.80 (11/11) |
| symbolic_views-16 | 39830.08 (11/11) | 383.20 (11/11) | 384.82 (11/11) | 13444.95 (11/11) | 383.22 (11/11) | 383.25 (11/11) |
| offset_views-8 | 291.74 (11/11) | 233.29 (11/11) | 235.87 (11/11) | 239.59 (11/11) | 233.36 (11/11) | 233.25 (11/11) |
| offset_views-16 | 553.25 (11/11) | 239.60 (11/11) | 245.34 (11/11) | 289.57 (11/11) | 239.95 (11/11) | 239.63 (11/11) |
| cache_scopes-8 | — (0/11) | — (0/11) | — (0/11) | — (0/11) | — (0/11) | — (0/11) |
| cache_scopes-16 | — (0/11) | — (0/11) | — (0/11) | — (0/11) | — (0/11) | — (0/11) |
| boolean_sat-8 | 231.24 (11/11) | 226.59 (11/11) | 226.58 (11/11) | 226.58 (11/11) | 226.59 (11/11) | 231.41 (11/11) |
| boolean_sat-16 | 244.37 (11/11) | 227.30 (11/11) | 227.17 (11/11) | 227.25 (11/11) | 227.20 (11/11) | 244.76 (11/11) |
| boolean_unsat-8 | 230.15 (11/11) | 231.41 (11/11) | 231.43 (11/11) | 231.41 (11/11) | 231.35 (11/11) | 230.31 (11/11) |
| boolean_unsat-16 | 242.09 (11/11) | 249.25 (11/11) | 249.27 (11/11) | 249.24 (11/11) | 249.15 (11/11) | 242.41 (11/11) |
| boolean_alias-16 | 273.35 (11/11) | 290.80 (11/11) | 398.44 (11/11) | 290.82 (11/11) | 291.44 (11/11) | 242.83 (11/11) |

Median millions of instructions among known answers; Unknown costs excluded.

| Comparator | Subset | Seeds | Pairs | All / comparator | Lost | Gained |
|---|---|---|---:|---:|---:|---:|
| baseline | all | 0-9 | 250 | 0.4794 | 0 | 0 |
| baseline | all | held-out-103 | 25 | 0.4682 | 0 | 0 |
| baseline | original | 0-9 | 100 | 0.9929 | 0 | 0 |
| baseline | original | held-out-103 | 10 | 0.9927 | 0 | 0 |
| no_coverage | all | 0-9 | 250 | 0.7737 | 0 | 0 |
| no_coverage | all | held-out-103 | 25 | 0.7764 | 0 | 0 |
| no_coverage | original | 0-9 | 100 | 0.9966 | 0 | 0 |
| no_coverage | original | held-out-103 | 10 | 0.9965 | 0 | 0 |
| no_coverage | target | 0-9 | 30 | 0.1352 | 0 | 0 |
| no_coverage | target | held-out-103 | 3 | 0.1389 | 0 | 0 |
| no_equalities | all | 0-9 | 250 | 0.7615 | 0 | 0 |
| no_equalities | all | held-out-103 | 25 | 0.7461 | 0 | 0 |
| no_equalities | original | 0-9 | 100 | 0.9959 | 0 | 0 |
| no_equalities | original | held-out-103 | 10 | 0.9953 | 0 | 0 |
| no_equalities | target | 0-9 | 70 | 0.3802 | 0 | 0 |
| no_equalities | target | held-out-103 | 7 | 0.3537 | 0 | 0 |
| no_cache | all | 0-9 | 250 | 0.9999 | 0 | 0 |
| no_cache | all | held-out-103 | 25 | 0.9999 | 0 | 0 |
| no_cache | original | 0-9 | 100 | 1.0000 | 0 | 0 |
| no_cache | original | held-out-103 | 10 | 1.0001 | 0 | 0 |
| no_cache | target | 0-9 | 0 | — | 0 | 0 |
| no_cache | target | held-out-103 | 0 | — | 0 | 0 |
| eager | all | 0-9 | 250 | 1.0040 | 0 | 0 |
| eager | all | held-out-103 | 25 | 1.0049 | 0 | 0 |
| eager | original | 0-9 | 100 | 1.0000 | 0 | 0 |
| eager | original | held-out-103 | 10 | 1.0000 | 0 | 0 |
| eager | target | 0-9 | 50 | 1.0197 | 0 | 0 |
| eager | target | held-out-103 | 5 | 1.0237 | 0 | 0 |


The raw immutable records, every command, hashes, versions, scheduling evidence,
program inputs and outputs remain under
`precompile/16e323ec/benchmark/{runs/heap-four-optimizations-v1,heap-four-optimizations-v1}/`.
`analyze_next.py` authenticates complete cell coverage, revision/host/config/binary
provenance, expected answers and every completed Sat snapshot again before
producing the checked-in CSV. No cells were rerun or replaced.



## Default decision and fresh replay plan

The completed seeds 0–9 show lazy/eager = 1.0197 on the 50 Boolean target
pairs, including a substantial Boolean-alias regression. Held-out 103 gives
1.0237. Lazy refinement did not meet the preregistered benefit bar: keep the
implementation available but make it opt-in. Template caching preserves the
backend encoding/trajectory while avoiding redundant construction; retain it,
but its workload limits do not establish a throughput benefit.

Before any new measurement, preregister a replay of baseline, all, and eager on
all 27 cases at fresh seed **104**: 81 cells, the same frozen `16e323ec` client,
same limits and independent checks. No old cells are rerun. `--eager-replay`
selects this matrix; `--library-revision` records the actual frozen library
separately from the runner's newer source revision. This checks the selected
eager configuration, rather than presenting hindsight selection as a new gain.
The production change after the first matrix is `lazy_boolean: false`
in the default options. The benchmark client explicitly sets every option, so
its eager arm is the exact selected solver configuration. Repeat all landing
gates for the default change.


### Fresh-seed result

All **81 replay cells** completed once at seed 104, with 25/27 complete solves
in each arm, six Unknowns on the same scope cases, and no wrong answer or lost
solve. Lazy/eager is **1.0238** on the five Boolean target pairs; the alias case
is again 290.70M versus 242.74M instructions. The negative lazy verdict survives
replay. The selected eager configuration uses **0.4796** of baseline instructions
on the 25 shared solved cases (about **52.0% less**). This one fresh-seed check
validates the selection; it does not replace the ten-seed distributions above.

The [replay CSV](2026-09-22-heap-four-eager-replay.csv) contains all cases and
arms. Raw data are under
`precompile/591f9e69/benchmark/{runs/heap-four-eager-replay-v1,heap-four-eager-replay-v1}/`.
Source revision 591f9e69 is the replay harness and preregistration; the manifest
explicitly records candidate library 16e323ec and baseline library cb50c87e.
Measured binaries and policies remained frozen throughout both matrices.


### Final landing verification

After changing the default to eager, every gate passed again: all-feature build,
Clippy with warnings denied, formatting, documentation with warnings denied,
**12,243/12,243 nextest tests** (17 skipped), **114 doc tests** (31 ignored),
all **832 CVC5 reference cases**, and Z3 **4.16.0** parity (**176 correct,
one inconclusive, zero wrong**). The final frozen-CLI perf gate reports
**1.000 conflicts and decisions**, secondary wall ratio **1.00**, nine nontrivial
pairs and three agreeing trivial cases. Heap semantics, proof/Unknown boundaries,
and the independent validator are unchanged by the default decision.
