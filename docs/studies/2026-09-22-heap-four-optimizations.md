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

## Results

Pending the preregistered run and landing gates.
