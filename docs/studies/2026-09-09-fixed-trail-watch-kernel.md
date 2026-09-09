# A watcher kernel with a fixed assignment view

## Registration

The previous specialized-propagation experiment only removed optional branches;
it did not qualify. This changes the borrowing and execution boundary of the
long-watcher loop. A non-inlined scanner receives separate clause/watch stores
and an immutable trail view. It processes consecutive watchers until it produces
a unit, a conflict or completion. On a unit it saves read/write cursors and returns
the literal and reason by value; the driver performs the existing assignment,
reason diagnostic, LRAT and lazy-HBR operations, then resumes with a fresh view.
There is no borrowed clause or assignment pointer across those operations.

This targets the hot loop's live state, spills and repeated base reloads, not
watcher density or persistent satisfaction caching. Existing profiles identify
those costs, but PGO and slice rewrites previously showed that fewer instructions
need not save cycles. The extra unit-boundary calls may outweigh any gain.
There is no presumption that this architecture beats the existing loop.

Keep the exact current blocker test, eager watched-pair normalization, literal
scan order, satisfied-tail parking, unassigned-tail movement, compaction, conflict
tail and reason order. BIG propagation and phantom tick accounting stay unchanged.
Bounded propagation, LRAT and lazy HBR remain supported. Active BCP diagnostics or
observers use the original loop so their per-entry reports remain exact; ordinary
builds can eliminate that fallback. Profiling's outer timer still covers both.
Tests select the original loop as an independent state oracle even when all
features are enabled. No new unsafe code, solver heuristic or tick formula.
Kissat `src/proplit.h` and CaDiCaL `src/propagate.cpp` are semantic references.

Use cached **`19d4d47`** as the exact scalar engineering control. Current main
`c174dbf` has no differences in Cargo configuration or the compiled SAT/core/proof/
time/test-corpus sources, verified before implementation. Use the same lockfile,
compiler and ordinary portable release profile for treatment, from a clean
committed descendant of the registration. Pin source and binary hashes. This
avoids another control build, not the fresh paired cost observations below.

At most FOUR new cells: circuit scalar then kernel, seed 0, MAXC=40000, CPU 10,
CaDiCaL preset, model output, explicit `NIXIE_SWEEP=0`, all other study overrides
cleared. Whole-invocation user instructions are primary; user cycles/conflict
must decrease by at least 5% with non-increasing instructions and identical
complete stdout to advance. Only then run si2 kernel then scalar. The four-cell
geomean must have cycles/conflict <=0.95 and instructions <=1.00, and neither
si2 ratio may exceed 1.03. One active PMU, >=99.9% coverage; record every cell once
under `fixed-trail-watch-kernel`, including immediate subprocess completion.
A 300-second emergency timeout is not a policy. SAT models are independently
checked; budget Unknown remains an unsolved prefix. Report solved-at-cap. No
inline, cursor, chunk-width or dispatch tuning follows observed results.

This small screen can reject, not establish broad performance merit. No new
Kissat or CaDiCaL runs; their cached mode-matched gap remains reference context.
Before measurement: exhaustive small propagation-state comparisons, explicit
unit/resume/conflict-tail and backtrack/budget tests, checked-model/proof paired
solves, instrumentation-fallback coverage, all SAT tests, clippy, formatting and
the committed release build. A source landing additionally requires the full
workspace build/nextest/doc-test/clippy/fmt/doc gates and fresh installed-Z3 4.16.0
parity. Failure archives the kernel and lands the finding on main.

## Result: below the cost gate; kernel archived

Only the first two registered cells ran. The fixed-trail kernel did not meet
the 5% cycles/conflict advancement gate, so si2 was not run. No cursor, inline,
dispatch or chunk-size variants followed. Production propagation remains
unchanged. This screen does not establish broad performance merit or a floor
on what a different propagation architecture could achieve.

| circuit, seed 0, 40,000-conflict cap | Scalar `19d4d47` | Kernel `d7a77da` | Kernel / scalar |
|---|---:|---:|---:|
| Whole-invocation user instructions | 12,064,003,189 | 11,954,763,092 | 0.990945 |
| Whole-invocation user cycles | 4,981,073,094 | 4,907,586,627 | 0.985247 |
| User cycles/conflict | 124,526.827 | 122,689.666 | 0.985247 |
| Branches | 2,677,288,238 | 2,692,544,808 | 1.005699 |
| Branch misses | 61,542,806 | 61,839,262 | 1.004817 |
| Reported verdict | Unknown | Unknown | — |
| Solved at cap | 0/1 | 0/1 | unchanged |

Instructions fell 0.91% and measured cycles/conflict fell 1.48%, below the
registered advancement threshold. This is one bounded pair, not an estimated
population effect or a statistically established neutral result. The cost of
yielding each unit, scanning and resuming is included. The experiment does not
separately identify call overhead versus reduced live state; do not infer a
successful spill reduction from the architecture alone. The measured branch
and miss counts both increased slightly. The isolated borrowing boundary does
not produce a qualifying whole-invocation saving in this implementation.

Both complete stdout files are byte-identical, including all printed search
counters, and also match the previously cached circuit prefix. Their SHA-256
is `abf7160aba5efe114034ca76964f868cd3191a7c0d969bf4db887ad225368b4d`.
Unknown at the cap remains unsolved; there is no SAT-model or UNSAT-proof
claim for these measurement cells. CPU 10 was pinned before perf started;
`cpu_atom` supplied all four events at 100.00% coverage and `cpu_core` was
not counted. Secondary wall times were 1.219 / 1.119 seconds; they are not the
decision metric. No new reference-solver runs or repeat cells were used.

## Correctness checks and reproducibility

All **1,014 SAT tests passed, one skipped**, with all features enabled, after
correcting one new test fixture. The five new tests cover 1,296 combinations
of small assignment states, watch orientations, HBR and propagation budgets,
followed by backtracking; a direct unit/resume/conflict-tail case; observer
fallback selection; inprocessing interaction; and paired solves on 24 generated
formulas with exhaustive truth classification, model checks, identical proof
transcripts and independent LRAT verification of UNSAT cases. They compare
clause contents/metadata, trail, watches, BIG, solver counters, propagation
prefix and abort state, ticks and relevant inprocessing marks with the original
loop. SAT clippy with all features/targets, workspace formatting, and the clean
committed ordinary release build also passed.

The initial direct test expected a chain of units during one trigger's watch
scan, but placed two intended unit literals in the unwatched tail. An undefined
tail correctly moves a watch, so the conflict occurred later on a different
clause. Running both implementations before the expectation assertion showed
identical conflicts and complete compared state. Putting the intended units in
the watched pair corrected the fixture; no production correction was needed.
The original failed run and the separate original-loop confirmation are retained
alongside the passing logs. HBR's arena/BIG growth occurs after the scanner
returns and before a fresh borrow; watched-list order, eager normalization,
compaction and the unvisited conflict tail match the original loop. These
checks qualify the bounded experiment, not a production source landing. The
rejected source did not run the full workspace or fresh Z3 qualification gates.

Registration: `710beda2d8af888016b5f539e29deccb410404bb`.
Candidate: `d7a77da4a196fb96aa40ee1ec72e855bd83dcd12`, cached as
`precompile/d7a77da/stats_solve`, binary SHA-256
`1f4f0b86f2837a571b8322d3bca9b0d8640596b0fa86d7d947cb696e19af09e2`.
Control: `19d4d47a04b37c4e1e98f3a508d713fd9da06ec6`, binary SHA-256
`3cb1f6e64843d5730867d34e2f1264dd14adba2ee2b0654a70876f9fd5887883`.
Both use the same ordinary release configuration and dependency lock
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`,
Rust 1.96.0 / LLVM 22.1.2, with no native-target or custom Rust flags.

Canonical records under each commit's `benchmark/runs/fixed-trail-watch-kernel/`
are scalar **`fae61bbc99926510`** and kernel **`811e3a93ee8184af`**. Raw perf,
stdout/stderr and immediate subprocess completion records live under the
corresponding `benchmark/fixed-trail-watch-kernel/` directory. The candidate
directory also preserves the manifest, runner, source patch and verified source
bundle (requiring the registration commit), compiler/lock/binary identity,
qualification logs and independently recomputed record/PMU/output/ratio checks.
The experimental worktree and temporary branches were removed after archival.

## Cost-driven follow-up

The [two-phase stable-filter kernel](2026-09-09-two-phase-watch-kernel.md)
reuses this borrowing boundary and state oracle, but changes the filtering
algorithm so the prefix/suffix invariants remove repeated compaction tests.
That combined implementation passes its separate two-input cost screen.
Its candidate flamegraph and generated-code analysis account for the remaining
costs. This does not change the failed gate above or isolate the original
kernel's contribution; the implementations were measured on different cells.
