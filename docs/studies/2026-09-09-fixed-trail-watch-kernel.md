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
