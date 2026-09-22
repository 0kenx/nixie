# Optional cumulative performance experiment

Pre-registered 2026-09-22, before collecting baseline or treatment cells.
Baseline source: 591f9e69 (the optional-task implementation is fa8c0675).

The candidate under investigation eliminates whole-model domain copies when
forcing one cumulative start candidate. Static inspection found copies both
in value filtering and inside nested presence-support tests. First collect an
instruction profile of the baseline; reject this target if copying is not a
material cost. Keep the propagation rules, visits, trial order, explanations,
BigInt arithmetic, independent validators, and proof contract identical.
Do not add cache state or change the SAT search policy.

Use pinned CPU 0 and `perf stat -x, -e instructions:u`, summing counted hybrid
PMU rows and rejecting missing counters. This covers process startup, model
construction, callbacks, domain copies, timetable construction, allocation,
validation, printing and destruction. It excludes kernel instructions; no
kernel-dependent mechanism is changed. Wall time is diagnostic only. Each
cell has a 120-second external safety cap, never a solver policy input.

Seven callback families: unknown independent admissions, all present, all
absent, shared admission, individually blocked admissions, 141-bit start
values, and four unrelated start variables per scheduled task. Sizes are
8 tasks x 8 starts and 32 tasks x 16 starts, with two scoped rounds each.
Public solver and certified solver cases use 4 tasks x 4 starts for each
family and two scoped rounds. Seeds 0..9 rotate value declaration order and
set the SAT seed; reserve 10..19 for fresh-seed confirmation after selection.
All solver cases have a known SAT witness; unknown callback results are
partial propagation states and never counted as solved SAT instances.

Gate: every paired output byte must agree (callback result, all consequences
and full ordered explanations; solver verdict and conflicts/decisions/
propagations). Also require the existing exhaustive optional-schedule oracles
and full repository verification gates. No heuristic is introduced, so the
unchanged implementation is the exact-computation control; a randomized
heuristic placebo would test a different claim. If trajectory identity fails,
stop and investigate; do not interpret an instruction ratio as an optimization.

Go bar: callback instruction geomean treatment/control <= 0.90, no family
geomean > 1.05, and public ordinary/certified geomeans <= 1.05. Report per-family
and per-mode ratios, baseline distributions, solved-at-cap, and all failed
cells. Within 5% is neutral. Do not generalize constructed CP workloads to
whole-solver speed. Fresh seeds must confirm the same bar. Performance cells
are immutable: use benchstore records, source/binary/harness hashes, host,
explicit compiler/build settings, command line, and the exact generated case
identity; reuse an existing cell. Baseline and treatment use the same driver,
external Cargo manifest, lockfile, build directory, release settings and CPU.
The external package allows compiling the driver against clean baseline
sources before this new example exists there; retain its manifest and lock
with the binary. Final example source is the identical measured driver.
