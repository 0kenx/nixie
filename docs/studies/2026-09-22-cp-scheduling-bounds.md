# CP bounds reuse and Z3 scheduling reference

The integrated candidate `23933fa6` uses **0.5450 times Z3's user CPU
instructions for ordinary solves and 0.5777 times for certified solves**
on the held-out scheduling grid (paired geometric means). It uses
0.6866/0.6924 times the preceding
Nixie version's instructions. Larger 8x16 cases still favor Z3 (ordinary
Nixie/Z3 1.5715); this is not a claim about hard industrial scheduling.
The optimization-only and integrated-source comparisons below are separate.

Cumulative feasibility now computes each immutable domain's exact minimum and
maximum at most once within a callback. Two lazy cache levels avoid allocation
for absent/zero-use tasks and non-cumulative queries. Singleton trials bypass
the cache without updating it, including all tasks sharing the trial variable.
The cache cannot survive a callback or a scope change. Event ordering, BigInt
arithmetic, half-open semantics, first witnesses, explanations, independent
model validation and the complete checked proof chain remain required.

The [pre-registration](../../bench/cp_perf/bounds_protocol.md) fixes the grids,
controls, acceptance bar and held-out seeds. A baseline instruction profile
attributed about 93% of samples on the large all-present callback to cumulative
feasibility, with repeated extrema scans prominent. Bounds-only selection
produced a callback instruction ratio of 0.8309 and ordinary end-to-end ratio
of 0.9670 relative to the preceding Nixie implementation. The latter is neutral
under the repository's 5% band. A subsequent sparse end-to-end profile identified
model evaluation as the next bottleneck; the second-stage protocol was written
before measuring local replay evaluation reuse.

## Reference and measurement

**The external performance reference is Z3 4.16.0.** All Nixie/Z3 figures are
paired geometric means of whole-process user CPU instructions, not elapsed
time. Ratios below one favor Nixie. Nixie before/after ratios are separately
identified and isolate implementation costs; they are not Z3 comparisons.
The earlier [borrowed-trial study](2026-09-22-cp-scheduling-perf.md) also compared
against preceding Nixie, not Z3.

The unchanged public Rust driver has SHA-256
`e15f17e802fccad51603c6e7dc2921bd32263e6578297be4eed7889be9834797`.
Both Nixie arms use the same external Cargo package, lockfile, compiler and
release profile with debug level 1 and default library features. This differs
from the workspace LTO CLI profile. Frozen binaries and immutable benchstore
records live under `precompile/<full-source-sha>/benchmark/`; raw stdout and
counter stderr are retained. All runs pin CPU 0 and require at least 99% PMU
coverage. No changed work is hidden behind a solver-only tick counter.

[`reference.py`](../../bench/cp_perf/reference.py) generates equivalent QF_LIA
for Z3: finite integer start domains, Boolean presences (including shared ones),
and exact cumulative load checks at every present task's start. With nonnegative
demands, any overload begins at such an event; the strict end inequality gives
half-open intervals. Every Z3 model is independently checked with arbitrary-
precision Python integers. Unknowns, missing values and invalid models fail the
run. Nixie's model/proof checks execute inside its measured process; the Python
check of Z3's extracted model executes outside Z3's measured process. This
asymmetry is explicit, not a claim of identical certification work.

There are seven admission/integration families, shapes 4 tasks x 4 starts and
8 x 16, two push/check/pop rounds, and ordinary/certified Nixie modes. All have
SAT witnesses; ample-capacity and forced-absence cases do not measure hard
packing, UNSAT search or scalable proof enumeration. The Z3 cells are reused
between the two Nixie modes. Callback-only diagnostics have no matching Z3 API
and are reported only as Nixie before/after measurements.

Baseline `df564313` contains the preceding borrowed-trial optimization. Snapshot
`1b6269ce` isolates bounds reuse; `c6e4d9c3` merges contemporary theory fixes and
is the exact-computation control for replay reuse. We report this intervening
source change rather than attributing unrelated work to CP. No search heuristic
is introduced: the unchanged computation is the control, and every paired
Nixie transcript must be byte-identical (ordered callback consequences and
premises, solver verdicts, conflicts, decisions and propagations).

## Optimization-only confirmation

The optimization-only snapshot is `ef63b45d`. Within one independent model
validation, it retains concrete Boolean watch evaluations for statement checks
and evaluates each additional consequence/premise at most once. It never reads
SAT phases as evidence, never omits a vocabulary or certificate check, and never
retains values across validations. Undetermined premises still fail closed.

Held-out seeds 10..19, geometric instruction ratios:

| Mode and shape | Previous Nixie / Z3 | Current Nixie / Z3 | Current / previous Nixie |
|---|---:|---:|---:|
| Ordinary, all cases | 0.7937 | 0.5352 | 0.6743 |
| Ordinary, 4x4 | 0.2035 | 0.1857 | 0.9125 |
| Ordinary, 8x16 | 3.0959 | 1.5426 | 0.4983 |
| Certified, all cases | 0.8344 | 0.5677 | 0.6804 |
| Certified, 4x4 | 0.2225 | 0.2047 | 0.9196 |
| Certified, 8x16 | 3.1287 | 1.5750 | 0.5034 |

The ordinary/certified **Nixie/Z3** ratios were 0.5399/0.5726 on selection seeds;
the held-out ratios confirm the finding. Reusing model evaluations alone,
compared with the merged bounds-only control, has held-out ordinary/certified ratios
0.6943/0.7002 (selection 0.6921/0.6979). The combined change reduces ordinary/certified
instructions by about 33%/32% against previous Nixie. Those percentages are
**not** reductions against Z3.

The callback diagnostic confirms a 0.8383 current/previous ratio on fresh
seeds (140 byte-identical partial-state transcripts). All-present and shared
presence families have ratios 0.3617 and 0.8084; the other families are neutral.
This is a Nixie component comparison, not a Z3 comparison.

No family regresses beyond the neutral band. Z3 still wins on the larger-case
aggregate and particularly on sparse 8x16 models: current ordinary Nixie/Z3 is
9.2955 there. The overall geomean must not hide this limitation. Conversely,
small constructed cases include startup/parsing cost and do not establish an
advantage on difficult industrial CP problems.

The [paired CSV](2026-09-22-cp-scheduling-bounds.csv) contains all 280 held-out
ordinary/certified comparisons, their ten-seed baseline distributions, candidate
and Z3 instruction counts. Each reference grid has 140/140 independently
validated Z3 SAT cells and 280/280 validated Nixie SAT cells, all within the
120-second cap. Selection and held-out reports reject every output mismatch;
all paired Nixie transcripts agree. No missing, censored or invalid-model cells
were dropped. The same Z3 cells are reused across candidate and ablation
comparisons. Bounds-only and second-stage measurements are retained as separate
immutable source revisions rather than overwriting the first experiment.

## Soundness audit

The producer's domains remain immutable throughout a callback. Cached extrema
borrow that snapshot, and both ordinary and forced-presence singleton trials
bypass cached values for every aliased start. Empty domains remain infeasible;
invalid indices remain undetermined. Absence and zero-duration/demand skips
precede bounds access. Lazy initialization changes no iteration, event ordering,
witness or explanation, including presence assumptions.

The model-replay cache is separate from the producer and is populated only by
the existing model evaluator. Formula watches are evaluated as formulas; the
cache cannot substitute a SAT assignment for a missing model value. Statement
oracles and table/domain/graph certificate checks still execute. Callback
push/fix/final-check/pop order is unchanged. The evaluator's live-tableau-read
flag is monotone within this invocation; replay never resets it, so reusing a
previous evaluation cannot erase its evidence. The cache is destroyed before
any later model, scope or check. Tests reject false/unknown formula premises,
exercise watched and unwatched negations, change the model between validations,
and reject foreign vocabulary even when its model value is true. Existing
forged-certificate regressions remain in place.

The independent optional-schedule oracles cover 43,740 partial states and
4,860 scoped public verdicts with imported/exported checked refutations. The
524,880 borrowed-versus-materialized trial comparisons now also reuse the
bounds context across trials and compare its unmodified state with a fresh
context after each trial. This checks against cache poisoning independently of
the outer solver. The Z3 harness has exact-model/parser regressions as well.

Variable durations/demands, variable capacity, stronger cumulative propagation,
and specialized scalable proof witnesses remain separately scoped follow-ups.
None is implemented or implied by these cost reductions.

## Verification record

All-features build and the five focused user-model replay tests pass; the
three independent Z3 harness tests pass. Z3 parity records installed 4.16.0:
176 decisive matches, zero wrong answers, one inconclusive `array_unique`,
no timeouts or errors. Its generated JSON and logs are retained with the
cached binary (the repository ignores generated parity JSON).

The preliminary full suite timed out after 600 seconds in
`re_running_the_search_on_an_unchanged_goal_converges`: 8,626 tests passed,
one timed out and 3,662 were not run after fail-fast. This run began before
the replay change and is not the final verification result. This existing
SMT-only test registers no user propagators, so neither changed path executes;
its previous landing log recorded 396.913 seconds. The timeout is retained as
evidence rather than reported as a pass or silently dropped. That run used the same solver budgets/assertions and the documented
600-second outer nextest allowance on this loaded host.

The performance landing gate passes against the frozen CLI: all 12 verdicts
match, with conflict and decision geomeans exactly 1.000 across the nine
nontrivial instances. The candidate CLI SHA-256 is
`33abfbc2988c89bde380eb5989c39bfef5e88855122db4dc10e1aace46ea822a`;
its hash was checked against the workspace binary after parity. The gate
used the cached immutable path, never a concurrently rebuilt Cargo target.
These SAT counters establish landing neutrality; the complete-work CPU
instruction study above measures the changed CP and replay work.

The same repeated-search regression passes on the final source in 306.040
seconds with the same 600-second outer cap. No test, solver budget, seed or
assertion was changed to obtain the pass; this diagnostic wall time is not a
performance claim for either optimization.

## Main integration confirmation

While verification ran, `df8017a2` landed transcendental arithmetic on main.
Merge snapshot `23933fa6` includes that feature and both optimizations above.
Its held-out confirmation reuses the original baseline and Z3 cells and again
has 280/280 byte-identical, independently validated Nixie SAT transcripts.
The [combined CSV](2026-09-22-cp-scheduling-bounds-combined.csv) records every
count. These are the integrated-revision figures:

| Mode and shape | Current Nixie / Z3 | Current / previous Nixie |
|---|---:|---:|
| Ordinary, all cases | 0.5450 | 0.6866 |
| Ordinary, 4x4 | 0.1890 | 0.9288 |
| Ordinary, 8x16 | 1.5715 | 0.5076 |
| Certified, all cases | 0.5777 | 0.6924 |
| Certified, 4x4 | 0.2080 | 0.9349 |
| Certified, 8x16 | 1.6043 | 0.5128 |

The difference from the pre-merge candidate is inside the 5% neutral band;
we do not attribute unrelated main changes to the optimization. Large sparse
ordinary cases remain 9.3285 times Z3's instruction cost. One startup attempt
stopped during store discovery when an unrelated finite-field record disappeared
between enumeration and reading. It ran no benchmark cells. The original log
is retained; restarting discovery did not repeat or discard any measurement.

The pre-merge full suite passed all 12,291 tests (17 skipped), including the
previously timed-out scope regression. Its explicit ignored certification
canary passed in 136.958 seconds. Clippy, formatting and warning-free rustdoc
also passed after integration; the combined full verification is recorded below.

The integrated callback diagnostic has ratio 0.8502 (140 identical callback
transcripts; no family exceeds 1.05). Integrated Z3 parity again has 176
decisive matches, zero wrong answers and one inconclusive `array_unique`.
The integrated performance gate also passes: all 12 verdicts match and the
nine nontrivial conflict/decision ratios are exactly 1.000. Its frozen CLI
SHA-256 is `3ffde84e8e6f8ae83fdb8903e1441661a737f10b4f26a0460621b3cc9d87fa7e`.

The first integrated full-suite attempt passed 8,637 tests and timed out on
the same convergence regression at 600.045 seconds; fail-fast left 3,693 tests
unrun. A replacement wrapper initially duplicated an existing timeout override.
That superseded run was stopped when the configuration audit found that the
first matching override would keep the old limit. Its log and configuration
are retained. The corrected wrapper changes the single existing convergence
override to 1,200 seconds and disables fail-fast; all other outer limits remain
600 seconds. It changes no test inputs, assertions, seeds or solver budgets.
These are verification-wrapper events, not failed or repeated benchmark cells.

The corrected integrated full-suite run passes **all 12,331 tests**, with 17
normally skipped tests. The convergence regression finishes in 299.005 seconds;
the complete run takes 480.666 seconds. Those times describe verification
only, not solver performance. The increased outer allowance changed no result
and was not needed by the completed run.

The integrated ignored certification canary passes (332.397 seconds). Final
Clippy (`--all-features --all-targets -- -D warnings`), formatting, warning-free
rustdoc, and all 114 doctests pass (31 doctests ignored). Rustdoc receives
`-D warnings` through `.cargo/config.toml`; `cargo test --doc --workspace
--all-features` runs doctests separately from nextest. All-features build,
12,331-test full suite, canary, parity and both performance gates are clean on
the integrated source. Compiler/environment metadata, exact temporary nextest
configurations, all completed/aborted verification logs, raw profiles and
reports are retained under the landed revision's
`precompile/<sha>/benchmark/cp-bounds-verification/`.
