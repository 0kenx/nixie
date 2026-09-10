# Production-kernel propagation work ledger

## Decision and source audit

Keep Kissat in the requested mode as the performance target. CaDiCaL is an
additional implementation reference, not a replacement target. The supplied
six-instance comparison motivates short break/crn anchors, but its raw runs,
versions and counter scopes have not been provided. RUSAGE_CHILDREN user time
is CPU user time, not wall time. Equal aggregate propagation counts do not
establish equal binary/long-clause work, or exclude search-work outliers.
Whole-process time divided by propagations also includes analysis, elimination,
allocation and every other phase; it is not time sampled inside propagation.

Nixie scheduling ticks charge one plus estimated logical watch-list lines per
processed literal, after the binary pass. They omit arena accesses, watch
moves and assignments. Changing that formula would change budgets and search.
CaDiCaL src/propagate.cpp and Kissat src/proplit.h additionally charge these
three events. Both estimate 128-byte lines, but their entry sizes and event
scopes differ: CaDiCaL Watch is 16 bytes on this host; Kissat uses 4-byte words
(one for binary, two for long watchers). Their totals are not interchangeable.
CaDiCaL also excludes lucky-phase propagation from its reported search totals.

Existing bcp-stats counters are process-global atomics and select the scalar
fallback. Other diagnostic branches compile out of normal builds. Introduce
an opt-in bcp-work feature with per-solver counters in both the production
kernel and fallback, without changing kernel selection or scheduling ticks.
No shared mutable counters, runtime gate, new unsafe code or solver policy.

## Ledger contract

Count dequeued literals separately from scans actually started: a step-limit
abort can dequeue without inspecting any list. Count actual binary visits
separately for primary and overflow, their assignments/conflicts, reached
nonempty long lists, visited watches, attempted clause reads (including
deleted headers), first-watch satisfaction, tail literal probes, true-tail
parking, moves, long assignments and conflicts. Derive blocker hits from
visited watches minus clause reads. Unvisited conflict tails are not visits.

Publish a reference-shaped estimate: started literals + 128-byte list-line
estimates + clause reads + watch moves + assignments. Use the actual Nixie
entry sizes and the two binary spans, never phantom binary counts. As in the
references, line estimates charge whole list lengths at entry, including an
unvisited suffix after an early conflict. Only reached long lists are charged.
This is a work estimate, not measured cache misses, CPU cycles, or a directly
comparable Kissat search_ticks value. Raw components remain available.

Scope is calls to this Solver's propagate method, including calls from
inprocessing and failed lucky attempts. Unlike the legacy propagation counter,
which lucky.rs restores after a failed attempt, this ledger retains that work. It excludes other propagation engines, conflict analysis,
allocation, clause maintenance, proof operations and formula loading. Snapshot
differences can measure caller-defined phases. It must never drive policy.

## Verification and bounded observation, registered before execution

Require hand-counted outcomes, aborted/partial scans, both binary spans,
unit resumption, compaction, failed-lucky counter rollback and independent
solver isolation. Extend existing
kernel/scalar equivalence tests to compare the ledger too. Run default and
all-feature SAT tests and the repository's full qualification gates before
landing. Inspect ordinary release code to confirm feature-off instrumentation
is absent. All-feature timings are ineligible as production speed measures.

After qualification, permit one ledger-enabled crn_11_99_u seed-0 diagnostic
solve, MAXC=10000000, NIXIE_SWEEP=0, otherwise the existing stats_solve defaults.
Reuse production stdout from record 0840cab28aa276cb (fd01d0b); main's SAT
source is identical before this change. Require byte-identical ordinary
stdout, including all search counters; extra ledger output goes to stderr.
Store the new observation once with source/binary/config identity. It is not
a performance comparison or a proof-checked UNSAT result. No new Kissat run,
full panel, tuning sweep, or claim that equal event counts predict speed.

## Implications for the next optimization

The tick blind spot is real, but the campaign also used whole-process PMU
instructions, cycles and branch misses. The last tail classifier removed
24.89% of instructions and increased wall by 6.97%; an unchanged semantic
ledger cannot explain execution cost by itself. See
[the measured rejection](2026-09-10-single-tail-classifier.md).

The 2026-09-07 inline-binary arm already tested a different, 12-byte tagged
watch representation and changed visit order. Its negative result is evidence
against repeating that exact arm, not proof that every integrated binary
representation must lose. A new attempt must identify the removed dependency
and price dispatch, maintenance, entry width and ordering. Raising the BVE
occurrence limit or disabling BVE changes the workload; propagation throughput
under that ablation is not an isolated measurement of the propagation loop.

## Implemented and qualified

Build `stats_solve` with `--features bcp-work` to emit the cumulative ledger
to stderr. Library callers read `solver.stats().propagation_work`; snapshots
are solver-local and copyable. The production scanner remains selected unless
another observer explicitly requests the legacy path. The feature adds no
unsafe code or global counters. Its 19 raw fields and derived blocker-hit and
estimated-tick totals never feed solver decisions.

Six focused regressions cover hand-counted live/deleted misses, both binary
spans and conflict replay, step-limit aborts, empty lists, Rayon isolation,
line rounding/wide sums, and failed-lucky rollback. Existing exhaustive
kernel/scalar checks compare the ledger as part of complete solver state,
including 1296 small-state cases and independent LRAT/model checks. The
ledger-only feature combination also passes the focused scanner tests with
ordinary 8-byte watchers; all-feature observers use 12-byte watchers and are
accounted at their actual size.

Qualification completed with the retained root Cargo.lock SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`:
workspace build, strict Clippy, formatting and docs passed; **10881 workspace
tests passed, 13 skipped**; **1013 default SAT tests passed, 1 skipped**;
**111 doc tests passed, 29 ignored**. The first workspace attempt stopped on
a missing external corpus in the new worktree. Linking the available primary
checkout corpora fixed access; the complete rerun passed. No test was skipped
to bypass that failure. Installed Z3 **4.16.0** parity gives **174 Correct,
1 Inconclusive**, zero wrong/error/timeout. The inconclusive case is
`array_unique.smt2`, where Z3 returns Unknown; it is not counted as a match.

The ordinary release `.text` is **994535 bytes, byte-identical** to cached
production fd01d0b, SHA-256
`56f7e4077946924c614a7749b94ee23a6b1be38fcd42dd279ce37acdb8bd91c3`.
Thus the feature-off executable contains no additional ledger machine code.
Whole-binary hashes differ; whole-binary identity is not claimed. The ledger
release has a distinct 998391-byte `.text` and its diagnostic output marker;
the ordinary release has no such marker. This audit uses binary sections,
not another solver execution or a timing comparison. Completed debug build
artifacts were deleted after qualification, recovering about 83 GB.

## Single crn observation

Qualified code landed as **38e4f53c**. The one registered capture is canonical
record **760297a9084a5f60**, with raw artifacts under
`precompile/38e4f53/benchmark/propagation-work-ledger/`. Complete ordinary
stdout is byte-identical to reused control **0840cab28aa276cb**: 87939
conflicts, 3817687 reported propagations, 13068482 scheduling ticks. No new
control, Kissat run, timing comparison or full panel was executed. Reported
UNSAT is retained as unknown/unverified in the canonical store; the observation
was not proof-checked. [All counts and identities](assets/2026-09-10-propagation-work-ledger.json)
are retained with this study.

The ledger counts **3826944** dequeues/scans, including **9257** dequeues
hidden by failed-lucky rollback in the legacy counter. No step-limit abort
occurred in this capture. Denominators below include those lucky attempts.

| Event | Count | Per started literal |
|---|---:|---:|
| Binary edge visits (primary + overflow) | 413688 | 0.1081 |
| Long-watch visits | 115235008 | 30.1115 |
| Clause lookups, including deleted headers | 42045160 | 10.9866 |
| Tail literal probes | 76240226 | 19.9220 |
| Watch moves | 25549265 | 6.6762 |
| Long-clause assignments | 3337228 | 0.8720 |

Blockers discharge **73189848 visits (63.51%)** without a clause lookup.
The lookup outcomes reconcile exactly: 18958 deleted/non-live, 3345236
first-watch satisfied, 9710052 true-tail parked, 25549265 moved, 3337228
assigned and 84421 conflicting. Tail scans inspect **1.9710 literals** on
average. Binary visits split into 276100 primary and 137588 overflow, with
252915 assignments and 4801 conflicts. Long lists are nonempty on 3656057
started literals; binary lists on only **152442 (3.98%)**.

The reference-shaped estimate is **84416613**, or **6.4596x** the old
scheduling ticks. Its components are 3826944 started literals, 179336 binary
list-line estimates, 9225765 long list-line estimates, 42045160 clause reads,
25549265 moves and 3590143 assignments. Neither estimate is cycles. The new
estimate omits separate charges for tail probes, as do the cited reference
formulas; their exact raw count is available. It must not be substituted for
Kissat search_ticks or used to claim a new relative-speed number.

### What this changes about the next lever

Long-watch processing dominates counted work on this short anchor. Moving
binary *entries* into the watch loop does not remove its 115 million long
visits or 25.5 million moves. Sparse binary lists do **not** bound the fixed
cost or cache pollution of probing the three binary-directory arrays on
every literal; those need hardware attribution before ruling the structure
out. An event-count estimate cannot establish a cycle share for either path.

The next implementation candidate is the narrow whole-watch-list engine:
complete assignments inside the long scan while retaining a separate call
boundary around that scan. This combines the archived complete engine's
removal of per-unit yields with the production kernel's narrower live state,
aiming to avoid the arena reload/register-pressure regression observed in
[the tail-classifier rejection](2026-09-10-single-tail-classifier.md). This
capture establishes 3.34 million long assignments where that boundary matters;
it does not measure the cost of the proposed replacement. Price call setup,
state commits and callbacks, inspect the generated dependencies, and use the
short break/crn anchors with a held-out check. Unchanged ledger totals would
be expected for an execution-only rewrite and are not a rejection criterion.
Kissat remains the wall-time target; CaDiCaL is an additional diagnostic
reference. No new engine or speedup is claimed in this instrumentation step.
