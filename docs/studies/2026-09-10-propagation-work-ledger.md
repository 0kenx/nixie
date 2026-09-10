# Production-kernel propagation work ledger

## Decision and source audit

Keep Kissat in the requested mode as the performance target. CaDiCaL is an
additional implementation reference, not a replacement target. The supplied
six-instance comparison motivates short break/crn anchors, but its raw runs,
versions and counter scopes have not been provided. RUSAGE_CHILDREN user time
is CPU user time, not wall time. Equal aggregate propagation counts do not
establish equal binary/long-clause work, or exclude search-work outliers.

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
inprocessing. It excludes other propagation engines, conflict analysis,
allocation, clause maintenance, proof operations and formula loading. Snapshot
differences can measure caller-defined phases. It must never drive policy.

## Verification and bounded observation, registered before execution

Require hand-counted outcomes, aborted/partial scans, both binary spans,
unit resumption, compaction and independent solver isolation. Extend existing
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
