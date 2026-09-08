# Packed blocker runs

## Pre-registration

The order-preserving tile prototype still traversed most entries and paid
for mask repair and frequent suffix rebuilding; it cost 1.818x instructions.
The positive-certificate window also failed. The learned-clause census then
rejected broadly dropping expensive clauses: most of their work belonged to
clauses with some observed direct use. This experiment changes storage so
one true blocker can skip a physically contiguous group without per-entry
metadata traversal.

Under an explicit `bcp-packed` feature, retain a scalar append buffer and a
packed word buffer per populated grouped list. A group stores one blocker,
a member count, and `(clause ID, arena reference)` pairs. The blocker is a
literal of every member clause. Initial packing requires 64 scalar entries.
Repacking requires at least 32 entries of scalar-buffer growth since the
last attempt and at least as many scalar entries as packed members. Failed
packing attempts also advance that growth threshold. Group only multiplicities
of at least four. Sort by `(blocker, clause ID)`; leave smaller groups in the
scalar buffer. Shrinking groups may keep fewer members until a later repack.
No threshold tuning follows the measurements.

Process packed groups before the scalar entries present at list entry.
Refreshes that change a packed member's blocker append to the scalar buffer
for the next visit. Moves append to the new trigger's buffer. Preserve the
current group and all unvisited groups/scalar entries after a conflict, and
requeue the trigger. Every non-satisfied member uses the existing scalar
clause semantics, including eager watched-pair normalization, first-wins
replacement selection, explanations, LRAT, budgets and phantom tick counts.
The reference is Kissat `src/proplit.h` and CaDiCaL `src/propagate.cpp`.

Expose a **scalar grouped control** that uses exactly the same buffers,
packing, update rules and visit order but checks every member. The bulk arm
may skip members only while the shared blocker is actually true; positive
truth is monotone during a forward scan. Initially false/unassigned blockers
must be re-read as earlier members can assign them. No truth cache survives
backtracking. Full transcripts and state must match between bulk and scalar
grouped arms. Grouping can change the old flat solver's search, so the flat
baseline is context, not the control for the bulk-skipping claim.

All generic watch operations must see both buffers: addition, removal,
snapshots/restoration, clear, scope rollback, reference relocation, debug
audits and sweeping. Mutable flat access explicitly materializes the list.
No new unsafe indexing, truncated IDs/counts, or silent lost watchers.
Diagnostic features may enumerate skipped members so their logical counts
remain exact; those builds are not performance arms.

## Four-run rejection screen

Start at committed `3405dd3`; use a clean committed candidate with sweeping
explicitly disabled (`NIXIE_SWEEP=0`) in both arms to retain the user's
mode-matched scope. Build portable release `stats_solve` with `bcp-packed`.
Run circuit_48in64out scalar/bulk, then j3037 bulk/scalar: seed 0, 40,000
conflicts, CPU 10, 300-second emergency timeout. Four invocations total;
no new reference runs, tuning, repeats or profiling runs. Existing flat
`2202f0e` cells are descriptive context only.

Primary: whole-process user instructions, including packing, buffer
maintenance, parsing and cleanup. Target: cycles/conflict. Also report total
cycles, conflicts, ticks, branches/misses, verdict and solved-at-cap. Preserve
raw artifacts and use `benchstore.py` once per cell. Reject unavailable or
multiplexed PMU data as evidence. SAT models must satisfy the original CNF;
unverified UNSAT observations remain unverified in the store.

Reject on any grouped-arm trajectory/state discrepancy, or failure to reduce
geometric-mean instructions and cycles/conflict by at least 5%, or either
input regressing more than 5% on either metric. A passing one-seed screen
only licenses further testing; it is not a qualified default flip or a
Kissat-parity claim. A failed screen removes the prototype and records the
finding. A positive result still needs fresh-seed/corpus confirmation and
an assessment of the changed grouped search against the ordinary solver.

Before any positive source landing: exhaustive storage/compaction and
lifecycle tests, mid-group truth transitions, conflict-tail/requeue checks,
bulk/scalar full-state and proof identity, differential SAT/model checks,
all workspace build/nextest/doctest/clippy/fmt/doc gates, and ordinary plus
explicitly enabled Z3 parity. A soundness discrepancy blocks use regardless
of measured cost.
