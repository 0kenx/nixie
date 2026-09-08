# Separate packed and scalar propagation loops

## Registration

The [native packed-run screen](2026-09-08-packed-blocker-runs.md) rejected
`9d76e31`: bulk skipping removed repeated member work, but the implementation
still dispatched every scalar-buffer entry through a multi-state cursor.
The full grouped kernel was much more expensive than the cached ordinary
solver on both anchors, with changed search making that comparison context
rather than a causal estimate.

This is a fixed-search engineering follow-up. Start at committed `9d76e31`,
replace the shared per-member cursor with separate packed-group and scalar
loops, and keep the previous packing policy, group/scalar order, blocker
refresh rules, conflict tails, snapshots, stored clause order, budgets,
ticks, reasons and proof semantics exactly. The scalar append buffer uses
the ordinary in-place watcher loop. Group members with changed blockers still
append for the next visit; never revisit that suffix in the current pass.
Packing thresholds and storage format are unchanged. Do not add unsafe code
or a new search policy.

The old cursor implementation remains available only for differential tests,
so the new bulk kernel must agree on full internal state and LRAT transcripts,
including repeated propagation, conflicts/requeue, backtracking, grouping and
snapshot restoration. The ordinary scalar semantics are checked against
Kissat `src/proplit.h` and CaDiCaL `src/propagate.cpp`.

## Two-cell screen

Two new invocations only: circuit then j3037, new direct-loop bulk arm,
seed 0, 40,000-conflict cap, CPU 10, 300-second emergency timeout. Build
portable release `stats_solve` with `bcp-packed` from a clean committed tree;
set `NIXIE_SWEEP=0`, `NIXIE_PACKED_SCALAR=0`, and print the model. Reuse the
previous bulk cells `fc545d247db0c834` and `43cedb597d965bb1` as the exact-search
implementation controls. Full stdout must match those controls byte for byte.
No new scalar-grouped, reference or old ordinary-solver runs.

Primary: whole-process user instructions, including all new loop and packing
costs. Also capture user cycles/conflict, total cycles, branches/misses,
conflicts, ticks and solved-at-cap. Require nonmultiplexed PMU coverage and
validate SAT models against original inputs. Preserve/store every run once.

Reject any trajectory discrepancy. Advancing requires at least 20% fewer
instructions and cycles/conflict in geometric mean against the old bulk
implementation, no per-input increase above 5%, **and** instruction totals
below the cached ordinary `2202f0e` counts on both inputs (12,055,575,175 for
circuit; 29,603,064,159 for j3037). The latter is an engineering screening
constraint, not causal evidence that grouped search improves the ordinary
solver. A faster rejected prototype alone is insufficient progress toward
the Kissat objective.

A pass licenses further fresh-seed/corpus qualification against ordinary
Nixie, including matched controls for the changed grouping order. It does
not establish the value of bulk skipping versus scalar grouping or authorize
a default change. All workspace build/nextest/doctest/clippy/fmt/doc and
ordinary plus enabled Z3 parity gates are required before positive source
landing. A rejection removes this prototype and records evidence and the
remaining cost, without tuning or repeating these cells.
