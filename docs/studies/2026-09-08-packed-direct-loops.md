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

## Result: iterator cost confirmed, overall advancement rejected

Clean committed candidate `cca3ff8ca0bee491b39afcd4c85dd4a41f35a703`, source
tree `3a4455480e74ccd46b7c7c83e0b36dd59c3f4334`; portable release binary
SHA-256 `c7452f4b19c0f008ce620a4bdec61552aecb0ad46c60d7530ec52d7b4e6b5031`.
Rust 1.96.0 / LLVM 22.1.2, no RUSTFLAGS/profile overrides. Cargo.lock SHA-256:
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.

The scalar buffer now uses an ordinary read/write loop. A separate loop
processes packed groups; compile-time macro expansion shares the exact clause
miss semantics without a per-member iterator dispatch. Packing eligibility
is inline, while actual repacking is cold. The old cursor is compiled only
for tests. Group/scalar ordering, membership, thresholds, conflict tails,
refreshed suffixes and search semantics are unchanged.

Exactly two new invocations ran. Both returned Unknown at 40,000 conflicts;
solved-at-cap remains 0/2. Their complete stdout is byte-identical to the
registered old-bulk controls, including all printed counters. CPU 10's active
`cpu_atom` user events had 100% scheduling coverage; inactive `cpu_core`
entries were excluded.

| Input | User instructions | User cycles | Cycles/conflict | Branch misses | Wall s | Record |
|---|---:|---:|---:|---:|---:|---|
| circuit | 13,072,997,070 | 5,738,304,381 | 143,457.6 | 69,728,536 | 1.319 | `5ee65f2ef723c070` |
| j3037 | 30,603,633,591 | 19,835,499,075 | 495,887.5 | 215,286,826 | 4.378 | `d1155d9b5a29c668` |

| Direct / old bulk implementation | Instructions | Cycles/conflict | Branches | Branch misses |
|---|---:|---:|---:|---:|
| circuit | 0.751848 | 0.663210 | 0.851525 | 1.025102 |
| j3037 | 0.700129 | 0.693838 | 0.818610 | 1.009030 |
| Geometric mean | **0.725528** | **0.678351** | — | — |

This fixed-search comparison confirms a substantial implementation cost:
27.45% fewer instructions and 32.16% fewer cycles/conflict in geometric mean.
Both implementation-relative gates pass. The **ordinary-cost constraint
fails on both inputs**, however:

| Input | Direct instructions / cached ordinary `2202f0e` instructions |
|---|---:|
| circuit | 1.084394 |
| j3037 | 1.033800 |

The ordinary comparison remains descriptive because grouping changes search;
it does not identify the remaining cost as storage, sorting or search. It
also does not justify a claim that this closes the Kissat gap. Per the
registration, do not advance, tune the packing thresholds, repeat cells, or
reinterpret the now-cheaper rejected prototype as the ordinary baseline.
No new scalar-grouped or reference runs were made. The grouped kernel is
removed again, with committed source and measurements archived.

## Verification and evidence

- All **756 SAT library tests** passed with all features. Eight applicable
  focused tests also passed with only `bcp-packed`, excluding diagnostic
  features. SAT all-feature/all-target clippy, ordinary SAT compilation,
  formatting/diff checks and the release build passed.
- The 32 ten-variable truth-table cases now compare all four combinations:
  old/direct loop and scalar/bulk skipping. Results, internal trail/watch/
  clause/stats/tick state and LRAT transcripts agree. The original seven SAT
  model checks and 25 independent UNSAT proof checks remain in the test.
- Every miss exit across literal polarities, conflict/requeue and backtrack
  compares direct bulk against the old bulk implementation as well as direct
  scalar against direct bulk.
- A new test forces each of **101 conflict-prefix boundaries** in a list with
  two packed groups and scalar entries, including changed-blocker suffixes.
  It compares exact state before and after snapshot restoration, real arena
  compaction, backtracking and another propagation.
- Enabled group, region and learned-clause collectors agree between old bulk
  and direct bulk. Storage removal, relocation and packing-growth tests pass.
- This rejected experiment was not landed as production code or taken through
  full workspace/parity release gates; it makes no production-fix claim.

Canonical cells are under
`precompile/cca3ff8/benchmark/runs/packed-direct-loops/`; both passed schema,
path and record-ID validation. The adjacent `benchmark/packed-direct-loops/`
directory contains raw outputs, PMU files, start/completion records, summaries,
runner, build metadata and verification logs. `source.bundle` contains both
experimental commits relative to `cb5aadf`; `source.patch` is the whole
prototype and `direct-loop.patch` isolates this rewrite. The bundle verifies
against main. The binary is cached; the temporary checkout and branch are
removed after landing this finding.

The result closes the proposed iterator-overhead follow-up. It does not
establish a benefit for native grouping on ordinary Nixie. Further work should
address costs in the ordinary core or use separately justified structural
compression, rather than continue refining this rejected grouped trajectory.
