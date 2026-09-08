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

## Result: rejected

Candidate `9d76e3180fab0b91a48739d7511d1a41f6c71e7c` was built from a
clean committed worktree. Its parent `cb5aadf` integrates the registration
and committed main; the intervening dispatch certificate fix does not change
this SAT example. Portable release binary SHA-256:
`5d81dffac889962d69fea7dce9c3a3911a1a8b5bb2b393e31b61d73e42fe9400`.
Rust 1.96.0, LLVM 22.1.2, no RUSTFLAGS/profile overrides; Cargo.lock SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.

Exactly four invocations ran, in the registered order. Each reached 40,000
conflicts and returned Unknown. Bulk/scalar stdout is byte-identical on both
inputs, including all printed search counters. Solved-at-cap is 0/2 in each
arm. CPU 10's active `cpu_atom` user PMU supplied all four events with 100%
scheduling coverage; the inactive `cpu_core` entries were not counted.

| Input | Arm | User instructions | User cycles | Cycles/conflict | Branch misses | Wall s |
|---|---|---:|---:|---:|---:|---:|
| circuit | scalar grouped | 19,448,450,465 | 8,042,594,931 | 201,064.9 | 69,577,070 | 1.869 |
| circuit | bulk grouped | 17,387,819,560 | 8,652,315,279 | 216,307.9 | 68,021,081 | 1.968 |
| j3037 | scalar grouped | 44,098,833,988 | 27,911,681,487 | 697,792.0 | 213,560,578 | 6.176 |
| j3037 | bulk grouped | 43,711,399,635 | 28,588,069,214 | 714,701.7 | 213,360,217 | 6.326 |

| Bulk / matched scalar control | Instructions | Cycles/conflict | Branch misses |
|---|---:|---:|---:|
| circuit | 0.894047 | 1.075811 | 0.977636 |
| j3037 | 0.991214 | 1.024233 | 0.999062 |
| Geometric mean | **0.941378** | **1.049706** | — |

The instruction gate passes narrowly (5.86% fewer); the required cycle
reduction fails, and circuit exceeds the 5% per-input cycle-regression limit.
The geometric-mean cycle result is inside the repository's neutrality band,
not evidence for a qualified regression estimate. It nevertheless fails the
registered requirement of a 5% reduction. There is no default change, repeat,
holdout, parameter search, or new Kissat invocation.

The cached flat `2202f0e` controls are only context: grouped bulk costs
1.4423x circuit instructions and 1.4766x j3037 instructions against them.
Grouping changes the search, so those ratios cannot isolate implementation
cost. They do prevent presenting the matched-control instruction saving as
an improvement over ordinary Nixie. The tick counts likewise describe the
new search, not the costs of packing or cursor maintenance; user instructions
cover the entire invocation, including those costs.

### What was implemented and verified

Groups use a native u32 buffer with one blocker/count header and eight bytes
per member, plus a scalar append buffer. Snapshots retain the native buffers
and repacking thresholds. A streaming cursor performs in-place compaction,
keeps changed-blocker members in the next-visit suffix, and preserves unvisited
group/scalar tails on conflicts. Every clause miss retains the current eager
normalization, replacement, reason, unit-proof and hyper-binary semantics.
The feature excludes all of this from ordinary builds. Both experimental
arms use the same storage, cursor and ordering; only positive-run skipping
differs. Diagnostic builds enumerate skipped members for exact observation.

Verification before the screen:

- Full SAT library run: 754 tests passed. The final observer-only test was
  then added; all eight focused tests passed with all features, and the seven
  applicable tests passed with only `bcp-packed`.
- Every abort position in a 100-watcher list; mid-group positive transitions;
  refreshed suffix non-revisitation; exact snapshot/group-threshold rollback;
  failed-pack growth gating; group/scalar deletion and real arena relocation.
- All miss exits, trigger requeue and backtracking across literal polarities,
  with 64-member groups; bulk/control trail, watches, clause database counts, stats
  and ticks agree.
- 32 independent ten-variable truth tables: seven SAT models checked against
  the input and 25 UNSAT LRAT proofs independently checked. Both arms agree
  on the checked state fields and proof transcripts.
- Enabled watch-group, region and learned-clause observers produce identical
  reports across a unit-then-bulk-skip sequence.
- SAT all-feature/all-target clippy, ordinary SAT compile check, formatting,
  diff checks and the release build passed. No production fix is claimed;
  the rejected feature was not landed or taken through full workspace/parity
  release gates.

### Evidence and next constraint

Result-store records under `precompile/9d76e31/benchmark/runs/packed-blocker-runs/`:

| Input | Scalar record | Bulk record |
|---|---|---|
| circuit | `107b7abe786bd64f` | `fc545d247db0c834` |
| j3037 | `274a708313f3d3da` | `43cedb597d965bb1` |

The adjacent `benchmark/packed-blocker-runs/` directory holds raw stdout,
stderr, PMU files, start/completion records, summaries, runner, build metadata,
verification logs and the committed source patch/bundle. All four canonical
records passed schema/path/ID validation. The binary remains cached;
the prototype checkout and branch are removed after recording this result.

The native representation does remove repeated positive-member work on
circuit, but that alone does not produce the required cycle reduction. Do not
retry these thresholds or present the scalar-grouped null as the ordinary
solver baseline. The implementation still funnels scalar-buffer entries and
individual group misses through a multi-state cursor. Separating those loops
and retaining the original scalar buffer loop would be a distinct engineering
hypothesis, requiring exact state identity to this prototype before reusing
its cells. It is not a measured improvement or a reason to retain this kernel.
Broader shared-satisfaction claims remain unproved.

## Evidence correction (2026-09-08)

The registration requested full state equality, but the implemented helper
compared `ClauseDatabase` using its custom `Debug` output. That output contains
counts, not individual clause literals or metadata. Trail, watch lists,
statistics, ticks and LRAT transcripts were compared; per-clause contents were
not directly compared by that helper. Earlier descriptions of these checks as
"full internal state" overstated their coverage. Independent model/proof checks
and the performance rejection remain valid; this correction does not establish
a propagation defect. Future representation experiments must compare every
clause's literal order and metadata explicitly, including activity bits.
