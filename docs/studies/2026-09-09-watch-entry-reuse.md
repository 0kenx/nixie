# Persistence of individual satisfied watcher entries

## Registration

The whole-list reuse census failed below 0.6% coverage: either one watcher
changed or one blocker assignment died. This different granularity asks whether
many individual entries survive those events. It does not reopen the rejected
whole-list cache, AVX2 gathers or grouped kernels. No skipping mechanism or
search policy is implemented in this step.

Observe every visit of a fixed one-in-64 hash sample of literal keys. At a
completed scan retain each resulting watcher tuple (clause ID, arena reference,
blocker) with its observer-only assignment identity. At the next visit match
entries independently, allowing insertion, removal and reordering of other
entries. Match duplicate tuples one-to-one, never multiply one prior entry
into several matches. A reusable entry requires the exact tuple and the same
still-positive assignment stamp. Same-value reassignment is not survival.

Only actually visited prefixes count, including on conflict. A conflict scan
creates no replacement history; this deliberately conservative protocol uses
only completed scans. Clear histories at solve/scope boundaries; full solver
reset discards them. Bound histories at 262,144 entries per list, one million
total entries and 65,536 lists, and report every omitted entry/list. Existing
assignment-stamp code and its tests are reused from archived `164b5ec`.
Stamp overflow permanently disables reuse identification. There is no observer
state, hook or branch in ordinary builds.

The immediate blocker-hit branch has no clause-state effect. A true blocker
stays true during a propagation pass; no assignment is backtracked inside it.
Thus these exact matches identify entries whose usual visit would be a hit.
Kissat `src/proplit.h` and CaDiCaL `src/propagate.cpp` are the reference semantics;
Nixie's existing loop fixes all observable ordering, compaction and accounting.
An eventual active-entry representation would also need exact restoration on
backtrack, mutation invalidation and tick parity. This census does not price or
implement any of that machinery.

Report all-key and sampled actual watcher visits, independently reusable visits,
reusable contiguous-run bins, whole-list survival for context, and conflict-epoch
breakdowns. Count new certificates needed after completed scans separately from
certificates retained unchanged; this estimates renewal pressure without charging
an unnecessary rebuild as if it were an implementation requirement. Runs through
unvisited conflict tails are excluded. Instrumented time is not a cost result.

Advance only if BOTH si2 and circuit have >=40% reusable sampled visits overall
and after conflict 16,384, >=25% of all sampled visits in reusable runs of at least
four, and at least four reusable visits per newly established certificate, with
no omissions or unexplained trajectory differences. These are opportunity and
amortization gates, not speedup estimates. Failure rejects this conservative
completed-scan protocol; it is not a ceiling for all possible entry lifetimes.
No sampling, cutoff or lifetime tuning follows the result.

At most TWO new observer runs, based on current main `789263d`: si2-b03m and
circuit_48in, seed 0, MAXC=40000, CPU 10, ordinary CaDiCaL preset, model output,
explicit `NIXIE_SWEEP=0`; clear all other study overrides. No new reference or
control runs. Reuse exact stdout from `19d4d47` si2 record `b5af28e0b5de204b` and
`e15d0bf` circuit record `d9efc6203ff711eb`; source/binary differences do not support
cost comparisons, only byte-exact diagnostic identity. Independently check SAT
models; Unknown remains an unsolved prefix. Store each new cell exactly once in
`precompile/<sha>/benchmark/runs/watch-entry-reuse/` with raw evidence and the
conditional manifest. Use complete actual-watch visit counts as the observation
metric, never as a claim to cover all solver costs.

Before running: exact matching/multiplicity, churn, same-value reassignment,
conflict-prefix/run-bin and capacity tests; assignment lifetime/overflow tests;
paired observed/unobserved solves with explicit clause state, checked models
and LRAT proofs; all SAT tests, clippy, formatting and committed release build.
Archive a rejected observer and land its finding. Production source landing
requires the full workspace verification gates and fresh installed-Z3 4.16.0
parity. The throughput objective remains open.

## Result: entries survive, but renewal pressure fails the gate

Exactly two observer runs completed from clean committed source
**`d3aee8cf341b2fc75b877f49eb8a4f3062592bc1`**, a direct descendant of
registration **`059afd6`**. Binary SHA-256:
`ccff3dccb24252b31e859974e098d539705d6f9d2420f97101397a1184e846b3`.
Rust 1.96.0 / LLVM 22.1.2, portable release with `bcp-entry-reuse`, lockfile
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
No new control or reference run, timing comparison, threshold adjustment or
additional seed followed.

| sampled observation | si2-b03m | circuit_48in |
|---|---:|---:|
| actual watcher visits | 2,501,701 | 1,853,673 |
| independently reusable visits | 898,452 | 375,892 |
| reusable fraction, all epochs | **35.91%** | **20.28%** |
| reusable fraction after conflict 16,384 | **37.18%** | **18.18%** |
| visits in reusable runs of at least four | 882,986 (35.30%) | 274,395 (14.80%) |
| newly established certificates | 999,900 | 1,271,773 |
| reusable visits / new certificate | **0.899** | **0.296** |

Neither input reaches 40% overall or late coverage. Circuit also misses the
25% run-coverage gate. Both are far below four reused visits per new
certificate. **No entry-deactivation representation is built.** The coarse
whole-list result understated individual persistence, but the finer protocol
still does not qualify its expected bookkeeping burden. These are sampled
logical events, not instructions, cycle savings or measured implementation
costs. In particular, do not describe the 35.91% fraction as a speedup.

The census records 878,720 / 233,858 visits with no matching prior tuple, and
724,529 / 1,243,923 visits whose matching tuple lost its assignment identity
(si2 / circuit). Thus assignment expiration alone accounts for 67.11% of
sampled circuit visits. The renewal counts measure new certificates needed
at completed-scan boundaries; they do not charge every intervening watch
mutation or cost a production invalidation/indexing mechanism. Conversely,
not retaining certificates across conflict scans omits some potential reuse.
The result rejects the registered completed-scan protocol, not all possible
entry lifetimes or a universal performance ceiling. Do not tune this same
protocol on these observations.

There are zero capacity omissions and zero non-positive blockers at completed
sampled scans. Si2 / circuit cover 11,882 / 45,981 selected-key list visits;
all-key actual watcher totals are 161,699,940 / 100,167,701. The observer also
reproduces the archived whole-list census exactly: 6,383 / 10,318 reusable
whole-list visits, the same sampled denominators and all-key visit totals.
This provides a cross-version consistency check of sampling and prefix accounting.

## Verification and disposition

Si2 completes SAT at **39,246 conflicts**, with its model independently checked
against every original clause. Circuit returns budget **Unknown at 40,000
conflicts**; it is an unsolved prefix, not a verified verdict. Complete stdout,
including every printed counter and model, matches the registered cached
controls byte-for-byte. Solved-at-cap stays 1/1 and 0/1 respectively.
Canonical record IDs: **`b25d66da2b831af0`** and **`96bb00cb50b177b8`**.

All **1,017 SAT tests passed**, with one existing skip, after the final lifecycle
changes. Eight focused tests cover one-to-one matching of duplicate tuples,
independent survival under list churn, every tuple field, reassignment identity,
conflict-prefix run truncation, omitted-visit accounting, capacity bounds,
chronological retention, clear/resize, stamp saturation, and solve/push/pop/reset
boundaries. Twenty paired formulas use exhaustive truth-table classification,
explicit clause payload/metadata and trail/watch/stat/model equality, identical
LRAT transcripts, independent SAT-model checks and independent UNSAT LRAT checks.
During every observed real visit, an assertion checks that a claimed reusable
entry actually takes the ordinary blocker-hit path.

The audit confirmed that production SAT code does not clone and restore old
`Trail` snapshots, which could otherwise rewind an observer serial. Both trail
assignment entry points stamp assignments, and all unassignment paths invalidate
queries through the literal values. Full solver reset explicitly clears history
before clause IDs restart. This closes the lifecycle assumptions separately
from the per-entry matcher tests.

Strict all-target/all-feature SAT clippy, formatting and the committed release
build passed. The observer is archived, not landed in production; no full
workspace or SMT parity qualification is claimed. Main receives this finding.
Source bundle/patch (including the runner), binary identity, manifest, raw
reports/stdout/stderr, canonical schema records, validation summary and all
build/test logs are retained under
`precompile/d3aee8c/benchmark/watch-entry-reuse/` and
`precompile/d3aee8c/benchmark/runs/watch-entry-reuse/`. The temporary checkout and
its branches are removed after this document lands. The Kissat gap remains open.
