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
