# Empty long-watch propagation

## Registration

The closed complete engine saved instructions without establishing a wall
gain. Before another representation rewrite, remove unnecessary ownership
transfers on a trigger with no long watchers. The production driver currently
takes and restores its vector even when empty. Its scanner wrapper is inline
and already guards the actual scan call: this is **not** a claim that an empty
trigger calls the out-of-line watcher kernel. Earlier arena-locality and
single-exit tail-scan studies already argue against repeating those changes.

Move the existing tick calculation before vector extraction, then continue
for an empty list when the ordinary kernel is selected. Preserve binary-first
propagation, binary-conflict requeue, bounded-step behavior, phantom binary
ticks, saturating counters, and final conflict-free-prefix publication. Active
observers and the legacy test oracle keep their original empty-list path.
No unsafe code, watch selection, search policy, or new per-entry operation.
Kissat `src/proplit.h` and CaDiCaL `src/propagate.cpp` likewise charge the
trigger before scanning; an empty long list cannot skip binary implications.

Preflight: compare full solver state with the existing legacy oracle for empty
lists, reserved empty vectors, binary chains/conflicts, phantom-only lists,
stable/focused tick saturation, budgets, backtracking, and LRAT. Run the SAT
suite with ordinary and all features, strict SAT Clippy and formatting. Inspect
generated code before measurement: the empty path must bypass vector clearing,
restoration and drop handling, with no second list lookup on the nonempty path.
If this fails, stop without running a solver cost cell.

Budget: at most two new cost invocations, j3037 then (only after passing)
summle, using cached production controls instead of retiming them. Portable
release Rust 1.96.0 / LLVM 22.1.2 and retained lockfile
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
CPU 15 Atom, seed 0, MAXC=10000000, PRINT_MODEL=1, NIXIE_SWEEP=0,
NIXIE_DEFINITIONS=0; other study overrides cleared. Whole-process user
instructions are primary; grouped user cycles, wall, faults, switches and
off-CPU fraction are secondary. Warm input/binary, anonymous tmpfs output,
GNU time 1.10, emergency 300 s. No own build/test overlaps measurement.
Store every start and completion once; no repeat on a bad timing.

Reuse production j3037 record `0ec1f4bfcfe8f5f9` and summle record
`02d916e9af5fe4da`, both `fd01d0b`. Require identical complete stdout,
>=99.9% PMU coverage, zero major faults and <=5% off CPU. A screen advances
only with <=0.95 instructions and <=0.95 wall versus its retained control;
different measurement windows limit any causal wall claim. Validate any SAT
model independently. Unproved UNSAT is recorded unknown/unverified.
Reuse requested-mode Kissat context; no new reference runs. A negative uses
retained profiles and current assembly to account for remaining/introduced
costs; no extra profile or source tuning is licensed by this screen.

Source promotion additionally requires the full workspace build, nextest,
doctest, Clippy, fmt, documentation and installed Z3 4.16.0 parity gates.
Otherwise archive the source and commit the finding, with no solver change.

## Result: insufficient work removed; not promoted

One new cost invocation ran on candidate
`8d47c45f38ffba22a314018fcd0d26f6520170df`. The second input, further
variants and a new profile were not run. Production propagation is unchanged.

| j3037, seed 0, complete invocation | Cached production `fd01d0b` | Candidate | Candidate / production |
| --- | ---: | ---: | ---: |
| User instructions | 254596496994 | 251218933140 | 0.986734 |
| User cycles | 164287697694 | 171473201120 | 1.043737 |
| Wall seconds | 36.13 | 37.76 | 1.045115 |
| Conflicts | 330565 | 330565 | 1.000000 |
| Propagations | 323390316 | 323390316 | 1.000000 |

The 1.33% instruction reduction fails the registered 5% advancement bar;
there is no observed wall saving. This single comparison with a retained
control is neither a population speedup/regression estimate nor a statistical
neutrality claim. The requested-mode cached Kissat reference remains 18.04 s
on j3037 (`45a3c8f2e3057841`); this change does not close that gap.

Complete stdout is byte-identical to the control, SHA-256
`a904b7f02cd4dc6ac5abd11a0754072e9f32af0ab18409dc293edf1242c1cb9b`.
The reported UNSAT has no independent original-CNF proof in this cost run,
so canonical record **`2c9ac2c96ad4974b`** is unknown/unverified. Both arms
finish within the emergency cap with the same reported result.

The candidate records 37.37 s user / 0.18 s system, **0.556% off CPU**,
zero major faults, 64 involuntary and 413 voluntary switches, and 34112 KiB
peak RSS. All four grouped user events have 100% scheduling coverage. The
two constrained sleeping threads eligible for CPU 15 retain their identities
and exact schedstat runtime. Unconstrained foreign work and activity on other
cores remain visible in retained host snapshots (one-minute load about 14
before the run). The configured timing checks pass; they do not establish
shared-cache/frequency isolation or explain the observed cycle increase.

## Cost analysis and implications

The earlier [residual census](2026-09-10-residual-family-census.md) provides
an exact **213643006 nonempty long-list starts** on the same printed search
trajectory. Subtracting these from 323390316 propagations bounds empty-list
completions above by **109747310 (33.94%)**. It is an upper bound because
binary conflicts and bounded aborts can exit before a list starts. The same
capture offers **2095757035 watcher entries**, including conflict tails that
the scan might not reach. Neither count is a measured cycle share.

The code-generation check confirms a real removal. In the perf build, the
empty branches at `0x4b1c2` / `0x4b1ec` return to the next trigger at
`0x4aeaf`, before owner extraction at `0x4b1f2` and the three clearing stores
starting at `0x4b209`. The control clears the owner before charging ticks,
initializes cursor state, and traverses restoration and drop checks even for
an empty list. No watcher-kernel call was present in the old empty path, so
no such call saving is credited.

The candidate uses one indexed watch-row lookup, but reloads its length and
retains the old zero-length scan guard after extraction on the nonempty path.
That extra guard is a real introduced operation; this run does not isolate
its branch-prediction cost. The outer function is 3699 bytes with a 248-byte
local stack frame in the perf build. The binary loop, actual watch visits,
blocker/header dependencies, unit assignment and watch moves remain.
Full-process branches are 53305564689 and branch misses 2029321693;
these are not attribution to the new guard.

This explains the limited instruction result without inventing a causal
explanation for the wall observation: the removed ownership bookkeeping is
small relative to total executed work. Retained propagation flamegraphs in
the [cost review](2026-09-09-negative-results-cost-review.md) locate the
remaining scans; their different inputs/implementations cannot assign cycle
shares to this candidate. Another empty-list layout or branch annotation
screen is not justified by this result.

Combining this with the rejected complete engine is not automatically an
independent gain: keeping propagation views across triggers already targets
these ownership transfers. Its instruction saving and this 1.33% cannot be
added. A larger algorithmic change must reduce actual watcher/edge events or
their dependent dispatch, with binary-conflict ordering, budgets, phantom
ticks and final-prefix publication still explicit. Skipping empty triggers
does not license skipping an unvisited binary suffix or dropping tick work.

## Verification and retained source

Final candidate passes **1014 ordinary SAT tests and 1041 all-feature SAT
tests**, one existing skip in each suite, strict all-feature/all-target SAT
Clippy and workspace formatting. The added 32-case test compares full
clause/trail/watch/BIG/counter state, proof transcripts and propagation prefix
across binary conflicts, reserved empty vectors, additional phantom charges,
stable/focused saturation, budgets and backtracking, followed by root LRAT
unit flushing. Existing exhaustive state comparisons and independent LRAT
checks also pass. The new explicit phantom case adds ghost charges alongside
live binaries; it does not separately construct a trigger with only retired
edges, a narrower preflight than the registered phantom-only-list case.
There is no new unsafe code or shared mutable state.

Before code-generation inspection, the initial count-then-take source was
changed to borrow the watch slot once. The final ordinary suite was rerun
after that adjustment; the all-feature suite, Clippy and both binaries also
use the final source. No source tuning followed measurement. Full workspace
qualification and Z3 parity were not run for this rejected prototype; no
production source qualification is claimed.

The [source patch](assets/2026-09-10-empty-watch-fast-path.patch) applies to
registration `b74d015`. The cached source bundle requires that reachable
commit. `precompile/8d47c45/` retains both binaries, the compiler/lock identity,
source bundle/patch, tests, assembly/audit and once-only measurement evidence.
Release SHA-256:
`a2b016bf1b3a44dd6feb0ca6b78b7f60c222659f8055febc085295c05cb10161`;
perf SHA-256:
`7726aca8a250aa25e18401aa5b6e877f7dbca1c5cbb97ca8c9d64a3c9ba83c6f`.
The temporary worktree, branch, build tree and scratch files are removed;
cached benchmark records and binaries are retained for reuse.
