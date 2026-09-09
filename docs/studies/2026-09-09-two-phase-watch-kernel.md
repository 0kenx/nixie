# Two-phase stable filtering with a fixed trail

## Registration and causal hypothesis

This combines the archived [fixed-trail kernel](2026-09-09-fixed-trail-watch-kernel.md)
with the stable-filter algorithm described in the
[negative-results cost review](2026-09-09-negative-results-cost-review.md).
The earlier kernel retained the repeated `write != read` test. Here the
no-removal prefix and compaction suffix are separate const specializations.
The first removed or moved watcher transfers to the suffix; a unit yield
retains the phase through the read/write cursors. The suffix cannot call
another phase, so call depth is bounded independently of input size.

The semantic references are the existing scalar loop, Kissat's `proplit.h`,
and Rust 1.96's `Vec::retain_mut` two-phase filter. The implementation adds
no unsafe code. Preserve blocker-hit behavior even on deleted clauses,
eager pair normalization, tail scan order, parking versus moving watches,
stable list order, unvisited conflict tails, binary implications, phantom
ticks, budgets, proof operations and HBR. The immutable borrow ends before
assignment or HBR can grow the stores. Active observers use the complete
scalar loop; an independent test switch selects that oracle.

Assembly inspection preceded solver measurement. On ordinary portable
`perf` builds of scalar `6d492a4` and the prototype, the scalar blocker-hit
path loads all three watcher words and the assignment-array base, then
compares read/write positions. The new prefix loads only the blocker and
uses the assignment-array base passed into the kernel. Neither specialized
loop has a per-entry read/write equality branch. The suffix still has
write bounds checks, and payload scans still spill live state around watch
moves. The prefix-to-suffix move transition compiles as a tail jump; the
rare deleted-reference transition uses a bounded call. No branch sample
is being interpreted as a measured misprediction or an eliminable fraction.

The tradeoffs are explicit: dispatch and calling conventions at units and
list entry, two compiled scan bodies (803 and 983 bytes in the inspected
prototype), and a combined propagation/scan body size of 5238 versus 4327
bytes, about 21% larger. Smaller per-kernel stack frames do not establish
lower total stack use or fewer executed spills. The qualified baseline
profile attributes 56.64% of cycles to propagation and the census reports
short learned scans (1.77 literals/payload). These facts justify pricing
watcher filtering; they do not predict the saving or prefix coverage.

## Bounded cost and profile protocol

At most **five new solver invocations**, each recorded once in benchstore
under `two-phase-watch-kernel` with immediate completion records. The
pre-existing profile and observer are reused. No new reference-solver run.
Use source-clean binaries with the same portable `perf` profile, Rust
1.96.0 / LLVM 22.1.2 and dependency lock SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
Control is committed `6d492a4`; the candidate is a committed descendant of
this registration. Cache both binaries and full source identities.

1. Control then candidate: exact cached `circuit.factored.cnf`, seed 1,
   MAXC=10000000, model output, CaDiCaL preset and `NIXIE_SWEEP=0`. Pin CPU
   10 outside perf; clear other study overrides. Measure complete-invocation
   user instructions, cycles, branches and branch misses with only explicit
   atom-PMU events. Require >=99.9% scheduling coverage for every event.
   A 300-second emergency timeout is not solver policy. Require identical
   complete stdout and independently check both SAT witnesses on both the
   factored and original CNFs. Unknown remains unsolved, not a verified match.
2. Capture **one candidate LBR profile**, whether the pair is positive,
   neutral or negative. Reuse the qualified period 10472903, 128-page buffer,
   CPU 10 and `{cpu_atom/cycles/uS,cpu_atom/instructions/u}` group, with
   sampled CPU and running-time reads, no outer stat. Require no loss or
   throttling, >=99.9% coverage in every read, all samples on CPU 10,
   >=99.9% user-mode and resolved self cost, and >=1000 raw cycle samples
   for a broad component diagnosis. Counter reads are sampled-prefix costs,
   never complete-solve measurements. Separate prefix, suffix and outer
   propagation by symbol addresses, retain the interactive flamegraph and
   inspect expensive paths. Failure remains a failed capture; do not rerun.
3. Only if the factored pair has cycles/conflict <=0.95 and instructions
   <=1.00 with exact output identity, run original si2 at seed 0, MAXC=40000,
   candidate then control, with otherwise identical cost settings. Require
   both two-input geometric means <=0.95 cycles/conflict and <=1.00
   instructions, and neither si2 ratio above 1.03. Report solved-at-cap too.

This is a small engineering screen, not a population estimate. There is
no search-policy change: complete trajectory identity and the scalar state
oracle are mandatory. Do not combine percentages from older experiments.
If it is below the cost gate, diagnose the candidate's remaining cost and
name a concrete repair/shared-cost combination or explain why the available
opportunity is too small. Any follow-up needs its own recorded hypothesis;
no inline/dispatch/width tuning against this pair.

Before these invocations: full SAT tests with all features, focused ordinary
kernel tests, SAT clippy with all features/targets, formatting, and a clean
committed optimized build. A production source landing additionally needs
the full workspace build/nextest/doctest/clippy/fmt/doc gates and fresh
installed-Z3 4.16.0 parity. An unsuccessful prototype is archived with source,
binary, tests and cost/profile evidence; its finding lands on main.

## Result: the combined implementation passes the bounded screen

All five registered invocations completed; none was repeated. Both cost
pairs have byte-identical complete stdout. Factored circuit finishes SAT
at **91833 conflicts** and original si2 finishes SAT at **39246 conflicts**,
before its 40000 cap. Both arms solve both inputs, so solved-at-cap is
2/2 in each arm. Every witness was independently checked against its input;
the factored witnesses also satisfy every clause of the original circuit.

| Whole-invocation cost | Control `6d492a4` | Candidate `bdfcaf3` | Candidate / control |
|---|---:|---:|---:|
| Factored circuit: instructions | 25192500038 | 23959548404 | 0.951059 |
| Factored circuit: cycles/conflict | 193113.508 | 174500.384 | 0.903616 |
| Original si2: instructions | 27350367299 | 25881371428 | 0.946290 |
| Original si2: cycles/conflict | 358651.148 | 272071.669 | 0.758597 |
| Two-input geometric mean: instructions | — | — | **0.948671** |
| Two-input geometric mean: cycles/conflict | — | — | **0.827937** |

Instructions fall **5.13%** across the two inputs. Measured cycles/conflict
fall **17.21%**, with non-increasing instructions on both and no si2
regression. Both advancement/combined gates pass. The changes remove
executed instruction and branch work on identical search trajectories;
they do not improve conflict counts. Combined branch and branch-miss ratios
are 0.962540 and 0.988691.

This is evidence for this combined implementation on two inputs, not a
broad speedup estimate or proof of a superadditive interaction. The older
kernel was measured on a different prefix and cannot supply a factorial
interaction term. Host interference remains material: instrumented wall
times were 4.34/14.40 seconds for factored control/candidate and 10.34/3.53
seconds for si2 candidate/control. Active event times were much shorter in
the delayed candidate invocations. All four explicit atom events had
100.00% scheduling coverage, but that does not remove effects of descheduling,
frequency or shared resources on cycles. The instruction reduction is the
stronger result; the larger cycle ratios need broader confirmation. No
wall-clock speedup is claimed, and no extra pair was run to improve it.

## Candidate flamegraph and the remaining cost

The [interactive candidate flamegraph](assets/two-phase-watch-kernel.svg)
contains **1613 raw cycle samples**, zero loss/throttling, all user-mode on
CPU 10, 100% enabled/running coverage in every sampled read and zero
unresolved self cost. ELF executable-segment addresses and the recorded
MMAP2 mapping resolve the PIE load bias, so the two generic scan symbols
are distinguished by their actual address ranges. LBR truncates some
caller chains; those stacks are explicitly grouped. The captured prefix
ends at 16892793045 cycles and 23957878843 instructions. These are not
complete-solve counters and are not compared with unprofiled solve costs.

| Candidate self attribution | Cycles | Counter-delta-attributed instructions |
|---|---:|---:|
| Compaction suffix | 29.32% | 27.93% |
| No-removal prefix | 23.06% | 21.78% |
| Outer propagation driver | 4.77% | 4.44% |
| Forward subsumption | 13.14% | 13.33% |

The prefix and suffix have 372 and 473 cycle samples respectively. The
prefix is substantial, so its cheaper blocker-hit path is not a vacuous
optimization. These are cost shares, not fractions of watcher visits.
The outer driver includes BIG and bookkeeping as well as unit/resume calls;
its 4.77% cannot all be assigned to the new call boundary. The combined
propagation share remains large, around 57.16% of the candidate's own cost.

In both phase bodies, the branch following the dependent arena deleted-flag
load receives the most cycle attribution (19.09% of prefix, 17.12% of
suffix samples). Blocker-value loads, the reference-null comparison,
watch-destination stores and spills also remain visible. Such samples do
not establish branch mispredictions or the savings from removing a guard.
The compaction suffix still reads and copies a 12-byte watcher, checks write
bounds, and holds clause identity live through the miss/move path. The
current kernel improves the control flow but does not remove those costs.

The next composable representation is still **cold activity plus a direct
8-byte watcher**, with stable ID stored in the vacated header word. It
could reduce suffix copies, cross-list stores and live metadata without
reintroducing the old ID-to-arena dependency. The cost review's relocation,
deleted-tombstone identity, observer, detachment and snapshot obligations
remain mandatory; the current result does not resolve them. Do not add a
scan cursor on clause width alone: the unchanged sampled learned scans
are short. Do not delete the bounds/lifetime guards based on branch samples.

## Reproducibility and source checks

Registration: `f99e69b`. Candidate source:
`bdfcaf3e28a9b2fafabb55acb2d7028290e0f8c6`. Control source:
`6d492a43f15c5addfef42b550efeb405b3969ad6`. Their cached `stats_solve-perf`
SHA-256 values are respectively
`834e998b0b4b3adf45e3cc41fd8f365cdff6e69e7970c181b8d8874e51e9692f` and
`9e38743f94322df4221444ef67f9742c9be7a2b29968d5b631263a3861db60c8`.
The same lock/compiler/profile are pinned above. No native target or custom
optimization flags were used. The temporary control worktree was removed
immediately after caching its build.

Canonical records under each commit's `benchmark/runs/two-phase-watch-kernel/`:

| Cell | Record |
|---|---|
| Factored control cost | `a0cb710251bab073` |
| Factored candidate cost | `10564b94c329796e` |
| Candidate LBR profile | `11d1f203adaa6e2a` |
| si2 candidate cost | `6916f9655d848114` |
| si2 control cost | `76780b1b4af18d1e` |

Adjacent `benchmark/two-phase-watch-kernel/` directories retain runner,
source/build identity, lock, immediate completion records, raw perf data,
stdout/stderr, complete-cost summaries, phase-address mapping, disassembly,
cycle annotation and folded stacks. All five record IDs, content-addressed
paths, binary hashes and both output identities were checked independently;
the SVG parses as XML and contains both phase labels. Factored output SHA-256
is `87eb5896119b2e0d389bd7495929722291351a3889509b1c549dab3c593814c4`,
matching the earlier profile/observer and feasibility solve too. si2 output
SHA-256 is `c25ba0a9a391a198ca92943e0e5f07eab463efa505980699e3245d712173d30f`.

Before measurement, **1024 SAT tests passed, one skipped**, with all
features. All seven kernel tests passed again in an ordinary build. The
oracle covers 1296 small-state combinations, backtracking and budgets,
eager normalization, HBR, LRAT, inprocessing, models and independently
checked UNSAT proofs. Two focused tests check the first-hole transition,
unit yields in each phase, satisfied deleted watchers, conflict tails,
all-kept completion and removal of the final entry. SAT clippy with all
features/targets, workspace formatting and the clean committed optimized
build passed. Production qualification also passed on the candidate source:

- All-features workspace build.
- **10809 workspace nextest tests passed, 12 skipped**; 111 doc tests passed,
  29 ignored.
- Strict all-features/all-targets workspace clippy, formatting and docs.
  Docs use `RUSTDOCFLAGS="-D warnings"` with `cargo doc`.
- Fresh installed **Z3 4.16.0** parity: **174 agreements, zero disagreements,
  one inconclusive** of 175 (`array_unique`: Nixie Unsat, Z3 Unknown).
  Unknown is not counted as agreement. The Linux snapshot is retained with the qualification evidence.
  Current `.gitignore` excludes parity snapshots, unlike the older
  harness documentation; the complete result is in the immutable cache.

The five invocation limit describes the performance screen; the required
workspace/proof/Z3 safety checks are separate. No extra Kissat or CaDiCaL
cost cell was run. Qualification commands, compiler/input identity, logs
and immediate exit records are retained in the candidate's `qualification/`
directory. Both the implementation and its tests land on main, together
with this result and the flamegraph.

The ordinary release `stats_solve` and CLI binaries were also built and
cached. The cost screen continues to refer to its pinned `perf` binaries;
no release cost cell was added. The completed study leaves no experimental
source branch or worktree; cached binaries and the recorded evidence remain.
