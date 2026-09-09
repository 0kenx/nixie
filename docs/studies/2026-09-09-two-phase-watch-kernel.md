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
