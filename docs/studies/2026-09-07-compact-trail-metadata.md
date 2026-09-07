# Compact trail metadata

## Registration

The trail's private metadata vector stores `VarInfo.value`, but every value
read uses the separate per-literal `values` array. Keep the public `VarInfo`
type unchanged and introduce a private metadata record containing only
level, reason, and trail index. This reduces each internal record from
20 to 16 bytes on the measured target and eliminates unused value stores
on assignment, size backtracking, and clear. Keep existing level/reason
reset semantics exactly, including chronological trail compaction.

Reference: Kissat `src/assign.h` separates assignment metadata from literal
values; CaDiCaL `src/var.hpp` likewise keeps levels/reasons separate from
truth values. No reason encoding, clause-id range, unsafe indexing, search
policy, or public type change is needed here.

Use the same reduced-run protocol as eager watch normalization: cached
`0263862` release baseline (source identical through the documentation-only
commits), two seed-0 screen cells (break/circuit), then seeds 1–3 on break,
crn, circuit, si2 if promising, plus j3037 seed 1 as a larger held-out case.
Reuse all baseline and reference cells. CPU 10, complete user-mode hardware
instructions primary, cycles confirmation, same flags and conflict cap.
Require exact printed diagnostics/model identity. Land a performance claim
only with at least 5% lower geometric-mean cycles on the confirmation panel,
non-increasing instructions, and no input over 5% worse. Report this small
panel's limits; the user has explicitly reduced the benchmark run count.

Before landing, verify all trail mutation paths with focused tests, run SAT
differentials/model validation, the full workspace gates and fresh Z3 parity
using the available version. Preserve measurements, including regressions.

## Verdict: rejected at the two-cell screen

Both outputs were byte-identical, including the checked circuit SAT model.
Instructions T/B were 0.9944 (break) and 0.9976 (circuit); cycles T/B were
1.0155 and 1.0769. This does not qualify for confirmation or a performance
landing. The source and unexecuted draft regression test were removed; the
patch and binary are archived with the two PMU records. These measurements
do not establish a multi-seed regression or its cause.

API audit correction: `VarInfo` is public only within the private `trail`
module and is not re-exported, so a future justified representation change
can simplify that existing type directly. Keeping an unused compatibility
record is unnecessary. Do not retry merely for the 20-to-16-byte footprint
saving without evidence that metadata traffic dominates the workload.

## Measurement limitation discovered after the screen

A subsequent host process check found another task's multi-core SAT sweep
on CPUs 10–17, including this experiment's CPU 10. The recent screens may
have overlapped that workload; their cycle differences cannot be treated as
quiet paired measurements against the older cached baseline. Preserve all
rows and rejection decisions as screening outcomes; the hardware-cycle
cause is unresolved. No claim of a cycle regression is justified here.
Further cycle qualification uses fresh paired cells on a separate P-core.
