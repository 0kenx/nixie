# Investigating larger CP scheduling cases

Pre-registration, 2026-09-23. Baseline is landed `7ab18362` (source of
its cached binaries: `f43db048`). Z3 4.16.0 remains the external reference.
The previous 8x16 ordinary ratios are 6.8371 for sparse and 2.3328 for
all-present. Investigate before changing propagation or search policy.

First collect instruction-sampled profiles from frozen binaries, pinned to
CPU 0. Profile invocations use extra rounds for sampling and are diagnostics,
not new comparable performance cells. The sparse family has four unrelated
finite-domain variables per task; inspect domain/callback and explanation
overhead separately from the all-present cumulative sweep. Existing all-family
2-round performance cells are reused, not rerun.

Sampling totals appear inconsistent with the existing process-counter totals.
Before interpreting new measurements, compare the generic `instructions:u`
and explicit `cpu_core/instructions/u` events in the same diagnostic process
(50 rounds, seed 10, all-present 8x16), then check sampled-period accounting.
This is counter calibration, not a performance claim or a replacement cell.
Record the outcome and any invalidated evidence explicitly.

After that, preregister the scaling grid and any candidate before running its
performance comparison. Require independently checked models/proofs, exact
BigInt/half-open semantics, no absent-task scheduling restrictions, and the
existing certificate contract. Any optimization must retain exact transcripts
and be measured on ten paired seeds plus ten confirmation seeds; a policy
change instead needs its own matched null. No wall-time performance claim.

## Scaling grid (before measurement)

Keep the driver, profile, two pushed rounds and 120-second external cap. Add
8x32, 16x16, 16x32 and 32x16 task/domain shapes, in unknown, all-present and
sparse families: ten seeds 10..19, ordinary/certified Nixie and Z3. The sparse
family still adds four unrelated finite-domain variables per task. These are
240 Nixie and 120 Z3 cells. They are a diagnostic baseline distribution, not
optimization selection or confirmation. No production solver change is made
in this investigation. Existing 8x16 cells are reused for the starting point.

The existing reference harness now accepts explicit shape/family selectors;
default workloads and encodings are unchanged. Its new hash identifies new
measurements; do not rerun existing small-grid cells merely for the new hash.
Use source `f43db048` for the frozen Nixie binary and this harness commit for
the Z3 records. Every returned Z3 model is independently validated as before;
Nixie's internal model and certificate checks remain enabled. Report each
family/shape/mode's Nixie/Z3 geometric mean and ten-seed min/median/max, all
solved-at-cap outcomes and Nixie's search counts. Avoid an overall scalar
which lets small cases hide a growing gap.

Counter calibration gave 3,087,105,858 instructions for both generic and
explicit-core events in the same pinned process, with 100% coverage and an
identical transcript. The initial 1M-period profile had 156 throttle events;
20M sampling still throttled. Use 100M-period profiles with extra rounds and
verify zero throttle/lost events. These profiles locate costs; their sample
fractions are approximate and are not end-to-end improvement measurements.
