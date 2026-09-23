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
