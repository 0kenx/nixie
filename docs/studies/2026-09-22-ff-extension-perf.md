# Binary extension-field performance study

The pre-registered workload, controls, counter-coverage argument, acceptance
bar, and run-once protocol are in `bench/ff_extension_perf/README.md`.
Production baseline is `df564313`; the benchmark-only commit adds no solver
changes. CPU instructions, not elapsed time, are the primary metric.

## Preflight finding, before measured cells

Untimed functional checks validate all 13 generated cases at seed zero.
The initial budget probe used a depth-64 shared square/add expression over
F256; it produced no verdict within the external 120-second safety cap.
A short sampled profile of that running process concentrated on one tight
loop, but the cached release executable is stripped, so that sample does
not identify a source-level cause. Preserve it as diagnostic evidence,
not a completed performance cell or an instruction ratio.

The measured budget probe is fixed at depth 16, which returns Unknown.
The depth-64 input is retained as a separate diagnostic and must be
investigated with a symbol-enabled build. No measurement or benchmark cell
was rerun; these were functional checks without cost collection.

## Results

Pending the pre-registered baseline profile and paired cells. A prospective
optimization must preserve exact results, model readback, and deterministic
budget charges. No performance improvement is claimed by this registration.
