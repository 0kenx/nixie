# Persistent positive blocker certificates

## Pre-registration

The user's committed `22e05d8` mode-matched panel still has exactly the
conflicts and ticks of `0263862`. The relation factorizer is an explicit
offline tool; ordinary solves do not invoke it. This experiment targets the
ordinary propagation loop, without changing scheduling or search decisions.

Read the blocker values of at most sixteen consecutive long-clause watchers
into a mask of **positive** certificates. Keep the mask across intervening
scalar miss visits and retain runs of certified watchers together. A true
literal stays true throughout a propagation call: assignments are monotone
until backtracking, which cannot occur inside this scan. A non-positive
snapshot is never a certificate: re-read it at the actual scalar visit,
because earlier propagation may have assigned it either sign. Rebuild the
mask for every window and discard it at list exit, including conflict exit.

The four-blocker prefix experiment in `2026-09-07-bcp-blocker-batching.md`
discarded all lookahead after the first miss and failed. This experiment
retains only the positive facts across misses. The earlier warning against
retaining later values is necessary for non-positive values; positive facts
are monotone. No watch reordering, changed arena normalization, new unsafe
indexing, or changed tick accounting is permitted. Instrumentation must
observe exactly the same visits and outcomes. Kissat `src/proplit.h` is the
reference for the existing blocker-before-payload shortcut.

Use an isolated checkout based on `4926f73` (the intervening Kitten sweep
is default-off), with a clean committed scalar baseline and clean committed
candidate. Build both with `cargo build --locked --release -p nixie-sat
--example stats_solve`, the same lockfile/toolchain, no `RUSTFLAGS`, and no
instrumentation features. Record both source and binary hashes. The supplied
`22e05d8` binary has no build manifest, so its wall-time panel is context,
not a PMU control for an independently built candidate.

To respect the request for fewer runs, the rejection screen is exactly two
available inputs: circuit_48in64out and j3037_10_mdd_bm1, seed 0, 40,000
conflicts, CPU 10. Run scalar/candidate on circuit, then candidate/scalar on
j3037: four invocations total. No width tuning, repeated cells, fresh Kissat
panel, or extra attribution runs. Store all results using `benchstore.py`.
Count whole-process user-mode instructions as the primary complete-work
metric, cycles/conflict as the target metric, and branch misses as context.
Counters include parsing, preprocessing, solving and cleanup; ticks alone
do not measure this engineering change.

Reject on any difference in printed search counters, verdict or model, or
failure to reduce geometric-mean cycles/conflict by 5% with non-increasing
instructions and no family exceeding a 5% cycle regression. A passing
single-seed screen is preliminary evidence only, not a qualified speedup.
Search identity is the null for this engineering change; a trajectory change
invalidates that control and is not accepted as a heuristic improvement.

Before a source landing, require targeted tests of stale negative snapshots,
positive certificates across misses, compaction, conflicts and backtracking,
the full workspace build/nextest/doctest/clippy/fmt/doc gates, and Z3 parity.
If the screen fails, remove the prototype and land this study's negative
result, preserving its source patch, binaries and raw records in the cache.
