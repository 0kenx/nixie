# Persistent positive blocker certificates

**Verdict: rejected at the four-run screen. No propagation change landed.**

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

## Result

The two clean committed arms were scalar `2202f0e` and prototype `8d46d96`.
Both used Rust 1.96.0 / LLVM 22.1.2, the portable release profile, no build
flag overrides, and lockfile SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
Binary SHA-256 values:

- Scalar: `49ad1bee056f6f1c23fab56cc424aca76880b303b6f9d62436c924b9745b094d`.
- Prototype: `c42019e40cfa786b44da6430e34171da98e74fc3515eb9aa41bfb3eccaa9bc3a`.

| Input, seed 0, 40k conflicts | Scalar cycles/conflict | Prototype cycles/conflict | Instructions T/B | Cycles T/B | Branch misses T/B |
|---|---:|---:|---:|---:|---:|
| circuit_48in64out | 121,118.89 | 127,430.66 | 1.0152 | 1.0521 | 1.0643 |
| j3037_10_mdd_bm1 | 422,633.16 | 452,309.55 | 1.0605 | 1.0702 | 1.0456 |

The screen's geometric-mean ratios are **1.0376 instructions** and
**1.0611 cycles/conflict**. Both inputs reached the 40,000-conflict cap in
both arms. Complete stdout, including every printed search counter, was
byte-identical within each pair. Both results are honestly recorded as
`unknown`; there is no SAT model or UNSAT proof to certify at this cap.
All four PMU events were 100% scheduled on CPU 10. There were exactly four
new invocations, no repeated cells and no new Kissat runs.

The prototype failed every performance part of the registered gate: it did
not reduce cycles, increased instructions, and exceeded the per-family
cycle-regression limit. Retaining certificates across misses did not pay for
its mask construction and scan bookkeeping on these inputs. Branch misses
also increased on both. This is a rejection of this fixed-width prototype,
not a multi-seed estimate or an assertion that every possible bulk blocker
representation must fail. Do not repeat this mask design or tune its window
width against these same two observations as if they were fresh evidence.

The targeted regressions exercised positive certificates across deletion,
watch movement and unit propagation; stale zero snapshots becoming true;
stale zero snapshots becoming false before a conflict; conflict tail
preservation and requeue; full and partial windows; and backtracking.
All **725 default-feature SAT library tests** and **741 all-feature SAT
library tests** passed, including the three new regressions. The latter
also exercises the existing watch-group and region-observation tests.
Formatting and patch-whitespace checks passed. The early rejection stopped
before the full workspace and Z3 gates; no solver source is being shipped
from this experiment, and those unrun gates are not claimed as passes.

## Retained evidence

Canonical records live in `precompile/<sha>/benchmark/runs/bcp-positive-certificates/`:

| Input | Scalar record (`2202f0e`) | Prototype record (`8d46d96`) |
|---|---|---|
| circuit_48in64out | `14ed9b8263997cd2` | `21e084b71d834174` |
| j3037_10_mdd_bm1 | `0bebb5d32ccff96d` | `4396d0793d0d210d` |

Each arm's `precompile/<sha>/benchmark/bcp-positive-certificates/` contains
its build manifest and raw PMU/stdout/stderr files. The scalar directory
also contains the four-cell manifest and `screen.py`, which refuses to
repeat completed cells or silently retry interrupted starts. The prototype
directory contains the tested source patch, build/test logs, and a Git
bundle preserving the exact experimental commit with `2202f0e` as its
prerequisite. The ordinary propagation source stays unchanged on `main`.

The user's committed `22e05d8` panel remains the gap measurement. This
experiment has not closed that gap. The earlier certified relation
factorization remains a separate structural avenue, but it still requires
integration and a controlled total-cost comparison before ordinary-solver
improvements can be claimed.
