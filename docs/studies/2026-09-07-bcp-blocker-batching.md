# BCP blocker batching: cycles per conflict

**Verdict: rejected at the one-seed screen; prototype removed.**

## Pre-registration

The previous throughput campaign found that instruction reductions often do
not reduce cycles. This experiment targets the dependency chain and branch
for each satisfied watcher, without changing the search policy.

Read four adjacent watchers' blocker values independently, compute the length
of their satisfied prefix, and retain that prefix together. Stop at the first
non-true blocker and process it with the existing scalar path. Never retain a
watcher past that point using an earlier value: propagation can change later
blockers. Preserve watcher order, arena normalization, conflict tails, and
all tick accounting. No new unsafe indexing or CPU-specific instructions.

Reference: Kissat `src/proplit.h` checks a blocker before accessing a large
clause. This groups only that existing read-only shortcut; all non-shortcut
visits retain Nixie's current semantics. It is distinct from the previously
rejected changes to watcher width, BIG ordering, and arena layout.

Available corpus: all four files in `satcomp2024/bench` (j3037, si2-b03m,
constraints_17, circuit_48in). The older campaign's other anchors are absent.
Use the CaDiCaL preset, seeds 0 through 9, 40,000-conflict limit, pinned CPU
10, sequential alternating baseline/treatment order. Build both with the
same `perf` profile and no instrumentation features. A one-seed screen may
reject the mechanism early; it cannot establish an improvement.

Record whole-process user-mode PMU instructions as the deterministic primary
metric, plus cycles, branches, branch misses, elapsed time and every printed
search counter. Include parsing, preprocessing and cleanup in both arms;
cycles/conflict is an amortized invocation cost, not isolated conflict
analysis time. Reuse result-store cells and keep raw output with the binary.
Kissat and CaDiCaL references use the same instances/seeds/conflict cap; their
different searches are context, not controls for the engineering change.

Reject on any trajectory difference (including ticks, verdict, model and
search counters). Land only with at least 5% lower geometric-mean cycles per
conflict, no family regressing by more than 5%, and non-increasing geometric-
mean instructions. Ten paired seeds per file are mandatory for a positive
claim. If rejected, remove the prototype and record the result here.

Before a source landing: workspace build, full nextest suite, doctests,
clippy, formatting, documentation, SAT model/differential checks, and the
Z3 parity suite. Missing inputs and existing failures must be reported
explicitly; they do not count as successful checks.

## Screen result

Baseline: `482b806`, `cargo build -p nixie-sat --example stats_solve
--profile perf`. Treatment: the four-blocker prefix implementation described
above, with safe slice access and `copy_within` for a retained prefix after
the compaction cursors split. Treatment cells are explicitly marked dirty
and excluded from reuse. Source patch, binaries, manifests and raw PMU/output
files are retained under `precompile/482b806/benchmark/bcp-blocker-batching/`;
schema records are under its sibling `runs/bcp-blocker-batching/`.

| seed 0, 40k cap | conflicts | instructions T/B | cycles/conflict T/B |
|---|---:|---:|---:|
| j3037 | 40,000 | 1.0264 | 1.0425 |
| circuit_48in | 40,000 | 1.0068 | 1.0795 |
| constraints_17 | 40,000 | 1.0357 | 1.0100 |
| si2-b03m | 39,246 (SAT) | 1.0200 | 1.0969 |

All printed search counters, verdicts and the SAT model were byte-identical;
the SAT model was checked against every original clause. PMU events were
100% scheduled on CPU 10. The extra mask construction, speculative blocker
reads and prefix-copy bookkeeping increase instructions on every file;
branch misses also increase on every file. This does not pass the
pre-registered screen. These single-seed measurements reject this prototype,
not all possible batching implementations; no multi-seed performance claim
or Kissat comparison is made for this rejected arm.

A fresh cycle-sampled profile on si2-b03m (`MAXC=40000`, same seed) attributes
23.1% of samples to propagation, 21.2% to elimination, and 13.2% to forward
subsumption. Thus the existing campaign's BCP-heavy anchors do not describe
every family. Inprocessing work is a material part of amortized
cycles/conflict on this available instance.
