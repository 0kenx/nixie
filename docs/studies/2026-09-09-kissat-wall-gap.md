# Return to the Kissat wall-time target

The user's renewed direction is explicit: close the gap to **Kissat,
especially wall time**. Hardware counters and flamegraphs are diagnostics;
they do not establish that this target improved. Z3 is only the mandatory
correctness gate for solver changes. It is not the performance comparator.
The [two-phase kernel](2026-09-09-two-phase-watch-kernel.md) is now on main
at `b9ae745`; its noisy instrumented timings do not establish a wall gain.

## Registered direct comparison

At most **six new solver invocations**, with no perf/profiler instrumentation:
original circuit, seed 0, control Nixie `6d492a4`, available Kissat 4.0.4,
then candidate Nixie `b9ae745`. Only if all timings qualify and candidate
wall/control wall <=0.95 with identical Nixie stdout, run original si2 in
reverse arm order (candidate, Kissat, control). This is a small rejection /
current-gap screen, not a population claim. Do not repeat a started cell or
rerun a bad timing. A new baseline build creates its missing ordinary-release
cache entry and its worktree is removed immediately afterward.

Use ordinary portable release Nixie binaries with the same pinned lock and
Rust 1.96.0 / LLVM 22.1.2; candidate code is exactly the qualified `bdfcaf3`
source, with documentation-only changes through `b9ae745`. Nixie uses the
CaDiCaL preset, explicit `NIXIE_SWEEP=0`, model output, seed 0 and a 10000000
conflict cap. Clear other study overrides. Kissat uses `--statistics`, the
same seed/cap, and the user's exact switches:

```
--probe=0 --preprocess=0 --factor=0 --substitute=0 --sweep=0
--vivify=0 --transitive=0 --backbone=0 --congruence=0
```

These switches do not equate search heuristics or tick units. Preserve all
three binaries' hashes and the reference source/build identity. Use CPU 10
for every arm. Read the binaries and each input before its batch to put them
in the filesystem cache, without invoking a solver. Capture solver stdout
and stderr in anonymous RAM-backed files and persist them only after timing,
so result-store writes cannot stall the solve. GNU time 1.10 measures the
entire target invocation, including parse/model output. Record wall, user and
system time, major faults and voluntary/involuntary context switches. The
Python runner's enclosing elapsed time is a separate diagnostic. Its delayed
wakeup must not masquerade as measured solver wall time. A 300-second kill
is only an emergency bound.

**Wall time is primary for this engineering comparison**, following the
user's latest instruction. It is never a solver-policy input. Require SAT
witnesses independently checked against the original input and identical
complete Nixie outputs. Do not count Unknown as a verified comparison.
Require `(wall - user - system) / wall <=0.10` on every cell before interpreting
the batch as a wall comparison; retain all observations if it fails. This
screens gross off-CPU contamination, not all cache/frequency/shared-resource
noise. Report candidate/control and both Nixie/Kissat wall ratios, conflicts,
wall/conflict, CPU times and solved-at-cap. The ratio to Kissat is the target;
source-preserving Nixie controls separate execution-cost changes from it.

Store every cell once under `kissat-wall-gap`, with immediate completion
records and model checks. No new source change, full suite, Z3 run or broad
benchmark panel is part of this measurement-only follow-up.
