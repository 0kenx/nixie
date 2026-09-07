# Reuse the selected literal when moving a watch

## Registration

The baseline disassembly reloads `clause[1]` after `swap(1, j)` to find the
destination watch list, although the selected literal is already available.
Express the exchange with scalar stores and use the selected literal as the
destination. Retain the previous unconditional pair normalization and exact
scan order. This is the explicit replacement-store shape of Kissat's
`proplit.h`, with Nixie's existing satisfied-replacement semantics unchanged.
The old watched literal is read rather than inferred, so the exchange has
identical semantics for every valid slice with `j >= 2`.

Reduced-run protocol: cached `0263862` release baseline, CPU 10, seed-0
break/circuit screen, then seeds 1–3 on break/crn/circuit/si2 plus j3037 seed 1
if promising. No new references. Exact diagnostic/model identity mandatory.
Instructions primary, cycles confirmation. Require confirmation geometric
mean cycles <= 0.95, instructions <= 1, no input above 1.05 cycles; run all
workspace gates, SAT differentials/models and fresh available-Z3 parity
before landing solver code. Preserve every cell, including bad results.

## Core-allocation amendment before measurement

Before measuring this candidate, the host check found another task's SAT
sweep sharing CPU 10. Use P-core CPU 2 instead, with fresh paired baseline
and candidate cells (new configuration identity). Screen break/circuit at
seed 0. Also test the archived eager-normalization binary at this new layout:
its earlier instruction and branch-miss reductions deserve an uncontended
cycle screen. This is six cells in total, not reruns of CPU-10 cells. The
other narrow source screens saved less than 0.6% instructions and stay
rejected. Do not combine candidate changes before this isolated screen.

Artifact correction: the legacy runner included CPU in the canonical record
key but omitted configuration from raw filenames. The first CPU-2 baseline
therefore overwrote the CPU-10 break/seed-0 raw perf text. Both canonical
counter records survive; the CPU-10 counts were independently audited before
this incident. Its lost perf file now contains an explicit provenance marker,
not reconstructed output. CPU-2 output was relocated, and all subsequent raw
directories include the configuration hash. The balanced six-seed standing
CSV (seeds 1–6) is unaffected. Do not re-run the lost cell or treat its marker
as raw evidence.

## Screen verdict

The separate-core paired screen preserves byte-identical outputs. Watch-value
reuse is below the bar: break/circuit instructions T/B 0.9948 / 0.9956 and
cycles 1.0008 / 0.9909. Source removed. The eager-normalization arm instead
shows cycles 0.9127 / 0.9361, with instructions 0.9867 / 0.9881 and branch
misses 0.8642 / 0.8628. That mechanism reopens for fresh-core confirmation;
the earlier contested-core screen cannot establish its cycle behavior.
