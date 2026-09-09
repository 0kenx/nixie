# Factored search cost with a qualified sampler

This is a new, coarser diagnostic protocol, registered before its solver
invocations. The [failed DWARF capture](2026-09-09-factored-search-cost.md)
remains rejected. No source, representation or search policy changes here.

## Profiler qualification

A finite Rust workload alternates otherwise identical dependent arithmetic
loops in a 3:1 ratio through a known caller chain. Five synthetic workload
invocations tested sampling settings; none invoked a solver. CPU-wide event
selection and a 1024-page buffer were rejected before workload execution by
the installed permissions. Neither host permissions nor sysctls were changed.

Hardware LBR call-stack recording recovered the known caller chain and
approximately 75/25 self shares without lost samples. Rates of 1999 Hz and
499 Hz still emitted 3065 and two throttle records respectively. A fixed
4000007-cycle period emitted 331 throttle records. An 8000009-cycle period
removed throttling but aliased with the loop, reporting 82.73/17.27. The
unchanged workload rejects that period. The final configuration,
**10472903-cycle period, 128-page buffer**, produced **1146 samples, zero
lost/throttled samples, all on CPU 10, and 100% scheduling coverage** in
every sampled counter read, with **75.04/24.96** cycle shares and the known
caller chain. Its cycle periods sum to within 0.00001% of
the final sampled cycle counter. Evidence and the exact raw-data parser are
under `precompile/1f3f316/benchmark/profiler-qualification/`.

Record only the workload using explicit atom-PMU events in a group:
`{cpu_atom/cycles/uS,cpu_atom/instructions/u}`. `--running-time` includes
the group's enabled/running times in each sample. Pin outside perf and
record the sample CPU. There is no outer `perf stat`: recorder work is not
attributed to the workload. Read counters stop at the last sample and are
**sampled-prefix counters**, not complete-solve cost measurements. Perf's
group report repeats each sample for both events; count raw cycle samples,
not the sum in its report header. Report cycles and instructions separately.

## One profile and one conditional observer

Reuse the two cached binaries from committed source `1f3f316` and the exact
factored CNF, original CNF and old witness pinned in the preceding study.
Use CPU 10, seed 1, CaDiCaL preset, MAXC=10000000, sweep disabled, model
printing and a 300-second emergency timeout. Clear other study overrides.
Do not rebuild, transform again, rerun the rejected cell, or rerun controls.

The profile must complete with a SAT model checked on both CNFs. Require
at least **1500 raw cycle samples**, no loss or throttling, one sampling
PMU, CPU 10 for every sample, at least 99.9% scheduling coverage in every
read, at least 99.9% user-mode samples and at least 99.9% resolved self cost.
Retain any kernel IP skid in the denominator. This coarser screen uses a
stronger **55% propagation self-cost gate**; self cost is a lower bound
on inclusive propagation, independent of caller-stack truncation. The
previous 10000-sample protocol is not being retroactively passed or relaxed.
This screen selects only a broad next target; it cannot estimate small
speedups or establish a general improvement. A failure ends this protocol
without another solver profile.

Only if that gate passes, run one existing stride-16 `clause-traffic`
observer with identical settings. Require byte-identical complete stdout,
both model checks, at least 1000 clause-epoch rows and no omission/overflow.
Use the preceding study's original/learned opportunity rules unchanged:
total original work below 40% rejects the original-five-literal engine;
an aggregate above 40% cannot establish its width-specific gate; learned
work at least 50% selects the learned-clause path if the original gate is
not established. Payloads plus scans are an unweighted long-clause proxy;
BIG has its own visit/unit/conflict counts and zero payload/scan counts.
Learned widths are recorded at the first visit of each epoch. Neither the
traffic runtime nor these proxy shares are predicted cycle savings.

At most **two new solver invocations**. Retain each invocation immediately,
including any rejection; never overwrite or rerun a started cell. Record
qualified observations in benchstore, then land the diagnosis and the
specific next target on main. Any subsequent implementation needs its own
soundness argument and registered cost/null screen.
