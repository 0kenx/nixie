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

## Result: learned-clause propagation is the next target

Both registered solver invocations completed SAT at **91833 conflicts**,
315010 decisions and 8369710 propagations. Both witnesses independently
satisfy every clause of the factored and original CNFs. Complete stdout is
byte-identical between the two invocations and the historical feasibility
solve. There were no new control/reference runs.

The profile has **1543 raw cycle samples**, zero loss or throttling, all
user-mode on CPU 10, 100% scheduling coverage in every group read and zero
unresolved self cost. The sampled prefix ends at 16159689719 user cycles
and 25169404903 instructions; these are not complete-solve cost numbers.
The group report's duplicated events must not double the sample count.

| Component, self attribution | Cycles | Instructions attributed through sampled counter deltas |
|---|---:|---:|
| Propagation | **56.64%** | 53.56% |
| Forward subsumption | 12.51% | 12.82% |
| Remaining `solve_with_theory` body | 7.32% | 7.23% |
| Shrink/minimize driver | 3.24% | 3.13% |
| Analysis marking | 2.14% | 2.10% |

[Interactive flamegraph](assets/factored-search-cost-lbr.svg), generated
offline with installed Inferno from the retained cycle-weighted stacks.
Truncated caller chains are explicitly grouped; self attribution remains
available even when LBR cannot retain the whole caller chain. Instruction
shares attribute work between successive cycle samples to the sampled IP;
they are not exact per-function instruction counters. The graph and the
instruction-level annotation locate work, not causal savings.

The propagation self gate passed, so the stride-16 observer ran. Its 31535
learned clause-epoch rows have no omission or overflow. The long-watch
channel reports:

| Clause status at visit | Visits | Blocker hits | Payload accesses | Tail literals examined | Units | Conflicts |
|---|---:|---:|---:|---:|---:|---:|
| Original | 4486591 | 2785094 | 1701497 | 2047978 | 339054 | 3369 |
| Learned | 11191663 | 6806117 | 4385546 | 7764469 | 156554 | 2442 |
| Deleted | 48957 | 47834 | 1123 | 0 | 0 | 0 |

These are sampled counts, without multiplying by sixteen. Original work is
at most **23.58%** of payloads plus scans, so the original-five-literal
engine fails its 40% gate. Learned work is **76.41%**, passing its 50%
gate. Learned scans average only **1.77 literals per payload access**;
recorded clause lengths alone would exaggerate the opportunity for a scan
cursor. BIG separately reports 469675 visits, 52119 units and 102 conflicts;
its payload and scan counts are zero by definition.

The implementation audit follows the learned-clause path: watcher reads,
blocker-value loads, arena addressing, eager pair normalization, short tail
scans, list movement and reason creation. The dominant sampled assembly
addresses include the null/deleted tests and cross-list stores. A sample
landing on a branch after a dependent load does **not** establish a branch
misprediction or the saving from deleting that branch. The zero/rare
logical outcomes in the traffic report make that distinction essential.

The [negative-results cost review](2026-09-09-negative-results-cost-review.md)
records the first concrete combinations and the lifetime obligations that
an implementation must satisfy. No performance improvement is claimed here.

## Evidence and validation

Canonical observations are **`1f0c7049a285827a`** (profile) and
**`dde4d4c8163a47ae`** (traffic), under
`precompile/1f3f316/benchmark/runs/factored-search-cost-lbr/`. Adjacent
`factored-search-cost-lbr/` retains the manifest, runner, immediate
completion records, reports, sample stacks, folded stacks, assembly
annotation, traffic rows and raw `profile.data`. The exact input/binary
hashes remain those of the preceding study. Both records were validated
against their content-addressed paths and identities. No source build or
solver qualification suite was repeated for this documentation-only result.
