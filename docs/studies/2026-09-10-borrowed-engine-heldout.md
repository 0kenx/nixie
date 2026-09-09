# Borrowed propagation engine: independent input screen

## Scope and registration

The [borrowed-reason candidate](2026-09-10-borrowed-propagation-reasons.md)
removed 19.93% of whole-process instructions on j3037, with identical output,
but 34.866% off-CPU time invalidated wall qualification. That record and its
verdict remain unchanged. This is a new comparison on **crn_11_99_u and
summle_x4044**, neither previously measured for this candidate. It is not a
j3037 retry, a si2 confirmation under the failed prior gate, or a new source
variant manufactured to obtain another timing cell.

First review of further mechanisms found no justified cheap replay removal.
`Trail::backtrack_to_with_callback` rewinds to the level boundary because
retained out-of-order assignments can lose consequences recorded at higher
levels. Strengthening/probe resets in `learn.rs` also protect hanging units;
the earlier [work audit](2026-09-09-propagation-work-audit.md) already bounds
the scheduled exit resets at less than 0.5% of circuit propagations. The
local CaDiCaL backtracking and Kissat propagation implementations preserve
these obligations. No rewind, assignment level, watch choice or tick policy
changes follow this review. Further layout/lookahead work must address the
costs already recorded in the negative-results review.

Use the existing exact cached binaries, avoiding new builds or changes:

- Production `fd01d0b596d4640ab63e4b126bd62595d1c24016`, release SHA-256
  `8c18517990b8e9aad3273fc0acd354362599c806ce6f9a596e231d98851bacde`.
- Candidate `d8e78052eeb17f319c5408efde5a1daea72749cd`, release SHA-256
  `82e099fecfabd7382c92bce45eefaf63496add11f99327fc0e065f4e16ddaee2`.
- Both portable Rust 1.96.0 / LLVM 22.1.2, identical retained Cargo.lock.
  Candidate preflight passed 1047 all-feature SAT tests, strict SAT Clippy,
  formatting, five strict-provenance Miri tests and native Rayon ownership.
  Main's later changes are outside this DIMACS SAT invocation; SAT source
  still matches qualified production. No new source qualification is claimed.

Inputs are the checked-in SAT fixtures:

| Input | SHA-256 |
| --- | --- |
| `crn_11_99_u.cnf` | `301a5351b7cec4bbc27bf066df769db2870c1e3f3948d6c2ff0b7a9f6bab52eb` |
| `summle_x4044.cnf` | `6fdc72e329cc9c034aed42dde04a5b4446acdb0565dd4995a224a9ebec03037e` |

Four new cost invocations, in this fixed order: crn production, crn candidate,
summle candidate, summle production. No quality-failed or interrupted cell
is repeated. Use the once-only result store, suite `borrowed-engine-heldout`,
protocol `borrowed-engine-heldout-v1`. Seed 0, CaDiCaL preset, MAXC=10000000,
PRINT_MODEL=1, NIXIE_SWEEP=0, NIXIE_DEFINITIONS=0; clear other study overrides.
CPU 15 Atom, ordinary release, warm input/binary, anonymous tmpfs outputs,
GNU time 1.10 and whole-process user instructions/cycles with grouped
`cpu_atom` events. Emergency timeout 300 s; timers never enter solver policy.

Before each pair require a ten-second CPU 15 idle fraction of at least 95%,
CPU pressure avg10 at most 1%, and one-minute load at most 12 on this 20-core
host. Record the host/affinity snapshots and competing build/solver activity;
these checks reduce contention but cannot establish machine isolation.
Constrained threads including CPU 15 must be sleeping futex workers whose
identity and schedstat runtime remain exactly unchanged throughout the pair.
No owned build or test overlaps a cost invocation. A failed host preflight
spends no solver cell; leave the pair pending until conditions permit it.

Record complete output, model validation against every original SAT clause,
counter coverage, faults, user/system/wall times and switches. Require exact
Nixie stdout identity within each pair, >=99.9% PMU coverage, zero major
faults and <=5% off CPU for both arms. Raw UNSAT without a checked proof stays
unknown/unverified in canonical records. Runtime ratios are a bounded
engineering screen on two fixed trajectories, not a seed/suite geomean or
an established causal estimate under arbitrary shared-host interference.

Advance only if both pairs qualify, geometric-mean candidate/production
instructions and wall are each <=0.95, and neither input exceeds 1.03 on
instructions or wall. A missing usable timing is not a passing gate. If
successful, allow one available-Kissat comparison per input, reusing an exact
compatible record if present, with the user's flags below. These two reference
cells contextualize the remaining gap; they do not replace the paired Nixie
controls. No source tuning follows the observed results.

```
--probe=0 --preprocess=0 --factor=0 --substitute=0 --sweep=0
--vivify=0 --transitive=0 --backbone=0 --congruence=0
```

If the cost gate fails, retain the existing candidate flamegraph and inspect
the executed cost/assembly against it. At most one new summle LBR diagnostic
is allowed if its long-clause cost is not explained by that j3037 profile;
no timing is taken from it and no measured repair follows this screen.
Passing the cost screen still requires the full workspace build, nextest,
doc-tests, strict Clippy/fmt/docs and installed-Z3 4.16.0 parity before source
promotion. Preserve the prior candidate archive, all results and any remaining
qualification limits. Commit the completed finding on main and remove owned
temporary artifacts.

## Pre-execution host allocation clarification

Four ten-second CPU-15 preflights failed before any solver invocation.
Its idle fractions were 12.74%, 85.08%, 85.97% and 84.15%; foreign Rust
builds and solver sweeps were active. These are host observations, not
candidate performance results. No cost cell, repair or profile has run.

Permit another **Atom** core before starting the comparison, using only
host idleness, never solver performance, to allocate it. At a ten-second
preflight, prefer CPU 15 if it qualifies; otherwise select the lowest-numbered
Atom CPU with at least 95% idle time and no active constrained userspace
thread. Keep the same <=1% CPU-pressure and <=12 one-minute-load thresholds.
Record every core's idle fraction and the selected core, then lock that core
for both input pairs and any reference cells. If the locked core becomes
busy, wait or leave the remaining cells pending; do not move a measured pair
to another core. Preserve all failed CPU-15 observations and explicitly put
the selected CPU in the manifest and canonical flags before launching.

This allocates an unused execution resource for an unstarted panel; it does
not change the candidate, inputs, order, thresholds or four-cell budget,
supersede the invalid j3037 result, or permit a timing retry. No foreign
process is moved or stopped. Full-machine isolation remains unestablished.

### Launch feasibility amendment, still before any cost observation

The all-Atom preflight also failed: four cores were continuously occupied
and all remaining Atom cores had 66–81% idle time, with CPU pressure only
0.14%. No solver has run. The preliminary 95% idle requirement is too
restrictive to launch this bounded screen on the currently shared workstation.
Change **only the launch idle threshold to 70%**, keeping the same core
selection/locking rule, <=1% pressure and <=12 load requirements. Retain
the original runner and all failed preflights. This amendment precedes every
candidate/control observation and makes no inference about their costs.

The actual acceptance gates are unchanged: both completed arms need <=5%
off-CPU time, >=99.9% PMU coverage, zero major faults, unchanged constrained
worker runtime and exact stdout. All four cells still run at most once.
Call this a comparison under moderate shared load, not isolated timing.
Even a passing screen retains the limitation that shared cache/frequency
effects are not separated. If the actual timing gates fail, archive the
instruction evidence with missing usable wall qualification; no retry or
post-result threshold amendment follows.

## Four-cell result: executed work falls, wall does not improve

CPU 15 was selected and retained. Both pairs meet the **unchanged actual
measurement-quality gates**, with 100% PMU coverage, no major faults,
0.57–1.36% off CPU and no runtime increase on constrained sleeping workers.
Foreign solver sweeps remained active on other cores; shared-cache/frequency
effects remain an attribution limit. Both full stdout comparisons are exact;
both summle SAT models satisfy every clause of the original input. Crn's raw
UNSAT is unverified without a checked proof and remains Unknown in the store.

| Input / arm | Instructions | User cycles | Wall | Conflicts |
| --- | ---: | ---: | ---: | ---: |
| crn production | 11003252708 | 6547224939 | 1.44 s | 87939 |
| crn candidate | 10072242765 | 6589315626 | 1.47 s | 87939 |
| summle candidate | 21903374032 | 23782329275 | 5.29 s | 19333 |
| summle production | 26021361201 | 22139139371 | 4.97 s | 19333 |

Instructions fall **8.46% on crn and 15.83% on summle**. Wall ratios are
1.02083 and 1.06439; the two-input geometric means are 0.8778 instructions,
1.0398 cycles and 1.0424 wall (candidate/production, rounded). This fails
the wall-improvement gate and summle's <=1.03 individual guard. Crn stays
inside the wall neutrality band; summle is slower in this paired observation.
Do not promote these two fixed trajectories to a population regression claim.

Canonical records, in execution order: `0840cab28aa276cb`,
`80bc043f011d740c`, `e2d317ccc921704d`, `02d916e9af5fe4da`.
Crn has 3817687 propagations and summle 32793359 in both arms. No new
Kissat cells follow the failed advancement gate. Existing reference records
were audited; none exactly matched this protocol/core/seed combination.

The 19.93% j3037 instruction reduction now has independent-input support,
but fewer instructions again do not demonstrate progress on wall. The old
j3037 timing remains invalid; these new records do not repair it.

## One summle diagnostic, before execution

Use the already permitted summle LBR diagnostic to resolve the different
workload's remaining cost. Reuse the exact cached candidate perf binary;
no rebuild, repair or additional control. Same core, input, seed and solver
flags, with terminal memory reporting and grouped user cycles/instructions.
Use a fixed **1048576-cycle sampling period** to obtain enough samples from
this shorter solve; LBR caller stacks, 128 mmap pages and sample-read counters.
Require at least 1000 samples, no lost/throttled records, >=99.9% PMU/user
coverage and <=0.1% unresolved self cycles. Preserve a quality failure without
retrying. Compare output after removing exactly the terminal memory line and
independently check its model. Diagnostic elapsed time is never cost evidence.
Inspect hot addresses against the unchanged perf assembly, including the
borrowed-reason setup/read sites, binary spans and long-watch access chain.
No measured repair or extra profile follows this four-cell screen.
