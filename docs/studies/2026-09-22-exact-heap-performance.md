# Exact heap performance: measured fragment and scaling limits

This is a measurement of the `HeapSolver` exact-heap-to-LIA reduction, not a
native separation-logic decision procedure or an implementation of list segments.
The [preregistered design](../../bench/heap_perf/README.md) and harness landed at
`32e2b695` before the first measured cell. The implementation and budgets remained
fixed throughout the experiment. No heuristic treatment or causal speedup claim is made;
there is no matched-null experiment here.

The suite contains allocation, forced aliasing, conflicting stored values,
reordered ownership, and Boolean negations of exact heaplets. All locations and
values are integers, nil is zero, ownership is exclusive, and heaps are finite
partial functions. Reference SL uses CVC5's native `pto`/`sep` semantics. The
UF+array configurations encode exact domains, validity and stored values, and
reconstruct a finite witness rather than accepting an infinite array as a heap.
See [the fragment specification](../HEAP.md) for supported Boolean contexts and
validity-to-satisfiability translation. This benchmark adds no fractional
permissions, inductive predicates, magic wand, or heap proof certificates.

## Findings

The 1,040 planned observations all completed: **960 validated decisive results,
80 inconclusive observations, and no wrong answers**. Of the 80 inconclusive
observations, 50 are Nixie safety-cap timeouts (20 primary cells plus 30 region
probes), 20 are CVC5 SL `Unknown` results, and 10 are Z3 array `Unknown` results.
The reference Unknown results occurred under their registered resource budgets;
this experiment did not request `:reason-unknown`. No cell was rerun or dropped.

| Configuration | Primary runs solved / 200 | Inconclusive cases, all ten seeds |
|---|---:|---|
| Nixie exact-heap reduction | 180 | negative-8, negative-16: outer timeout |
| CVC5 native SL | 180 | negative-8, negative-16: Unknown |
| CVC5 UF+arrays | 200 | None |
| Z3 UF+arrays | 190 | permutation-16: Unknown |

The current fragment is useful on the positive allocation and contradiction
families. At 16 allocated cells, Nixie's median whole-pipeline cost is **433 million
instructions**, compared with 3,706 million for CVC5 SL, 561 million for CVC5
arrays, and 3,077 million for Z3 arrays. All ten seeds complete in each arm.
On the 16-cell permutation contradiction, Nixie also completes all ten seeds
at a 261-million median; CVC5 SL takes 27,220 million and CVC5 arrays 839 million,
while Z3 arrays return Unknown at the configured budget.

**Negated heaplets are the performance boundary exposed here.** With four
negated four-cell heaplets, Nixie's median is 814 million instructions, but its
seed range is **277 million to 5.134 billion** (18.6x max/min). CVC5 SL's median
is 5.794 billion, versus 296 million for CVC5 arrays and 263 million for Z3 arrays.
At eight and sixteen heaplets, Nixie times out at every seed and CVC5 SL returns
Unknown at every seed; both array configurations solve every case. These formulas
have a simple five-cell witness regardless of the named four-cell heaplets, so
this is an implementation/search limitation, not a lack of a small finite model.
A seed-zero report would have overstated Nixie's four-heaplet median cost by 6.3x.

Distribution summaries are in the [aggregate CSV](2026-09-22-exact-heap-performance.csv).
The following medians are descriptive whole-pipeline measurements:

| Case | Nixie | CVC5 SL | CVC5 array | Z3 array |
|---|---:|---:|---:|---:|
| allocate-2 | 244.07 (10/10) | 280.46 (10/10) | 275.87 (10/10) | 253.43 (10/10) |
| allocate-4 | 247.83 (10/10) | 322.52 (10/10) | 287.83 (10/10) | 264.85 (10/10) |
| allocate-8 | 282.59 (10/10) | 623.31 (10/10) | 335.33 (10/10) | 448.11 (10/10) |
| allocate-16 | 433.48 (10/10) | 3705.63 (10/10) | 561.11 (10/10) | 3077.13 (10/10) |
| alias-2 | 242.80 (10/10) | 271.96 (10/10) | 270.38 (10/10) | 249.22 (10/10) |
| alias-4 | 243.51 (10/10) | 274.71 (10/10) | 272.24 (10/10) | 249.98 (10/10) |
| alias-8 | 245.47 (10/10) | 281.50 (10/10) | 277.32 (10/10) | 251.81 (10/10) |
| alias-16 | 251.71 (10/10) | 300.96 (10/10) | 294.14 (10/10) | 257.62 (10/10) |
| values-2 | 243.07 (10/10) | 273.21 (10/10) | 270.96 (10/10) | 249.10 (10/10) |
| values-4 | 244.03 (10/10) | 277.12 (10/10) | 273.23 (10/10) | 249.90 (10/10) |
| values-8 | 246.60 (10/10) | 287.86 (10/10) | 279.66 (10/10) | 251.81 (10/10) |
| values-16 | 255.23 (10/10) | 320.88 (10/10) | 300.81 (10/10) | 258.15 (10/10) |
| permutation-2 | 243.24 (10/10) | 286.36 (10/10) | 279.74 (10/10) | 253.16 (10/10) |
| permutation-4 | 244.47 (10/10) | 466.32 (10/10) | 300.31 (10/10) | 269.95 (10/10) |
| permutation-8 | 248.16 (10/10) | 2330.71 (10/10) | 385.19 (10/10) | 547.22 (10/10) |
| permutation-16 | 261.03 (10/10) | 27219.96 (10/10) | 839.24 (10/10) | — (0/10) |
| negative-2 | 255.22 (10/10) | 835.90 (10/10) | 283.23 (10/10) | 257.22 (10/10) |
| negative-4 | 813.85 (10/10) | 5794.11 (10/10) | 296.33 (10/10) | 263.32 (10/10) |
| negative-8 | — (0/10) | — (0/10) | 322.77 (10/10) | 275.96 (10/10) |
| negative-16 | — (0/10) | — (0/10) | 375.51 (10/10) | 302.95 (10/10) |

Millions of user-space instructions, median of completed runs; solved/10 in parentheses.
Min/max distributions and RSS are in the linked aggregate CSV. Unknown partial work is excluded.

| Comparison | Shared decisive cells / 200 | Geometric mean Nixie / reference |
|---|---:|---:|
| cvc5-sl | 180 | 0.441 |
| cvc5-array | 180 | 0.888 |
| z3-array | 170 | 0.894 |

| Case | Encode M instructions | Check M instructions | Extra validation instructions | Backend terms |
|---|---:|---:|---:|---:|
| allocate-2 | 0.565 | 1.504 | 2398.000 | 26 |
| allocate-16 | 6.517 | 183.515 | 21866.000 | 614 |
| alias-2 | 0.598 | 0.195 | — | 26 |
| alias-16 | 6.546 | 2.585 | — | 614 |
| values-2 | 0.790 | 0.250 | — | 32 |
| values-16 | 9.132 | 3.297 | — | 620 |
| permutation-2 | 0.965 | 0.318 | — | 34 |
| permutation-16 | 13.513 | 4.735 | — | 622 |
| negative-2 | 2.237 | 10.581 | 3813.000 | 146 |
| negative-16 | — | — | — | — |

The paired ratios use **different completion subsets**, so they cannot rank the
four configurations. In particular, the 0.888 ratio against CVC5 arrays excludes
the twenty seeded runs that arrays solve and Nixie does not. Completion counts and the
per-family table carry that missing information.

Nixie's endpoint regions identify useful costs without claiming a full profile.
At 16 allocated cells, encoding is 6.517 million instructions, check is 183.515
million, and an extra independent heap validation is only 21,866 instructions.
Backend terms grow from 26 at two cells to 614 at sixteen. Validation is not the
observed bottleneck in these completed allocation cases.

For the capped sixteen-heaplet negation probes, FIFO logs confirm that encoding
finished before the later timeout: its ten region counts span 124,338,368 to
124,341,775 instructions. The check probes time out; the ten validation regions
are never reached. Those encoding observations are diagnostic only and are not
included in completed-run aggregates above. The main expensive region is check,
not heaplet construction or the extra validation call.

The next investigation should examine relevance of pairwise heap-map definitions
and arithmetic search under all-negative heap assertions. In the source,
[HeapSolver::reify](../../nixie-solver/src/heap/mod.rs) permanently installs pairwise
relations; `check` asks the QF_LIA backend to solve before
[model extraction](../../nixie-solver/src/heap/model.rs) constructs its generic
all-false heap witness. This is a source-based hypothesis for follow-up, not a
profile proving the internal cause. The experiment makes no policy change or
hindsight-selected seed/configuration recommendation.

## Measurement interpretation

Each of 20 cases has ten seeds in each of four configurations: Nixie, CVC5 native
SL, CVC5 UF+arrays, and Z3 UF+arrays. These are 800 whole-pipeline cells. Another
240 Nixie cells measure encoding, checking, or an extra independent validation
call at the preregistered endpoint sizes. Reference versions are CVC5 **1.3.4**
and Z3 **4.16.0**. The machine is an Intel Core Ultra 7 265K; measurements are
pinned to CPU 2 and record the CPU-core PMU's retired user-space instructions.
Every counted interval requires at least 99.9% coverage and exactly one counted
instruction event. Raw records include exact binaries, input hashes, source
revision, flags, seed, machine identity, host load, and tool versions.

The primary metric covers the complete user-space pipeline, including the
Python harness, input translation, process launch, encoding, search, extraction,
independent finite-map checking, and destruction. It excludes kernel execution.
For small cases, most instructions are outside Nixie's measured encoding/check
regions. For example, allocation with two cells takes a median 244.07 million
whole-pipeline instructions, versus 0.565 million in encoding and 1.504 million
in check. **Do not interpret small whole-pipeline ratios as solver-kernel
speedups, or subtract separately measured regions to manufacture such ratios.**
The regions include FIFO-control overhead and need not sum to the total.

The reference configurations have different input interfaces and implementations.
These comparisons do not isolate the causal effect of a representation. They
also do not establish that native SL beats arrays, or that the current reduction
beats a native SL solver in general. All five families are synthetic; there are
no real-program verification corpora, inductive predicates, incremental workload
measurements, or heaps larger than the declared case sizes here.

Every decisive result is checked against an authenticated schema proof; every
SAT result also has an independently checked concrete heap. The UNSAT schemas
have direct proofs: duplicate ownership, contradictory values at one owned
address, or H AND NOT H. This is not validation of a Nixie-generated heap proof.
CVC5 cannot use `--check-models` with separation heaps, so the harness extracts
its actual heap model. No model following an `Unknown` verdict counts as a
validated SAT result.

Fixed budgets are 10,000 conflicts / 100,000 decisions for Nixie and 2,000,000
resource units for each reference solver. Resource units are not comparable
across solvers. The outer 20-second safety cap uses wall time only to stop a
run; wall time never controls solver policy or enters the primary cost metric.
The host had other load, recorded per cell: the one-minute load average before
runs ranged from 7.09 to 46.99 on 20 logical CPUs. Perf 7.1.8 ran on Linux 7.2.2
with Python 3.13.14. Completion counts are observations
under these exact budgets and environment, not a budget-normalized ranking.
All `Unknown` and timeout observations remain inconclusive. Their partial costs
are excluded from completed-run medians and paired ratios. A later region never
reached before timeout is explicitly `unmeasured_region`, with a zero storage
placeholder that is excluded from cost aggregates.

The extra validation region measures a second call to `validate_model`; `check`
already includes mandatory extraction and validation. Child peak RSS is retained
as a secondary diagnostic in the CSV; it can include the Python parent's
inherited memory floor and is not an isolated heap-solver memory measurement.
No wall-time, RSS, or seed-zero result is used to claim an improvement.

## Reproduction and evidence

Frozen binaries and raw immutable records are in
`precompile/32e2b695/benchmark/heap-exact-v1/` and
`precompile/32e2b695/benchmark/runs/heap-exact-v1/` on the measurement host;
`heap_perf` and `nixie` are cached in `precompile/32e2b695/`. Existing cells are
reused, never rerun. The committed aggregate CSV contains all case/configuration
medians, minima, maxima, completion counts, RSS and available backend term counts.
Regenerate the tables without invoking a solver:

```sh
python3 bench/heap_perf/analyze.py \
  precompile/32e2b695/benchmark/runs/heap-exact-v1 \
  precompile/32e2b695/benchmark/heap-exact-v1/analysis
```

Verification before the harness landed: all-feature build; 12,205 nextest tests
passed, 17 skipped; 114 doctests passed, 31 ignored; Clippy, formatting and
rustdoc warnings gates clean. Nextest used four threads. An initial run timed
out the existing repeat-search scope test during concurrent compilation; the
complete integrated rerun passed it at 299.729 seconds, without changing tests
or their timeout settings. Both run logs are retained. Z3 4.16.0 parity had 176
decisive agreements, one inconclusive (`array_unique`: Z3 Unknown), and no wrong
answers. The performance landing gate against `97b2b968` passed with conflict
and decision ratios of 1.000 on nine core cases and three external extensions.
Seven Python harness checks and twenty size-three calibration checks passed.
The calibration cases are not part of the measured matrix. Calibration fixed
the CVC5 constant-array option and established perf's five-byte FIFO acknowledgement
before preregistration; it did not tune any solver or select any measured seed.
