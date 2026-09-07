# Structured propagation regions: registered traffic screen

**Result: the registered AND/XOR subset fails on all three inputs.** No gates
were recognized in the activation snapshots. The same census shows substantial
learned-clause traffic. A post-hoc static audit also identifies a different,
exactly factorable eight-variable representation in circuit; it is described
separately below and does not reopen the failed screen.

This is idea 2 from the [propagation agenda](2026-09-07-nixie-propagation-redesign.md),
following the rejected shared-blocker tile kernel. The question is whether
recognized structure accounts for enough actual BCP work to justify a native
block representation. Gate counts alone cannot answer it.

## Scope and semantic reference

Observe the existing solver without changing assignments, clauses, watch
order, reasons, schedules, ticks or verdicts. Detect two-input AND definitions
from one ternary and its two binary side clauses, following CaDiCaL
`src/gates.cpp::find_and_gate` and Nixie's congruence detector. Recognize strict
three-variable XOR parity classes using Nixie's existing `XorDetector`, with
canonical literal order. Require every defining clause; no approximate match.
Retain exact clause IDs and literal signatures as certificates.

At activation, take a bounded snapshot of live original binary/ternary clauses.
Deduplicate equal signatures deterministically. Join detected gates that share
variables using iterative union-find. Components of at least four gates are
candidate regions; smaller components are reported separately. These are
undirected candidate components, not compiled acyclic circuits. ITE,
cardinality, larger parity constraints and native SMT structure are outside
this first screen. Failure only rejects this recognized subset on this panel.

At every sampled event, a gate clause counts as certified only if all clauses
of at least one retained certificate still exist, are live original clauses,
and have exactly their recorded literals (order independent). Count invalidated
certificates separately. Component labels refer to the activation snapshot;
live components may later split. Therefore even certified candidate-region
traffic is an optimistic opportunity for this snapshot's blocks, not proof
that a whole block is currently executable. Clause IDs are never reused.
New clauses and variables are classified against the fixed snapshot; repeated
solves accumulate observations, and explicit activation replaces the snapshot
and counters. A full solver reset discards the snapshot before IDs restart.
Scope changes never allow deleted support clauses to certify
traffic. The observer has no solver-state semantics.

## Fixed telemetry

The opt-in `bcp-regions` feature is absent from default builds. Sample every
256th propagated trigger with a nonempty binary or long-watch list, using a
per-solver deterministic ordinal. Observe only entries actually visited,
including conflict-prefix termination. Classify binary edges and long watchers
separately. For each, count visits, immediate satisfaction, clause-payload
accesses, replacement-tail literal inspections, propagations and conflicts.
Report visits at conflict count zero, during conflicts 1–16,383, and from
16,384 onward. The zero bin includes search before its first conflict.

Classes distinguish certified candidate-region clauses, certified small-gate
clauses, invalidated gate certificates, other original clauses, learned
clauses and missing/deleted clauses. Non-gate original and learned clauses
are each split into entirely within one candidate region, crossing its
boundary, and outside. Boundary labels describe variable incidence, not an
explanation-cost estimate. Propagation/conflict counts measure requests for
reasons; they do not measure the cost of expanding future block explanations.

Cap snapshots at two million variables, two million distinct short-clause
signatures and two million gates. Reject activation on exhaustion rather than
silently omit data. Counters describe sampled BCP events; they are not a
complete physical cost metric. Instrumented times and cycles are not compared.

## Three-cell decision

Start from `9b330d4`. Run only three observed cells, CaDiCaL preset, CPU 2,
seed 1: break and circuit under the existing ten-million-conflict cap, and
noL capped at 100,000 conflicts. Reuse controls `50fa8316e92aed2a`,
`a6b0151744a458c1` and `4e70e8d19a55d4c0`. Byte-compare complete stdout and
independently check the circuit SAT model. Record each cell once in benchstore,
with manifests, source/binary/input hashes and raw reports. No reference runs,
new controls, seed sweeps or configuration tuning.

Advance this subset to a shadow block evaluator only if at least two inputs
have **≥25% of all sampled edge-plus-watch visits in certified candidate-region
clauses**, with no omitted coverage or changed stdout. The same ≥25% threshold
must hold for visits at conflicts ≥16,384 on each passing input. Also report
binary/long coverage separately, replacement-scan coverage, reason demand and
boundary traffic. The combined visit fraction is a structural event statistic,
not an equal-cost model of binaries and long clauses or a predicted speedup.
Passing justifies measuring execution, boundary and explanation costs in the
next step; it cannot justify a kernel or a default change. Failure stops this
registered subset without tuning or further performance runs.

Before landing the observer, run all required workspace gates, targeted
certificate/compaction/scope/conflict-prefix tests, exact diagnostic/proof
identity tests, and fresh available-Z3 parity. The observer is explicitly
activated in the parity library runner for an additional instrumented check.

## Observation format and verification details

The report schema is `nixie-region-traffic/1`. `counts[channel][class][metric]`
uses channels binary / long watchers, and these classes in order:
candidate-region gate, small gate, invalidated gate certificate, other original
local / boundary / outside, learned local / boundary / outside, missing or
deleted clause. Metrics are visits, immediate satisfaction, payload-access
attempts, replacement-tail inspections, propagations and conflicts.
`by_conflicts[bin][channel][class]` stores visits in the three registered bins.
Immediate satisfaction means a true implied literal for a binary edge or a
true cached blocker for a long watcher; it excludes later satisfaction tests.
Original/learned classes follow the current clause header, not an immutable
derivation history. Sampling and these counters never enter a solver budget.

The canonical first copy of each equal short-clause signature supplies the
certificate. Duplicate copies outside those selected certificates are counted
as other clauses. A changed or removed support clause invalidates its retained
certificate even if an equivalent replacement was added under a new ID. Thus
this census is neither complete extraction of all possible encodings nor an
upper bound on all possible structural optimizations.

`stats_solve` activates the snapshot after parsing with `NIXIE_REGION_STATS=256`.
For additional SMT parity, the standalone harness's `bcp-regions` feature and
`NIXIE_REGION_PARITY=1` activate every SAT solver's hooks against an empty
reference snapshot. This exercises counting/classification throughout the
private Context runner; direct truth-table, scope, mutation, conflict-tail and
LRAT-identity tests cover the nonempty certificate paths. This parity switch
is absent from ordinary builds and is cleared by the measurement runner.

## Implementation verification

Nine focused tests cover signed AND/XOR truth tables, incomplete/duplicate
encodings, exact certificate repair/invalidation, arena relocation, component
and boundary classes, capacity errors, push/pop, full reset with reused IDs,
binary/long conflict prefixes, and exact SAT/UNSAT search and LRAT transcripts.
The observer and runner are opt-in; there is no block evaluator or search-policy
change in this slice.

All required gates passed after integrating the concurrent SMT/BV changes:
workspace all-features build; 10,652 nextest tests (12 skipped); 111 doctests
(29 ignored); strict clippy, fmt and strict docs. Fresh Z3 4.16.0 parity gave
169 agreements, zero disagreements and one inconclusive case in both ordinary
and instrumented library runners. `array_unique.smt2` is unresolved because
Z3 returns Unknown; it is not counted as an agreement.

Integration also fixed formatting in the incoming `injective_repair` test and
a public rustdoc link to a private AST method. The latter was the sole source
change after the full tests; reconstructing its old comment reproduced the
exact tested source fingerprint. Strict docs and both parity runs then passed
on the final source. Partial pre-integration checks and the failed docs check
are retained separately from the completed verification.

## Registered result

Exactly three new observation cells completed at seed 1, using all three
cached controls. Complete stdout was byte-identical in every cell, including
search diagnostics and the circuit model. That model also satisfies every
original input clause. Break's reported UNSAT has no newly checked proof;
its canonical record remains unverified/unknown. NoL reports Unknown at the
100,000-conflict cap. These are observations, not throughput comparisons.

| Input | Reported answer / conflicts | Distinct short clauses at activation | Sampled edge-plus-watch visits | Recognized AND/XOR gates | Registered gate |
|---|---|---:|---:|---:|---|
| break_unsat_06_07 | UNSAT / 33,293 | 4,388 | 389,608 | 0 / 0 | fail |
| circuit_48in64out | SAT / 186,114 | 0 | 3,138,836 | 0 / 0 | fail |
| noL_11_14 | Unknown / 100,000 | 7,821 | 730,306 | 0 / 0 | fail |

Certified region traffic is zero overall and in the late conflict bin on all
three inputs. No capacity limit was exceeded. The registered ≥25% coverage
criterion therefore fails, and no shadow AND/XOR block evaluator or additional
performance run follows. This is an absence of the recognized patterns, not
an invalidation-rate result or a claim that all useful structure is absent.

### Learned clauses account for much of the observed work

| Input | Learned visits / all visits | Learned share from conflict 16,384 onward | Learned tail inspections / all tail inspections | Learned propagations / all propagations |
|---|---:|---:|---:|---:|
| break | 350,270 / 389,608 = **89.90%** | **93.28%** | 283,720 / 301,711 = **94.04%** | 2,766 / 20,307 |
| circuit | 1,735,463 / 3,138,836 = **55.29%** | **56.19%** | 1,177,736 / 1,666,682 = **70.66%** | 22,957 / 81,765 |
| capped noL | 639,354 / 730,306 = **87.55%** | **88.67%** | 453,132 / 510,147 = **88.82%** | 2,336 / 15,186 |

These are sampled BCP counts. Visits include both binary edges and long
watchers; tail inspections are literal checks after the watched pair. The
denominator also retains visits to missing/deleted clauses (722 on break,
11,181 on circuit, zero on noL). Original/learned status is the live header
flag. These observations do not price an edge and a long watcher equally in
cycles, count full explanation expansion, or establish clause usefulness.
Learned clauses can prevent large amounts of search without often being the
immediate reason. In particular, low direct-use counts do not justify deleting
them. The result motivates idea 3's per-clause traffic/use census and a separate
matched-null design before any retention policy is tested.

## Post-hoc static audit: circuit uses eight-variable relations

The zero result prompted a read-only input audit, without another solver run.
Circuit contains **64 unit clauses and 168,000 clauses of width eight**, so
the registered short-clause recognizer cannot represent its structure.
Break's raw widths are `{1: 1, 2: 4482, 3: 386, 4: 18, 10: 150}`; noL's are
`{1: 14, 3: 7821}`. Activation counts above are after parsing/normalization
and canonical deduplication, and are not raw input-width counts.

Group circuit's non-unit clauses by their sorted eight variable IDs. Each
clause forbids one complete assignment: a positive literal contributes a zero
bit and a negative literal a one bit. All **700 groups** contain **240 distinct
forbidden assignments**, leaving **16 allowed assignments** each. This accounts
for every non-unit input clause. All 70 four-variable projections were checked
against each group's allowed rows. Every group has a bijective projection onto
four Boolean inputs: 655 groups have one possible projection, 42 have two,
one has three and two have four. These are exact local relation facts.

There is consequently a simple smaller encoding. Choose the lexicographically
first valid projection. For each of its 16 input assignments and each of the
four remaining variables, emit the implication from those four input values
to that output value. This yields **64 clauses of width five per group**.
An exhaustive check of all 256 assignments for each of the 700 groups
(179,200 assignment checks) found exactly the same allowed rows as the original
encoding. Shared variables between groups do not invalidate local logical
equivalence, and the 64 original units remain unchanged.

| Non-unit representation | Clauses | Literal slots |
|---|---:|---:|
| Original eight-variable relations | 168,000 | 1,344,000 |
| Audited four-input/four-output factorization | 44,800 | 224,000 |

That is **73.33% fewer non-unit clauses and 6× fewer non-unit literal slots**.
It is an offline, exhaustively checked encoding candidate; it has not been
applied by Nixie or benchmarked. The smaller encoding also propagates outputs
after four input assignments, so it changes search and cannot be presented as
a trajectory-preserving throughput optimization.

**Next circuit-specific candidate:** implement proof-emitting factorization of
these small relations, with original-clause provenance, exact equivalence
checks, deterministic extraction bounds and a complete fallback. Resolve away
the three unmentioned outputs to justify each five-literal clause through
checkable intermediate steps; do not claim that an arbitrary final clause is
already RUP. Register the comparison and its matched null before performance
evaluation, and keep the strongest relevant Kissat reference. Actual native
table propagation would additionally need incremental state, backtracking and
explanations. The offline size reduction is not a measured runtime improvement.

This audit is exploratory and specific to circuit. It does not change the
AND/XOR screen's verdict or qualify a default change. The learned-clause
traffic on break and noL remains the broader throughput lead.

## Stored evidence

Registration: `c92e953` (also carried into main as `ef0a426` during concurrent
integration). Observer and measured source:
`2f8df46f3aff2e9833f84c53e5abe41d44a35c91`.
Binary: `precompile/2f8df46/stats_solve-regions`, SHA-256
`9ec366caba31dda56d6b71f0c7097d45623baf2de3b1b3fc65461c736e631f67`.
The build manifest records Rust 1.96.0, the portable release recipe, final
source fingerprint and dependency-lock hash. Concurrent SMT/BV changes were
included in verification; they do not change the DIMACS SAT search paths used
by these cells, whose complete stdout matched their controls.

| Input | Observation record | Reused control |
|---|---|---|
| break | `815c59961e36e0ae` | `50fa8316e92aed2a` |
| circuit | `14a9f7a6db3d615f` | `a6b0151744a458c1` |
| capped noL | `0f8746909b6f6bd5` | `4e70e8d19a55d4c0` |

Manifests, raw stdout/stderr, summaries and the verdict are in
`precompile/2f8df46/benchmark/structured-region-traffic/`; canonical records
are under that commit's `benchmark/runs/structured-region-traffic/`.
The same raw directory contains `input-width-audit.json`,
`circuit-relation-audit.json` (all supports, allowed rows and valid projections)
and `circuit-factorization-audit.json` (chosen projections and replacement
clause hashes). These static analyses introduce no new solver cells.

The final correctness logs and both fresh parity reports are in
`precompile/2f8df46/benchmark/region-traffic-verification/`; interrupted
pre-integration checks and the incoming formatting failure have separate
directories. Binary hashes, canonical record IDs, control stdout and report
arithmetic were independently checked from saved artifacts. The temporary
worktree and build products are removed after landing the result; cached
binaries and canonical evidence remain available for reuse.
