# Learned-clause traffic and later direct use

**Result: the registered breadth gate fails.** The temporal cost signal passes
on j3037 but fails on circuit. No active-set policy or default change follows.

## Registered question

This is the next stage of idea 3 in `2026-09-07-nixie-propagation-redesign.md`.
The region census already found learned clauses responsible for 55–90% of
sampled visits. Previous usage-versus-glue and retention-percentage studies
did not establish a useful policy. The new question is whether **recurring
propagation cost per clause** supplies information those scores miss.

Add a compile-time `clause-traffic` observer, absent from ordinary builds.
Select clause IDs with a fixed hash and stride 16, independently of their
traffic, size, glue, tier, use or solver RNG. For every selected learned
clause, count all actual binary/long visits, blocker hits, payload accesses,
replacement-tail inspections, unit propagations, conflicts and clauses
expanded in the main first-UIP resolution loop. Keep separate 4,096-conflict
epochs and record the observed length, glue and tier when each row starts.
Track sampled original/deleted traffic separately. Do not call a clause
"unused": the census does not price minimization, proof traversal, or the
search it might prevent without ever becoming a direct reason.

Counter storage is bounded, with explicit omitted-event and overflow flags.
IDs are append-only inside one observation session. Starting a solve,
push/pop and full reset clear the session; reports describe only the current
session. The observer must not alter clauses, trail values, RNG, watch order,
tick schedules, proof IDs or any solver budget. Compare full diagnostics and
proof transcripts in tests. The semantic reference is the existing Nixie
propagation/resolution loops and Kissat `proplit.h`, `analyze.c`, `reduce.c`.

Exactly **two new observation runs**: circuit_48in64out and j3037_10_mdd_bm1,
seed 0, 40,000-conflict cap, CPU 10. Reuse the clean `2202f0e` scalar outputs
from the persistent-blocker screen as exact trajectory controls; do not rerun
them or Kissat. Use a committed portable release binary. Instrumented time
and PMU cost are not performance estimates. Record every cell once through
`benchstore.py`, with source/binary/input hashes and raw reports.

For each completed adjacent epoch pair, rank sampled learned clauses by
prior-epoch payload accesses plus tail inspections (ties by clause ID).
Report the top quarter's fraction of next-epoch measured work, and the part
of that work belonging to clauses with zero next-epoch direct units,
conflicts or first-UIP uses. Separately report all-clause work/use
concentration, tier/glue/length strata, and observations censored by deletion
or missing future rows. Missing rows are **not** zero future use. Exclude the
partial final epoch from prediction. This is a prospective prediction check
on the existing trajectory, not a counterfactual deletion experiment.

Advance to a cost-aware active-set policy only if both inputs have at least
1,000 sampled learned rows, no observation omissions/overflow or trajectory
difference, and the previous epoch's most expensive quarter accounts for at
least 25% of next-epoch work with zero observed direct use in at least half
the eligible epoch pairs. Otherwise close this signal at this screen. No
parameter/stride/epoch-width search follows the result.

A later policy needs a matched null with identical physical accounting,
selection counts, timing and code paths, but cost histories assigned to
different eligible clauses. It must include accounting/reactivation work and
compare total work and solved-at-cap, not just cycles/conflict. This census
does not license changing solver defaults or claim a speedup.

Before landing the observer: targeted count, tail, lifecycle, capacity and
exact proof/search-identity tests; full workspace build, nextest, doctests,
clippy, formatting and strict docs; fresh available-Z3 parity. Retain the
source, toolchain and all evidence in the binary/result cache.

## Observation interface

Build `stats_solve` with `--features clause-traffic` and set
`NIXIE_CLAUSE_TRAFFIC=16`. Library callers use
`Solver::enable_clause_traffic(NonZeroU64)` and
`Solver::write_clause_traffic(writer)`. The JSON schema is
`nixie-clause-traffic/1`; each row identifies one clause in one epoch. Its
`counts[channel][metric]` uses binary/long channels and metrics visits,
immediate blocker hits, payload accesses, tail inspections, unit assignments,
conflicts, and main first-UIP expansions. The initial conflict clause also
counts as one first-UIP expansion when that loop reads it. Consequently these
are event counts, not counts of distinct semantic uses.

Length/glue/tier are observed at the row's first event, not necessarily at
learning or the epoch boundary. Tier values are Local=3, Mid=2, Core=1.
`final_status` is the clause's status when the report is written, not a
retirement timestamp. Original and deleted clauses have separate aggregate
counters. Literal order, strengthening and arena relocation cannot alias
IDs; a promoted original stops adding learned rows. Reset clears records
before IDs restart.

The storage cap is 250,000 clause/epoch rows; the ID index cannot exceed the
row count. Exceeding it reports omitted events by channel/metric. Counter
overflow is also explicit. Neither failure influences solving. The analysis
script refuses either kind of incomplete census. A shared diagnostic session
guard prevents nested public solve calls from clearing outer preprocessing
counts; all early returns release it, and it preserves Solver's Send/Sync
traits. The observer remains enabled after push/pop/reset but starts with
empty records. Re-enabling explicitly also starts a fresh session.

`bench/suite/scripts/clause_traffic_probe.py` checks the exact cached control
stdout and applies the registered analysis. Top-quarter selection uses the
prior epoch only, descending work with clause-ID tie breaks, taking
`max(1, floor(prior_rows / 4))` clauses. Its future-work denominator includes
all learned rows in the next epoch, including newly observed clauses.
Missing future rows remain censored even if the clause is deleted at report
time. Four independent Python tests cover hindsight selection, partial
epochs, missing future rows, direct uses, and invalid observation reports.

The standalone parity harness has a `clause-traffic` feature.
`NIXIE_CLAUSE_TRAFFIC_PARITY=1` explicitly activates stride-one collection in
every constructed SAT solver, including Context's private cores. This is
only available in instrumented builds and is cleared for ordinary parity
and benchmark runs.

## Registered result

Source `27e79fcf05b9a02738ab4b8de2a500b409c98581`; exactly two new census
invocations, both at seed 0 and the 40,000-conflict cap. Both report Unknown,
as do their cached `2202f0e` controls. Complete stdout is byte-identical for
each pair, including every printed search counter. No observations were
omitted and no counter overflowed. No control or reference cell was repeated.

| Input | Sampled learned clauses | Clause/epoch rows | Payloads + tail inspections | Passing complete epoch pairs | Registered gate |
|---|---:|---:|---:|---:|---|
| circuit_48in64out | 2,502 | 5,836 | 1,311,095 | 0 / 8 | fail |
| j3037_10_mdd_bm1 | 3,056 | 11,142 | 7,045,142 | 4 / 8 | pass |

The table below gives the fraction of next-epoch work caused by the previous
epoch's most expensive quarter **with zero next-epoch observed direct use**.
The threshold was 25% in at least half of each input's eligible pairs.
The incomplete final epoch is excluded, and missing future rows contribute
no hypothetical unused work.

| Prior epoch | Circuit | j3037 |
|---|---:|---:|
| 0 | 2.51% | 19.49% |
| 1 | 5.07% | 24.47% |
| 2 | 1.98% | 20.51% |
| 3 | 3.56% | 29.04% |
| 4 | 7.63% | 32.71% |
| 5 | 4.37% | 24.46% |
| 6 | 14.65% | 33.34% |
| 7 | 18.88% | 28.91% |

The broad active-set premise therefore does not advance. A j3037-only gate
selected after seeing these results would be a new, hindsight-selected
hypothesis, not a passing version of this registration. Do not tune the
epoch width or selection fraction against these two observations.

### What the traffic actually supports

The most expensive tenth of sampled learned clauses accounts for 40.74%
of measured work on circuit and 40.20% on j3037. However, clauses with **no
observed direct use anywhere in the run** account for only 6.01% and 5.77%
of work respectively. Much of the cost belongs to clauses used at some
point; a rarely used clause is not necessarily dispensable. Missing
minimization/proof/indirect search uses make even those small fractions
optimistic opportunities, not justified deletions.

Length strata offer an implementation lead, not a new policy result. Clauses
of observed length 3–6 account for 47.27% of learned work on circuit but only
10.82% on j3037; ternaries alone account for 3.03% and 0.74%. Clauses of
length at least 17 account for 30.95% and 65.98%. Thus an inline-ternary
kernel cannot address much of this measured learned-clause cost. A cheaper
representation/processing path for useful clauses has broader potential
than a policy that merely removes high-traffic clauses. The existing
grouping census remains relevant, but any new representation must avoid the
per-entry maintenance that defeated the previous tile and mask kernels.

These are exact event counts on sampled identities and two search prefixes.
They are not cycles, full-corpus estimates, or measurements of a policy that
was never run. This step does not close the Kissat throughput gap.

## Verification and evidence

All required gates passed on the implemented source: all-features build;
**10,696 nextest tests** (12 skipped); **111 doctests** (29 ignored); strict
all-target clippy; formatting; strict documentation. The all-feature SAT
library's **747 tests** include nine new census/propagation regressions.
The four Python analysis tests pass. The tests cover counts, epoch changes,
sampling, deleted/original classification, capacity and overflow, writer
errors, conflict tails, mid-visit assignments, nested sessions, scopes,
reset, Send/Sync, and exact SAT/UNSAT model/search/LRAT transcript identity.

Fresh ordinary and explicitly instrumented Z3 **4.16.0** parity each report
**169 correct, zero disagreements, one inconclusive** out of 170.
`array_unique.smt2` is Nixie UNSAT / Z3 UNKNOWN and is not counted as an
agreement. Source fingerprints confirm the compiler inputs did not change
between verification and the committed observation build.

Canonical census records:

- Circuit: `d2d350a53ab84ab2`, reusing control `14ed9b8263997cd2`.
- j3037: `a984dde3270003c3`, reusing control `0bebb5d32ccff96d`.

They live under `precompile/27e79fc/benchmark/runs/learned-clause-traffic/`.
The sibling `learned-clause-traffic/` directory contains the manifest,
immediate subprocess records, exact stdout/stderr, reports and summaries.
`precompile/27e79fc/clause-traffic-build.json` pins the lockfile, toolchain,
portable release recipe and binary SHA-256
`b1f5d1bb3f3f3766bbac9fa4877378234b131e6f595362081b49bd392a1547bb`.
The separate observation build and the verification pipeline's observation
build produced the same binary hash. Verification logs, ordinary and
instrumented parity records, and compiler-source fingerprints are retained
under `precompile/27e79fc/benchmark/clause-traffic-verification/`.
