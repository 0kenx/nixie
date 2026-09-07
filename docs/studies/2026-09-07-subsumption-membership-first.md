# Subsumption membership before binary-clause liveness

**Verdict: rejected at the one-seed screen; prototype removed.**

## Pre-registration

Baseline solver source: `482b806` (the following `4a88b3c` changes only
documentation). The si2-b03m cycle profile in the blocker-batching study
attributes 13.2% of samples to `subsume_round`.

The binary check currently loads `refs[bin_id]` and the arena clause before
reading `mark[other]`. If neither polarity of `other` occurs in the candidate,
the edge cannot subsume or strengthen it, regardless of whether its clause is
live. Read the mark first and reject zero marks before the dependent clause
loads. Keep the liveness check for every potential subsumption/strengthening.
CaDiCaL `src/subsume.cpp:try_to_subsume_clause` likewise tests `marked(other)`
in its binary shortcut; Nixie additionally needs liveness validation because
its BIG can retain stale edges.

This is an order-preserving filter, with no change to budgets, marks, RNG,
candidate selection, proof premises or produced clauses. Require byte-identical
printed solver counters and models, including the subsumption/elimination
counts and ticks. Add a regression that leaves a deleted binary edge in the
BIG and would incorrectly delete or strengthen a candidate if its membership
test bypassed liveness.

Measure all four available competition CNFs at 40,000 conflicts, CPU 10,
seeds 0–9, same perf-profile baseline binary and PMU events as the blocker
study. Reuse those baseline cells. Primary metric: whole-invocation user-mode
instructions; required cycle confirmation: amortized cycles/conflict, plus
branches and misses. Alternate arm order by seed. A one-seed screen can
reject but cannot justify a positive claim.

Go bar: at least 5% lower geometric-mean cycles/conflict, non-increasing
instructions and no family over 5% worse. A component improvement above 5%
with neutral end-to-end results may land under BENCHMARKING.md only with the
required evidence on all paths executing this shared pass. Otherwise remove
the prototype and retain the finding. Run the full repository verification
gates, explicit doctests, SAT differentials/model checks and Z3 parity before
landing source. Report Kissat and CaDiCaL reference measurements separately;
their different searches are not the paired engineering control.

## Screen result

Every printed search counter and verdict matches the baseline, including
the checked SAT model on si2-b03m. User-mode PMU event scheduling was 100%.

| seed 0, 40k conflict cap | instructions T/B | cycles/conflict T/B |
|---|---:|---:|
| j3037 | 0.9906 | 1.0714 |
| circuit_48in | 1.0004 | 1.0302 |
| constraints_17 | 0.9972 | 1.0352 |
| si2-b03m | 0.9989 | 1.0049 |

Instruction effects are below 1%; this fails the cycle bar. No improvement
claim is made from one seed. The code was removed before landing and no
new tests are needed for a production change that did not survive screening.
Dirty pilot records, the exact source patch, and raw outputs are in
`precompile/482b806/benchmark/bcp-blocker-batching/membership-first/`, with
schema records in `runs/bcp-blocker-batching/`. They are not reusable
committed-source results.

The source-level profile explains the small leverage: the hottest
subsumption samples lie in the longer-clause loop, not the binary shortcut.
The separate elimination profile has a much sharper concentration: over
half its samples are in the CSR connect loop. That loop reconstructs an
absolute fill address from a span boundary plus a relative cursor for every
occurrence, then increments a second occurrence count already computed by
the preceding sizing pass. This is a separate, directly observed target.
