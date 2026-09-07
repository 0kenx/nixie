# Structured propagation regions: registered traffic screen

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
and counters. Scope changes never allow deleted support clauses to certify
traffic. The observer has no solver-state semantics.

## Fixed telemetry

The opt-in `bcp-regions` feature is absent from default builds. Sample every
256th propagated trigger with a nonempty binary or long-watch list, using a
per-solver deterministic ordinal. Observe only entries actually visited,
including conflict-prefix termination. Classify binary edges and long watchers
separately. For each, count visits, immediate satisfaction, clause-payload
accesses, replacement-tail literal inspections, propagations and conflicts.
Report visits before search, during conflicts 1–16,383, and from 16,384 onward.

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
