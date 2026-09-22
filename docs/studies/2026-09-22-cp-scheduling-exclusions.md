# CP snapshot and exclusion-witness costs

This experiment extends the existing optional cumulative implementation by
removing repeated work in its finite-domain callback. It adds no propagation
rule, task feature, search policy or proof shortcut. The external performance
reference is installed Z3 4.16.0; Nixie before/after comparisons are separate.

Candidate `44f30970` passes the pre-registered performance bar. On confirmation
seeds its ordinary/certified **Nixie/Z3 instruction ratios are 0.4778/0.5086**.
Against the preceding Nixie baseline, ratios are 0.8951/0.8984 (about 10% fewer
instructions). These are paired geometric means, not wall-clock speedups.

## Protocol and ablation

The [pre-registration](../../bench/cp_perf/explanation_protocol.md) fixes the
acceptance bar, controls and measurements before each candidate. Baseline
`345ecfec` includes the previous bounds/model-evaluation reuse and subsequent
main changes. The baseline sparse 8x16 profile identifies domain reconstruction
and repeated exclusion-witness searches as substantial costs.

First-stage `0bb2d4f6` retains a fixed indicator's premise position while
reconstructing each callback's immutable domains. An exclusion uses that index
and its known domain, instead of searching every domain and reason again.
The unchanged independent checker still validates every produced witness.
Selection ordinary/certified current/previous ratios were 0.9629/0.9637:
**neutral, below the pre-registered bar**, despite an improvement on larger
cases. This stage is retained as an ablation, not reported as a standalone win.

The second stage removes BigInt membership scans for unknown indicators: in
a valid snapshot of unique values, an unknown indicator is excluded exactly
when a different indicator is fixed true. It also borrows the selected fixed
value during reconstruction and stops cloning discarded alternatives. Global
candidate trials still run in their original order, including for values
already excluded by exactly-one semantics. First witnesses and all premises
remain identical.

The unchanged benchmark driver, reference harness, external release profile
(default features, debug level 1), lockfile and compiler match both Nixie arms.
The primary metric is whole-process `instructions:u` pinned to CPU 0, requiring
at least 99% counter coverage. Z3's matching `df564313` cells are reused, not
rerun. Selection seeds are 0..9; confirmation seeds 10..19 are fresh to this
candidate, not a new corpus. Raw outputs, counters, profiles, manifests and
immutable benchstore records are retained in the primary binary cache.

These are seven SAT admission/integration families, 4x4 and 8x16 shapes,
ordinary/certified modes and two push/check/pop rounds. They do not measure
hard packing, UNSAT proof scaling or general SMT speed. Nixie's checking is
inside the measured process; Z3's extracted models are checked independently
in Python outside Z3's measured process. Unknowns are never counted as solves.
Callback-only diagnostics have no directly comparable Z3 API.

## Confirmation results

| Mode and shape | Previous Nixie / Z3 | Current Nixie / Z3 | Current / previous Nixie |
|---|---:|---:|---:|
| Ordinary, all | 0.5338 | 0.4778 | 0.8951 |
| Ordinary, 4x4 | 0.1860 | 0.1802 | 0.9692 |
| Ordinary, 8x16 | 1.5321 | 1.2666 | 0.8267 |
| Certified, all | 0.5661 | 0.5086 | 0.8984 |
| Certified, 4x4 | 0.2049 | 0.1992 | 0.9719 |
| Certified, 8x16 | 1.5640 | 1.2989 | 0.8305 |

No family regresses beyond the 5% neutral band. Ordinary family ratios versus
previous Nixie are absent 0.9002, blocked 0.9153, present 0.9521 (neutral),
shared 0.9144, sparse 0.8132, unknown 0.9064 and wide 0.8709. The larger sparse
case falls from 9.3031 to 6.7606 times Z3's instructions: a substantial remaining
gap despite the improvement. The larger all-present case remains 2.2557 times
Z3. Small startup-sensitive cases must not hide those limitations.

Selection ordinary/certified ratios versus previous Nixie were 0.8953/0.8984;
the confirmation grid supports the same result. Isolating the second stage
against the first-stage ablation gives selection ratios 0.9297/0.9323. We did
not measure confirmation cells for the neutral first stage alone.

The [paired CSV](2026-09-22-cp-scheduling-exclusions.csv) retains all 280
confirmation comparisons and each ten-seed baseline distribution. Each seed
grid has 280/280 decisive checked Nixie SAT cells per arm and 140/140 checked
Z3 SAT cells, with no lost, censored or invalid-model cells. All paired Nixie
transcripts agree byte for byte, including search counters. The same Z3 cells
serve both modes; they are not independent additional reference samples.

Callback diagnostics also retain 280/280 exact transcript matches per grid
(140 partial callback states and 140 small public solves). Their confirmation
callback ratio is 0.9614, neutral overall; absent is 0.9117 and wide is 0.9494.
Other callback families are neutral, and none regresses beyond 5%. Partial
callback `Unknown` states are not counted as SAT solves. These component
figures compare Nixie revisions, not Nixie with Z3.

## Soundness and certification audit

- Construction rejects duplicate values and indicators. Thus an unknown
  indicator cannot denote the same value as a different true indicator.
- Snapshot values and reason order are preserved, including malformed values,
  conflicting true indicators and the last selected value in an invalid
  snapshot. Invalid snapshots exit before the optimized membership test.
- Presence premises are appended after domain premises. Shared or complemented
  presence aliases cannot change the first domain witness's position. Scheduling
  arithmetic and absent-task semantics remain in the existing feasibility code.
- Witness hints are untrusted. `DomainCertificate::check` still verifies the
  exact original domain, positive premise, excluded value and index bounds.
  The solver separately authenticates the statement and checks premise truth.
- Independent CP model validation, callback model replay, original-declaration
  finite lemma checking, Boolean reconstruction and LRAT/export/import checking
  are unchanged. The producer's hint is not an axiom accepted by those gates.
- The extra index vector exists only in one callback's snapshot. It cannot
  retain a decision across callback, model, push/pop or reset boundaries.

The new exhaustive regression checks all 4,096 unknown/false/true/malformed
assignments of six indicators across three domains with 141-bit values and a
presence alias. It compares snapshot domains with a separate reconstruction,
checks every exclusion against an independent exactly-one oracle, compares
every witness with the original search, and checks every emitted implication
against the independent finite-domain lemma checker. A second regression
rejects foreign/negative/same-value/out-of-range premise hints and malformed
conclusions. A third pins the original global witness when both an all-different
constraint and exactly-one semantics exclude the same value. Existing optional
scheduling and exported-proof oracles remain
part of the full verification suite.

## Verification setup

All Cargo compilation uses release mode. Full workspace tests use local
`CARGO_PROFILE_RELEASE_LTO=false` and `CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16`
in a separate verification target directory; optimization level remains 3.
The first full-LTO test build and a queued refresh were interrupted before
running tests because linking hundreds of test executables was costly. Their
logs are retained. Production CLI build/parity/perf gates use the repository's
usual release profile; CP instruction measurements use the unchanged external
profile described above. No profile change is credited as a CP optimization.
An attempted focused test invocation through the external driver manifest
was rejected because dependency packages with dev-dependencies cannot be tested
as members of that driver workspace; the real workspace suite is the test gate.
