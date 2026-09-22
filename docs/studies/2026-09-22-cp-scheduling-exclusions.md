# CP snapshot and exclusion-witness costs

This experiment extends the existing optional cumulative implementation by
removing repeated work in its finite-domain callback. It adds no propagation
rule, task feature, search policy or proof shortcut. The external performance
reference is installed Z3 4.16.0; Nixie before/after comparisons are separate.

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
conclusions. Existing optional scheduling and exported-proof oracles remain
part of the full verification suite.
