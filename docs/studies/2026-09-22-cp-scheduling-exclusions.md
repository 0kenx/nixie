# CP snapshot and exclusion-witness costs

This experiment extends the existing optional cumulative implementation by
removing repeated work in its finite-domain callback. It adds no propagation
rule, task feature, search policy or proof shortcut. The external performance
reference is installed Z3 4.16.0; Nixie before/after comparisons are separate.

The CP-only candidate `afb4e85b` reduces instructions by about 10%. After
integrating main through `10d37a7d`, candidate `f43db048` retains an 8.5–8.7%
reduction against the preceding Nixie baseline. Its confirmation
**Nixie/Z3 instruction ratios are 0.4871/0.5178** for ordinary/certified solving.
These are paired geometric means, not wall-clock speedups. Both candidates
pass the pre-registered performance bar; the integration delta is separate
from the CP optimization's effect.

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

## CP-only confirmation results

| Mode and shape | Previous Nixie / Z3 | Current Nixie / Z3 | Current / previous Nixie |
|---|---:|---:|---:|
| Ordinary, all | 0.5338 | 0.4778 | 0.8951 |
| Ordinary, 4x4 | 0.1860 | 0.1802 | 0.9692 |
| Ordinary, 8x16 | 1.5321 | 1.2667 | 0.8267 |
| Certified, all | 0.5661 | 0.5086 | 0.8984 |
| Certified, 4x4 | 0.2049 | 0.1992 | 0.9719 |
| Certified, 8x16 | 1.5640 | 1.2988 | 0.8304 |

No family regresses beyond the 5% neutral band. Ordinary family ratios versus
previous Nixie are absent 0.9002, blocked 0.9153, present 0.9521 (neutral),
shared 0.9144, sparse 0.8132, unknown 0.9064 and wide 0.8709. The larger sparse
case falls from 9.3031 to 6.7610 times Z3's instructions: a substantial remaining
gap despite the improvement. The larger all-present case remains 2.2557 times
Z3. Small startup-sensitive cases must not hide those limitations.

Selection ordinary/certified ratios versus previous Nixie were 0.8953/0.8984;
the confirmation grid supports the same result. Isolating the second stage
against the first-stage ablation gives selection ratios 0.9297/0.9323. We did
not measure confirmation cells for the neutral first stage alone.

The optimization-only source is `44f30970`; its confirmation ratios were also
0.4778/0.5086 against Z3 and 0.8951/0.8984 against previous Nixie. After the
release-Clippy guard fix below, `afb4e85b` repeats the confirmation grid with
a newly frozen binary, retaining every transcript and the same finding.
This is integration replay, not additional independent selection data.

The [paired CSV](2026-09-22-cp-scheduling-exclusions.csv) retains all 280
final merged confirmation comparisons and each ten-seed baseline distribution. Each seed
grid has 280/280 decisive checked Nixie SAT cells per arm and 140/140 checked
Z3 SAT cells, with no lost, censored or invalid-model cells. All paired Nixie
transcripts agree byte for byte, including search counters. The same Z3 cells
serve both modes; they are not independent additional reference samples.

Callback diagnostics also retain 280/280 exact transcript matches per grid
(140 partial callback states and 140 small public solves). Their confirmation
callback ratio is 0.9615, neutral overall; absent is 0.9117 and wide is 0.9494.
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

## Verification setup and retained attempts

All Cargo compilation uses release mode. Nextest workspace tests use local
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

Release Clippy exposed a pre-existing configuration mismatch in SAT diagnostics:
`check_fixpoint` was compiled in release unit tests although its only caller
is guarded by `debug_assertions`. Its definition now uses the same guard.
This changes no search policy or runtime check. The original Clippy failure
is retained; the complete gate is rerun after this correction.

Before integration with the September 23 main branch, release build, Clippy,
rustdoc, doctests, formatting and the Python harness checks passed. Z3 4.16.0
parity had 176 decisive matches, no disagreements and one inconclusive case
(`array_unique.smt2`: Z3 Unknown). A complete 12,349-test run passed 12,348
and timed out on the fixed-seed `odd_width_identity_pairs_hold` at 180 seconds;
18 tests were already skipped by the suite. An earlier attempt timed out on
the fixed-input F4/Buchberger comparison and was stopped; the complete run
used a local 600-second allowance for that test and it passed. These attempts
are preserved, not counted as a clean full-suite pass. Final integration
verification is recorded separately below.

## September 23 integration

Merged main through `10d37a7d` into `f43db048`. The only source conflict was
the independently fixed debug-only SAT diagnostic: keep the outer caller-matched
configuration guard and remove the redundant dead-code expectation. Main also
changed array model construction, transcendental handling and graph callbacks,
including boxing drained entries in the shared user-propagator journal. The
CP declarations, snapshot producer and independent certificate checkers were
unchanged by that merge. The journal still restores the exact consequence in
reverse operation order; boxing changes ownership representation only.

Rebuilt the unchanged driver/profile and replayed the same confirmation grid
once under the new source/binary identity. All 280 transcripts remain identical
to the original Nixie baseline, with all models checked and no lost cells.
The merged result includes the intervening main changes and must not be credited
entirely to this CP patch:

| Mode and shape | Previous Nixie / Z3 | Merged Nixie / Z3 | Merged / previous Nixie |
|---|---:|---:|---:|
| Ordinary, all | 0.5338 | 0.4871 | 0.9126 |
| Ordinary, 4x4 | 0.1860 | 0.1835 | 0.9867 |
| Ordinary, 8x16 | 1.5321 | 1.2931 | 0.8440 |
| Certified, all | 0.5661 | 0.5178 | 0.9147 |
| Certified, 4x4 | 0.2049 | 0.2023 | 0.9875 |
| Certified, 8x16 | 1.5640 | 1.3250 | 0.8472 |

No family exceeds the 5% regression band. The large sparse cases still cost
6.8371/6.9078 times Z3, and large all-present cases cost 2.3328/2.3657 times
Z3. The final 8.5–8.7% improvement versus old Nixie does not establish a general
scheduling advantage over Z3. Cached counter stderr across the baseline,
CP-only candidates and reference has 100% coverage; all runs were CPU-pinned.

Merged callback diagnostics retain 280/280 exact transcripts. The callback
geomean is 0.9742 of old Nixie (neutral); all-present is 1.0470, still inside
the pre-registered per-family 5% band. Its 32x16 size does regress to 1.0765
(the 8x8 size is 1.0184), so the aggregate must not hide that component cost.
This appears only after integrating the intervening main changes; the CP-only
all-present family was 0.9748. No causal attribution among those main changes
was measured. The cached reports retain every size and baseline distribution.

The merged release build, release Clippy (`--all-targets`, warnings denied),
rustdoc (warnings denied via `.cargo/config.toml`), formatting and three Python
harness tests passed. The separately enabled arrangement canary
`pete_cxs_bp_is_unsat_on_every_trajectory` passed. The final perf landing gate
uses the frozen all-features CLI against canonical `28e82c65` with external
`GATE_CAP=600`: 12/12 decisive matching verdicts; the nine nontrivial pairs
have conflict and decision geomeans exactly 1.000. The earlier 150-second
attempt on `44f30970` had eleven solved matches and one shared cap; that
censored attempt is retained. Wall times are diagnostic, not optimization
evidence.

The complete merged Nextest run passed **12,367/12,367 tests**, with the suite's
18 existing skips unchanged; the arrangement canary above was run separately.
The local configuration retained all repository overrides and gave only the
fixed-input F4/Buchberger and 150-case odd-width identity tests a bounded
600-second allowance. Both passed (190.553 s and 290.432 s); the existing
600-repetition scope convergence test passed in 450.582 s. No test case, seed,
assertion or solver budget was removed or relaxed. Normal workspace release
profiles are used for doctests, CLI build, Clippy, docs and parity; only the
Nextest binaries use the test-link overrides stated above.

Release workspace doctests passed: **114 passed, 31 ignored**, with no failures.
The installed Z3 comparator remains 4.16.0, binary SHA-256
`e01bc8bcd4d487be9666873545532ff4cd705ad4cd746f616290fac756f12c46`;
this is the same executable as the reused CP reference cells.

Final Z3 differential parity: **176 decisive matches, 0 disagreements,
1 inconclusive, 0 timeouts/errors** out of 177 cases. The inconclusive case
is `array_unique.smt2` (Nixie Unsat, Z3 Unknown); it is not counted as a match.
All source verification and final measurements use `f43db048`; the subsequent
landing commit changes only this report and its paired CSV. Frozen ordinary
and all-features CLIs, the measurement binary, manifests, counter records,
profiles, complete verification logs and both local Nextest configurations
are retained in `precompile/` under their source/landing revisions.
