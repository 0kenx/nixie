# Optional cumulative tasks in the existing CP engine

`CpModel::cumulative_optional` extends the existing cumulative global with
Boolean presence conditions. `Task` and `cumulative` remain source compatible.
`OptionalTask` accepts a Boolean term, an existing finite-domain start, and
constant nonnegative `BigInt` duration/demand. Both APIs share the same internal
cumulative representation and timetable. There is no second constraint engine,
new solver dependency, or external solver call.

## Reference rules and scope

Read before implementation, from OR-Tools' `stable` source on 2026-09-22:

- [`TimeTablingPerTask::BuildProfile`](https://github.com/google/or-tools/blob/stable/ortools/sat/timetable.cc)
  uses only present tasks with nonempty compulsory parts.
- [`SchedulingConstraintHelper`](https://github.com/google/or-tools/blob/stable/ortools/sat/scheduling_helpers.h)
  distinguishes present/absent/unknown, records presence reasons, and conditions
  optional interval bounds on presence.
- [`Cumulative`](https://github.com/google/or-tools/blob/stable/ortools/sat/cumulative.cc)
  guards the single-task demand/capacity condition by presence and positive size.

Nixie's finite-domain adaptation tests candidate starts against its existing
exact mandatory-part timetable. Unknown conditions never justify unconditional
start pruning. Presence trials change all shared/complemented occurrences,
then check the timetable and individual start supports; an impossible trial
proves the opposite condition. This detects an over-capacity positive-duration
task even without a compulsory part, and can prove absence when each possible
start is blocked by other present tasks. No trial reduction feeds another one.

Every recorded reason comes from the original callback assignment. The trial
presence is discharged into the conclusion, never assumed in the explanation.
For present-task start filtering, the actual presence assumption remains in the
reason. Reasons can be larger than necessary; there is no minimality claim.

Zero duration or demand contributes no load. Endpoints are half open and all
arithmetic remains `BigInt`, including accumulated loads. Negative capacity is
infeasible even for empty/all-absent task lists, preserving the existing API.
An absent start still obeys its declared exactly-one finite domain and any
independent constraints; absence removes only scheduling restrictions.

Variable durations/demands/capacity require a separate design for declarations,
arithmetic links, conditional explanations, model checking, and certificates.
Energetic reasoning, edge finding, and stronger joint-support cumulative
filtering are also separate follow-ups. None is implemented by this change.
There is no throughput, proof-size, or performance-improvement claim.

## Independent layers examined

| Layer | Invariant and evidence |
|---|---|
| Construction and domains | Validate all task starts, sorts, durations and demands before changing the model. Existing exactly-one domain assertions/certificates remain in force. Atomic rejection and malformed retained presence meanings have dedicated tests. |
| Presence identity | Canonicalize a condition and its direct negation to one signed condition. Shared tasks switch together. Formula/domain correlations may be relaxed during finite lemma enumeration; this enlarges supports and cannot prove an invalid lemma. Public tests cover Boolean formulas and presence equal to a start indicator. |
| Timetable and filtering | Only known-present tasks supply mandatory parts. Candidate exclusions and presence trials use original domains/assignments. Independent unit-slot enumeration checks every emitted implication, rather than checking only a final solver answer. |
| Explanation polarity | Known presence appears in start-pruning premises. An impossible trial concludes its negation. Removing a necessary presence premise fails independent checking. No unexplained reduction is reused. |
| User-propagator adapter | Existing watched-formula encoding, SAT-variable freezing, signed literals, and complementary watch delivery apply unchanged. Constants are interpreted explicitly by CP. No callback registration or trust classification is bypassed. |
| Scope state | CP has no new mutable search cache. Existing manager snapshots restore watched assignments and pending consequence queues. The callback oracle pushes/pops every partial state; public tests use nested assertion scopes and check model/proof invalidation. |
| Model replay | Ordinary CP model validation now independently checks retained declarations before callback replay, using the existing finite checker. Missing presence assignments fail closed. The checker evaluates resource use directly at active starts, independently of the event sweep. |
| Lemma certificates | Existing `CpLemma` records enumerate start values and distinct presence values under premises and negated conclusion, subject to the deterministic work budget. Shared/complemented occurrences share a Boolean digit. No callback/filtering function is called by the checker. |
| Canonical Boolean encoding | Include presence terms even when no application assertion mentions them. Model-blocker reconstruction reads these terms alongside domain indicators. Original conditions/formulas are supplied outside the proof; an artifact cannot replace them. |
| Complete refutation | Existing version-2 envelope, canonical input-clause equality, and independent LRAT checking remain required. Tests export/import/refute, reject presence-premise tampering, reconstruct after an unrecorded search, and check saved proofs against saved scoped inputs. |

## Exhaustive and focused evidence

`nixie-theories/src/cp/optional_tests.rs` enumerates two-task scheduling with
both durations and both demands in `0..=2`, capacity in `-1..=2`, independent,
shared, and complemented presence conditions. Starts are in `{0,1}`. It checks
15,552 complete-valuation checks against an independent unit-slot oracle and visits
43,740 partial callback states (all nonempty start subdomains crossed with
unknown/false/true presence). Every emitted conflict/consequence is checked
against every satisfying concrete schedule and separately by the finite lemma
checker. Each partial state is popped, with no pending queue left behind.

Focused callback tests cover removal of required presence premises, absent
start freedom, missing model values, atomic construction failures, and forced
absence after exhausting candidate starts despite an empty compulsory part.

`nixie-solver/tests/cp_optional_scheduling.rs` checks 4,860 scoped public solver
verdicts: the same duration/demand range at capacity one, both start choices,
unknown/false/true presence and all three sharing patterns. Every UNSAT verdict
has an exported/imported proof checked against independently retained inputs.
Further cases cover 141-bit starts/durations/demands/capacity, coincident
endpoints, zero duration/demand, true/false/formula presence, start-indicator
aliases, proof tampering, saved scoped proofs, empty negative capacity, and
reconstruction without application assertions or prior recorded leaves.

The runnable `optional_resource_allocation` example admits/cancels GPU batches
alongside a mandatory service through ordinary Boolean assertions.

## Verification record

The final source includes concurrent `main` commits through
`aa9e9d1b` (the independent array soundness fix). Required checks on this
combined revision:

| Check | Result |
|---|---|
| `cargo build --all-features` | Passed |
| `cargo nextest run --workspace --all-features -j 4` | 12,236 passed; 17 configured skips, with the runner-only timeout accommodation below |
| Strict all-features/all-targets Clippy | Passed |
| `cargo fmt --all -- --check` | Passed |
| Warning-denying `cargo doc --no-deps --all-features` | Passed; `-D warnings` comes from the existing `.cargo/config.toml` |
| Workspace all-features doctests | 114 passed; 31 ignored |
| Explicit ignored `pete_cxs_bp_is_unsat_on_every_trajectory` canary | Passed on the combined workspace build |
| Runnable GPU-allocation example | Both admission and cancellation checks passed |
| Z3 4.16.0 parity | 176 decisive agreements, zero wrong verdicts; one inconclusive `array_unique.smt2` comparison (Nixie UNSAT, Z3 Unknown), never counted as agreement |

The first performance gate, before integrating the concurrent array fix,
passed all twelve verdicts and nine nontrivial counter comparisons against
pinned `28e82c65`: conflict/decision geomeans 1.000. The combined revision's
150-second gate printed PASS with eight nontrivial comparisons, but both
binaries timed out on `WS_500_16_90_70.apx`. That pair is not agreement evidence.
A new gate configuration uses an outer cap of 600 seconds on every cell to
recover the missing comparison; the cap changes no solver policy or seed.
The two lower-cap logs are retained, not silently replaced. These are required
landing checks, not a heuristic experiment or a CP performance claim.

Final higher-cap gate: **PASS**, all twelve verdicts matched, nine nontrivial
counter comparisons and three trivial cases; no timeouts or lost samples.
Conflict and decision geomeans are both **1.000**. The observational wall ratio
is 0.97, not an improvement claim. The release binary SHA-256 is
`de3f02187f5a4dfeb16b6048154ca3000e74d9f1b68dca629820655b9253c6c1`.

The release binary is cached under `precompile/<landed-commit>/nixie`.
Raw gate logs, parity JSON, the exact temporary test-runner configuration,
and command/environment records are retained alongside it under
`benchmark/cp-optional-scheduling/`. No binary or scratch corpus is committed.

The initial full-suite compilation exhausted the temporary filesystem while
linking debug test binaries. It produced no full-suite result. Only this task's
build artifacts were deleted. The repeated verification uses the primary
checkout's untracked Cargo.lock, offline Cargo, four build/test workers,
disabled incremental compilation, and debug info level zero. Test assertions,
solver budgets and seeds are unchanged. The first reduced-output suite reached
8,266 passes before the existing
`re_running_the_search_on_an_unchanged_goal_converges` test hit its outer
five-minute limit. The final run temporarily raises runner termination counts
to at least ten 60-second periods, following the prior complete-CP-proof study's
loaded-host procedure. The original runner configuration is restored before
commit; no test assertion or solver budget is weakened.
The initial Clippy pass found two range-loop style issues in the new test;
these were corrected before the final strict pass.

An additional `cargo check -p nixie-theories --no-default-features` did not reach
CP: unchanged `nixie-math` sources fail with 142 compilation errors, beginning
with `std::cmp::Ordering` / `rustc_hash::FxHashMap` imports in `ff/poly.rs` and
missing allocation macros in `ff/field.rs`. Those sources are identical to
`main`; this optional check establishes no `no_std` support claim for the new
API. Do not repeat it without first addressing that separately scoped math
portability work. The required all-features builds are independent of this
pre-existing limitation.
