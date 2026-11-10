# Correctness-only reconstruction and per-capability gates

The user rejects the remaining 1.28973x cost and requests rollback of the
migration, reapplication of correctness patches only, measurement of that
baseline, and an apply/drop decision for each additional change under the gate
protocol. This supersedes the earlier all-capabilities migration decision.

## Registered reconstruction

Start from pre-migration source `af14b6d2`, not from the assumption that a whole
migration commit is a correctness patch. Preserve historical measurements,
regression evidence and unrelated baseline work. Use an isolated worktree whose
parent is current main; the eventual landing is a forward commit, never a reset
or rewrite of main. Do not land the bare old source with its known wrong answers.

Retain a change in the initial baseline only for an identified invalid verdict,
invalid model/proof, memory unsafety, exact-arithmetic defect, state/scope defect,
or invalid resource-result contract in existing behavior. Record the reproducer
and independently examined layers. Necessary representation/API dependencies
must be named as dependencies, not silently counted as standalone features.
A known missing certificate may produce Unknown or a model error; it must not
be replaced by a successful-looking default. Improving Unknown to Sat/Unsat is
additional solving coverage, not on its own a correctness justification.

The audit inventory is `bench/migration034/rebuild-plan.json`. Each original
slice must end with an explicit split/retain/drop decision. Source-level
subtraction is checked against the old and rejected trees so optional features
cannot survive merely through a dependency-heavy commit.

## Baseline verification and measurement

Use standard release builds, all required workspace/all-feature checks and
separate doctests, installed Z3 4.16.0 parity, and the unchanged pinned perf gate.
Preserve tests that expose incorrect existing behavior. Tests for withdrawn
capabilities belong to their candidate patches, rather than being silently
weakened to declare the old feature present. Record any deliberate loss of
solving coverage separately from soundness.

Measure the same 24 SATLIB and 48 SMT-LIB inputs, 30-second caps, 8 GiB, CPU
assignment and complete-process instruction counter. Reuse existing before,
migrated, rollback, cost-fixed, Z3, Kissat and CaDiCaL cells. Record all outcomes,
solved-at-cap and the original common-solve cohort. No task-owned build/test
runs overlap performance measurement. Every new cell is recorded once.

## Additional-capability decision protocol

Before measuring each candidate, register its exact source, intended user
benefit, targeted correctness/coverage cases, affected paths and acceptance bar.
Compare it with the measured correctness-only baseline and with the cumulative
accepted tree. Run the applicable release, differential and pinned performance
gates before landing. For any search-policy change, use a matched null, at least
ten effective common seeds, complete-work counters, baseline distributions and
fresh-seed replay; the single-default snapshot cannot authorize it.

Require zero wrong answers and no lost standing solves. Treat aggregate cost
within the documented 5% band as neutral, never as evidence of a speedup. A
feature needs a concrete coverage/API benefit even when cost-neutral. A cost
outside that band requires specific benefits and family-level accounting; the
rejected aggregate regression cannot be reintroduced by approving individually
small slices. Prefer dropping an optional feature or restricting it to its
explicitly requested use over charging unrelated inputs. Invalid controls,
unverified behavior or benefit-free complexity fail the decision gate. Record
negative results and apply/drop reasons on main as well as successful changes.

The source reconstruction and its first cost snapshot are recorded below; neither is a verified landing yet.

## Reconstruction audit in progress

The isolated tree reconstructs pre-migration source and replays the identified
correctness obligations. The inventory now records the split for all 27 original
slices. Additional capabilities are withheld pending their own decisions; this
is not yet a verified or landed correctness-only result.

Withdrawn source includes overflow predicate syntax, the QF_AUF alias, added
refinement statistics, finite-array cardinality/completeness, guard sampling,
expanded datatype separation, the formal package, diagnostic tools, automatic
array completion, finite-UF publication search, datatype publication proposals,
numeric projection proposals, alternative function defaults, zero-division
proposals and general function-consistency retry loops. Exact evaluation,
published-model validation and reconstruction of the actual solver/MBQI candidate
remain. Small complete Bool/BV expansion is retained for its direct invalid-model
obligation (14 quantified model failures documented in the original migration),
not merely for extra solves.

### Numeric UF pins: replacement obligation

The previous matched intervention isolates the expensive extra ordinary-UF
numeric constant pin (not the older array and quantified-function purifier
pins). Its 10-seed treatment/null cost was 11.19348x on Wisa and 4.29175x on
wisas; fresh-seed ratios were 5.54625x and 3.72814x. Those results are reused,
not remeasured. The final-value guard is under test as the replacement.

Layers examined independently:

* Encoding: Boolean term-position coverage and array ITE definitions remain;
  array-interface pins remain. Only ordinary Apply arguments lose the new eager
  numeric pin. Existing purifier pins are retained.
* Arithmetic primitive: the pin recognizer is now a read-only exact-value
  helper. The review found native i64 remainder overflow at MIN/-1; checked
  remainder now declines instead of panicking, including the div path.
* Integration: missing pins can omit a concrete function-point collision. They
  do not justify accepting a candidate whose equal arguments have different
  results. No new speculative equality or conflict is fabricated.
* Model interpretation: the final guard reads literal/compound semantics before
  model assignments, uses the pure exact value reader, refuses missing/defaulted
  values and budget exhaustion, and checks one result for every concrete tuple
  of each affected function. Uninterpreted values use the candidate's EUF
  classes; unsupported concrete values decline.
* Scope/state: the first candidate inferred affected functions from the final
  EUF snapshot. Full-suite verification exposed over-broad coverage of interpreted
  constant-array applications. The revised encoder journals the exact ordinary
  applications whose numeric pins it omits. Pop removes those entries in lockstep
  with their clauses; reset clears them. Rebase retains them with the retained
  clauses. Constants pinned later by another interface need no extra certificate.
  Every point of an affected function is still checked, including nonliteral
  argument points, so narrowing the trigger does not hide a real collision.
* Result handling: conflicting or uncertified candidates become Unknown with
  model/core cleared before the result is cached. Removal of proposal searches
  never turns an unsuccessful certificate into success.
* Reference: Z3 `smt_model_generator.cpp::mk_func_interps` constructs function
  entries from the argument values, which is the relevant coherence obligation;
  `smt_context.cpp::check_finalize` is the final-result validation boundary.

Focused tests exercise equal concrete arguments with conflicting results,
stale assignments to literals, missing/defaulted values, and certificate budget
exhaustion. Existing exact-real and deep constructor-DAG regressions remain.

## Correctness-only cost snapshot (verification pending)

Source candidate: `4e991ae0cd18e8760c5e2f2c8360290bb08fcf15`.
Binary SHA-256: `35c8cd7e0018844e07ca81d3b27ec3ef5cb8b6c6f6dd4509cceadece15b68219`.
The candidate is isolated, not yet landed on main. The manifest is
`bench/migration034/correctness-only-manifest.json`; the complete report and
per-case table are `correctness-only-results.json` and `.csv` beside it.

All 72 candidate cells completed once, with 408 cached baseline/reference
cells reused (480 total). No task-owned compilation or test run overlapped
measurement. The same 30 s cap, 8 GiB, CPUs 2/5 and complete-process user
instructions were used. This remains a default-configuration snapshot, not a
statistical claim about a heuristic. Reference versions remain Z3 4.16.0,
Kissat 4.0.4 and CaDiCaL 3.0.1 as pinned in the reused manifests.

| Measure | Correctness-only candidate |
|---|---:|
| SAT solved | 24/24 (12 sat, 12 unsat) |
| SAT instruction geomean / pre-migration | 0.996510x (neutral) |
| SMT solved | 24/48 (6 sat, 18 unsat) |
| SMT other outcomes | 10 unknown, 13 timeout, 1 existing allocation error |
| Original SMT cohort retained | 23/23 |
| Original-cohort SMT geomean / pre-migration | 1.075913x |
| Original-cohort SMT geomean / original migration | 0.786595x |
| All 24 shared SMT solves / previous cost-fixed version | 0.840647x |
| Decisive reference disagreements | 0 |

The same solved set as the rejected migration is retained. Relative to the
pre-migration version, the previously reported gain on
`QF_BV/brummayerbiere4/unconstrained05.smt2` and loss on
`QF_AUFLIA/array_benchmarks/misc/pipeline-invalid.smt2` remain; this rollback adds
no new loss. The error on `QF_BV/pspace/shift1add.29940` is unchanged.

The large numeric-pin regressions disappear: Wisa uses 31,546,076,191
instructions (0.996305x pre-migration, versus 12.419x in the rejected version);
wisas uses 14,056,463,362 (0.996507x, previously 4.693x). Both remain unsat.
The previous controlled intervention and the final-value consistency regressions
support removing the eager pins while retaining the actual model obligation.

The dominant residual is `QF_UF/20190906-CLEARSY/0016/00194.smt2`: 71,781,866
instructions versus 10,896,510 before migration (6.587602x). It remains sat.
The prior attribution localized this to published-model validation, which the
correctness reconstruction retains; the optional replacement-model searches
are absent. The other 22 original-cohort cases have a 0.990847x geomean.
Total instructions over all 23 paired solves are 0.988171x, reported as context,
not substituted for the preregistered geomean. Smaller positive costs remain
on BV3296 (1.107988x), IDL parity (1.095846x), FISCHER (1.081175x) and TwoSquares
(1.080735x); their earlier source-interval attribution is in the cost
investigation study. The aggregate alone does not prove every instruction is
necessary, and no residual is described as an optional feature benefit.

Release clippy (all targets/features), formatting and warnings-denied docs
passed before this measurement. The first focused run passed all ten
function-consistency tests and 83 other tests; four obsolete capability
expectations produced honest Unknowns. Their exact capability expectations
are preserved under `bench/migration034/candidates/`; baseline regressions
retain the contradiction and invalid-model rejection obligations. Full release
workspace tests, doctests, current-Z3 parity and the pinned performance gate are
still required before landing.

Additional independent exit-path review: `check_with_assumptions` calls the
ordinary guarded `check` before saving its model and popping the temporary
scope; an Unknown has no model to carry. Cache entries are installed after the
new guard and the existing assert/push/pop/reset invalidation remains in place.
The sequence fast path lowers to a fresh ordinary `Solver::check` (which runs
the guard), then evaluates every original assertion against the fixed lifted
model before accepting Sat. `check_sat_only` retains its explicitly documented
Boolean-abstraction contract; it is not used by the ordinary SMT check path.
The pure value reader validates scalar sorts, uses exact wide values, recomputes
compound terms and has a depth-limited explicit evaluator; it does not consult
live arithmetic/EUF/SAT state to make a failed candidate read true.

The three previously gated equivalent-work reductions (EUF application-presence
bookkeeping, borrowing the arithmetic equality cache, and reusing an unchanged
printed reading within one settlement) remain implementation details of the
retained checks. They introduce no capability or search choice; their previous
scope/idempotence regressions and complete-work measurement are preserved in
`2026-11-10-migration034-cost-investigation.md`. The reconstruction does not
reintroduce the redundant scans/copies while removing optional semantics.

A separate correctness replay of the three preserved capability inputs used
both cached pre-migration and candidate binaries plus installed Z3 4.16.0.
This was not a cost measurement and ran after the performance cells finished.
The original enum case printed Sat but returned the unresolved expression
`(= (full red) (full blue))` for a value that Z3 evaluates to true in the
constrained scope. The old zero-division model omitted `f` entirely and returned
unresolved division terms as values. The reconstruction withholds both models
and reports Unknown, preserving the enum contradiction's Unsat. The shadowed
array-completion case was already Unknown before migration and remains Unknown;
Z3 answers Sat. Exact outputs are cached as `capability-replay.json` beside the
candidate's verification logs. These are evidence for keeping validation while
withholding extra model search, not evidence that the withheld capabilities
have no potential benefit.

## Additional capability gates

**Formal harness — drop at the required-verifier gate.** The package requires
an unpublished `oxiformal` checkout and `cargo formal`. The current dev-shell
PATH has no `cargo-formal`; no corresponding crate exists under the supplied
reference checkouts. The original package explicitly distinguishes its plain
boundary tests from proof. Reintroducing it would provide no verified formal
capability and would carry a separate toolchain/maintenance obligation. It has
no solver-runtime cost, but zero runtime cost does not substitute for a verified
benefit. No external toolchain was fabricated and no historical upstream proof
result was relabeled as a Nixie result.

**Diagnostic tools — focused gate passed, final decision pending.** Exact
`scripts/round4` sources from `5c2b6bed` passed all nine Python tests. This
candidate touches no Rust/Cargo input, so it neither changes the frozen solver
binary nor introduces a new solver-cost cell. Actual Z3 smoke controls are
queued after build/test activity, as the tools' own methodology requires.

### Full-suite rejection of the first candidate

The first full release build passed. Nextest ran 12,760 tests: 12,745 passed,
15 failed, and 20 were skipped. All failures were Unknown versus expected Sat;
this is a rejected candidate, not a clean verification result. Doctests, parity
and the pinned gate had not yet run. Logs are preserved separately from the
subsequent verification so the failure is not overwritten.

The first defect was an interpreted constant-array application incorrectly
classified as an ordinary UF. Restoring its array default pin and journaling
only actually omitted ordinary-UF interfaces makes
`const_array_consistent_stays_sat` pass. The focused rerun passed all ten
function-consistency tests, including a real encoding/pop journal regression.
Fourteen remaining capability expectations still fail; their old models are
being replayed independently before classifying or changing those tests.
The measured 4e991ae0 binary is preserved as the original experiment; revised
source requires its own binary identity and cost cells.

Independent Z3 4.16.0 replay directly falsified the old models for the six-value
composite datatype and the mutually recursive datatype distinctness cases.
Several quantified old models omitted their function definitions; satisfiable
pins only establish that an extension exists, not that a complete model was
published. The diagnostic candidate initially counted these as `model_ok`; its
new `model_partial_consistent` outcome and regression keep that distinction.
The set-family replays remain unresolved and are not counted as matches.

The recursive `sum(k) = 6` input is a genuine coverage loss: the old `k = 3`
model replays successfully. Both modes of the existing pin-ablation binary
(pins enabled/disabled, with optional capabilities present) still find it.
Thus pin omission alone does not explain the loss. The reconstructed driver
tries candidates k = 4 and k = 9, rejects them by concrete recursive evaluation,
then exhausts its existing rounds with Unknown. Function-collision refinement
is an additional capability to evaluate; this loss is explicitly retained as
its positive coverage control, never described as removal of a wrong answer.

The 14 original failed test contracts and exact CLI inputs are preserved under
`bench/migration034/candidates/coverage-contracts/`. The baseline now explicitly
tests Unknown where no verified model remains, and preserves all contradiction
and scope/round-count assertions. The 696-case datatype oracle has an exact
19-input incompleteness allowlist; additional Unknowns and every decisive
disagreement still fail. These changes record deliberate coverage withdrawal,
not 14 solver fixes or successful differential agreements.
