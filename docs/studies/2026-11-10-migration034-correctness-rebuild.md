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

**Diagnostic tools — apply.** The restored tools, with the partial-model
accounting fix below, pass ten Python tests and four actual Z3 4.16.0 controls:
a falsifying datatype model, a consistent partial function model, a valid
recursive-function model, and a valid constant-array model. This candidate
touches no Rust/Cargo input, so the binary and its cost cells are identical.
The benefit is concrete: the tools detected invalid historical models and now
correctly distinguish incomplete model pins from a verified complete model.

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

## Revised correctness-only verification

Source `f8a621f4587295f3bff68959fbf46ead81340f00` scopes the omitted-interface
certificate and records the explicit coverage withdrawals above. The default
release binary SHA-256 is
`e9abf3db9c63567ccf5cabd03a43c63c34b9e91c2ba02c83d9379140c59a1846`.
All required release checks passed: all-feature build, all-target/all-feature
clippy, formatting, warnings-denied documentation, **12,760 nextest tests**
(20 skipped), and **117 doctests** (31 ignored).

Z3 **4.16.0** parity: **169 decisive agreements, zero disagreements, eight
inconclusive**. The pre-existing comparator Unknown on `array_unique` remains.
The seven new Nixie Unknowns are UFLIA `congruence_closure`, `division_property`,
`idempotent`, `injective`, `monotone_basic`, `surjective`, and UFLRA
`real_monotone`. They are explicitly lost coverage versus the rejected migration,
not parity matches. They become focused positive controls for the optional
refinement/publication gates.

The unchanged pinned performance gate (`28e82c65`, 150 s cap) passes: all 12
verdicts agree, with conflicts and decisions geomeans **1.000x** over the nine
nontrivial pairs. Full-work SATLIB/SMT-LIB measurement is separately registered
in `correctness-scoped-manifest.json`; it started only after every verification
process and this gate finished. The 72 new cells and 480 reused cells are
reported in `correctness-scoped-results.json` and its CSV companion. Against
pre-migration, SAT instructions are **0.996912x** and SMT instructions on the
original 23-case cohort are **1.077592x**, versus **1.367811x** for the original
migration. All 24 SAT inputs and 24 of 48 SMT inputs are solved, with zero
decisive reference disagreements. The SMT remainder is ten Unknowns, thirteen
timeouts, and one existing allocation error. The measured solved set is
unchanged versus the rejected migration; this does not erase the seven
separate parity coverage losses above. The pre-migration pipeline-invalid
solve remains a timeout and the unconstrained BV solve remains gained.

The remaining 7.76% aggregate cost is not a claim that all retained work is
irreducible. A diagnostic profile succeeded with user-only call chains after
the host rejected kernel-callchain access. Launcher locale processing occupied
many samples; it is excluded from solver attribution. No host settings changed.
Full-process retired instructions, not profile sample percentages or wall time,
remain the primary cost measurement.


### General function retries — drop

The isolated production candidate `001cd07b` restores only the three guarded
Ackermann refinement/re-solve sites. The clause construction was checked against
Z3 `src/smt/dyn_ack.cpp:407`: all differing argument equalities guard the result
equality. The final model guard remains active. On the unchanged 72-input sample,
SAT cost is **1.000008x** and SMT cost **1.000523x** versus the correctness-only
baseline, with no gained/lost solves or decisive disagreement. Of the focused
coverage contracts, only the recursive `sum(k)=6` case recovers Sat with k=3;
none of the seven lost parity cases recovers.

This apparent benefit did not survive the registered seed controls. Diagnostic
`487d19b3` encodes both the real congruence implication and the same implication
for a detached reserved function with identical arguments/signature in both
active arms, then asserts one through the same path. Only valid congruence
lemmas are introduced. Mode is read once per process. Ten common seeds and
held-back 87109 ran once with 30-second limits and full instruction counters.
**All 33 off/real/null runs solve with k=3.** The off distribution varies greatly;
the default-seed loss is not a replicated completeness benefit. Ten seeds never
activate either intervention. At the remaining seed, real asserts 65 units and
null 64: this is not a fully matched control. `retry-control-summary.json`
records the ratios but they cannot establish semantic merit. The fresh seed
also gains nothing. The candidate therefore fails the acceptance protocol and
is dropped; neither the retry activation nor diagnostic hooks remain enabled.

All raw cells are retained under their source SHAs. This is a negative
experiment, not a claim that function refinement can never help. Do not retry
this default-seed argument without an active, matched control and replicated
coverage benefit. Full-suite revalidation is unnecessary for the rejected
candidate: its withdrawal restores byte-identical Rust/Cargo source to the
already verified correctness-only baseline.
