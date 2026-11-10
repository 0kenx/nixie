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

No source rollback or correctness-only performance result is claimed yet.

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
* Scope/state: affected functions are recomputed from the current model's EUF
  snapshot, not a sticky flag that could survive pop. No new scope table is
  introduced. Existing result invalidation owns the cached verdict and model.
* Result handling: conflicting or uncertified candidates become Unknown with
  model/core cleared before the result is cached. Removal of proposal searches
  never turns an unsuccessful certificate into success.
* Reference: Z3 `smt_model_generator.cpp::mk_func_interps` constructs function
  entries from the argument values, which is the relevant coherence obligation;
  `smt_context.cpp::check_finalize` is the final-result validation boundary.

Focused tests exercise equal concrete arguments with conflicting results,
stale assignments to literals, missing/defaulted values, and certificate budget
exhaustion. Existing exact-real and deep constructor-DAG regressions remain.
