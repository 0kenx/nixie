# Migration 0.3.4 SMT cost investigation

## Registered investigation

The user requires an explanation for the observed 1.3678 geometric-mean
instruction ratio, accepting increased cost only where directly required for
correctness. The prior policy rollback is `507ce04c`. No assumption is made that
it removes the measured cost.

First measure that cached, standard-release binary on the unchanged 72-instance
sample using `bench/migration034/rollback-manifest.json`. Retain the existing
suite identity, instance bytes, CPU assignment, clean environment, 30-second
external timeout, 8 GiB limit and whole-process instruction metric. Reuse all
264 completed migration/reference cells; execute only the 72 new rollback cells.
The original manifest and results remain historical evidence.

Next localize the changes using cached intermediate release binaries and
instruction sampling. The initial diagnostic cases are the five largest
completed-pair instruction increases (Wisa, CLEARSY, wisas, FISCHER and plan-16)
and the lost `pipeline-invalid` solve. Selection is explicitly retrospective:
these are fault-localization inputs, not a held-out performance claim. Freeze
each additional binary/configuration manifest before executing it; store each
measurement once and reuse it. Sampling runs have their own configuration and
do not replace the original cost observations. Check build-profile provenance
before using intermediate costs for attribution.

For each localized change inspect callers, generated constraints, theory state,
model validation and scope restoration. Classify the cost as required correctness
work, avoidable implementation overhead, or unsupported search-policy change.
An existing correctness test justifies its obligation, not arbitrary execution
cost on unrelated inputs. Preserve the obligation while removing repeated or
irrelevant work where equivalence can be established.

No heuristic optimization is authorized by a favorable single-default number.
Any proposed search-policy change requires a separately registered matched null,
at least ten effective seeds, complete-work counters and fresh-seed replay under
`AGENTS.md`. A correctness fix requires a reproducer and independent inspection
of the affected invariants. A semantics-preserving implementation change must
establish what is preserved, including budget accounting and generated order;
if it changes search policy, it enters the heuristic protocol instead.

Acceptance requires the full release verification gates, current Z3 4.16.0
parity, and the pinned SAT gate, plus the same full SMT sample for any resulting
binary. Report all gained/lost solves and disagreements alongside costs. Never
justify the aggregate increase solely by saying the migration contains soundness
fixes. Record unresolved costs and negative experiments explicitly.

## Initial localization

The rollback snapshot completes all 72 new cells and reuses all 264 existing
cells. SAT remains 24/24; SMT remains 24/48 (18 Unsat, 6 Sat, 10 Unknown,
13 timeouts, one allocation failure). There are no decisive disagreements with
available labels/references. On the same 23 common SMT solves the instruction
ratio is **1.36965**. The policy rollback therefore does not explain or fix the
1.3678 observation. The SAT ratio is 1.00208 on 24 pairs.

Cached adjacent revisions localize the large UFLIA costs and pure-arithmetic
overhead to slice nine, `1106bd4d` → `c8abf146`. Wisa rises from about 32.0 to
393.7 billion instructions; wisas rises from 14.25 to 66.30 billion. FISCHER
and plan-16 retain identical SAT decisions/propagations/conflicts/restarts while
their instruction costs increase. A scan-based `EufSolver::has_app_nodes` is now
called on every assignment, even on graphs containing only leaves. Tracking the
first live application can answer the exact same question without scanning;
this implementation change is under verification, not yet a landed result.

Separate, registered dump configurations show byte-identical initial CNF and
term-to-variable sidecars on both UFLIA cases across the adjacent interface
commits. Their changed search therefore begins after that initial encoding.
The new shared-interface bookkeeping and theory facts still require attribution;
the existence of correctness regressions in that slice does not settle it.

CLEARSY's increase is separate: `029ce7ad` costs 11.25 million instructions and
the next slice, `8ca3622a`, costs 110.36 million, with unchanged SAT counters.
That slice introduces published-model certification. The pipeline timeout is
already present at `68c36c44`, before the interface changes. Neither is attributed
to slice nine. Exact diagnostic costs and artifact paths are recorded in
[`cost-localization.json`](../../bench/migration034/cost-localization.json).

## Numeric-pin matched control (registered before measurement)

The isolated ablation `99005ad2` traces exactly one new fact on both UFLIA
inputs: the literal `4` is introduced into the arithmetic tableau as a fixed
interface variable. Disabling only the new shared-interface pin loop restores
the original decisions, propagations, conflicts and restarts on both inputs.
The unrelated FISCHER and CLEARSY controls are unchanged. One instrumented Wisa
run hits the 30-second cap; its partial instruction count is censored, not a
completed-cost comparison. This identifies the intervention but does not prove
its semantic benefit or justify its default activation.

Use the isolated `83cdf7be` diagnostic for a matched control, never as a
production solver. All arms create the same reserved, otherwise unused numeric
alias at the same intervention point. The real arm adds the literal's fixed
column; the null adds the same-valued fixed column for that alias, which has no
function-argument meaning. Thus the injected column count, value, insertion
point and code path match; only its connection to the user function differs.
The off arm adds neither column. Pre-existing pins are untouched. This is a
single-check diagnostic: its auxiliary registration set is not a production
scope-state design.

Measure the two identified UFLIA inputs with all three arms at the ten common
SMT-LIB seeds `7919 * i`, for `i = 1..10`. Reserve seed `87109` (`i = 11`) for
fresh-seed replay, with no intervening parameter selection. Seeds are inserted
as `(set-option :random-seed N)` into frozen copies; `Context::set_option`
forwards them to the embedded SAT engine. Store the actual seed in each record,
not merely in a filename. Use 30 seconds, 8 GiB, the same physical CPU per input,
and complete-process instructions. Rotate arm order, retain all censored runs,
and run no other task-owned compilation/tests during measurement.

Check that the initial CNF agrees across arms and that the real/null fact traces
have the same pin count/value. Verify that the null actually changes trajectories
relative to off; an inert null invalidates the control. Report real/null cost on
jointly solved agreeing runs, solved-at-cap for every arm, the off distribution,
and the held-back seed separately. These two retrospectively selected cases
cannot support a general speedup claim or justify a new default heuristic.

Correctness is a separate veto: inspect the existing ground-function consistency
and candidate validation paths, and probe the missing-interface counterexamples.
A necessary pin is retained even when expensive. An eager activation with no
correctness dependency and no demonstrated semantic benefit is withdrawn rather
than tuned to these two inputs. Any resulting production change still needs the
full gates and unchanged 72-instance snapshot.

## Matched-control outcome

All 66 cells completed with Unsat, matching the original Z3 4.16.0 evidence
and corpus labels. On the ten registered seeds, real/null whole-process
instruction geomeans are **11.19348 on Wisa** and **4.29175 on wisas**.
The held-back seed is independently **5.54625** and **3.72814**, respectively.
Initial CNF is byte-identical across all three arms at every seed; real and
null each trace exactly one value-4 pin, and off traces none. The null changes
SAT counters relative to off on nine of eleven seeds for each case, so it is
not an inert perturbation. All ten seed overrides produce distinct off-arm
trajectories. The no-pin baseline instruction distributions (minimum / median /
maximum, billions) are 23.824 / 29.775 / 36.469 for Wisa and
11.971 / 15.398 / 33.811 for wisas. Complete summaries and trace checks are in
[`pin-control-results.json`](../../bench/migration034/pin-control-results.json);
the immutable records and frozen seeded inputs are under the diagnostic
`83cdf7be` cache entry. This is evidence of a regression on these two selected
cases, not a general performance estimate or authorization to remove a fact.

The intervention's semantic connection, rather than merely allocating an
additional fixed arithmetic column, accounts for the large cost. Restoring the
old search would require removing or deferring a theory-interface fact, not
merely avoiding redundant allocation. Neither successful end-to-end small
probes nor candidate repair establishes that this is safe: the functional
collision pass has explicit work/lemma caps, and some model evaluators can
return undetermined without providing a universal certificate. The new pin is
therefore retained while its implementation cost is investigated. This does
**not** declare the 11.19x cost necessary or acceptable.

Independent layers inspected include coefficient-preserving purification,
closed-constant folding, generated-lemma interface registration, scoped
arithmetic bounds, equality-entailment certificates, EUF congruence, candidate
Ackermann repairs and published-model validation. Z3's
`theory_arith_core.h::internalize_numeral` likewise fixes numeral interfaces
with exact lower and upper bounds. A new theory-level regression exercises
entailed equality with/without the live pin, its retraction and reassertion
across pop, reason provenance and reset. It protects the obligation independently
of an outer model checker; it is not an end-to-end false-Sat reproducer.
The earlier coefficient-int/real probes are negative evidence: both versions
and Z3 already refute them, so they cannot justify the new pin on their own.

## Equivalent-work reductions under verification

Three changes leave interface facts, search choices, budgets and proof
obligations in place:

- Track the first live EUF application rather than scan all nodes for each
  assignment. Nodes are append-only within a scope and pop removes a suffix;
  nullary applications count, leaves do not. A direct scan oracle checks nested
  scopes, slot reuse and reset.
- Reuse an unchanged published-model reading within one settlement call. Repeat
  validation after discarding a candidate or attempting repair; retain the
  independent typed-value check. The regression changes the interpretation and
  scopes to ensure no result survives model mutation.
- Borrow the cached Diophantine verdict rather than clone its entire incumbent
  at each check. Copy a conflict core only when returning it, and a witness only
  when actually attempting it. Equality assertion/pop invalidation and rejected
  incumbent handling remain unchanged. This removes copying, not an entailment
  test, certificate, arithmetic solve or budget charge.

The complete release verification below has passed. The unchanged 72-instance
snapshot remains the separate acceptance measurement of actual SMT cost.

An additional 18-script correctness matrix varies Int/Real arguments,
Int/Bool/uninterpreted results, point bounds, coupled linear equations and a
bounded-domain collision. With the isolated pin disabled, four Real cases
change from Unsat to Unknown; no wrong decisive answer is observed. The pin
therefore demonstrates additional solving coverage on those cases. This is
not evidence that the full measured performance penalty prevents wrong
answers. Two satisfiable Real cases remain Unknown in both arms; Z3 4.16.0
provides the same comparator throughout. Inputs, full outputs and the driver
are archived under the `99005ad2` diagnostic cache's
`benchmark/migration034-cost-attribution/correctness-probes/`.

The archived Wisa sampling record cannot provide reliable caller attribution:
its user call chains mostly contain only the leaf frame. Reprocessing it with
inclusive children does not recover the missing ancestry. Do not use that
profile to claim that all simplex work is specifically entailment probing.
Its flat samples motivated the cache-copy reduction; the controlled instruction
measurements, not sampling percentages, determine the final cost result.

A further call-site audit narrows the classification. The encoder registers the
new pin eagerly, but **the arithmetic fact is installed only by
`nelson_oppen_combine`, whose sole caller is the final theory check**. The SAT
engine reaches that check after it has exhausted unassigned branch variables,
before saving/returning a model (`search_ext.rs`). This is not an extra
per-assignment branching proposal or an eager arithmetic solve at encoding.
The pin makes a numeral participate in exact shared-term entailment; successful
entailments merge EUF classes with explanations, and newly induced equalities
are checked back against arithmetic before acceptance. Merely delaying this
work until a full SAT candidate would reproduce its present placement.

That establishes a direct connection to theory-consistency validation, but
not that its implementation or induced trajectory is cost-minimal. In
particular, neither the flat profile nor the small probes proves that every
additional instruction is necessary to prevent a wrong verdict. The retained
fact and the unapproved magnitude of its cost must not be conflated. Removing
it would require a replacement guarantee at that same acceptance boundary;
outer best-effort repair is not such a guarantee.

## Verification of the equivalent-work reductions

All nine verification steps completed successfully on the final, hash-checked
Rust sources, using the standard release profile (LTO, one codegen unit):
all-feature build; full workspace/all-feature nextest (**12,794 passed,
20 skipped**); doctests (**117 passed, 31 ignored**); all-feature/all-target
Clippy with warnings denied; formatting; documentation with warnings denied by
`.cargo/config.toml`; official Z3 parity; default-feature CLI build; pinned perf
gate. The new arithmetic pin, EUF scope and model-reading regressions all pass.

Installed Z3 **4.16.0** gives **176 decisive agreements, zero disagreements,
one inconclusive** (`array_unique`: Nixie Unsat, Z3 Unknown). The pinned
`28e82c65` performance gate passes all twelve verdict comparisons, with
conflict and decision geomeans **1.000** on nine nontrivial pairs and three
trivial cases. The default 150-second gate cap was not overridden; the separate
requested SATLIB/SMT-LIB snapshot continues to use 30 seconds. No changed
search policy is inferred from these same-counter implementation reductions.

The binary, source hashes, full gate logs, driver and parity JSON are retained
under the fix commit's `precompile` entry. These checks establish this landing's
verification bar; they do not erase the separately recorded numeric-pin cost.
