# Explained CP global constraints

`nixie_theories::cp::CpModel` provides user-defined finite-domain constraints
through `Solver::register_cp`. This is a Rust API, not a new SMT-LIB theory.
The underlying `Solver::register_user_propagator` also accepts custom callbacks.
No external solver or FFI is used.

```rust
use nixie_core::ast::TermManager;
use nixie_solver::{Solver, SolverResult};
use nixie_theories::cp::CpModel;

let mut tm = TermManager::new();
let mut cp = CpModel::new(&tm);
let mut vars = Vec::new();
for name in ["x", "y", "z"] {
    let entries = (1..=3).map(|value| {
        let indicator = tm.mk_var(&format!("{name}={value}"), tm.sorts.bool_sort);
        (value.into(), indicator)
    }).collect();
    vars.push(cp.variable(entries, &mut tm)?);
}
cp.alldifferent(vars)?;
let mut solver = Solver::new();
solver.register_cp(cp, &mut tm)?;
assert_eq!(solver.check(&mut tm), SolverResult::Sat);
# Ok::<(), nixie_theories::cp::CpError>(())
```

Indicators are ordinary Boolean variables: callers can assert them, negate them,
put them in Boolean formulas, or read them from the returned SMT model. An
indicator means that its CP variable takes the associated `BigInt` value.
Values need not fit a machine integer. `bind_integer` optionally equates these
indicators with equality atoms over an existing SMT Int term. That binding uses
the existing arithmetic engine, including its ordinary completeness limits.
Use the same `TermManager` throughout, and keep `CpVar` handles local to their
own model. Duplicate values, reused indicators within a model, ill-typed bindings,
incorrect table arities, and negative task durations/demands are rejected.

| Constraint | Semantics | Partial-domain filtering |
|---|---|---|
| `alldifferent` | All values pairwise distinct | Bipartite matching; forced-edge support tests detect Hall sets |
| `table` | Tuple belongs to an allowed relation | Exact tuple supports, including repeated variables |
| `regular` | Word has an accepting automaton path | Layered reachability and forced-symbol support tests |
| `circuit` | Successors form one Hamiltonian cycle over every node | Matching, range/self-edge filtering, forced proper-subtour elimination |
| `cumulative` / `cumulative_optional` | Present tasks never exceed constant capacity | Present-task timetable overload, candidate-start filtering, and optional-presence trials |

`regular` permits nondeterminism but no epsilon transitions. When a variable
occurs repeatedly, reachability relaxes the correlation for partial domains;
this can miss pruning but cannot remove a valid word. Complete words are checked
exactly. Empty words require the initial state to be accepting.

`circuit` uses zero-based node indices and includes **every** node. It is the
Hamiltonian variant, not OR-Tools' optional-node/self-loop variant. The empty
circuit is true; a one-node circuit requires successor zero. Multiple disjoint
cycles are forbidden.

`cumulative` uses exact `BigInt` arithmetic and half-open intervals
`[start, start + duration)`. Coincident end/start events are combined before
checking resource usage. Zero-duration tasks consume no resource. Negative
capacity is infeasible even with no tasks. Durations, demands and capacity are
constants. `cumulative(Vec<Task>, capacity)` retains its mandatory-task API.
`cumulative_optional(Vec<OptionalTask>, capacity, &mut tm)` accepts each task's
`presence: TermId`, `start: CpVar`, `duration: BigInt`, and `demand: BigInt`.
Presence can be a Boolean variable, its negation, a Boolean formula, or a
constant; `true` mixes mandatory tasks into the same resource constraint.
Invalid presence sorts and negative durations/demands are rejected atomically.

An absent task consumes nothing and contributes no scheduling restriction to
its start. The start remains an ordinary declared finite-domain variable:
exactly-one semantics and any other constraints or integer bindings still apply.
An empty start domain is therefore infeasible even for an absent task. A
zero-demand task, like a zero-duration task, consumes nothing. Negative capacity
remains infeasible when all tasks are absent.

Only known-present tasks contribute mandatory parts to the timetable. Candidate
start exclusions are explained using that presence knowledge. Unknown tasks do
not prune their starts. To test a condition, the propagator assigns it a trial
truth value, changes every shared/complemented occurrence together, and checks
both the timetable and individual candidate-start support. An impossible trial
implies the opposite condition. The trial is discharged into the conclusion;
it is never added as an assumed premise. This can force absence even when no
start is fixed and the optional task has no mandatory part. Every reduction
uses the original callback assignments, not another unreported reduction.

The [resource-allocation example](../nixie-solver/examples/optional_resource_allocation.rs)
models an eight-GPU cluster: a mandatory service occupies four GPUs throughout
an evening window, and two optional two-hour batches each require four GPUs.
Ordinary Boolean assertions decide admission. When both batches are accepted,
they must occupy nonoverlapping windows; cancelling one removes its resource
usage without restricting its start. Run it with:

```sh
cargo run -p nixie-solver --example optional_resource_allocation
```

The API pattern is:

```rust,ignore
cp.cumulative_optional(vec![OptionalTask {
    presence: accept_training, // ordinary Boolean condition
    start: training_start,     // existing CpVar
    duration: 2.into(),
    demand: 4.into(),
}], 8.into(), &mut tm)?;
```

Variable durations/demands (and variable capacity) are separate future work:
they require new declarations, conditional arithmetic, propagation rules, and
independent proof/model semantics. Stronger cumulative filtering—energetic
reasoning, edge finding, and broader joint-support reasoning—is also separately
scoped and is **not implemented**. No performance improvement is claimed.

An empty domain is infeasible. A zero-arity table containing the empty tuple is
true; an empty relation is false, including at arity zero. Repeated variables in
`alldifferent` are infeasible. These corner cases are intentional.

## Callback and explanation contract

Register at assertion scope zero **before the first check**. Registration is
permanent until `Solver::reset`; assertions can subsequently use normal
push/pop, repeated checks and assumptions. Registration at a later point returns
an error, preventing watches on previously eliminated SAT variables. Reset
removes registrations along with assertions. Mutable client state must follow
search `push`/`pop`; each SAT search and model validation has an outer scope that
is unwound on every exit. An externally shared callback must not mutate its
constraint semantics between checks (cached verdicts and learned clauses assume
fixed semantics).

Watches are Boolean terms. `on_fixed` receives the watched term and the term
manager's Boolean true/false constant. A `Consequence` represents
`justification[0] AND ... AND justification[n] => term`. Reasons are **signed
Boolean literals**, not unsigned watched-term identifiers. The allowed vocabulary
is watched terms and their negations, plus Boolean constants. The adapter checks
that all reasons are currently true; unknown/unregistered reasons or consequences
fail closed to `Unknown`. `Unsat(reasons)` means that the conjunction of those
true antecedents is impossible; the adapter negates them to form a conflict
clause. An empty reason denotes an unconditional client axiom. Clients are trusted
to prove the implication; the adapter cannot establish arbitrary theory validity.

The CP implementation explains each reduction independently using the current
indicator assignments. It never uses an unreported local reduction as a premise.
This first implementation prefers complete, sometimes large explanations and
recomputes supports rather than maintaining reversible matching caches. It makes
no throughput claim relative to specialized CP solvers. `cumulative` does not
implement edge finding or energetic reasoning, and `circuit` filtering is not
full domain consistency. All five constraints are exact on complete assignments.

Callbacks run during CDCL(T) assignment propagation and final checks. Watched SAT
variables are frozen against elimination. An independent gate replays the
returned model through the callbacks, including models returned by specialized
solver shortcuts: an incomplete or rejected model becomes `Unknown`. Registered
callbacks also prevent `check_sat_only` from bypassing the theory. The generic
callback's default final check is `Unknown`; implement it explicitly to certify
complete assignments. Equality/disequality callbacks and decision hints in the
older manager interface are not connected to the SMT adapter; use Boolean
equality atoms for this interface.

Arbitrary client axioms have no proof exporter/checker: proof-producing or
certified checks with arbitrary user callbacks return `Unknown`. Built-in CP
registrations support the complete checked proof chain described below, as
do graph and FSM registrations through `register_graph`/`register_fsm`
(their `GraphLemma` records share the CP proof envelope, version 2). SMT unsat cores, when available, are relative to the permanently installed
client constraints; they do not serialize those constraints.

## Reference and audit basis

The callback architecture follows the read-only Z3 implementation
`../temp/z3/src/smt/theory_user_propagator.cpp`: fixed events, explained
consequences, final checking, and search scope callbacks. Nixie's Boolean-only
interface states its narrower vocabulary explicitly. Constraint semantics were
checked against OR-Tools' [CP model definitions](https://github.com/google/or-tools/blob/stable/ortools/sat/cp_model.proto),
[matching implementation](https://github.com/google/or-tools/blob/stable/ortools/sat/all_different.cc),
and [cumulative implementation](https://github.com/google/or-tools/blob/stable/ortools/sat/cumulative.cc).

The implementation audit covers independent layers: finite-domain representation
and one-value semantics; each global predicate; explanations and literal polarity;
callback manager rollback (including overwritten values, equalities, watches,
registrations, and pending consequences); SAT variable freezing and callback
composition; repeated checks/reset/assertion scopes; specialized solver exits;
model validation; and proof/certification boundaries. Exhaustive tests compare
all reductions from 1,715 partial-domain cases against independently enumerated
concrete solutions, and integration tests compare all five constraints against
135 complete assignments. Additional regressions exercise Hall pruning, aliases,
subtours, wide scheduling arithmetic, malformed explanations, and lifecycle rules. The independent model gate also checks consequence
reasons directly, without relying on a preceding search callback.

| Audited layer | Independent evidence |
|---|---|
| Domain cardinality and construction | `domain_exactly_one_and_invalid_construction` rejects two true indicators, empty domains, malformed tuples, and negative durations |
| Complete constraint predicates | `all_five_constraints_reject_and_accept_complete_assignments` checks 135 assignments against separate predicates |
| Partial reductions and conflict reasons | `every_partial_domain_reduction_has_a_valid_explanation` checks emitted implications against all concrete solutions, across 1,715 partial-domain states |
| Matching strength | `hall_set_forces_a_value_before_any_variable_is_fixed` checks Hall pruning directly, before SAT integration |
| Scope state | `restores_overwrites_equalities_watches_and_pending_consequences` checks each manager table and queue independently |
| SAT integration and backtracking | `search_combines_propagators_and_boolean_constraints` requires conflicts from interacting constraints; `hall_sets_and_repeated_checks_and_scopes` checks repeated checks and scoped retraction |
| SMT combination | `integer_binding_combines_with_arithmetic` refutes an equality incompatible with the global constraint |
| Result validation and client trust | `user_callbacks_fail_closed_on_bad_reasons_and_incomplete_checks`, `registration_lifecycle_reset_and_certification`, and `specialized_shortcuts_cannot_skip_user_constraints` exercise the honesty gates |
| Numeric and endpoint exactness | `cumulative_bigints_and_half_open_zero_duration` uses 101-bit values and touching/zero-duration intervals |

Verification details and the pre-existing tuple reconstruction defect found
by the full suite are recorded in the [implementation study](studies/2026-09-16-cp-and-tuple-reconstruction.md).

A broader [generated-oracle study](studies/2026-09-16-cp-generated-oracle.md)
checks 244 varied instances, including conjunctions of globals: 6,704 complete
assignments, 37,810 callback states, 171,301 emitted consequences/conflicts,
and 6,100 public solver verdict/model checks. The independent oracle checks
explanations against all satisfying base assignments and exercises nested
rollback. The original campaign supplied bounded testing evidence. The complete
proof path below now additionally checks generated UNSAT certificates.

## Checkable table lemmas

Built-in `table` reductions and conflicts now carry a
`Consequence::table_certificate`. Retain `CpModel::table_statements()` before
consuming the model to check emitted steps independently:

```rust,ignore
let originals = cp.table_statements();
let (assertions, watches, propagator) = cp.into_propagator();
// Install watches and callbacks in a UserPropagatorManager as usual.
// A solver integration must install assertions too (register_cp does this).
// For each consequence obtained from manager.get_consequences():
if let Some(certificate) = &consequence.table_certificate {
    let original = originals.iter()
        .find(|statement| certificate.is_for(statement))
        .ok_or("unregistered table")?;
    certificate.check(original, consequence.term, &consequence.justification)?;
}
```

A certificate covers every original allowed row. Each row identifies an
out-of-domain value, incompatible aliased columns, a blocking premise, or a
value incompatible with the negated conclusion. The checker uses only the
immutable original table, its finite-domain indicator meanings, and the exact
premises/conclusion. It does not call propagation, inspect current assignments,
or rerun search. Integer comparisons remain exact. Unused premises weaken the
lemma; the solver separately requires **all** stated premises to be currently
true.

`Solver::register_cp` retains the original statement identities. The adapter
rejects substituted statements or invalid witnesses with `Unknown`, including
on the direct final-conflict path and independent model replay. Certificates
and their immutable statements survive callback queue snapshots; popping a
scope restores the pending queue rather than replaying a stale branch.

This is a certificate for a **conditional table lemma relative to the original
CP domains and constraint**. Domain-only reductions/conflicts have the specialized certificates described
below. Arbitrary callbacks without certificates retain their documented
trusted-client contract. Complete CP proof export additionally checks the finite
semantics of every admitted lemma and the final LRAT refutation.

See the [table-certificate study](studies/2026-09-16-cp-table-certificates.md)
for the soundness argument, adversarial checks, and verification record.


## Checkable domain lemmas

`CpModel::domain_statements()` retains immutable original exactly-one domains.
Built-in domain-only reductions and conflicts carry
`Consequence::domain_certificate`. A `DomainCertificate` proves one of three
rules against the retained domain:

- Two distinct positive indicators imply false (`DistinctFixed`).
- A positive indicator excludes a different value (`Exclusion`).
- A negative premise for every original value implies false (`Exhausted`).

An empty original domain has an empty exhaustion cover. A repeated premise
cannot stand in for two different selected values or two different exclusions.
Every indexed premise must have the exact required polarity. Unsupported
conclusions, omitted coverage, and invalid indexes are rejected. The checker
uses only the statement and implication, independently of the callback's
current-domain computation. It checks indexes and uses exact original indicator
meanings; it neither searches nor converts integer values to machine integers.

The checking interface parallels table certificates: retain the originals,
authenticate with `is_for`, then call
`certificate.check(original, consequence.term, &consequence.justification)`.
`register_cp` installs domain identities only after successful registration;
reset revokes them. The solver checks **every** attached certificate, including
when a consequence carries both kinds, and independently checks current premise
truth. The same checks run on direct final conflicts and model replay.

These rules establish conditional lemmas relative to the declared exactly-one
semantics. At least one value is also asserted to the SAT solver; at-most-one
reasoning is lazy. These local certificates also remain usable separately from the complete proof
chain below. See the [domain-certificate study](studies/2026-09-16-cp-domain-certificates.md)
for the trust boundary and verification evidence.

## Complete checked CP proofs

On `std` builds, with `SolverConfig::default().certified()` or `.with_proof()`, built-in CP models
can now return checked `Sat` and `Unsat`. Arbitrary user callbacks still fail
closed, including when installed alongside a CP model.

The chain is:

1. Retain immutable original CP declarations separately from the proof,
   including typed integer bindings and signed optional-task presence conditions. Validate the generated domain/link
   assertions against those declarations. The main solver's generated CP
   assertion entries are excluded from the original application-assertion inputs;
   the proof reconstructs their meaning from the validated declarations.
2. Check each explanation `premises => conclusion` against those declarations.
   Exactly-one domain semantics restrict possible values. An independent finite
   checker enumerates assignments of an original global and rejects a lemma if
   any compatible assignment falsifies it. Aliased positions share one value.
   The checker does not call the propagator, matching, partial-domain filtering,
   or solver search. Optional scheduling leaves enumerate each distinct presence
   condition along with the relevant finite-domain values; shared/complemented
   occurrences share one Boolean digit. Formula/domain correlations may be
   relaxed, enlarging the support set and conservatively rejecting some valid
   lemmas. The canonical Boolean encoding preserves the actual formulas and
   aliases. Presence conditions are included in replay/model-blocking inputs
   even when application assertions never mention them. All five globals are covered, including empty/aliased
   inputs, nondeterministic automata, exact large integers, and half-open tasks.
3. Reconstruct a canonical Boolean encoding of the original active assertions,
   domain/link assertions, and checked implication clauses. Additional EUF or
   linear-arithmetic leaves must pass their existing independent verifiers.
4. Generate an LRAT refutation in a fresh SAT solver. Require its entire input
   clause list to equal the canonical list, then independently check derivation
   of the empty clause. The search engine's verdict alone is never enough.

A certified `Sat` additionally requires independent exact evaluation of every
original global, presence valuation, and exactly-one domain, and the existing
assertion/model gate. Ordinary CP `Sat` results also pass the independent
statement evaluator before callback replay; missing presence values fail closed.
Optional scheduling uses the existing `CpLemma` records and version-2 envelope,
with no new trusted axiom or proof bypass. Removing a needed presence premise
invalidates a lemma and its complete proof.

The [optional-scheduling study](studies/2026-09-22-cp-optional-scheduling.md)
records the reference rules, audited layers, exhaustive oracles, and landing gates.

```rust,ignore
let mut solver = Solver::with_config(SolverConfig::default().certified());
solver.register_cp(cp, &mut tm)?;
// Add the application's assertions, then retain the original proof inputs.
let (originals, graphs, assertions) = solver.cp_proof_inputs();
if solver.check(&mut tm) == SolverResult::Unsat {
    let proof = solver.get_cp_proof().ok_or("missing CP proof")?;
    let text = proof.to_text();
    let imported = nixie_solver::CpProof::from_text(&text)?;
    imported.check(&originals, &graphs, &assertions, &mut tm, 10_000_000)?;
    let dimacs = imported.dimacs(&originals, &graphs, &assertions, &mut tm, 10_000_000)?;
    // `dimacs` and `imported.lrat` can also be given to an external LRAT checker.
}
```

The versioned text envelope exports the explanation leaves and LRAT body.
Original inputs are intentionally supplied independently: the proof cannot choose
what problem it refutes. Term IDs belong to the retained original `TermManager`;
this is a Rust API proof format, not an SMT-LIB/Alethe encoding of CP declarations.
DIMACS plus LRAT alone establishes only the propositional refutation; `check`
checks its connection to the original CP problem as well. `get_proof()` does not
represent CP declarations; use `get_cp_proof()`.

Proofs are invalidated by assert/push/pop/reset and settings changes. Saved proof
values remain checkable against saved original inputs. `check_with_assumptions`
pops its temporary scope and discards its proof, just like the existing proof
API; use explicit push/assert/check and capture the proof before pop when an
assumption-scoped artifact is needed. Conditional lemma records may survive pop:
they are rechecked against permanent declarations, never treated as asserted facts.

Finite lemma checking can be exponential. Production reconstruction allows ten
million semantic work steps per checking pass, 100,000 SAT conflicts per
reconstruction/replay solver, and 10,000 model-blocking iterations. Missing
search leaves are reconstructed from independently checked CP/SMT model
blockers. A required step that exceeds these limits, an unsupported SMT
combination, or a failed refutation yields `Unknown`.
Specialized polynomial witnesses for the remaining globals would improve proof
checking cost; they are not required for the validity of this complete chain.
No throughput or proof-size improvement is claimed. See the
[complete-proof study](studies/2026-09-16-cp-complete-proof.md) for verification.

Cumulative candidate checks borrow a singleton start override instead of
copying all domains. This preserves the same filtering and explanations,
including tasks sharing a start variable. The scoped public-API benchmark
and controlled instruction measurements are recorded in
[the scheduling performance study](studies/2026-09-22-cp-scheduling-perf.md).

Cumulative bounds are also reused lazily within each callback; singleton
trials never modify these cached extrema. During independent model replay,
concrete Boolean evaluations are reused only within that model's validation.
Every statement, certificate and consequence remains checked. The
[Z3-reference study](studies/2026-09-22-cp-scheduling-bounds.md) reports explicit
Nixie/Z3 instruction ratios separately from Nixie before/after measurements.

Domain snapshots retain the premise position of a fixed value. Exactly-one
exclusions use that position to produce the same witness, which still passes
the independent domain checker. Unknown indicators need no repeated BigInt
membership scan, and snapshot construction stops copying alternatives after
a fixed value is found. This local reuse does not survive a callback or scope.
The [exclusion study](studies/2026-09-22-cp-scheduling-exclusions.md) records
the controlled Z3 comparison and unchanged explanation/proof checks.
