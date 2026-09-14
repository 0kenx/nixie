//! Bounded model checking, end to end.
//!
//! These are the first checks in the repository that go all the way from TLA+
//! source to a solver verdict, so they pin both directions: a specification
//! with a reachable violation must produce one at the right depth, and one
//! without must not produce a spurious counterexample.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome, SetupError};

fn check(src: &str, init: &str, next: &str, inv: &str, depth: u32) -> Outcome {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare(&spec, module, init, next, inv, &[], &mut tm).expect("prepares");
    bmc.check(depth, &mut tm).expect("checks")
}

fn setup_err(src: &str, init: &str, next: &str, inv: &str) -> SetupError {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    Bmc::prepare(&spec, module, init, next, inv, &[], &mut tm)
        .err()
        .expect("should not prepare")
}

/// A counter that starts at 0 and increments. `x < 3` fails after three steps,
/// and must be reported at exactly that depth — not earlier, not later.
const COUNTER: &str = r"
---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv  == x < 3
====
";

#[test]
fn a_reachable_violation_is_found_at_the_right_depth() {
    assert_eq!(
        check(COUNTER, "Init", "Next", "Inv", 10),
        Outcome::Violation { step: 3 }
    );
}

#[test]
fn a_shorter_bound_finds_nothing() {
    assert_eq!(
        check(COUNTER, "Init", "Next", "Inv", 2),
        Outcome::NoViolationWithin(2)
    );
}

/// The bound is exact: two steps reach `x = 2`, which satisfies `x < 3`.
#[test]
fn the_bound_is_off_by_nothing() {
    assert_eq!(
        check(COUNTER, "Init", "Next", "Inv", 3),
        Outcome::Violation { step: 3 }
    );
}

/// A genuinely invariant property must not produce a counterexample however
/// deep the search goes. A spurious `Violation` here is the model-checking
/// equivalent of a wrong `sat`.
#[test]
fn an_inductive_invariant_is_never_violated() {
    let src = r"
---- MODULE Bounded ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == IF x < 5 THEN x' = x + 1 ELSE x' = x
Inv  == x >= 0 /\ x <= 5
====
";
    assert_eq!(
        check(src, "Init", "Next", "Inv", 12),
        Outcome::NoViolationWithin(12)
    );
}

/// An action that does not mention `y'` leaves `y` free to take any value —
/// that is what TLA+ means, and encoding it as unchanged would hide real
/// counterexamples.
#[test]
fn an_unmentioned_variable_is_unconstrained() {
    let src = r"
---- MODULE Free ----
EXTENDS Integers
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1
Inv  == y = 0
====
";
    assert_eq!(
        check(src, "Init", "Next", "Inv", 3),
        Outcome::Violation { step: 1 }
    );
}

/// ...and `UNCHANGED` is what pins it down.
#[test]
fn unchanged_pins_a_variable() {
    let src = r"
---- MODULE Pinned ----
EXTENDS Integers
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ UNCHANGED y
Inv  == y = 0
====
";
    assert_eq!(
        check(src, "Init", "Next", "Inv", 4),
        Outcome::NoViolationWithin(4)
    );
}

/// A rigid `CONSTANT` must not be allowed to change between steps. If it were
/// treated as a state variable, `N` could differ at each step and this
/// invariant would appear to fail.
#[test]
fn a_constant_does_not_change_between_steps() {
    let src = r"
---- MODULE Rigid ----
EXTENDS Integers
CONSTANT N
VARIABLE x
Init == x = N
Next == x' = x
Inv  == x = N
====
";
    assert_eq!(
        check(src, "Init", "Next", "Inv", 5),
        Outcome::NoViolationWithin(5)
    );
}

/// Priming distributes: `(x + 1)'` is `x' + 1`, so this is the same machine as
/// `COUNTER` and must fail at the same depth.
#[test]
fn priming_distributes_over_arithmetic() {
    let src = r"
---- MODULE Distr ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == (x + 1)' = x + 2
Inv  == x < 3
====
";
    assert_eq!(
        check(src, "Init", "Next", "Inv", 6),
        Outcome::Violation { step: 3 }
    );
}

#[test]
fn a_missing_definition_is_named() {
    assert_eq!(
        setup_err(COUNTER, "Init", "Nope", "Inv"),
        SetupError::NoSuchDefinition("Nope".to_string())
    );
}

/// A **set-valued state variable** is checked, which the arena encoding could
/// never do: its candidate members are whatever the transition relation puts
/// there, so there is no statically knowable list. The solver's finite-set
/// sort carries it instead.
#[test]
fn a_set_valued_state_variable_is_checked() {
    let src = r"
---- MODULE Sets ----
EXTENDS Integers
VARIABLE s
Init == s = {1}
Next == s' = s
Inv  == 1 \in s
====
";
    assert_eq!(
        check(src, "Init", "Next", "Inv", 3),
        Outcome::NoViolationWithin(3)
    );
}

/// ...and a violation in one is found, so the previous test is not passing
/// merely because nothing is constrained.
#[test]
fn a_set_valued_state_variable_can_violate() {
    let src = r"
---- MODULE SetsBad ----
EXTENDS Integers
VARIABLE s
Init == s = {1}
Next == s' = s
Inv  == 2 \in s
====
";
    assert_eq!(
        check(src, "Init", "Next", "Inv", 3),
        Outcome::Violation { step: 0 }
    );
}

/// A set that **grows** across steps — the shape the arena cannot express at
/// all, because `s@1`'s members depend on the action taken.
#[test]
fn a_growing_set_is_tracked_across_steps() {
    let src = r"
---- MODULE Grow ----
EXTENDS Integers
CONSTANT v
VARIABLE s
Init == s = {}
Next == s' = s \cup {v}
Inv  == ~(v \in s)
====
";
    // After one step `v` is in `s`, so the invariant fails at step 1.
    assert_eq!(
        check(src, "Init", "Next", "Inv", 4),
        Outcome::Violation { step: 1 }
    );
}

/// Set difference removes, and the invariant survives.
#[test]
fn set_difference_across_steps() {
    let src = r"
---- MODULE Shrink ----
EXTENDS Integers
CONSTANT v
VARIABLE s
Init == s = {v}
Next == s' = s \ {v}
Inv  == ~(2 \in s) \/ 2 = v
====
";
    assert_eq!(
        check(src, "Init", "Next", "Inv", 3),
        Outcome::NoViolationWithin(3)
    );
}

/// `ASSUME` constrains the `CONSTANT`s, and dropping it turns "holds for the
/// intended parameters" into "holds for every value" — a strictly harder
/// claim that fails on correct specifications.
///
/// Without the assumption `N > 0`, the solver is free to pick `N = 0`, and
/// `x < N` fails in the initial state.
#[test]
fn assumptions_constrain_the_constants() {
    let src = r"
---- MODULE Assumed ----
EXTENDS Integers
CONSTANT N
VARIABLE x
ASSUME N > 3
Init == x = 0
Next == x' = x
Inv  == x < N
====
";
    assert_eq!(
        check(src, "Init", "Next", "Inv", 3),
        Outcome::NoViolationWithin(3)
    );
}

/// The same specification without the assumption *must* report the violation,
/// so the test above is really testing the assumption and not something else.
#[test]
fn without_the_assumption_the_constant_is_arbitrary() {
    let src = r"
---- MODULE Unassumed ----
EXTENDS Integers
CONSTANT N
VARIABLE x
Init == x = 0
Next == x' = x
Inv  == x < N
====
";
    assert_eq!(
        check(src, "Init", "Next", "Inv", 3),
        Outcome::Violation { step: 0 }
    );
}

/// A dropped assumption must be counted, because it weakens the search: fewer
/// assumptions means more states look reachable, so a `Violation` may be an
/// artefact rather than a real trace.
///
/// The unsortable constant here has been chased twice. It was a tuple until
/// tuples became datatypes, then a sequence until sequences got a sort. What
/// is left is an **open record** — one where inference only ever saw a field
/// access, so the value may carry fields the type does not list — which is
/// refused on purpose, because a datatype over the known fields would make two
/// records that differ only in the rest compare equal.
#[test]
fn dropped_assumptions_are_counted_not_silent() {
    let src = r"
---- MODULE Dropped ----
EXTENDS Integers
CONSTANT N, R
VARIABLE x
ASSUME N > 3
ASSUME R.f = 2
Init == x = 0
Next == x' = x
Inv  == x < N
====
";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    let out = bmc.check(3, &mut tm).expect("checks");
    assert_eq!(out, Outcome::NoViolationWithin(3));
    assert_eq!(
        bmc.dropped_assumptions(),
        1,
        "an assumption over an open-record constant has no sort and must be reported"
    );
}

/// Apalache's `ConstInit` convention: a specification whose constants are
/// pinned by `--cinit=ConstInit` carries no `ASSUME`, so a checker that reads
/// only `ASSUME` sees arbitrary constants and reports a counterexample the
/// specification does not have.
///
/// `Bug1023.tla` in Apalache's own test suite is exactly this shape, and it is
/// how the false alarm was found.
const CINIT: &str = r"
---- MODULE CInit ----
EXTENDS Integers
CONSTANT t_min, t_max
ConstInit == t_min <= t_max
Init == TRUE
Next == TRUE
Inv  == t_min <= t_max
====
";

fn check_with(src: &str, constraints: &[&str], depth: u32) -> Outcome {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", constraints, &mut tm).expect("prepares");
    bmc.check(depth, &mut tm).expect("checks")
}

#[test]
fn a_constant_initializer_is_assumed_when_named() {
    assert_eq!(
        check_with(CINIT, &["ConstInit"], 3),
        Outcome::NoViolationWithin(3)
    );
}

/// ...and without it the constants really are arbitrary, so the test above is
/// testing the constraint rather than something else.
#[test]
fn without_the_constant_initializer_the_violation_returns() {
    assert_eq!(check_with(CINIT, &[], 3), Outcome::Violation { step: 0 });
}

/// A named constraint that does not exist is an error, not a silent skip: the
/// caller asked for it, and quietly checking a weaker specification is exactly
/// the shape of a false clean bill of health.
#[test]
fn a_missing_named_constraint_is_an_error() {
    let parsed = nixie_tla_syntax::parse_file(CINIT).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    assert_eq!(
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &["Nope"], &mut tm)
            .err()
            .expect("should not prepare"),
        SetupError::NoSuchDefinition("Nope".to_string())
    );
}

/// An invariant must be a **state** predicate. `Inv == UNCHANGED x` is an
/// action, so the specification is malformed rather than violated.
///
/// Found on Apalache's `UnchangedAsInv1663.tla`, where the checker happily
/// reported a counterexample: with no transition asserted at depth 0, the
/// next-state value in `UNCHANGED x` is unconstrained, so `~Inv` is trivially
/// satisfiable. The answer was a faithful reading of the encoded formula and a
/// meaningless statement about the specification.
#[test]
fn an_action_used_as_an_invariant_is_rejected() {
    let src = r"
---- MODULE ActionInv ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x
Inv  == UNCHANGED x
====
";
    assert!(
        matches!(
            setup_err(src, "Init", "Next", "Inv"),
            SetupError::Level {
                role: "an invariant",
                ..
            }
        ),
        "an action invariant must be rejected, not reported as violated"
    );
}

/// An initial predicate may not mention `'` either.
#[test]
fn an_action_used_as_an_initial_predicate_is_rejected() {
    let src = r"
---- MODULE ActionInit ----
EXTENDS Integers
VARIABLE x
Init == x' = 0
Next == x' = x
Inv  == x = 0
====
";
    assert!(matches!(
        setup_err(src, "Init", "Next", "Inv"),
        SetupError::Level {
            role: "an initial predicate",
            ..
        }
    ));
}

/// A temporal formula is not a next-state action.
#[test]
fn a_temporal_formula_is_not_a_next_state_action() {
    let src = r"
---- MODULE TemporalNext ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == [](x = 0)
Inv  == x = 0
====
";
    assert!(matches!(
        setup_err(src, "Init", "Next", "Inv"),
        SetupError::Level {
            role: "a next-state action",
            ..
        }
    ));
}

/// The level gate is one-sided: a level that could not be established is not
/// grounds for rejection, only a level that was *proved* too high.
#[test]
fn a_well_levelled_specification_still_passes() {
    assert_eq!(
        check(COUNTER, "Init", "Next", "Inv", 4),
        Outcome::Violation { step: 3 }
    );
}

/// A function-valued state variable encodes as an SMT array, so `f[i]` is a
/// select and `[f EXCEPT ![i] = v]` is a store.
///
/// The index is a `CONSTANT` rather than a literal on purpose: `f[1]` alone
/// does not say whether `f` is a tuple, a sequence or a function, and
/// inference reports that rather than guessing.
#[test]
fn a_function_state_variable_is_checked() {
    let src = r"
---- MODULE Fun ----
EXTENDS Integers
CONSTANT k
VARIABLE f
Init == f[k] = 0
Next == f' = [f EXCEPT ![k] = f[k] + 1]
Inv  == f[k] < 3
====
";
    assert_eq!(
        check(src, "Init", "Next", "Inv", 8),
        Outcome::Violation { step: 3 }
    );
}

/// `EXCEPT` must leave other indices alone — the store/select axioms doing
/// their job, which is what makes the array encoding faithful *inside* the
/// domain.
#[test]
fn except_leaves_other_indices_alone() {
    let src = r"
---- MODULE Untouched ----
EXTENDS Integers
CONSTANT j, k
VARIABLE f
ASSUME j # k
Init == f[k] = 0 /\ f[j] = 7
Next == f' = [f EXCEPT ![k] = f[k] + 1]
Inv  == f[j] = 7
====
";
    assert_eq!(
        check(src, "Init", "Next", "Inv", 5),
        Outcome::NoViolationWithin(5)
    );
}

/// A function-typed variable carries its domain, so an ordinary `f[x]` no
/// longer goes through the unmodelled-domain path. This used to assert the
/// opposite, and the flag flipping is the point: `arena::Value::Fun` gives a
/// function a domain as well as a graph.
#[test]
fn a_function_variable_has_a_modelled_domain() {
    let src = r"
---- MODULE Dom ----
EXTENDS Integers
CONSTANT k
VARIABLE f
Init == f[k] = 0
Next == f' = f
Inv  == f[k] = 0
====
";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(3, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(3)
    );
    assert!(
        !bmc.encoder().domain_unmodelled(),
        "a function-typed variable carries its own domain"
    );
}

/// What is still unmodelled, and must still say so: a function reached
/// *through* an application. `f[a]` is a select, and its result is a bare
/// array — the range sort carries no domain of its own — so `f[a][b]` leaves
/// TLA+'s undefinedness outside that inner domain unrepresented.
#[test]
fn a_nested_function_still_reports_an_unmodelled_domain() {
    let src = r"
---- MODULE Nested ----
EXTENDS Integers
CONSTANT k
VARIABLE f
Init == f[k][k] = 0
Next == f' = f
Inv  == f[k][k] = 0
====
";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(3, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(3)
    );
    assert!(
        bmc.encoder().domain_unmodelled(),
        "the inner function of `f[a][b]` is a bare array and has no domain"
    );
}

/// `Nat` is **not** an arbitrary set. Encoding it as an opaque set constant
/// leaves it unconstrained, so the solver may decide `0 \notin Nat` and report
/// `TypeOK == x \in Nat` violated in the initial state — a false
/// counterexample, found on `AddTwo.tla`.
///
/// Membership in the standard infinite sets is exactly expressible, so it is
/// encoded rather than declined: `x \in Nat` is `x >= 0`.
#[test]
fn membership_in_nat_is_not_a_free_choice() {
    let src = r"
---- MODULE AddTwoish ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 2
TypeOK == x \in Nat
====
";
    assert_eq!(
        check(src, "Init", "Next", "TypeOK", 4),
        Outcome::NoViolationWithin(4),
        "x starts at 0 and only grows, so it is always a natural"
    );
}

/// ...and the encoding is not simply "always true": a variable that goes
/// negative really does leave `Nat`.
#[test]
fn leaving_nat_is_detected() {
    let src = r"
---- MODULE Countdown ----
EXTENDS Integers
VARIABLE x
Init == x = 1
Next == x' = x - 1
TypeOK == x \in Nat
====
";
    assert_eq!(
        check(src, "Init", "Next", "TypeOK", 4),
        Outcome::Violation { step: 2 },
        "1, 0, then -1 leaves Nat at step 2"
    );
}

/// `Int` contains every integer, so membership is trivially true rather than
/// an unconstrained atom.
#[test]
fn membership_in_int_is_trivially_true() {
    let src = r"
---- MODULE AnyInt ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x - 1
TypeOK == x \in Int
====
";
    assert_eq!(
        check(src, "Init", "Next", "TypeOK", 3),
        Outcome::NoViolationWithin(3)
    );
}
