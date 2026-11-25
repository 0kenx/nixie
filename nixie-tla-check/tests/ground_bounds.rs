//! A range bound has to be **ground**, not literal.
//!
//! `CONSTANT N = 4` in a `.cfg` is a *substitution*: TLC replaces the constant,
//! so `0 .. N-1` becomes `0 .. (4-1)`. That is as ground as `0 .. 3` and has
//! exactly the same three members, but a check for a literal rejects it – and
//! `0 .. N-1` is how a ring of `N` nodes is written, so the rejection reached a
//! large part of the corpus (`EWD998` among them).
//!
//! The value is computed by `nixie-tla`'s evaluator rather than by a second
//! constant folder here. That is the right authority, not a convenience: it is
//! the implementation of TLA+ arithmetic that `bench/tla_eval` checks against
//! TLC, and two folders would be two semantics to keep in agreement.
//!
//! What must *not* change is the refusal. A genuinely symbolic bound still has
//! no candidate list, and these pin that too – inventing one would check a
//! different specification.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome, Roles};
use nixie_tla_syntax::parse_config;

/// One invariant, the common case. Built inline at each call site's option,
/// because the slice has to borrow from the caller's `&'r str` and a helper
/// returning `Roles<'r>` would have to conjure that borrow out of its own
/// parameter slot.
macro_rules! roles {
    ($init:expr, $next:expr, $inv:expr) => {
        Roles {
            init: $init,
            next: $next,
            inv: &[$inv],
            constraints: &[],
        }
    };
}

fn claim(vars: &str, defs: &str, init: &str, body: &str) -> Outcome {
    let src = format!(
        r"
---- MODULE Claim ----
EXTENDS Integers, FiniteSets
VARIABLE {vars}
{defs}
Init == {init}
Next == UNCHANGED <<{vars}>>
Inv  == {body}
====
"
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&loaded, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    bmc.check(0, &mut tm).expect("checks")
}

fn holds(vars: &str, defs: &str, init: &str, body: &str) {
    assert_eq!(
        claim(vars, defs, init, body),
        Outcome::NoViolationWithin(0),
        "`{body}`"
    );
}

fn fails(vars: &str, defs: &str, init: &str, body: &str) {
    assert_eq!(
        claim(vars, defs, init, body),
        Outcome::Violation { step: 0 },
        "`{body}`"
    );
}

// ======== an arithmetic bound ========

#[test]
fn a_range_whose_upper_bound_is_arithmetic() {
    holds("x", "", "x = 0", "Cardinality(0 .. (4 - 1)) = 4");
    holds("x", "", "x = 0", "0 .. (4 - 1) = {0, 1, 2, 3}");
}

#[test]
fn a_range_whose_lower_bound_is_arithmetic() {
    holds("x", "", "x = 0", "(1 + 1) .. 4 = {2, 3, 4}");
}

#[test]
fn a_wrong_claim_about_an_arithmetic_range_still_fails() {
    fails("x", "", "x = 0", "0 .. (4 - 1) = {0, 1, 2}");
}

/// The bound may be an arbitrarily deep ground expression – it is evaluated,
/// not matched.
#[test]
fn a_nested_ground_bound() {
    holds("x", "", "x = 0", "1 .. (2 * 3 - 4 \\div 2) = {1, 2, 3, 4}");
}

/// A definition is inlined before the bound is read, so a named bound works.
#[test]
fn a_bound_that_is_a_definition() {
    holds("x", "K == 2 + 1", "x = 0", "1 .. K = {1, 2, 3}");
}

/// A negative bound, which is where the literal check had its one concession
/// (`Kera::Neg`) and where the evaluator has to agree with it.
#[test]
fn a_negative_arithmetic_bound() {
    holds("x", "", "x = 0", "(0 - 2) .. (1 - 1) = {-2, -1, 0}");
}

/// An empty range is still a range: `3 .. (1 + 1)` has no members.
#[test]
fn an_empty_arithmetic_range() {
    holds("x", "", "x = 0", "3 .. (1 + 1) = {}");
}

// ======== a bound over a quantifier ========

#[test]
fn a_quantifier_over_an_arithmetic_range() {
    holds("x", "", "x = 0", "\\A i \\in 1 .. (2 + 1) : i < 4");
    fails("x", "", "x = 0", "\\A i \\in 1 .. (2 + 1) : i < 3");
}

// ======== a tuple index ========

/// The same defect, in a second place: a tuple is a function on `1..n`, and its
/// index had to be a literal too.
#[test]
fn a_tuple_indexed_by_an_arithmetic_expression() {
    holds("x", "", "x = 0", "<<10, 20, 30>>[1 + 1] = 20");
    fails("x", "", "x = 0", "<<10, 20, 30>>[1 + 1] = 10");
}

#[test]
fn except_on_a_tuple_at_an_arithmetic_index() {
    holds(
        "x",
        "",
        "x = 0",
        "[<<10, 20, 30>> EXCEPT ![3 - 1] = 99] = <<10, 99, 30>>",
    );
}

// ======== the refusal survives ========

const SYMBOLIC: &str = r"
---- MODULE Symbolic ----
EXTENDS Integers
CONSTANT N
VARIABLE x
Init == x = 1
Next == UNCHANGED x
Inv  == x \in 0 .. N - 1
====
";

/// With nothing pinning `N`, `x \\in 0..N-1` used to be refused because the
/// arena could not enumerate the range. Since membership became a comparison
/// (issue #22) the query is answered – and the answer is a **violation**:
/// with `N` free, `x = 1` leaves the invariant when `N = 1`. That is the
/// true verdict about the specification as written; what still refuses is
/// anything that needs the range's *elements* (a fold, a cardinality over a
/// set built from it), which no comparison can serve.
#[test]
fn a_symbolic_bound_is_answered_not_enumerated() {
    let parsed = nixie_tla_syntax::parse_file(SYMBOLIC).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let config = parse_config("").expect("config parses");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_with_config(
        &loaded,
        module,
        roles!("Init", "Next", "Inv"),
        &config,
        &mut tm,
    )
    .expect("prepares");
    let out = bmc.check(1, &mut tm).expect("checks");
    assert_eq!(
        out,
        Outcome::Violation { step: 0 },
        "with `N` free the invariant does not hold – the honest verdict"
    );
}

/// And the configuration is what makes it ground – the `EWD998` shape, end to
/// end: the `.cfg` pins `N`, the arithmetic is folded, the range enumerates.
#[test]
fn a_configured_constant_makes_an_arithmetic_bound_ground() {
    let parsed = nixie_tla_syntax::parse_file(SYMBOLIC).expect("parses");
    let loaded = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = loaded.root_module().expect("has a root module");
    let config = parse_config("CONSTANTS N = 4").expect("config parses");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_with_config(
        &loaded,
        module,
        roles!("Init", "Next", "Inv"),
        &config,
        &mut tm,
    )
    .expect("prepares");
    assert_eq!(
        bmc.check(1, &mut tm).expect("checks"),
        Outcome::NoViolationWithin(1)
    );
}
