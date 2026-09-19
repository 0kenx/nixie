//! The `Bags` standard-module vocabulary, encoded.
//!
//! A bag *is* a function whose range is the positive naturals (`Bags.tla`),
//! and the operators lower to the module's own definitions (see
//! `Lowerer::bag_desugar`), so what these tests pin is the whole pipeline —
//! desugar, types, the function encoding — answering over bag state:
//! ground construction in `Init`, symbolic reads through `CopiesIn` /
//! `BagIn`, and the honest decline when an *update* needs a function
//! definition over a symbolic domain, which the enumeration-based encoding
//! cannot serve (and never guesses at).

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome};

fn claim(vars: &str, init: &str, body: &str) -> Outcome {
    let src = format!(
        r"
---- MODULE Claim ----
EXTENDS Integers, Bags
VARIABLE {vars}
Init == {init}
Next == UNCHANGED <<{vars}>>
Inv  == {body}
====
"
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    bmc.check(0, &mut tm).expect("checks")
}

fn holds(vars: &str, init: &str, body: &str) {
    assert_eq!(
        claim(vars, init, body),
        Outcome::NoViolationWithin(0),
        "`{body}`"
    );
}

fn fails(vars: &str, init: &str, body: &str) {
    assert_eq!(
        claim(vars, init, body),
        Outcome::Violation { step: 0 },
        "`{body}`"
    );
}

// ---- construction and the empty bag ----

#[test]
fn set_to_bag_holds_one_copy_per_element() {
    holds(
        "token",
        "token = SetToBag({1, 2})",
        r"\A e \in {1, 2} : CopiesIn(e, token) = 1",
    );
    fails(
        "token",
        "token = SetToBag({1, 2})",
        r"\A e \in {1, 2} : CopiesIn(e, token) = 2",
    );
}

#[test]
fn empty_bag_has_no_members() {
    // `EmptyBag` is `[e \in {} |-> 1]` — a function over an empty domain,
    // the shape `collect_unsortable` must hand the inferred sort for (its
    // encoding used to decline with "no sort to give it").
    holds("b", "b = EmptyBag", r"\A e \in {1, 2} : ~BagIn(e, b)");
    holds("b", "b = EmptyBag", r"BagToSet(b) = {}");
}

// ---- symbolic reads through the state bag ----

#[test]
fn bag_in_reads_the_state_bag() {
    holds(
        "token",
        "token = SetToBag({1, 2})",
        r"/\ BagIn(1, token) /\ BagIn(2, token) /\ ~BagIn(3, token)",
    );
    fails("token", "token = SetToBag({1, 2})", r"BagIn(3, token)");
}

#[test]
fn copies_in_adds_across_two_state_bags() {
    holds(
        "token, out",
        r"/\ token = SetToBag({1, 2}) /\ out = EmptyBag",
        r"\A e \in {1, 2} : CopiesIn(e, token) + CopiesIn(e, out) = 1",
    );
    fails(
        "token, out",
        r"/\ token = SetToBag({1, 2}) /\ out = EmptyBag",
        r"\A e \in {1, 2, 3} : CopiesIn(e, token) + CopiesIn(e, out) = 1",
    );
}

// ---- ground bag algebra in the invariant ----

#[test]
fn ground_union_and_subbag_order_encode() {
    holds(
        "x",
        "x = 1",
        r"(SetToBag({1}) (+) SetToBag({2})) \sqsubseteq SetToBag({1, 2})",
    );
    fails(
        "x",
        "x = 1",
        r"SetToBag({1, 2}) \sqsubseteq (SetToBag({1}) (+) SetToBag({2}) (-) SetToBag({2}))",
    );
}

#[test]
fn ground_difference_keeps_the_positive_part() {
    holds(
        "x",
        "x = 1",
        r"BagIn(1, [e \in {1, 2} |-> 3] (-) [e \in {1} |-> 2])",
    );
    fails(
        "x",
        "x = 1",
        r"BagIn(2, [e \in {1, 2} |-> 3] (-) [e \in {2} |-> 3])",
    );
}

// ---- the honest decline ----

#[test]
fn state_bag_update_declines_rather_than_guessing() {
    // `token (-) SetToBag({e})` is a function definition over
    // `DOMAIN token` — a symbolic domain with no candidate list. The
    // encoding must say so, never approximate the update.
    let src = r"
---- MODULE Decline ----
EXTENDS Integers, Bags
VARIABLE token
Init == token = SetToBag({1, 2})
Next == \E e \in {1, 2} :
        token' = token (-) SetToBag({e})
Inv == TRUE
====
";
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    let err = bmc.check(1, &mut tm).expect_err("the update must decline");
    assert!(
        err.to_string().contains("enumerable"),
        "the decline names the enumerable-domain wall: {err}"
    );
}
