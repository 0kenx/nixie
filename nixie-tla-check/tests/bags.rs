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

// ---- issue #18: the EmptyBag binder and BagOfAll ----

/// The regression the issue names: two `EmptyBag`s at different element types
/// in one definition. `EmptyBag` used to lower with one fixed binder
/// `bag_e#0`, so inference keyed both element variables as the same name and
/// demanded `Str` and `Int` be one type.
#[test]
fn two_empty_bags_at_different_element_types() {
    // Each `EmptyBag`'s element type is fixed by the bag it is added to: one
    // is Int-keyed, the other Str-keyed. With the shared `bag_e#0` binder
    // both were one variable and this did not type check ("Str and Int").
    holds(
        "x",
        "x = 0",
        "EmptyBag (+) SetToBag({1}) = SetToBag({1})\n      /\\ EmptyBag (+) SetToBag({\"a\"}) = SetToBag({\"a\"})",
    );
}

/// `BagOfAll(F, B)` through Apalache's rewire: a fold adding
/// `[y \in {F(e)} |-> B[e]]` per element. Checked end to end, which pins the
/// lowering, the fold encoding and the order-independence audit together.
#[test]
fn bag_of_all_folds_the_image() {
    holds(
        "x",
        "x = 0",
        "LET F(e) == e + 1 IN BagOfAll(F, SetToBag({1, 2})) = SetToBag({2, 3})",
    );
    // A non-injective F merges copies: {1, 2} under `e |-> 1` is the bag
    // with two copies of 1.
    holds(
        "x",
        "x = 0",
        "LET G(e) == 1 IN BagOfAll(G, SetToBag({1, 2})) = [y \\in {1} |-> 2]",
    );
    // And an empty bag maps to an empty bag.
    holds("x", "x = 0", "BagOfAll(LAMBDA e: e, EmptyBag) = EmptyBag");
}

/// `IsABag` and `BagCardinality`, the two vocabulary items `TestBags.tla`
/// needs beyond the desugaring that already existed.
#[test]
fn is_bag_and_bag_cardinality_desugar() {
    holds("x", "x = 0", "IsABag(SetToBag({1, 2}))");
    fails("x", "x = 0", "IsABag([e \\in {1} |-> 0])");
    holds(
        "x",
        "x = 0",
        "BagCardinality(SetToBag({1, 2, 3})) = 3 /\\ BagCardinality(EmptyBag) = 0",
    );
}

/// `BagUnion(S)` folds bag addition over a set of bags — order-independent
/// because bag addition is pointwise `+`, which the `ApaFoldSet` audit now
/// recognizes structurally.
/// `BagUnion` lowers (Apalache's own fold) and the fold's body passes the
/// order-independence audit, but the **encode** still declines it end to
/// end: the base `EmptyBag` starts at an unconstrained element type while
/// the stepped accumulator's domain is at `Int`, and the function-valued
/// `ite_values` merge refuses the mixed shapes rather than guessing. That
/// gap is recorded here so the day it closes, this test gets its body back:
///
/// ```text
/// BagUnion({SetToBag({1, 2}), SetToBag({2, 3})}) = [e \in {1, 2, 3} |-> 1]
/// ```
#[test]
#[ignore = "encode: mixed element sorts between EmptyBag's base and the stepped accumulator"]
fn bag_union_folds_pointwise_addition() {
    let src = r#"
---- MODULE Claim ----
EXTENDS Integers, Bags
VARIABLE x
Init == x = 0
Next == UNCHANGED <<x>>
Inv  == BagUnion({SetToBag({1, 2}), SetToBag({2, 3})}) = [e \in {1, 2, 3} |-> 1]
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    let out = bmc.check(0, &mut tm).expect("checks");
    assert_eq!(out, Outcome::NoViolationWithin(0));
}

/// The binder-uniqueness invariant itself, as a unit: a tree with a repeated
/// binder is refused, and the trees these tests build are not.
#[test]
fn binder_uniqueness_holds_and_catches() {
    use nixie_tla::kera::{Kera, Name};
    use nixie_tla::lower::binder_uniqueness;
    // A shared binder: two quantifiers over the same name.
    let shared = Kera::And(vec![
        Kera::Forall {
            var: Name("x".into()),
            set: Kera::SetEnum(vec![]).rc(),
            body: Kera::Bool(true).rc(),
        }
        .rc(),
        Kera::Exists {
            var: Name("x".into()),
            set: Kera::SetEnum(vec![]).rc(),
            body: Kera::Bool(true).rc(),
        }
        .rc(),
    ])
    .rc();
    assert!(binder_uniqueness(&shared).is_err());
    // Distinct binders are fine, and sharing a *subterm* is not a repeat.
    let ok = Kera::And(vec![
        Kera::Forall {
            var: Name("x#1".into()),
            set: Kera::SetEnum(vec![]).rc(),
            body: Kera::Bool(true).rc(),
        }
        .rc(),
        Kera::Exists {
            var: Name("x#2".into()),
            set: Kera::SetEnum(vec![]).rc(),
            body: Kera::Bool(true).rc(),
        }
        .rc(),
    ])
    .rc();
    assert!(binder_uniqueness(&ok).is_ok());
}
