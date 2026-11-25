//! Frame analysis: candidate universes for set-valued state variables
//! (issue #20).
//!
//! The tests here are the analysis in isolation – the shape of the universe
//! a transition relation implies – plus the integration behaviours the issue
//! names as soundness hazards, through [`crate::bmc::Bmc`].

use nixie_core::TermManager;
use nixie_tla::Lowerer;
use nixie_tla_check::bmc::{Bmc, Outcome};
use nixie_tla_check::frames::{self, Input};

fn lower(src: &str, name: &str) -> nixie_tla::KeraRef {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("root").clone();
    let mut low = Lowerer::new();
    low.add_spec(&spec);
    low.lower_named(&module, name).expect("lowers")
}

fn module(body: &str) -> String {
    format!("---- MODULE M ----\nEXTENDS Naturals\nVARIABLE s, t\n{body}\n====\n")
}

/// The universe of `s` under a removal-only transition: exactly `Init`'s
/// elements – removal cannot introduce what was never there.
#[test]
fn removal_only_keeps_the_initial_universe() {
    let src = module(
        "Init == s = {\"a\", \"b\"}\n         Next == \\/ \\E x \\in s : s' = s \\ {x}\n               \\/ s' = s",
    );
    let init = lower(&src, "Init");
    let next = lower(&src, "Next");
    let frames = frames::analyze(&Input {
        fun_vars: Vec::new(),
        init: &init,
        next: &next,
        set_vars: vec!["s".into()],
        max_candidates: 64,
    });
    let u = frames.universe.get("s").expect("framed");
    assert_eq!(u.len(), 2, "the two initial elements: {u:?}");
}

/// `v' = v \cup {..}` under an existential over `v` itself: the universe is
/// the fixpoint of inheritance plus the added elements, which here stay
/// within the initial members plus the added literals.
#[test]
fn extension_under_self_binder_reaches_a_fixpoint() {
    let src = module(
        "Init == s = {1, 2}\n         Next == \\/ \\E x \\in s : s' = s \\cup {x}\n               \\/ s' = s",
    );
    let init = lower(&src, "Init");
    let next = lower(&src, "Next");
    let frames = frames::analyze(&Input {
        fun_vars: Vec::new(),
        init: &init,
        next: &next,
        set_vars: vec!["s".into()],
        max_candidates: 64,
    });
    let u = frames.universe.get("s").expect("framed");
    assert_eq!(u.len(), 2, "adding an existing member grows nothing: {u:?}");
}

/// Arithmetic-generated elements are ground-evaluated and deduplicated by
/// value: `t + 1` over `{1}` gives the *values* `1` and `2`, not a growing
/// family of distinct spellings of them.
#[test]
fn arithmetic_elements_collapse_to_values() {
    let src = module(
        "Init == s = {1}\n         Next == \\/ \\E x \\in s : s' = s \\cup {x + 1}\n               \\/ s' = s",
    );
    let init = lower(&src, "Init");
    let next = lower(&src, "Next");
    let frames = frames::analyze(&Input {
        fun_vars: Vec::new(),
        init: &init,
        next: &next,
        set_vars: vec!["s".into()],
        max_candidates: 64,
    });
    let u = frames.universe.get("s").expect("framed");
    // The fixpoint's rounds grow the universe by one value each until the
    // round budget stops it; what matters is that it is *values*, small, and
    // duplicate-free.
    assert!(
        u.len() <= 6 && u.len() >= 2,
        "a small duplicate-free universe: {u:?}"
    );
}

/// A set the transition rebuilds from a function set has no certain-superset
/// reading, so nothing from that assignment joins the universe: the honest
/// refusal is the *absence of invention*, and `Init`'s own elements are all
/// the universe ever claims.
#[test]
fn a_function_set_assignment_adds_nothing_to_the_universe() {
    let src = module("Init == s = {1}\n         Next == s' = [x \\in 1..3 |-> x]");
    let init = lower(&src, "Init");
    let next = lower(&src, "Next");
    let frames = frames::analyze(&Input {
        fun_vars: Vec::new(),
        init: &init,
        next: &next,
        set_vars: vec!["s".into()],
        max_candidates: 64,
    });
    let u = frames.universe.get("s").map_or(0, Vec::len);
    assert_eq!(u, 1, "only `Init`'s element; nothing from the function set");
}

// ======== the integration behaviours, through the checker ========

fn claim(spec: &str, inv: &str) -> Outcome {
    let parsed = nixie_tla_syntax::parse_file(spec).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("root");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare(&spec, module, "Init", "Next", inv, &[], &mut tm).expect("prepares");
    bmc.check(2, &mut tm).expect("checks")
}

/// The Channel shape – the corpus's headline blocker: a quantifier over a
/// set-valued variable whose transition removes a member under a binder over
/// the same set. With frames it checks, and the honest answer is no
/// violation within the bound.
#[test]
fn the_channel_shape_checks_to_a_verdict() {
    let src = r#"
---- MODULE Ch ----
EXTENDS Naturals
VARIABLE waitC
Init == waitC = {"c1", "c2"}
Next == \/ \E t \in waitC : waitC' = waitC \ {t}
        \/ waitC' = waitC
Inv == \A x \in waitC : x # "zz"
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::NoViolationWithin(2));
}

/// The issue's own regression: an invariant `\A x \in s : x > 0` with
/// `s' = s \cup {-1}` reachable **must** report the violation – a frame that
/// hid the added member would be the unsound direction.
#[test]
fn an_added_violating_member_is_still_found() {
    let src = r#"
---- MODULE Add ----
EXTENDS Naturals
VARIABLE s
Init == s = {1, 2}
Next == \/ s' = s \cup {-1}
        \/ s' = s
Inv == \A x \in s : x > 0
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::Violation { step: 1 });
}

/// A violation reachable only through *two* framed steps – remove a good
/// element, then read the invariant – still reports.
#[test]
fn a_violation_through_two_framed_steps_is_found() {
    let src = r#"
---- MODULE RM ----
EXTENDS Naturals
VARIABLE s
Init == s = {5, 7}
Next == \E x \in s : s' = s \ {x}
Inv == 5 \in s \/ 7 \in s
====
"#;
    // Removing both members takes two steps; the invariant breaks at step 2.
    assert_eq!(claim(src, "Inv"), Outcome::Violation { step: 2 });
}

/// `~\E x \in s : P` under frames is a universal claim over the universe –
/// not skolemized, and not silently satisfied.
#[test]
fn a_negated_existential_over_a_framed_set_is_checked() {
    // The existential is satisfiable (2 \in s), so its negation fails the
    // invariant at step 0.
    let src = r#"
---- MODULE NE ----
EXTENDS Naturals
VARIABLE s
Init == s = {2}
Next == s' = s
Inv == ~\E x \in s : x = 2
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::Violation { step: 0 });
}

/// Issue #20 step 4: a positive existential over an **unconstrained
/// `CONSTANT`** – no frame, no arena – skolemizes instead of declining:
/// `\E d \in Data : Send(d)` becomes `c \in Data /\ Send(c)`, the
/// membership kept as a set-theory constraint. `Channel.tla` is the corpus
/// cell this shape comes from.
#[test]
fn existential_over_symbolic_constant_encodes() {
    let src = r#"
---- MODULE Sk ----
CONSTANT Data
VARIABLE x
Init == x = "e0"
Send(d) == x' = d
Next == (\E d \in Data : Send(d)) \/ (x' = x)
Inv == x # "bad"
====
"#;
    // `Data` is unpinned, and a `CONSTANT` is universally quantified: the
    // instance `Data = {"bad"}` is legal, `\E d \in Data` may pick "bad",
    // and the invariant genuinely breaks. The negated invariant forces
    // `x' = "bad"`, so the witness reads back and the violation is reported.
    // Before the skolemization this was a decline: "a set-valued term with
    // no candidate list".
    assert_eq!(claim(src, "Inv"), Outcome::Violation { step: 1 });
}

/// The skolem's membership constraint is not decoration: `c \in Data`
/// participates, so an invariant contradicting membership *fails* through
/// the witness – the rewrite is satisfiability-exact, not a free choice.
#[test]
fn skolem_membership_constrains_the_witness() {
    let src = r#"
---- MODULE Sk2 ----
CONSTANT Data
ASSUME Data = {"e1", "e2"}
VARIABLE x
Init == x = "e0"
Next == \E d \in Data : x' = d
Inv == x \notin Data
====
"#;
    // Step 0 has x = "e0" and Inv says x \notin Data – fine (e0 is not
    // asserted to be in Data... and also not asserted out). Step 1 takes
    // the witness c with c \in Data and x' = c – the `ASSUME` pins Data to
    // two strings, so c reads back – and x' \in Data breaks the invariant.
    assert_eq!(claim(src, "Inv"), Outcome::Violation { step: 1 });
}

/// The honest refusal: with `Data` **completely** unconstrained, the
/// counterexample exists but the solver leaves the witness string
/// undecided, and the readback refuses to fabricate a value – the
/// independent replay could not verify a made-up witness. `Unknown`,
/// naming the shape, is the correct verdict.
#[test]
fn unconstrained_witness_refuses_rather_than_fabricates() {
    let src = r#"
---- MODULE Sk3 ----
CONSTANT Data
VARIABLE x
Init == x = "e0"
Next == \E d \in Data : x' = d
Inv == x \notin Data
====
"#;
    match claim(src, "Inv") {
        Outcome::Unknown(msg) => assert!(
            msg.contains("did not decide"),
            "the refusal names the undecided shape: {msg}"
        ),
        other => panic!("expected Unknown, got {other:?}"),
    }
}

/// Issue #20 step 5: a function constructor over `DOMAIN` of a state
/// function – the bag-update shape – instantiates over the domain's key
/// universe instead of declining. `token' = [n \in DOMAIN token |-> …]` was
/// "a set-valued term with no candidate list".
#[test]
fn fundef_over_domain_of_a_state_function_checks() {
    let src = r#"
---- MODULE BagUpd ----
EXTENDS Naturals
VARIABLE token
Init == token = [n \in {"e1", "e2"} |-> 2]
Next == token' = [n \in DOMAIN token |-> IF n = "e1" THEN 0 ELSE token[n]]
Inv == token["e1"] >= 0
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::NoViolationWithin(2));
}

/// The update must be *able* to break the invariant – the key universe may
/// over-approximate presence (solver-mediated) but never over-constrain the
/// transition: `token["e1"]` must reach 0.
#[test]
fn bag_update_reaches_its_violation() {
    let src = r#"
---- MODULE BagUpd2 ----
EXTENDS Naturals
VARIABLE token
Init == token = [n \in {"e1", "e2"} |-> 2]
Next == token' = [n \in DOMAIN token |-> IF n = "e1" THEN 0 ELSE token[n]]
Inv == token["e1"] > 0
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::Violation { step: 1 });
}

/// An `EXCEPT` at an **in-domain** key: the value the update writes is
/// visible to a quantifier over `DOMAIN` (instantiated over the key
/// universe), so the violation is found and replays.
#[test]
fn except_update_is_visible_to_domain_quantifiers() {
    let src = r#"
---- MODULE BagUpd3 ----
EXTENDS Naturals
VARIABLE token
Init == token = [n \in {"e1"} |-> 2]
Next == token' = [token EXCEPT !["e1"] = 0]
Inv == \A n \in DOMAIN token : token[n] > 0
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::Violation { step: 1 });
}

/// An `EXCEPT` at a **fresh** key keeps the domain – Apalache's both
/// `FunExcept` rules copy `dom(f)` unchanged and TLC errors on the shape,
/// so no checkable specification relies on the result. The invisible write
/// must not invent a domain member (which would be a spurious violation).
#[test]
fn except_at_a_fresh_key_keeps_the_domain() {
    let src = r#"
---- MODULE BagUpd4 ----
EXTENDS Naturals
VARIABLE token
Init == token = [n \in {"e1"} |-> 2]
Next == token' = [token EXCEPT !["e9"] = 0]
Inv == \A n \in DOMAIN token : token[n] > 0
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::NoViolationWithin(2));
}

// ---- issue #29: temporal properties as lassoes ----

/// Lasso checks go through the same `claim`-shaped helper, but with the
/// temporal entry point; the outcome is the ordinary one — a violating
/// lasso is a `Violation`, a bound with none is `NoViolationWithin`.
fn lasso(spec: &str, prop: &str, depth: u32) -> Outcome {
    let parsed = nixie_tla_syntax::parse_file(spec).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("root");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare_temporal(
        &spec,
        module,
        "Init",
        "Next",
        prop,
        &nixie_tla_syntax::TlcConfig::default(),
        &mut tm,
    )
    .expect("prepares");
    bmc.check(depth, &mut tm).expect("checks")
}

/// A two-state cycle: `[](x = 1)` is false on it (x is 0 every other
/// state), `[](x < 2)` is true, `<>(x = 5)` is false, `<>(x = 1)` is true.
/// The lasso closes on the cycle; the verdicts are the textbook ones.
#[test]
fn a_box_and_a_diamond_on_a_two_cycle() {
    let src = r#"
---- MODULE Cyc ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = IF x = 0 THEN 1 ELSE 0
====
"#;
    for (prop, want) in [
        // A two-state cycle's lasso is **three** steps: `InLoop` turns true
        // on the step into the repeated state, and the close needs the state
        // after it (s2 = s1 here, so the loop is s1→s2→s1).
        ("BoxFalse == [](x = 1)", Outcome::Violation { step: 3 }),
        ("BoxTrue == [](x < 2)", Outcome::NoViolationWithin(4)),
        // A diamond is refuted as soon as the loop is shown to never hit
        // its operand — at the close s2 = s1, one state before a box needs.
        ("DiaFalse == <>(x = 5)", Outcome::Violation { step: 2 }),
        ("DiaTrue == <>(x = 1)", Outcome::NoViolationWithin(4)),
    ] {
        let _ = src;
        let with_prop = format!(
            "---- MODULE Cyc ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = IF x = 0 THEN 1 ELSE 0\n{prop}\n====\n"
        );
        let name = prop.split(" ==").next().unwrap_or("");
        assert_eq!(lasso(&with_prop, name, 4), want, "{name}");
    }
}

/// The bound is honest: on a counter that reaches 3 at step 3 and stays,
/// the lasso closes at s4 = s3, so `<>(x = 5)` — never true — is refuted at
/// depth 4 and **not at depth 3** (no lasso of 3 steps or fewer exists:
/// s0..s3 are all distinct). "Nothing within k" is a bound, never a proof.
/// And `<>(x = 3)` *holds* on that lasso — the lasso is a real behaviour.
#[test]
fn the_bound_is_where_the_lasso_closes() {
    let src = r#"
---- MODULE Cnt ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = IF x >= 3 THEN x ELSE x + 1
Never == <>(x = 5)
Holds == <>(x = 3)
====
"#;
    assert_eq!(lasso(src, "Never", 3), Outcome::NoViolationWithin(3));
    assert_eq!(lasso(src, "Never", 4), Outcome::Violation { step: 4 });
    assert_eq!(lasso(src, "Holds", 6), Outcome::NoViolationWithin(6));
}

/// Apalache's `ManyBoxes`/`ManyDiamonds` shapes: redundant `[]`/`<>`
/// nestings over a two-cycle. `[][][][]<>(x = 1)` holds (x is 1 every
/// other state); `<><><><>(x = 2)` does not.
#[test]
fn nested_boxes_and_diamonds() {
    let src = r#"
---- MODULE Nest ----
EXTENDS Naturals
VARIABLES x, y
Init == /\ x = 0 /\ y = 1
Next == /\ x' = y /\ y' = x
Boxes == [][][][][]<>(x = 1)
BoxesBad == [][][][][][](x = 1)
DiamondsBad == <><><><><>(x = 2)
====
"#;
    assert_eq!(lasso(src, "Boxes", 6), Outcome::NoViolationWithin(6));
    assert_eq!(lasso(src, "BoxesBad", 6), Outcome::Violation { step: 3 });
    assert_eq!(lasso(src, "DiamondsBad", 6), Outcome::Violation { step: 2 });
}

/// `<>[]P` and `[]<>P` over a counter that settles: `<>[](x = 3)` holds
/// (it settles at 3), `<>[](x < 3)` does not, `[]<>(x = 0)` does not.
#[test]
fn diamond_box_and_box_diamond() {
    let src = r#"
---- MODULE Settle ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = IF x >= 3 THEN x ELSE x + 1
Good == <>[](x = 3)
Bad == <>[](x < 3)
Bad2 == []<>(x = 0)
====
"#;
    assert_eq!(lasso(src, "Good", 6), Outcome::NoViolationWithin(6));
    // Both are refuted at the first close s4 = s3 (a diamond is refuted as
    // soon as the loop is shown never to satisfy its operand).
    assert_eq!(lasso(src, "Bad", 6), Outcome::Violation { step: 4 });
    assert_eq!(lasso(src, "Bad2", 6), Outcome::Violation { step: 4 });
}

/// A construct the tableau has no rule for is **declined by name**, never
/// dropped: fairness, temporal quantifiers, a primed leaf, `-+->`.
#[test]
fn unsupported_temporal_constructs_decline_by_name() {
    let base = r#"
---- MODULE Dec ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
{prop}
====
"#;
    for (prop, needle) in [
        ("P == []<>(x' # x)", "prime"),
        ("P == WF_x(x' # x)", "fairness"),
        ("P == \\EE y : [](x = y)", "temporal quantifier"),
    ] {
        let src = base.replace("{prop}", prop);
        let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
        let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
        let module = spec.root_module().expect("root");
        let mut tm = TermManager::new();
        let err = Bmc::prepare_temporal(
            &spec,
            module,
            "Init",
            "Next",
            "P",
            &nixie_tla_syntax::TlcConfig::default(),
            &mut tm,
        )
        .err()
        .unwrap_or_else(|| panic!("`{prop}` must be declined"));
        let msg = err.to_string();
        assert!(msg.contains(needle), "`{prop}` names `{needle}`: {msg}");
    }
}
