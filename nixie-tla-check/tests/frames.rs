//! Frame analysis: candidate universes for set-valued state variables
//! (issue #20).
//!
//! The tests here are the analysis in isolation — the shape of the universe
//! a transition relation implies — plus the integration behaviours the issue
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
/// elements — removal cannot introduce what was never there.
#[test]
fn removal_only_keeps_the_initial_universe() {
    let src = module(
        "Init == s = {\"a\", \"b\"}\n         Next == \\/ \\E x \\in s : s' = s \\ {x}\n               \\/ s' = s",
    );
    let init = lower(&src, "Init");
    let next = lower(&src, "Next");
    let frames = frames::analyze(&Input {
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
        init: &init,
        next: &next,
        set_vars: vec!["s".into()],
        max_candidates: 64,
    });
    let u = frames.universe.get("s").map_or(0, Vec::len);
    assert_eq!(u, 1, "only `Init`'s element; nothing from the function set");
}

// ---- the integration behaviours, through the checker ----

fn claim(spec: &str, inv: &str) -> Outcome {
    let parsed = nixie_tla_syntax::parse_file(spec).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("root");
    let mut tm = TermManager::new();
    let mut bmc = Bmc::prepare(&spec, module, "Init", "Next", inv, &[], &mut tm).expect("prepares");
    bmc.check(2, &mut tm).expect("checks")
}

/// The Channel shape — the corpus's headline blocker: a quantifier over a
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
/// `s' = s \cup {-1}` reachable **must** report the violation — a frame that
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

/// A violation reachable only through *two* framed steps — remove a good
/// element, then read the invariant — still reports.
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

/// `~\E x \in s : P` under frames is a universal claim over the universe —
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
