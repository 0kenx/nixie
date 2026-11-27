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

/// An assignment the walk cannot read – here a set rebuilt from a function
/// constructor, read as a set – leaves the variable **unframed**, even
/// though `Init` gave it an element. The first version of this test pinned
/// the opposite ("`Init`'s own elements are all the universe ever claims"),
/// which is exactly the frame `--paranoid` falsified on `Rand.tla`: the
/// members the unreadable site adds are unknown, so no smaller universe is
/// a superset of them.
#[test]
fn an_unreadable_assignment_leaves_the_variable_unframed() {
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
    assert!(
        !frames.universe.contains_key("s"),
        "unframed: {:?}",
        frames.universe
    );
}

/// A set-valued conditional is read as both of its branches: an
/// over-approximation in the sound direction, not a refusal.
#[test]
fn a_conditional_assignment_reads_both_branches() {
    let src =
        module("Init == s = {1}\n         Next == s' = IF x \\in s THEN s \\cup {2} ELSE {3}");
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
    assert_eq!(u.len(), 3, "{{1, 2, 3}}: {u:?}");
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

/// With `Data` **completely** unconstrained, a `CONSTANT` is universally
/// quantified: the instance `Data = {"e0"}` is legal and `x \notin Data`
/// fails in the initial state. That step-0 violation needs no witness, and
/// it is reported and replayed.
///
/// This test used to expect `Unknown` here – "the solver leaves the witness
/// string undecided" – and it was passing for the wrong reason: the witness
/// was **one rigid constant** for the whole unrolling, so the readback of
/// state 0 asked for a variable the depth-0 query had never constrained
/// (it belongs to `Next@0`). With one witness per step, state 0 of a step-0
/// counterexample has none to read, and the real violation comes through.
#[test]
fn an_unpinned_constant_makes_the_step_zero_violation() {
    let src = r#"
---- MODULE Sk3 ----
CONSTANT Data
VARIABLE x
Init == x = "e0"
Next == \E d \in Data : x' = d
Inv == x \notin Data
====
"#;
    assert_eq!(claim(src, "Inv"), Outcome::Violation { step: 0 });
}

/// The same with the initial state safe: the step-1 violation goes through
/// the witness, which the query constrains (`d \in Data /\ x' = d`) and
/// the readback decides – once per step, from the state the quantifier is
/// evaluated in.
#[test]
fn a_witness_the_query_constrains_reads_back() {
    let src = r#"
---- MODULE Sk4 ----
CONSTANT Data
VARIABLE x
Init == x = "e0"
Next == \E d \in Data : x' = d
Inv == x = "e0" \/ x \notin Data
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("root");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    assert_eq!(
        bmc.check(2, &mut tm).expect("checks"),
        Outcome::Violation { step: 1 }
    );
    assert_eq!(
        bmc.verification(),
        Some(&nixie_tla_check::bmc::Verification::Replayed)
    );
}

/// The other side of that coin: the witness of an existential over an
/// **unframed** set is a concrete (symbolic) member where another variable
/// receives it. `Init == sent = {}` is readable, `sent' = sent \cup {c}`
/// under `\E d \in Data : Send(d)` grows `sent` by exactly the witness,
/// and `sent` is framed with it – the Channel shape, which must keep
/// checking: without the witness among the candidates, `\A m \in sent : …`
/// would skip the message just added.
#[test]
fn a_witness_received_by_a_framed_variable_is_its_candidate() {
    let src = r#"
---- MODULE Chan ----
CONSTANT Data
VARIABLE sent
Init == sent = {}
Send(d) == sent' = sent \cup {d}
Next == \E d \in Data : Send(d)
====
"#;
    let init = lower(src, "Init");
    let next = lower(src, "Next");
    let syms = nixie_tla::lower::Syms::from_names(["Data".to_string()]);
    let next = nixie_tla::lower::skolemize_with_syms_at(&next, true, &syms);
    let frames = frames::analyze(&Input {
        fun_vars: Vec::new(),
        init: &init,
        next: &next,
        set_vars: vec!["sent".into()],
        max_candidates: 64,
    });
    let u = frames.universe.get("sent").expect("`sent` is framed");
    assert_eq!(u.len(), 1, "the witness: {u:?}");
    assert!(
        u.iter().any(|e| {
            let text = format!("{e:?}");
            text.contains(nixie_tla::lower::SKOLEM_MARK)
        }),
        "{u:?}"
    );
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
/// temporal entry point; the outcome is the ordinary one – a violating
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
        // A two-state cycle's shortest lasso is **two** steps, `s0 → s1 →
        // s0`, the loop starting in the first state (`__InLoop` turns true
        // on the step into it). It was found at three, rotated to start in
        // `s1`, while the tableau also fixed `unroll` at `Init`: for a loop
        // starting in the first state that contradicts the step-0 equation
        // whenever a `[]` argument is false there (see `temporal.rs`).
        ("BoxFalse == [](x = 1)", Outcome::Violation { step: 2 }),
        ("BoxTrue == [](x < 2)", Outcome::NoViolationWithin(4)),
        // A diamond is refuted as soon as the loop is shown to never hit
        // its operand – at the close s2 = s1, one state before a box needs.
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
/// the lasso closes at s4 = s3, so `<>(x = 5)` – never true – is refuted at
/// depth 4 and **not at depth 3** (no lasso of 3 steps or fewer exists:
/// s0..s3 are all distinct). "Nothing within k" is a bound, never a proof.
/// And `<>(x = 3)` *holds* on that lasso – the lasso is a real behaviour.
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
    // The cycle `(0,1) → (1,0) → (0,1)`, two steps, the loop starting in
    // the first state – where `x = 1` is false.
    assert_eq!(lasso(src, "BoxesBad", 6), Outcome::Violation { step: 2 });
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

/// Issue #44, end to end: the lasso encoding's depth-8 query on a bounded
/// counter was answered a wrong `unsat` by the in-process solver – an
/// inprocessing round ran inside the `push` scope and its retirements
/// rested on scope-owned clauses. With the round confined to the base
/// scope (and inprocessing **on**, the shipped default), the lasso is
/// found at depth 8 and replayed.
#[test]
fn a_lasso_is_found_with_inprocessing_on() {
    let src = r#"
---- MODULE MBC ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = IF x >= 7 THEN x ELSE x + 1
W == <>(x = 999)
====
"#;
    assert_eq!(lasso(src, "W", 8), Outcome::Violation { step: 8 });
    // And nothing within 7: s0..s7 are distinct, so no shorter lasso exists.
    assert_eq!(lasso(src, "W", 7), Outcome::NoViolationWithin(7));
}

/// `s \in SUBSET (1..3)` is readable – `s`'s members are among `1..3` – and
/// the skolemized `Next`, `s' = (s \ {c}) \cup {c + c}`, grows that
/// universe by the witness's sum: a term over the per-step witness `c` that
/// denotes exactly the member the step adds. Read as "unreadable" this
/// assignment poisoned `s` (and took a `MCConsensus.tla` deadlock verdict
/// with it); read as *nothing*, it left `s` at the empty universe, which
/// the witness then grew to one term – the frame `--paranoid` falsified on
/// `Rand.tla`. Both universes were wrong.
#[test]
fn a_subset_membership_is_read_as_its_base_and_the_witness_is_a_candidate() {
    let src = module(
        "Init == s \\in SUBSET (1..3)\n         Next == \\E x \\in s : s' = (s \\ {x}) \\cup {x + x}",
    );
    let init = lower(&src, "Init");
    let next = lower(&src, "Next");
    let next = nixie_tla::lower::skolemize_infinite_existentials_at(&next, true);
    let next = nixie_tla::lower::skolemize_with_syms_at(
        &next,
        true,
        &nixie_tla::lower::Syms::from_names(["s".to_string()]),
    );
    let frames = frames::analyze(&Input {
        fun_vars: Vec::new(),
        init: &init,
        next: &next,
        set_vars: vec!["s".into()],
        max_candidates: 64,
    });
    let u = frames.universe.get("s").expect("`s` is framed");
    let ints: Vec<&str> = u
        .iter()
        .filter_map(|e| match e.as_ref() {
            nixie_tla::Kera::Int(i) => Some(i.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(ints, ["1", "2", "3"], "{u:?}");
    assert!(
        u.iter()
            .any(|e| { format!("{e:?}").contains(nixie_tla::lower::SKOLEM_MARK) }),
        "the witness's sum: {u:?}"
    );
    assert_eq!(u.len(), 4, "{u:?}");
}

/// An assignment with no certain-superset reading – `s \in P` for an
/// unpinned `CONSTANT` set – poisons the variable: nothing the transitions
/// grow can be a superset of members nobody can name, and `s` stays
/// unframed whatever the skolemized `Next` adds to it.
#[test]
fn an_unreadable_membership_leaves_the_variable_unframed() {
    let src = r#"
---- MODULE P ----
CONSTANT P
VARIABLE s, t
Init == s \in P
Next == \E x \in s : s' = (s \ {x}) \cup {x + x}
Inv == \A y \in s : y > 0
====
"#;
    let init = lower(src, "Init");
    let next = lower(src, "Next");
    let syms = nixie_tla::lower::Syms::from_names(["P".to_string(), "s".to_string()]);
    let next = nixie_tla::lower::skolemize_with_syms_at(&next, true, &syms);
    let frames = frames::analyze(&Input {
        fun_vars: Vec::new(),
        init: &init,
        next: &next,
        set_vars: vec!["s".into()],
        max_candidates: 64,
    });
    assert!(!frames.universe.contains_key("s"), "{:?}", frames.universe);
}
