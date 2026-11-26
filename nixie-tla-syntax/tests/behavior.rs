//! Reading a `SPECIFICATION` formula for its safety fragment (issue #46).
//!
//! `SPECIFICATION Spec` is how most TLC configurations name the system, and
//! until this decomposition existed every one of them was refused. These pin
//! what is accepted – the canonical `Init /\ [][Next]_vars`, in either order,
//! through nested conjunctions and temporal-level abbreviations – and, as
//! important, that every clause the bounded checker cannot preserve is
//! **named** in the refusal: a dropped fairness conjunct invents liveness
//! counterexamples, and a dropped `[]P` checks a weaker property.

use nixie_tla_syntax::{
    BehaviorFormError, Level, Loader, SafetyForm, UnsupportedClause, check_spec, parse_file,
    safety_form, visible_definition,
};
use std::path::PathBuf;

/// A single parsed module, as a spec with nothing followed.
fn single(src: &str) -> nixie_tla_syntax::LoadedSpec {
    nixie_tla_syntax::LoadedSpec::single(parse_file(src).expect("parses"))
}

/// Decompose `name` in a one-module spec, with its levels checked as a spec.
fn form<'s>(
    spec: &'s nixie_tla_syntax::LoadedSpec,
    name: &str,
) -> Result<SafetyForm<'s>, BehaviorFormError> {
    let module = spec.root_module().expect("a root module");
    safety_form(spec, module, &check_spec(spec), name)
}

/// The two names a decomposition yields.
fn named<'a, 'm>(form: &'a SafetyForm<'m>) -> (&'a str, &'a str) {
    (form.init.as_str(), form.next.as_str())
}

const CONFIG: &str = r"
------------------------------ MODULE Config -------------------------------------------
EXTENDS Integers
VARIABLE x
Init  == x = 0
Init2 == x = 2
Next  == UNCHANGED x
Next2 == x' = x + 2
Spec  == Init /\ [][Next]_x
Spec2 == Init2 /\ [][Next2]_x
Spec3 == [][Next2]_x /\ Init2
Spec4 == (Init2 /\ [][Next2]_x) /\ WF_x(Next2)
Spec5 == Init2 /\ ([][Next2]_x /\ SF_x(Next2))
Spec6 == /\ Init2
         /\ [][Next2]_x
Spec7 == /\ [][Next2]_x
         /\ Init2
SpecA == Init2
SpecB == [][Next2]_x
SpecC == Init2 /\ [](x > 0)
SpecD == Init2 /\ [][x' = x + 1]_x
SpecE == Init2 /\ [][Next2]_x /\ [][Next]_x
SpecF == Init2 /\ Init /\ [][Next2]_x
SpecG == Init2 /\ [][Next2]_x /\ (x' # x)
SpecH == Init2 /\ Safety
SpecI == Init2 /\ Progress
Safety == [][Next2]_x
Progress == WF_x(Next2)
SpecJ == Init2 /\ <>(x > 0)
SpecK == Init2 /\ ((x > 0) ~> (x > 1))
SpecL == Init2 /\ [][Next2]_<<x>>
SpecM == Init2 /\ [][Next2]_x /\ \EE y \in Int : [](x = y)
SpecN(n) == Init2 /\ [][Next2]_x
====
";

// ======== the canonical form ========

#[test]
fn the_canonical_form_yields_init_and_next_by_name() {
    let spec = single(CONFIG);
    assert_eq!(
        named(&form(&spec, "Spec").expect("decomposes")),
        ("Init", "Next")
    );
    // The names need not be `Init`/`Next`: they are whatever the formula says.
    assert_eq!(
        named(&form(&spec, "Spec2").expect("decomposes")),
        ("Init2", "Next2")
    );
}

/// The subscript is not consulted: `vars == <<a, b>>` or the tuple written
/// inline are the same `[Next]_vars`, and a stuttering step adds no state
/// whatever the subscript lists (see the module docs).
#[test]
fn the_subscript_may_be_a_tuple_written_inline() {
    let spec = single(CONFIG);
    assert_eq!(
        named(&form(&spec, "SpecL").expect("decomposes")),
        ("Init2", "Next2")
    );
}

/// Apalache accepts the two conjuncts in either order, and so does this.
#[test]
fn the_order_of_the_two_conjuncts_does_not_matter() {
    let spec = single(CONFIG);
    assert_eq!(
        named(&form(&spec, "Spec3").expect("decomposes")),
        ("Init2", "Next2")
    );
}

/// Apalache's own integration cells are exactly these shapes: `flattenAnds`
/// before matching. Parentheses and bulleted lists are flattened here too.
#[test]
fn nested_conjunctions_are_flattened() {
    let spec = single(CONFIG);
    for name in ["Spec6", "Spec7"] {
        assert_eq!(
            named(&form(&spec, name).unwrap_or_else(|e| panic!("{name}: {e}"))),
            ("Init2", "Next2"),
            "{name}"
        );
    }
}

/// `Spec == Init /\ Safety`, with `Safety == [][Next]_vars`: a state-level
/// name is an initial predicate, a temporal-level one is descended into, as
/// TLC's `processConfigSpec` does. `Progress == WF_x(Next2)` behind the same
/// shape is found too – the abbreviation cannot hide a fairness clause.
#[test]
fn a_temporal_level_abbreviation_is_descended_into() {
    let spec = single(CONFIG);
    assert_eq!(
        named(&form(&spec, "SpecH").expect("decomposes")),
        ("Init2", "Next2")
    );
    let src = CONFIG.replace(
        "SpecH == Init2 /\\ Safety",
        "SpecH == Init2 /\\ Safety\nSpecH2 == Init2 /\\ Safety /\\ Progress\nSpecH3 == Init2 /\\ Progress",
    );
    let spec = single(&src);
    let f = form(&spec, "SpecH2").expect("decomposes");
    assert_eq!(named(&f), ("Init2", "Next2"));
    // The abbreviation cannot hide it: the clause is reported as if written.
    assert_eq!(f.fairness.len(), 1);
    assert!(f.fairness[0].weak && !f.fairness[0].quantified);
    assert_eq!(f.fairness[0].rendered, "WF_x(Next2)");
    // Fairness on its own is no transition to unroll.
    assert!(matches!(
        form(&spec, "SpecH3"),
        Err(BehaviorFormError::NoSafetyPair {
            missing: "`[][Next]_vars` conjunct",
            ..
        })
    ));
}

// ======== fairness: reported, not assumed ========

/// Fairness: weak and strong, each rendered and located, and the two roles
/// still returned. A bounded invariant check gives the same answers with the
/// clause set aside – it removes no state from any finite prefix – so the
/// decomposition reports it and leaves the decision to the caller.
#[test]
fn fairness_is_reported_with_the_roles() {
    let spec = single(CONFIG);
    for (name, weak, rendered) in [
        ("Spec4", true, "WF_x(Next2)"),
        ("Spec5", false, "SF_x(Next2)"),
    ] {
        let form = form(&spec, name).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(named(&form), ("Init2", "Next2"), "{name}");
        assert_eq!(form.fairness.len(), 1, "{name}");
        let c = &form.fairness[0];
        assert_eq!(
            (c.weak, c.quantified, c.rendered.as_str()),
            (weak, false, rendered),
            "{name}"
        );
        // The clause is where the definition wrote it.
        assert!(
            c.span.start.line > 10 && c.span.end.line < 40,
            "{name}: {}",
            c.span
        );
    }
}

/// The per-process idiom: `\A self \in Node : WF_vars(node(self))`, alone
/// or as a bulleted list behind a definition. TLC treats each exactly as a
/// fairness conjunct, and so does this.
#[test]
fn quantified_fairness_is_reported_too() {
    let src = r"
---- MODULE Q ----
VARIABLE x
Node == {1, 2}
Init == x = 0
A(self) == x' = x
Next == \E p \in Node : A(p)
Fairness ==
  /\ \A p \in Node : WF_vars(A(p))
  /\ \A p \in Node : SF_vars(A(p))
Spec1 == Init /\ [][Next]_x /\ \A p \in Node : WF_x(A(p))
Spec2 == /\ Init
         /\ [][Next]_x
         /\ Fairness
Spec3 == Init /\ [][Next]_x /\ \A p \in Node : x' = x
====
";
    let spec = single(src);
    let f = form(&spec, "Spec1").expect("decomposes");
    assert_eq!(named(&f), ("Init", "Next"));
    let f = form(&spec, "Spec2").expect("decomposes");
    assert_eq!(named(&f), ("Init", "Next"));
    assert_eq!(
        f.fairness.len(),
        2,
        "through the abbreviation, in source order"
    );
    assert!((f.fairness[0].weak, f.fairness[0].quantified) == (true, true));
    assert!((f.fairness[1].weak, f.fairness[1].quantified) == (false, true));
    assert_eq!(f.fairness[0].rendered, r"\A … : WF_vars(A(p))");
    // A universal quantifier that is not fairness is a temporal clause of
    // another kind: refused by name.
    match form(&spec, "Spec3") {
        Err(BehaviorFormError::Unsupported(UnsupportedClause::Other { rendered, .. })) => {
            assert_eq!(rendered, r"\A … : x' = x");
        }
        other => panic!("{other:?}"),
    }
}

#[test]
fn a_temporal_safety_clause_is_reported() {
    let spec = single(CONFIG);
    match form(&spec, "SpecC") {
        Err(BehaviorFormError::Unsupported(UnsupportedClause::Other { rendered, .. })) => {
            assert_eq!(rendered, "[](x > 0)");
        }
        other => panic!("{other:?}"),
    }
    // Eventuality, leads-to and a temporal quantifier: each changes the set
    // of behaviours, each is named.
    for (name, rendered) in [
        ("SpecJ", "<>(x > 0)"),
        ("SpecK", "(x > 0) ~> (x > 1)"),
        ("SpecM", r"\EE … : [](x = y)"),
    ] {
        match form(&spec, name) {
            Err(BehaviorFormError::Unsupported(UnsupportedClause::Other {
                rendered: r, ..
            })) => assert_eq!(r, rendered, "{name}"),
            other => panic!("{name}: {other:?}"),
        }
    }
}

/// An action-level conjunct is not a transition relation and not an initial
/// predicate; TLC refuses it as well (`TLC_CANT_HANDLE_CONJUNCT`).
#[test]
fn an_action_level_conjunct_is_reported() {
    let spec = single(CONFIG);
    match form(&spec, "SpecG") {
        Err(BehaviorFormError::Unsupported(UnsupportedClause::Other { rendered, .. })) => {
            assert_eq!(rendered, "x' /= x");
        }
        other => panic!("{other:?}"),
    }
}

/// The action inside the brackets must be a definition name for there to be
/// a role to hand the checker; an inline action says so with its text.
#[test]
fn an_inline_next_state_action_is_reported() {
    let spec = single(CONFIG);
    match form(&spec, "SpecD") {
        Err(BehaviorFormError::Unsupported(UnsupportedClause::NextNotNamed {
            rendered, ..
        })) => assert_eq!(rendered, r"[][x' = x + 1]_x"),
        other => panic!("{other:?}"),
    }
}

/// Two next-state relations do not say which one the other's states come
/// from; TLC refuses the second. Two initial predicates are refused the same
/// way, naming the one already taken.
#[test]
fn duplicated_roles_are_reported() {
    let spec = single(CONFIG);
    assert!(matches!(
        form(&spec, "SpecE"),
        Err(BehaviorFormError::Unsupported(UnsupportedClause::TwoNextState {
            first,
            ..
        })) if first == "Next2"
    ));
    assert!(matches!(
        form(&spec, "SpecF"),
        Err(BehaviorFormError::Unsupported(UnsupportedClause::TwoInit {
            first,
            ..
        })) if first == "Init2"
    ));
}

/// A formula with no transition, or no initial predicate, is not a safety
/// specification a bounded check can unroll.
#[test]
fn a_formula_without_the_pair_is_reported() {
    let spec = single(CONFIG);
    assert!(matches!(
        form(&spec, "SpecA"),
        Err(BehaviorFormError::NoSafetyPair {
            missing: "`[][Next]_vars` conjunct",
            ..
        })
    ));
    assert!(matches!(
        form(&spec, "SpecB"),
        Err(BehaviorFormError::NoSafetyPair {
            missing: "state-level conjunct to unroll from",
            ..
        })
    ));
    let msg = form(&spec, "SpecA").expect_err("refused").to_string();
    assert!(
        msg.contains("the supported form is `Init /\\ [][Next]_vars`"),
        "{msg}"
    );
}

#[test]
fn a_missing_or_parametrized_definition_is_reported() {
    let spec = single(CONFIG);
    assert_eq!(
        form(&spec, "Nope"),
        Err(BehaviorFormError::NoSuchDefinition("Nope".into()))
    );
    assert_eq!(
        form(&spec, "SpecN"),
        Err(BehaviorFormError::HasParameters {
            name: "SpecN".into(),
            arity: 1
        })
    );
    assert!(
        form(&spec, "x").is_err(),
        "a VARIABLE is not a behaviour spec"
    );
}

// ======== where the formula may live ========

/// A scratch directory holding a set of modules, removed on drop.
struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str, files: &[(&str, &str)]) -> Self {
        let dir = std::env::temp_dir().join(format!(
            "nixie-tla-behavior-{tag}-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("scratch dir");
        for (name, body) in files {
            std::fs::write(dir.join(name), body).expect("write module");
        }
        Self(dir)
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

const BASE: &str = "---- MODULE Base ----\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\n\
                    ActionInv == x' >= x\nSpec == Init /\\ [][Next]_x\n====\n";

/// The Toolbox's model-file shape: `MC.tla` EXTENDS the specification and
/// `MC.cfg` says `SPECIFICATION Spec`. The formula, the initial predicate and
/// the action all live in the extended module, and all three resolve.
#[test]
fn a_specification_defined_in_an_extended_module_resolves() {
    let s = Scratch::new(
        "extends",
        &[
            ("Base.tla", BASE),
            (
                "MC.tla",
                "---- MODULE MC ----\nEXTENDS Base, TLC\nCONSTANT N\nASSUME N \\in Nat\n====\n",
            ),
        ],
    );
    let spec = Loader::new().load(&s.path("MC.tla")).expect("loads");
    let root = spec.root_module().expect("root");
    let form = safety_form(&spec, root, &check_spec(&spec), "Spec").expect("decomposes");
    assert_eq!(named(&form), ("Init", "Next"));
    assert_eq!(form.home.name.name, "Base");
    // And the roles the decomposition names are themselves visible.
    let init = visible_definition(&spec, root, "Init").expect("Init is visible");
    assert_eq!(init.module.name.name, "Base");
    assert!(init.params.is_empty());
    assert_eq!(
        visible_definition(&spec, root, "N"),
        None,
        "a CONSTANT is not a definition"
    );
}

/// The Toolbox's generated model files: `spec_146427254083041000 == Spec`, a
/// bare abbreviation in the model of a temporal formula defined in the
/// extended module – with fairness behind it. The abbreviation is seen
/// through, and the fairness reported: a level read in the model module's
/// own report would not know `Spec` at all.
#[test]
fn an_abbreviation_of_an_extended_temporal_definition_is_seen_through() {
    let s = Scratch::new(
        "abbrev",
        &[
            (
                "Base.tla",
                "---- MODULE Base ----\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\n\
                 Spec == Init /\\ [][Next]_x /\\ WF_x(Next)\n====\n",
            ),
            (
                "MC.tla",
                "---- MODULE MC ----\nEXTENDS Base\nspec_146427254083041000 ==\nSpec\n====\n",
            ),
        ],
    );
    let spec = Loader::new().load(&s.path("MC.tla")).expect("loads");
    let root = spec.root_module().expect("root");
    let f = safety_form(&spec, root, &check_spec(&spec), "spec_146427254083041000")
        .expect("decomposes");
    assert_eq!(named(&f), ("Init", "Next"));
    assert_eq!(f.home.name.name, "Base");
    assert_eq!(f.fairness.len(), 1);
    assert_eq!(f.fairness[0].rendered, "WF_x(Next)");
}

/// `MC.tla` instantiating the specification without naming it, which makes
/// its members visible unprefixed – `tlaplus-examples`' own model files.
#[test]
fn a_specification_visible_through_an_open_instance_resolves() {
    let s = Scratch::new(
        "instance",
        &[
            ("Base.tla", BASE),
            (
                "MC.tla",
                "---- MODULE MC ----\nVARIABLE x\nINSTANCE Base WITH x <- x\n====\n",
            ),
        ],
    );
    let spec = Loader::new().load(&s.path("MC.tla")).expect("loads");
    let root = spec.root_module().expect("root");
    let form = safety_form(&spec, root, &check_spec(&spec), "Spec").expect("decomposes");
    assert_eq!(named(&form), ("Init", "Next"));
    assert_eq!(form.home.name.name, "Base");
    // The root's own definition of the same name wins, as it does in TLA+.
    let s = Scratch::new(
        "shadow",
        &[
            ("Base.tla", BASE),
            (
                "MC.tla",
                "---- MODULE MC ----\nEXTENDS Base\nInit == x = 1\n====\n",
            ),
        ],
    );
    let spec = Loader::new().load(&s.path("MC.tla")).expect("loads");
    let root = spec.root_module().expect("root");
    let init = visible_definition(&spec, root, "Init").expect("visible");
    assert_eq!(init.module.name.name, "MC");
    assert_eq!(
        visible_definition(&spec, root, "Next").map(|d| d.module.name.name.as_str()),
        Some("Base")
    );
}

/// A named instance's member is written `I!Spec`, and the roles behind it
/// would have to resolve through the instance's substitution. Declined by
/// name rather than half-resolved.
#[test]
fn a_named_instance_member_is_declined_by_name() {
    let s = Scratch::new(
        "named-instance",
        &[
            ("Base.tla", BASE),
            (
                "M.tla",
                "---- MODULE M ----\nVARIABLE x\nI == INSTANCE Base WITH x <- x\n\
                 Spec == I!Spec\n====\n",
            ),
        ],
    );
    let spec = Loader::new().load(&s.path("M.tla")).expect("loads");
    let root = spec.root_module().expect("root");
    match safety_form(&spec, root, &check_spec(&spec), "Spec") {
        Err(BehaviorFormError::Unsupported(UnsupportedClause::Other { rendered, .. })) => {
            assert_eq!(rendered, "I!Spec");
        }
        other => panic!("{other:?}"),
    }
}

/// `extends_closure` is dependency-first with the module itself last, so a
/// builder that registers in order gets TLA+'s shadowing for free.
#[test]
fn the_extends_closure_is_dependency_first() {
    let s = Scratch::new(
        "closure",
        &[
            ("A.tla", "---- MODULE A ----\nG == 1\n====\n"),
            ("B.tla", "---- MODULE B ----\nEXTENDS A\nH == 2\n====\n"),
            ("C.tla", "---- MODULE C ----\nEXTENDS A\nK == 3\n====\n"),
            ("Top.tla", "---- MODULE Top ----\nEXTENDS B, C\n====\n"),
        ],
    );
    let spec = Loader::new().load(&s.path("Top.tla")).expect("loads");
    let top = spec.root_module().expect("root");
    let order: Vec<&str> = nixie_tla_syntax::extends_closure(&spec, top)
        .iter()
        .map(|m| m.name.name.as_str())
        .collect();
    assert_eq!(order.len(), 4);
    assert_eq!(order.last(), Some(&"Top"));
    let pos = |n: &str| order.iter().position(|x| *x == n).expect("in the closure");
    assert!(pos("A") < pos("B") && pos("B") < pos("Top"));
    assert!(pos("A") < pos("C") && pos("C") < pos("Top"));
}

// ======== the brief renderer ========

#[test]
fn brief_renders_the_shapes_a_diagnostic_needs() {
    let spec = single(CONFIG);
    let module = spec.root_module().expect("root");
    let body = |name: &str| {
        module
            .units
            .iter()
            .find_map(|u| match &u.kind {
                nixie_tla_syntax::UnitKind::OpDef {
                    name: n,
                    body,
                    params,
                    ..
                } if n.name == name && params.is_empty() => Some(body),
                _ => None,
            })
            .unwrap_or_else(|| panic!("no definition {name}"))
    };
    assert_eq!(
        nixie_tla_syntax::behavior::brief(body("Spec")),
        "Init /\\ [][Next]_x"
    );
    assert_eq!(
        nixie_tla_syntax::behavior::brief(body("Spec4")),
        "(Init2 /\\ [][Next2]_x) /\\ WF_x(Next2)"
    );
    assert_eq!(
        nixie_tla_syntax::behavior::brief(body("Spec6")),
        "(Init2 /\\ [][Next2]_x)"
    );
    assert_eq!(
        nixie_tla_syntax::behavior::brief(body("SpecK")),
        r"Init2 /\ ((x > 0) ~> (x > 1))"
    );
    assert_eq!(
        nixie_tla_syntax::behavior::brief(body("SpecD")),
        r"Init2 /\ [][x' = x + 1]_x"
    );
    // A level report that could not be established is not a refusal.
    assert_eq!(
        check_spec(&spec)[0].1.trusted_level_of("Spec"),
        Some(Level::Temporal)
    );
}
