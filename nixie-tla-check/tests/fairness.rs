//! Fairness assumptions on the lasso (issue #47).
//!
//! A `SPECIFICATION` that states `WF`/`SF` is **assumed** by a liveness
//! check: a lasso is reported only when it is a behaviour of the full
//! specification. These pin the issue's own acceptance list – an unfair loop
//! violates progress, the fairness assumption excludes it, a fair
//! counterexample is still reported, and weak and strong fairness differ on
//! an action that is enabled intermittently – plus what the checker does
//! with a clause it cannot assume.
//!
//! The lasso here is over `Next` as Apalache's `LoopEncoder` writes it, with
//! no stuttering step of its own (see `nixie_tla_check::temporal`): a
//! "stutter" is spelled as an explicit action that leaves the state alone,
//! which is also what makes `⟨Next⟩_v` – the subscript's change – the right
//! test for "taken".

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome, SetupError, SpecRoles};

use nixie_tla_syntax::{BehaviorSpec, LoadedSpec};

/// A `Next` with an explicit self-loop: the unfair behaviour a fairness
/// condition exists to rule out.
const STUTTER: &str = r"
---- MODULE Stutter ----
VARIABLE x
Init == x = 0
Step == x < 2 /\ x' = x + 1
Next == Step \/ (x' = x)
Spec == Init /\ [][Next]_x
FairSpec == Init /\ [][Next]_x /\ WF_x(Next)
NeverStuck == <>(x = 2)
====
";

/// Every behaviour flips `x` forever and no fairness condition objects:
/// a fair counterexample, still a counterexample.
const TOGGLE: &str = r"
---- MODULE Toggle ----
VARIABLE x
Init == x = 0
Next == x' = 1 - x
FairSpec == Init /\ [][Next]_x /\ WF_x(Next)
NeverTwo == <>(x = 2)
====
";

/// `Step` is enabled in every other state only. Under `WF` the Tick-only
/// cycle is fair (the action is not *continuously* enabled); under `SF` it
/// is not (enabled infinitely often, taken never) – and every cycle that
/// takes a `Step` grows `y`, so none closes.
const INTERMITTENT: &str = r"
---- MODULE Intermittent ----
VARIABLE x, y
Init == x = 0 /\ y = 0
Tick == x' = 1 - x /\ UNCHANGED y
Step == x = 0 /\ y' = y + 1 /\ UNCHANGED x
Next == Tick \/ Step \/ (x' = x /\ y' = y)
vars == <<x, y>>
WFSpec == Init /\ [][Next]_vars /\ WF_vars(Step)
SFSpec == Init /\ [][Next]_vars /\ SF_vars(Step)
Plain == Init /\ [][Next]_vars
AlwaysOne == <>[](x = 1)
====
";

/// The per-process idiom, quantified over a pinned `CONSTANT`. The members
/// are model values: with integers the lasso's set pairs mint integer
/// witnesses whose disequalities the arithmetic search pays for, which is
/// issue #49's remaining shape and not what this test is about.
const PER_PROCESS: &str = r"
---- MODULE PerProcess ----
VARIABLE done
Init == done = {}
Step(self) == self \notin done /\ done' = done \cup {self}
Next == (\E self \in Node : Step(self)) \/ (done' = done)
Spec == Init /\ [][Next]_done /\ \A self \in Node : WF_vars(Step(self))
NoFair == Init /\ [][Next]_done
AllDone == <>(done = Node)
====
";

const PINNED: &str = "CONSTANT Node = {n1, n2}\n";

/// Check the temporal property `prop` of `src` under the `SPECIFICATION`
/// its `.cfg` names – fairness included – to `depth`, with the conflict
/// budget the corpus harness uses. The verdict, and the checker it came from.
fn lasso(src: &str, cfg: &str, prop: &str, depth: u32) -> Result<(Outcome, Bmc), SetupError> {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let config = nixie_tla_syntax::parse_config(cfg).expect("config parses");
    let BehaviorSpec::Temporal(name) = &config.behavior else {
        panic!("the configuration names a SPECIFICATION");
    };
    let form =
        nixie_tla_syntax::safety_form(&spec, module, &nixie_tla_syntax::check_spec(&spec), name)
            .expect("decomposes");
    let roles = SpecRoles {
        init: form.init.clone(),
        next: form.next.clone(),
        inv: std::slice::from_ref(&prop),
        constraints: &[],
    };
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare_temporal_spec(&spec, module, roles, prop, &form.fairness, &config, &mut tm)?;
    bmc.set_check_deadlocks(false);
    bmc.set_conflict_limit(20_000);
    let outcome = bmc.check(depth, &mut tm).expect("checks");
    Ok((outcome, bmc))
}

fn outcome(src: &str, cfg: &str, prop: &str, depth: u32) -> Outcome {
    lasso(src, cfg, prop, depth)
        .unwrap_or_else(|e| panic!("prepares: {e}"))
        .0
}

/// Without fairness, the self-loop with `Step` enabled is a behaviour, and
/// it never reaches `x = 2`.
#[test]
fn an_unfair_loop_violates_progress_without_fairness() {
    assert_eq!(
        outcome(STUTTER, "SPECIFICATION Spec\n", "NeverStuck", 3),
        Outcome::Violation { step: 1 }
    );
}

/// `WF_x(Next)` rules it out: `⟨Next⟩_x` is enabled at the looping state and
/// never taken. Every other lasso within the bound reaches `x = 2`.
#[test]
fn weak_fairness_excludes_the_loop_it_forbids() {
    let (outcome, bmc) =
        lasso(STUTTER, "SPECIFICATION FairSpec\n", "NeverStuck", 3).expect("prepares");
    assert_eq!(outcome, Outcome::NoViolationWithin(3));
    assert_eq!(bmc.fairness().len(), 1);
    assert!(bmc.fairness()[0].guards.is_empty());
}

/// A lasso that takes the action is fair, and is still reported.
#[test]
fn a_fair_counterexample_is_still_reported() {
    let (outcome, bmc) =
        lasso(TOGGLE, "SPECIFICATION FairSpec\n", "NeverTwo", 3).expect("prepares");
    assert_eq!(outcome, Outcome::Violation { step: 2 });
    assert_eq!(bmc.loop_start(), Some(1));
    assert_eq!(
        bmc.verification(),
        Some(&nixie_tla_check::bmc::Verification::Replayed)
    );
    // The accumulators are the encoding's, not the specification's: they
    // stay out of the trace a consumer reads.
    let itf = bmc.counterexample_itf("Toggle").expect("a trace");
    let vars: Vec<String> = itf["vars"]
        .as_array()
        .expect("vars")
        .iter()
        .map(|s| s.as_str().unwrap_or("").to_string())
        .collect();
    assert!(vars.contains(&"x".to_string()));
    assert!(!vars.iter().any(|n| n.starts_with("__fair_")), "{vars:?}");
}

/// `Step` is enabled only where `x = 0`. The Tick-only cycle is fair under
/// `WF` – not continuously enabled – and violates `<>[](x = 1)`; the same
/// cycle is unfair under `SF`, and no cycle that takes a `Step` closes (`y`
/// grows), so `SF` finds nothing within the bound.
#[test]
fn weak_and_strong_fairness_differ_on_an_intermittently_enabled_action() {
    assert_eq!(
        outcome(INTERMITTENT, "SPECIFICATION WFSpec\n", "AlwaysOne", 2),
        Outcome::Violation { step: 2 }
    );
    for depth in 1..=4 {
        assert_eq!(
            outcome(INTERMITTENT, "SPECIFICATION SFSpec\n", "AlwaysOne", depth),
            Outcome::NoViolationWithin(depth),
            "depth {depth}"
        );
    }
}

/// `\A self \in Node : WF_vars(Step(self))` is one assumption per member:
/// the loop that does nothing is unfair while either step is enabled, and
/// the only state with nothing left enabled satisfies the property.
#[test]
fn quantified_fairness_is_assumed_per_member() {
    assert_eq!(
        outcome(
            PER_PROCESS,
            format!("{PINNED}SPECIFICATION NoFair\n").as_str(),
            "AllDone",
            1
        ),
        Outcome::Violation { step: 1 }
    );
    let (outcome, bmc) = lasso(
        PER_PROCESS,
        format!("{PINNED}SPECIFICATION Spec\n").as_str(),
        "AllDone",
        2,
    )
    .expect("prepares");
    assert_eq!(outcome, Outcome::NoViolationWithin(2));
    let instances = bmc.fairness();
    assert_eq!(instances.len(), 2);
    assert_eq!(instances[0].guards.len(), 1);
    assert_ne!(instances[0].bindings, instances[1].bindings);
}

/// A domain with no statically known members gives no instances to assume:
/// declined by name, never dropped.
#[test]
fn a_fairness_domain_without_known_members_is_declined_by_name() {
    let err = lasso(PER_PROCESS, "SPECIFICATION Spec\n", "AllDone", 2)
        .err()
        .expect("does not prepare");
    let SetupError::Lower { name, why } = &err else {
        panic!("a lowering error, got {err:?}");
    };
    assert!(name.contains("fairness"), "{name}");
    assert!(why.contains("no statically known members"), "{why}");
}

/// A lasso whose loop starts in the **first** state is found at its own
/// length. The tableau's `unroll` used to be fixed at `Init` as well as by
/// its step-0 equation, which contradicted each other for such a lasso
/// whenever a `[]` argument was false there; the violation then surfaced
/// only one step later, rotated, and a bound that reached the shorter form
/// only answered "no lasso violates" (found while testing fairness).
#[test]
fn a_loop_starting_in_the_first_state_is_found_at_its_own_length() {
    // The Tick-only cycle `(0,0) -> (1,0) -> (0,0)`: `<>[](x = 1)` fails on
    // it, and it is two steps long.
    let src = INTERMITTENT.replace(
        "Next == Tick \\/ Step \\/ (x' = x /\\ y' = y)",
        "Next == Tick \\/ Step",
    );
    assert_eq!(
        outcome(&src, "SPECIFICATION Plain\n", "AlwaysOne", 2),
        Outcome::Violation { step: 2 }
    );
}
