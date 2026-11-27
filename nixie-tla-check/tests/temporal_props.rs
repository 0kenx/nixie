//! The temporal structures the corpus writes, lowered to the tableau
//! (issue #29).
//!
//! The tableau (`nixie_tla_check::temporal`) was general over nesting; the
//! walk that lowers a property to it read four shapes wrong, and Apalache's
//! own suite has a cell for each:
//!
//! * a `LET` around the temporal structure (`LetIn.tla`) – its definitions
//!   were not in scope for the leaves below it;
//! * `A /\ B` and `A \/ B` with a temporal operand (`NestedTemporalInBool.tla`,
//!   `NoTemporalOperatorsInTemporalProp.tla`) – the parser delivers these as
//!   infix operators, and only a bulleted list was read;
//! * an action under `[]`/`<>` (`TemporalPropsOverActions.tla`) – an
//!   action-level operand is a leaf the tableau reads on each step, as it is
//!   in Apalache's `TableauEncoder`;
//! * a `LET`-bound definition of temporal level.
//!
//! Each is pinned with the verdict the oracle gives on the same cell.

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome, SetupError};

/// Prepare `prop` of `spec` as a lasso check and run it to `depth`: the
/// verdict, or the refusal.
fn try_lasso(spec: &str, prop: &str, depth: u32) -> Result<Outcome, SetupError> {
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
    )?;
    bmc.check(depth, &mut tm)
}

fn lasso(spec: &str, prop: &str, depth: u32) -> Outcome {
    try_lasso(spec, prop, depth).unwrap_or_else(|e| panic!("`{prop}`: {e}"))
}

/// The refusal of a property the walk declines, by its message.
fn refusal(spec: &str, prop: &str) -> String {
    try_lasso(spec, prop, 0)
        .expect_err("the property is refused")
        .to_string()
}

/// The two-state cycle of `LetIn.tla` and `NestedTemporalInBool.tla`:
/// `(0, 1) ↔ (1, 0)`.
const SWAP: &str = r#"
EXTENDS Integers
VARIABLE
    \* @type: Int;
    x,
    \* @type: Int;
    y
Init == /\ x = 0
       /\ y = 1
Next == /\ x' = y
       /\ y' = x
"#;

/// `LetIn.tla`: the `[]<>` sits under two `LET`s, and its leaf calls the
/// one that takes parameters and the one that names a variable. With the
/// definitions out of scope the leaf could not resolve; lowering the `LET`
/// by the ordinary path met the `<>`. `Liveness` holds on the cycle
/// (`2x + y = 2` at `(1, 0)`), `FalseLiveness` holds nowhere.
#[test]
fn a_let_around_the_temporal_structure_is_in_scope_for_its_leaves() {
    let src = format!(
        r#"
---- MODULE LetIn ----
{SWAP}
Liveness ==
    LET Plus(a,b) == a + b IN
    LET var1 == x IN
    []<>(Plus(Plus(var1,y), var1) = 2)
FalseLiveness ==
    LET Plus(a,b) == a + b IN
    LET var1 == x IN
    <>[](Plus(var1,y) = 2)
====
"#
    );
    assert_eq!(
        lasso(&src, "Liveness", 6),
        Outcome::NoViolationWithin(6),
        "the oracle: NoError"
    );
    assert_eq!(
        lasso(&src, "FalseLiveness", 6),
        Outcome::Violation { step: 2 },
        "the oracle: Error (its trace one step longer – the known tableau defect)"
    );
}

/// `NestedTemporalInBool.tla`: three conjuncts, each a different mix – a
/// diamond in a box, a diamond under a disjunction under a box, a negated
/// box in a diamond. And `NoTemporalOperatorsInTemporalProp.tla`'s
/// `x = 0 /\ []TRUE`, a state predicate conjoined with a temporal one.
#[test]
fn an_infix_connective_with_a_temporal_operand_is_a_tableau_node() {
    let src = format!(
        r#"
---- MODULE Nested ----
{SWAP}
Liveness == []<>(x = 1) /\ [](y < 1 \/ <>(y = 1)) /\ ~<>[](x > 5)
FalseLiveness == []<>(x = 1) /\ [](y < 1 \/ <>(y = 1)) /\ <>[](x > 5)
Mixed == x = 0 /\ []TRUE
Explicit == [](x = 0)
====
"#
    );
    assert_eq!(
        lasso(&src, "Liveness", 6),
        Outcome::NoViolationWithin(6),
        "the oracle: NoError"
    );
    assert_eq!(
        lasso(&src, "FalseLiveness", 6),
        Outcome::Violation { step: 2 },
        "the oracle: Error"
    );
    assert_eq!(
        lasso(&src, "Mixed", 4),
        Outcome::NoViolationWithin(4),
        "the oracle: NoError"
    );
    assert_eq!(
        lasso(&src, "Explicit", 4),
        Outcome::Violation { step: 2 },
        "the oracle: Error"
    );
}

/// `TemporalPropsOverActions.tla`: the operand of a temporal operator is an
/// action. `<>(<<x' = x + 1>>_x)` holds on the 4-cycle `0 → 1 → 2 → 3 → 0`
/// (three of its steps take it); `<>[]([x' = x + 1]_x)` fails on it (the
/// step `3 → 0` does not). A primed operand with no subscript reads the
/// same way. What stays refused by name is an action **beside** a temporal
/// operator under a propositional node: it would reach an `Init` equation,
/// where a prime means nothing.
#[test]
fn an_action_under_a_temporal_operator_is_read_on_each_step() {
    let src = r#"
---- MODULE Acts ----
EXTENDS Integers
VARIABLE
    \* @type: Int;
    x
Init == x = 0
Next == x' = IF x < 3 THEN x + 1 ELSE 0
Liveness == <>(<<x' = x + 1>>_x)
FalseLiveness == <>[]([x' = x + 1]_x)
Primed == <>(x' = x + 1)
WholeOperand == []((x' = x + 1) \/ x = 9)
BesideANode == [](<>(x = 9) \/ (x' = x + 1))
====
"#;
    assert_eq!(
        lasso(src, "Liveness", 5),
        Outcome::NoViolationWithin(5),
        "the oracle: NoError"
    );
    assert_eq!(
        lasso(src, "FalseLiveness", 5),
        Outcome::Violation { step: 4 },
        "the oracle: Error, four states"
    );
    assert_eq!(
        lasso(src, "Primed", 5),
        Outcome::NoViolationWithin(5),
        "no subscript: the action alone, and it is taken"
    );
    // An operand that is action-level throughout is one leaf, read on each
    // step – and the step `3 → 0` falsifies it, as it falsifies the
    // subscripted form above.
    assert_eq!(
        lasso(src, "WholeOperand", 6),
        Outcome::Violation { step: 4 }
    );
    let err = refusal(src, "BesideANode");
    assert!(
        err.to_string().contains("action-level"),
        "an action leaf beside a temporal node has no tableau rule: {err}"
    );
}

/// A `LET`-bound definition of temporal level expands in the tableau, as a
/// module-level one does.
#[test]
fn a_let_bound_temporal_definition_expands_in_the_tableau() {
    let src = format!(
        r#"
---- MODULE LetTemporal ----
{SWAP}
TProp == LET T == [](x < 2) IN T /\ <>(x = 1)
NeverOne == LET T == [](x < 2) IN T /\ [](x = 1)
====
"#
    );
    assert_eq!(lasso(&src, "TProp", 5), Outcome::NoViolationWithin(5));
    assert_eq!(lasso(&src, "NeverOne", 5), Outcome::Violation { step: 2 });
}

/// A function-valued state variable reaches the lasso check. The encoding
/// writes `__saved_flag' = IF __InLoop' = __InLoop THEN __saved_flag ELSE
/// flag` for it, an `IF` over functions the encoder refused (`Bug2107.tla`,
/// whose `P1`/`P2` are two of Apalache's cells: NoError). One step is
/// enough to state it: the `IF` is in every step's `Next`.
#[test]
fn a_function_valued_state_variable_reaches_the_lasso_check() {
    let src = r#"
---- MODULE Bug2107 ----
VARIABLES
    \* @type: Int -> Bool;
    flag
Init == flag = [p \in {1} |-> FALSE]
Next == flag' = [p \in {1} |-> IF TRUE /\ TRUE /\ TRUE THEN FALSE ELSE FALSE]
P1 == <>(TRUE)
P2 == [](TRUE)
NeverFlipped == <>[](flag[1])
====
"#;
    assert_eq!(
        lasso(src, "P1", 1),
        Outcome::NoViolationWithin(1),
        "the oracle: NoError"
    );
    assert_eq!(
        lasso(src, "P2", 1),
        Outcome::NoViolationWithin(1),
        "the oracle: NoError"
    );
    assert_eq!(
        lasso(src, "NeverFlipped", 1),
        Outcome::Violation { step: 1 }
    );
}
