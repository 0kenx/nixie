//! Regression tests for the "solver-final" fix package:
//!   1. Array soundness honesty gate (store=store extensionality).
//!   2. `Context::set_option` wiring of solve-time options + granular config API.
//!   3. `get-unsat-assumptions` / `get-assignment` command behaviour.
//!   4. `declare-sort` / `define-fun` are honoured (no longer silently ignored).

use oxiz_solver::{Context, SolverConfig, TheoryMode};

fn run_last(script: &str) -> String {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script executes");
    out.last().cloned().unwrap_or_default()
}

// ─────────────────────────── Array honesty gate ───────────────────────────

#[test]
fn store_store_conflict_concrete_index_is_unsat() {
    // (store a 0 1) = (store b 0 2) forces the read at 0 to be both 1 and 2.
    let r = run_last(
        r#"(set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= (store a 0 1) (store b 0 2)))
        (check-sat)"#,
    );
    assert_eq!(
        r, "unsat",
        "store=store conflict must be UNSAT (was spurious sat)"
    );
}

#[test]
fn store_store_conflict_symbolic_index_is_unsat() {
    // Same overwritten index i on both sides but different values → UNSAT.
    let r = run_last(
        r#"(set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (assert (= (store a i 1) (store b i 2)))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat");
}

#[test]
fn store_store_consistent_is_not_spurious_sat() {
    // (store a 0 1) = (store b 0 1) is genuinely satisfiable, but the syntactic
    // checks + EUF core cannot certify it, so the honesty gate reports unknown
    // (never a possibly-spurious sat).
    let r = run_last(
        r#"(set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= (store a 0 1) (store b 0 1)))
        (check-sat)"#,
    );
    assert_eq!(
        r, "unknown",
        "unrefuted store=store must be honest unknown, not sat"
    );
}

#[test]
fn var_store_alias_still_decided() {
    // The var=store alias path is unaffected by the gate: still concrete.
    let unsat = run_last(
        r#"(set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= b (store a 0 1)))
        (assert (= (select b 0) 2))
        (check-sat)"#,
    );
    assert_eq!(unsat, "unsat");

    let sat = run_last(
        r#"(set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= b (store a 0 1)))
        (assert (= (select b 0) 1))
        (check-sat)"#,
    );
    assert_eq!(sat, "sat");
}

#[test]
fn plain_select_sat_unaffected_by_gate() {
    let r = run_last(
        r#"(set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (= (select a i) 3))
        (check-sat)"#,
    );
    assert_eq!(r, "sat");
}

// ─────────────────────────── set_option wiring ───────────────────────────

#[test]
fn set_option_timeout_reaches_config() {
    let mut ctx = Context::new();
    ctx.set_option(":timeout", "2500");
    assert_eq!(ctx.solver_config().timeout_ms, 2500);
    assert_eq!(ctx.get_option("timeout"), Some("2500")); // leading ':' stripped
}

#[test]
fn set_option_limits_and_theory_mode_reach_config() {
    let mut ctx = Context::new();
    ctx.set_option("max-conflicts", "1000");
    ctx.set_option("max-decisions", "2000");
    ctx.set_option("theory-mode", "lazy");
    ctx.set_option("simplify", "false");
    let cfg = ctx.solver_config();
    assert_eq!(cfg.max_conflicts, 1000);
    assert_eq!(cfg.max_decisions, 2000);
    assert_eq!(cfg.theory_mode, TheoryMode::Lazy);
    assert!(!cfg.simplify);
}

#[test]
fn granular_and_full_config_setters_are_public() {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(42);
    ctx.set_max_conflicts(7);
    ctx.set_theory_mode(TheoryMode::Eager);
    assert_eq!(ctx.solver_config().timeout_ms, 42);
    assert_eq!(ctx.solver_config().max_conflicts, 7);

    // Full-config replacement path used by external portfolio drivers.
    let mut cfg: SolverConfig = ctx.solver_config().clone();
    cfg.timeout_ms = 999;
    ctx.set_solver_config(cfg);
    assert_eq!(ctx.solver_config().timeout_ms, 999);
}

#[test]
fn unknown_option_is_recorded_but_harmless() {
    let mut ctx = Context::new();
    ctx.set_option("random-seed", "12345");
    assert_eq!(ctx.get_option("random-seed"), Some("12345"));
}

// ──────────────────────── get-unsat-assumptions ────────────────────────

#[test]
fn get_unsat_assumptions_after_unsat() {
    let mut ctx = Context::new();
    ctx.execute_script(
        r#"(set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (check-sat-assuming ((not p)))"#,
    )
    .expect("script executes");
    let ua = ctx.get_unsat_assumptions();
    assert!(
        ua.starts_with('(') && ua.contains("not") && ua.contains('p'),
        "got: {ua}"
    );
}

#[test]
fn get_unsat_assumptions_errors_without_unsat() {
    let mut ctx = Context::new();
    ctx.execute_script(
        r#"(set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (check-sat)"#,
    )
    .expect("script executes");
    let ua = ctx.get_unsat_assumptions();
    assert!(
        ua.contains("error"),
        "expected error after non-assuming check, got: {ua}"
    );
}

// ───────────────────────────── get-assignment ─────────────────────────────

#[test]
fn get_assignment_reports_bool_consts() {
    let mut ctx = Context::new();
    ctx.execute_script(
        r#"(set-logic QF_UF)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert p)
        (assert (not q))
        (check-sat)"#,
    )
    .expect("script executes");
    let a = ctx.get_assignment();
    assert!(a.contains("(p true)"), "got: {a}");
    assert!(a.contains("(q false)"), "got: {a}");
}

// ─────────────────────── declare-sort / define-fun ───────────────────────

#[test]
fn declare_sort_and_define_fun_are_honoured() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            r#"(set-logic QF_UF)
        (declare-sort U 0)
        (declare-const x U)
        (declare-const y U)
        (define-fun two () Int 2)
        (assert (= x y))
        (check-sat)"#,
        )
        .expect("script executes");
    assert_eq!(out.last().map(String::as_str), Some("sat"));
    // declare-sort recorded for introspection.
    assert!(ctx.declared_sort_names().any(|(n, a)| n == "U" && a == 0));
    // define-fun (0-ary) registered as a constant so it appears in the model.
    assert!(ctx.get_fun_signature("two").is_none()); // 0-ary is a const, not a fun sig
}

// ──────────────────── Datatype polarity boundary ────────────────────

/// A Bool-sorted `(= A B)` is a `TermKind::Eq` — this AST has no `Iff` — and it
/// is satisfied with *both* sides false, so neither operand is asserted.
///
/// The datatype pre-check used to recurse into an equality's operands carrying
/// the enclosing polarity, so `(= ((_ is cons) x) p)` recorded a positive
/// `cons` tester for `x`.  Together with `((_ is nil) x)` that looked like two
/// different constructors for one variable and answered `unsat`.  The formula
/// is satisfiable with `x = nil, p = false` (`z3` answers `sat`).
#[test]
fn test_dt_bool_eq_polarity_boundary() {
    let r = run_last(
        r#"(set-logic ALL)
        (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
        (declare-const x Lst)
        (declare-const p Bool)
        (assert (= ((_ is cons) x) p))
        (assert ((_ is nil) x))
        (check-sat)"#,
    );
    assert_ne!(
        r, "unsat",
        "a tester behind a Boolean equality is not asserted; got: {r}"
    );
}

/// `(not (and A B))` is `(or (not A) (not B))`, so neither conjunct is
/// entailed.  The collector flipped polarity through `Not` but then descended
/// into the `And` conjuncts with that negative polarity, recording a *negative*
/// `cons` tester for `x`.  Against the asserted positive tester that fired the
/// "positive and negative tester for the same constructor" conflict.
/// Satisfiable with `x = (cons …), p = false` (`z3` answers `sat`).
#[test]
fn test_dt_demorgan_polarity_boundary() {
    let r = run_last(
        r#"(set-logic ALL)
        (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
        (declare-const x Lst)
        (declare-const p Bool)
        (assert (not (and ((_ is cons) x) p)))
        (assert ((_ is cons) x))
        (check-sat)"#,
    );
    assert_ne!(
        r, "unsat",
        "conjuncts of a negated And are disjunctive; got: {r}"
    );
}

/// Control: the genuinely contradictory testers, asserted unconditionally, must
/// still be refuted — the fixes above must not have disabled the checks.
#[test]
fn test_dt_conflicting_testers_still_unsat() {
    let r = run_last(
        r#"(set-logic ALL)
        (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
        (declare-const x Lst)
        (assert ((_ is cons) x))
        (assert (not ((_ is cons) x)))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat");
}

// ──────────────────── Datatype axiomatisation ────────────────────
//
// The CDCL(T) core has no dedicated datatype theory: `encode.rs` maps
// constructors, selectors and testers to plain SAT variables.  Every structural
// property below therefore has to come from the ground lemmas asserted by
// `solver::dt_axioms`, and every one of them was a false `sat` before that pass
// existed.  Each axiom is tested in *both* directions — an unsatisfiable
// instance and a satisfiable control — because over-correcting a false `sat`
// into a false `unsat` would be just as wrong.  Verdicts cross-checked with z3.

/// The shared `List Int` declaration used by the datatype axiom tests.
const LST: &str = "(declare-datatype Lst ((nil) (cons (head Int) (tail Lst))))";

/// `(head l)` is one ground term; it cannot hold two values.  The reported
/// defect: `sat`, with a model `l = nil` under which neither assertion holds.
#[test]
fn test_dt_selector_congruence_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const l Lst)
        (assert (= (head l) 10))
        (assert (= (head l) 11))
        (check-sat)"
    ));
    assert_eq!(r, "unsat", "one selector term cannot equal 10 and 11");
}

/// Control: the same accessor constrained *consistently* stays satisfiable.
#[test]
fn test_dt_selector_congruence_stays_sat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const l Lst)
        (assert (= (head l) 10))
        (assert (= (head l) 10))
        (check-sat)"
    ));
    assert_eq!(r, "sat");
}

/// A selector is a function of its argument: `a = b` forces `(head a) = (head b)`.
#[test]
fn test_dt_selector_congruence_on_equal_args_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const a Lst)
        (declare-const b Lst)
        (assert (= a b))
        (assert (= (head a) 1))
        (assert (= (head b) 2))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// The same congruence at a datatype-sorted result: `a = b ⇒ (tail a) = (tail b)`.
#[test]
fn test_dt_tail_congruence_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const a Lst)
        (declare-const b Lst)
        (assert (= a b))
        (assert (not (= (tail a) (tail b))))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// Control: *without* `a = b` the two accessors are unrelated.
#[test]
fn test_dt_selector_congruence_without_equality_stays_sat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const a Lst)
        (declare-const b Lst)
        (assert (= (head a) 1))
        (assert (= (head b) 2))
        (check-sat)"
    ));
    assert_eq!(r, "sat");
}

/// Selector over constructor: `(head (cons 7 t)) = 7`.
#[test]
fn test_dt_selector_over_constructor_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const t Lst)
        (assert (not (= (head (cons 7 t)) 7)))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// The same reduction at the recursive field: `(tail (cons 7 t)) = t`.
#[test]
fn test_dt_selector_over_constructor_recursive_field_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const t Lst)
        (assert (not (= (tail (cons 7 t)) t)))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// Control: asserting the reduction itself is satisfiable.
#[test]
fn test_dt_selector_over_constructor_stays_sat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const t Lst)
        (assert (= (head (cons 7 t)) 7))
        (assert (= (tail (cons 7 t)) t))
        (check-sat)"
    ));
    assert_eq!(r, "sat");
}

/// Tester correctness, positive direction: `((_ is cons) (cons 1 t))` holds.
#[test]
fn test_dt_tester_on_own_constructor_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const t Lst)
        (assert (not ((_ is cons) (cons 1 t))))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// Tester correctness, negative direction: `((_ is nil) (cons 1 t))` does not.
#[test]
fn test_dt_tester_on_other_constructor_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const t Lst)
        (assert ((_ is nil) (cons 1 t)))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// Control: both testers with their correct truth values.
#[test]
fn test_dt_tester_on_constructor_stays_sat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const t Lst)
        (assert ((_ is cons) (cons 1 t)))
        (assert (not ((_ is nil) (cons 1 t))))
        (check-sat)"
    ));
    assert_eq!(r, "sat");
}

/// Exhaustiveness: a value satisfies *at least* one tester.
#[test]
fn test_dt_exhaustiveness_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const l Lst)
        (assert (not ((_ is nil) l)))
        (assert (not ((_ is cons) l)))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// Mutual exclusivity: and *at most* one.
#[test]
fn test_dt_tester_exclusivity_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const l Lst)
        (assert ((_ is nil) l))
        (assert ((_ is cons) l))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// Control: the exhaustiveness disjunction is a tautology, not a conflict.
#[test]
fn test_dt_exhaustiveness_stays_sat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const l Lst)
        (assert (or ((_ is nil) l) ((_ is cons) l)))
        (check-sat)"
    ));
    assert_eq!(r, "sat");
}

/// The same exhaustiveness over a finite enumeration, phrased with equalities
/// instead of testers.
#[test]
fn test_dt_enum_exhaustiveness_unsat() {
    let r = run_last(
        r#"(set-logic ALL)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-const c Color)
        (assert (not (= c red)))
        (assert (not (= c green)))
        (assert (not (= c blue)))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat");
}

/// Control: ruling out two of three colours leaves the third.
#[test]
fn test_dt_enum_exhaustiveness_stays_sat() {
    let r = run_last(
        r#"(set-logic ALL)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-const c Color)
        (assert (not (= c red)))
        (assert (not (= c green)))
        (check-sat)"#,
    );
    assert_eq!(r, "sat");
}

/// Distinctness: values of different constructors are never equal.
#[test]
fn test_dt_constructor_distinctness_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const t Lst)
        (assert (= (cons 1 t) nil))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// Control: the disequality itself holds.
#[test]
fn test_dt_constructor_distinctness_stays_sat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const t Lst)
        (assert (not (= (cons 1 t) nil)))
        (check-sat)"
    ));
    assert_eq!(r, "sat");
}

/// Injectivity at a non-recursive field: `(cons a t) = (cons b t) ⇒ a = b`.
#[test]
fn test_dt_injectivity_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const a Int)
        (declare-const b Int)
        (declare-const t Lst)
        (assert (= (cons a t) (cons b t)))
        (assert (not (= a b)))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// Injectivity at the recursive field: `(cons 1 u) = (cons 1 v) ⇒ u = v`.
#[test]
fn test_dt_injectivity_recursive_field_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const u Lst)
        (declare-const v Lst)
        (assert (= (cons 1 u) (cons 1 v)))
        (assert (not (= u v)))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// Control: equal arguments really do build equal values.
#[test]
fn test_dt_injectivity_stays_sat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const a Int)
        (declare-const b Int)
        (declare-const t Lst)
        (assert (= (cons a t) (cons b t)))
        (assert (= a b))
        (check-sat)"
    ));
    assert_eq!(r, "sat");
}

/// Acyclicity: a datatype value is a finite tree, so `l = (cons 1 l)` has no
/// model.  Congruence alone never sees this — it happily merges the two — which
/// is why the property is so often missing and yields a false `sat`.
#[test]
fn test_dt_acyclicity_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const l Lst)
        (assert (= l (cons 1 l)))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// The same cycle two constructors deep.
#[test]
fn test_dt_acyclicity_depth_two_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const l Lst)
        (assert (= l (cons 1 (cons 2 l))))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// A cycle routed through two variables rather than one nested term — the case
/// a purely syntactic occurs-check misses.
#[test]
fn test_dt_acyclicity_through_two_variables_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const p Lst)
        (declare-const q Lst)
        (assert (= p (cons 1 q)))
        (assert (= q (cons 2 p)))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// A cycle closed through an accessor instead of a constructor.
#[test]
fn test_dt_acyclicity_through_selector_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const l Lst)
        (assert ((_ is cons) l))
        (assert (= (tail l) l))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// Control: the disequality is satisfiable, and so is a finite list.
#[test]
fn test_dt_acyclicity_stays_sat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const l Lst)
        (assert (not (= l (cons 1 l))))
        (assert ((_ is cons) l))
        (check-sat)"
    ));
    assert_eq!(r, "sat");
}

/// A selector applied to the *wrong* constructor is underspecified in SMT-LIB —
/// `(head nil)` may be any `Int` — so constraining it must stay `sat`.  Getting
/// this backwards would trade the false `sat` for an equally bad false `unsat`.
#[test]
fn test_dt_selector_on_wrong_constructor_stays_sat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (assert (= (head nil) 42))
        (check-sat)"
    ));
    assert_eq!(r, "sat", "(head nil) is underspecified, not constrained");
}

/// The same through a tester rather than a literal constructor.
#[test]
fn test_dt_selector_under_wrong_tester_stays_sat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const l Lst)
        (assert ((_ is nil) l))
        (assert (= (head l) 42))
        (check-sat)"
    ));
    assert_eq!(r, "sat");
}

/// Underspecified is not unconstrained: `(head nil)` is still a *function*
/// value, so it cannot be both 42 and 43.
#[test]
fn test_dt_selector_on_wrong_constructor_still_a_function_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (assert (= (head nil) 42))
        (assert (= (head nil) 43))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// Reconstruction: under its own tester a term *is* its constructor applied to
/// its own accessors.
#[test]
fn test_dt_reconstruction_under_tester_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const l Lst)
        (assert ((_ is cons) l))
        (assert (= (head l) 1))
        (assert (not (= l (cons 1 (tail l)))))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// The single-constructor case, where reconstruction is unconditional.
#[test]
fn test_dt_reconstruction_single_constructor_unsat() {
    let r = run_last(
        r#"(set-logic ALL)
        (declare-datatype Pr ((mk (fst Int) (snd Int))))
        (declare-const p Pr)
        (assert (not (= p (mk (fst p) (snd p)))))
        (check-sat)"#,
    );
    assert_eq!(r, "unsat");
}

/// Control: a record with two independent fields is satisfiable.
#[test]
fn test_dt_record_fields_stay_sat() {
    let r = run_last(
        r#"(set-logic ALL)
        (declare-datatype Pr ((mk (fst Int) (snd Int))))
        (declare-const p Pr)
        (assert (= (fst p) 1))
        (assert (= (snd p) 2))
        (check-sat)"#,
    );
    assert_eq!(r, "sat");
}

/// A nested accessor is still one ground term.
#[test]
fn test_dt_nested_selector_congruence_unsat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const l Lst)
        (assert (= (head (tail l)) 1))
        (assert (= (head (tail l)) 2))
        (check-sat)"
    ));
    assert_eq!(r, "unsat");
}

/// Control: accessors at different depths are independent.
#[test]
fn test_dt_nested_selector_stays_sat() {
    let r = run_last(&format!(
        "(set-logic ALL) {LST}
        (declare-const l Lst)
        (assert (= (head l) 1))
        (assert (= (head (tail l)) 2))
        (check-sat)"
    ));
    assert_eq!(r, "sat");
}

/// Scope discipline: the datatype lemmas are asserted into the SAT core at the
/// current level, so a `pop` must retract both the clauses and the "already
/// asserted" marks.  A leaked acyclicity lemma would keep refuting the popped
/// cycle; a leaked *mark* would stop the axiom being re-derived in a later
/// scope, so the same query is run twice around the `push`/`pop` and must give
/// the same answer both times.
#[test]
fn test_dt_axioms_retracted_on_pop() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(&format!(
            "(set-logic ALL) {LST}
            (declare-const l Lst)
            (push 1)
            (assert (= l (cons 1 l)))
            (check-sat)
            (pop 1)
            (check-sat)
            (push 1)
            (assert (= l (cons 1 l)))
            (check-sat)
            (pop 1)
            (assert (= (head l) 5))
            (check-sat)"
        ))
        .expect("script executes");
    assert_eq!(
        out,
        vec!["unsat", "sat", "unsat", "sat"],
        "datatype lemmas must be retracted with their scope and re-derivable"
    );
}

// ──────────── Datatype differential test against a brute-force oracle ────────────
//
// The axiom battery above pins the individual rules; this pass checks the
// *combination* of them over a whole formula space.  The universe is chosen so
// that a brute-force oracle is exact rather than approximate:
//
//   (declare-datatype Col ((red) (green) (blue)))
//   (declare-datatype Box ((empty) (full (item Col))))
//
// `Col` has exactly 3 values and `Box` exactly 4 (`empty`, `full c`), both
// finite and non-recursive, so a two-variable problem has a finite model space
// that can be enumerated in full — no depth bound, no approximation, and no
// wall-clock or random-seed dependence.  The one subtlety is `(item empty)`,
// which SMT-LIB leaves *underspecified*: the oracle models it as one extra free
// choice of `Col`, so a formula that pins it stays satisfiable exactly as the
// standard requires.

/// The three `Col` values.
const COL_NAMES: [&str; 3] = ["red", "green", "blue"];

/// A `Box` value: `None` is `empty`, `Some(c)` is `(full c)`.
type BoxVal = Option<usize>;

/// The four `Box` values, in a fixed order.
const BOX_VALS: [BoxVal; 4] = [None, Some(0), Some(1), Some(2)];

/// One complete interpretation: the two `Box` constants plus the value the
/// underspecified `(item empty)` takes.
struct Interp {
    b1: BoxVal,
    b2: BoxVal,
    item_at_empty: usize,
}

impl Interp {
    /// `(item b)` — the accessor is total, and on `empty` it takes whatever
    /// value this interpretation picked for it.
    fn item(&self, b: BoxVal) -> usize {
        b.unwrap_or(self.item_at_empty)
    }
}

/// One atom: its SMT-LIB text and its exact evaluation under an
/// interpretation, kept side by side so the two cannot drift apart.
type Atom = (&'static str, fn(&Interp) -> bool);

/// The atoms the generated formulas are built from.
fn atoms() -> Vec<Atom> {
    vec![
        ("(= b1 b2)", |i| i.b1 == i.b2),
        ("((_ is empty) b1)", |i| i.b1.is_none()),
        ("((_ is full) b2)", |i| i.b2.is_some()),
        ("(= (item b1) red)", |i| i.item(i.b1) == 0),
        ("(= (item b1) (item b2))", |i| i.item(i.b1) == i.item(i.b2)),
        ("(= b1 (full red))", |i| i.b1 == Some(0)),
        ("(= b2 (full (item b1)))", |i| i.b2 == Some(i.item(i.b1))),
        ("(= (item b2) green)", |i| i.item(i.b2) == 1),
    ]
}

/// One literal of the generated formulas: its SMT-LIB text, the exact
/// evaluator of the underlying atom, and whether the literal negates it.
type Literal = (String, fn(&Interp) -> bool, bool);

/// Every literal (atom and its negation).
fn literals() -> Vec<Literal> {
    let mut out = Vec::new();
    for (text, eval) in atoms() {
        out.push((text.to_string(), eval, false));
        out.push((format!("(not {text})"), eval, true));
    }
    out
}

/// Enumerate every interpretation of the universe: 4 × 4 × 3 = 48.
fn interpretations() -> Vec<Interp> {
    let mut out = Vec::new();
    for &b1 in &BOX_VALS {
        for &b2 in &BOX_VALS {
            for item_at_empty in 0..COL_NAMES.len() {
                out.push(Interp {
                    b1,
                    b2,
                    item_at_empty,
                });
            }
        }
    }
    out
}

/// Brute-force verdict for a conjunction of literals, given by index into
/// [`literals`].
fn oracle(selection: &[usize], lits: &[Literal]) -> &'static str {
    let models = interpretations();
    for interp in &models {
        if selection.iter().all(|&index| {
            let (_, eval, negated) = &lits[index];
            eval(interp) != *negated
        }) {
            return "sat";
        }
    }
    "unsat"
}

/// Deterministic differential sweep: every conjunction of up to three literals
/// over the eight atoms above (696 formulas), each checked against the exact
/// brute-force verdict.  Fully enumerative — no RNG, no seed, no timing
/// dependence — so a mismatch is reproducible from the reported indices alone.
#[test]
fn test_dt_differential_against_brute_force_oracle() {
    let lits = literals();
    let mut selections: Vec<Vec<usize>> = Vec::new();
    for i in 0..lits.len() {
        selections.push(vec![i]);
        for j in (i + 1)..lits.len() {
            selections.push(vec![i, j]);
            for k in (j + 1)..lits.len() {
                selections.push(vec![i, j, k]);
            }
        }
    }

    let mut mismatches: Vec<String> = Vec::new();
    for selection in &selections {
        let asserts: String = selection
            .iter()
            .map(|&index| format!("(assert {}) ", lits[index].0))
            .collect();
        let script = format!(
            "(set-logic ALL)
             (declare-datatype Col ((red) (green) (blue)))
             (declare-datatype Box ((empty) (full (item Col))))
             (declare-const b1 Box)
             (declare-const b2 Box)
             {asserts}
             (check-sat)"
        );
        let actual = run_last(&script);
        let expected = oracle(selection, &lits);
        if actual != expected {
            mismatches.push(format!("{asserts}=> oxiz {actual}, oracle {expected}"));
        }
    }

    assert!(
        mismatches.is_empty(),
        "{} of {} datatype formulas disagree with the brute-force oracle:\n{}",
        mismatches.len(),
        selections.len(),
        mismatches.join("\n")
    );
}
