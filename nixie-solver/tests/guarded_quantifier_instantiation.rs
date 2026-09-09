//! Regression tests for guarded instantiation of **boundary** quantifiers
//! (2026-09, the Ultimate Automizer `(not (and … (exists …)))` class).
//!
//! A quantifier behind a polarity boundary (an `or` disjunct, an `and`
//! conjunct under a negation, …) is not unconditionally asserted, so its
//! instances are *not* valid as unit clauses.  But two guarded clause forms
//! are valid in every model, because the guard's meaning *is* the
//! quantified formula:
//!
//! * boundary `q = forall x⃗. phi`:   `(!q | phi[t⃗])`
//! * boundary `q_e = exists x⃗. D`: the derived universal
//!   `not (exists x⃗. D) == forall x⃗. not D` yields `(q_e | not D[t⃗])`
//!
//! The SAT solver case-splits the disjunction; when it commits a
//! quantified branch, the guarded instances activate and can refute it.
//! This is what decides the Ultimate Automizer SV-COMP encodings
//! (`(not (and A B C (exists ((ielen Int)) D)))` with premises forcing
//! `A B C`): branches `!A !B !C` conflict, the `exists` branch commits
//! FALSE, the derived universal activates, and instantiating `ielen` with
//! the premise's own constant refutes the goal.
//!
//! Boundary *existentials* keep their `unowned` status for the `sat` gate
//! (the derived universal covers only the refutation direction; a witness
//! still has to be exhibited, and nothing here fabricates one).

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

fn last_status(output: &[String]) -> &str {
    output
        .iter()
        .rev()
        .find(|line| {
            let t = line.trim();
            matches!(t, "sat" | "unsat" | "unknown")
        })
        .map(String::as_str)
        .unwrap_or("<no verdict>")
}

/// The Ultimate Automizer shape, minimized: premises force every literal
/// conjunct, so the negated `and` must be satisfied through the exists
/// branch — which the premises also make true.  `unsat` (z3 agrees); the
/// guarded derived universal is what finds it.
#[test]
fn negated_and_with_exists_branch_is_unsat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const i Int)
        (declare-const ielen Int)
        (declare-const p Int)
        (declare-const bufsize Int)
        (assert (and (< i ielen) (<= 5 i)
                     (<= (+ (* 2 ielen) p) (+ bufsize 10))))
        (assert (not
          (and (<= 5 i)
               (<= (+ (* 2 ielen) p) (+ bufsize 10))
               (<= 4 i)
               (exists ((ielen2 Int))
                 (and (<= 6 ielen2)
                      (<= (+ (* 2 ielen2) p) (+ bufsize 10)))))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// A boundary universal whose branch is committed must be checked: the
/// disjunction's other disjunct is refutable, so the `forall` branch is
/// taken, and it is false (`x > x` never holds) – `unsat`.
#[test]
fn boundary_forall_committed_and_false_is_unsat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const c Int)
        (assert (= c 3))
        (assert (or (forall ((x Int)) (> x x)) (= c 4)))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// A boundary universal whose branch is *not* taken must not veto a
/// satisfiable goal: the second disjunct holds, the (false) universal's
/// guard is committed FALSE, and the round skips it – `sat`.
#[test]
fn boundary_forall_vacuous_stays_sat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const c Int)
        (assert (or (forall ((x Int)) (> x x)) (= c 4)))
        (assert (= c 4))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "sat");
}

/// The guarded clause itself is valid at any commitment, so it can never
/// manufacture a conflict for a genuinely satisfiable branch shape: the
/// universal is true (`x = x`), the disjunction is satisfiable either way.
#[test]
fn boundary_true_forall_stays_sat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const c Int)
        (assert (or (forall ((x Int)) (= x x)) (= c 4)))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "sat");
}

/// A boundary existential whose witness is a pool term gets its branch
/// *derived*: the guarded instance `(q_e | not (= 5 5))` forces `q_e`, the
/// disjunction is satisfied, and the goal stays `sat` through a real
/// derivation rather than a lucky free Boolean.
#[test]
fn boundary_exists_witness_in_pool_derives_sat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const y Int)
        (assert (= y 7))
        (assert (or (exists ((v Int)) (= v 5)) (= y 8)))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "sat");
}

/// Refuting a boundary existential needs arithmetic (`2v+1 = 8` has no
/// integer solution – a parity fact), which no finite instantiation set
/// derives; the honest verdict is anything but a wrong decisive one.
#[test]
fn boundary_exists_needs_arithmetic_is_never_wrong() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const y Int)
        (assert (= y 7))
        (assert (or (exists ((v Int)) (= (+ (* 2 v) 1) 8)) (= y 8)))
        (check-sat)
    "#);
    assert_ne!(last_status(&output), "sat");
}

/// The witness direction stays honest: a boundary existential that IS
/// satisfiable keeps the goal `sat` (nothing forces a witness, but nothing
/// refutes the branch either; the model certifier or exhaustion decides).
#[test]
fn boundary_exists_witnessable_stays_sat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const y Int)
        (assert (= y 7))
        (assert (exists ((v Int)) (= (+ (* 2 v) 1) 7)))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "sat");
}
