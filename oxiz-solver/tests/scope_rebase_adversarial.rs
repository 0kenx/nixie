//! Adversarial probes for `Solver::rebase_theory_state` (task #26).
//!
//! `tests/scope_leak_hazard.rs` pins the reproductions the fix was written
//! against.  This file attacks the fix from the other side: it looks for seams
//! the rebase does *not* cover, and for facts the rebase might drop that the
//! trail replay cannot re-derive.
//!
//! Two failure directions are probed, because the fix can break either way:
//!
//! * **false `unsat`** — a retracted branch's facts survive into a later round
//!   or a later `check-sat` (the original hazard);
//! * **false `sat`** — the rebase throws away a fact that the SAT trail replay
//!   does *not* re-derive, so a genuinely unsatisfiable goal is answered `sat`.
//!
//! Every script below states its own model or refutation in the doc comment, so
//! the expected verdict is independent of the implementation.

use oxiz_solver::Context;

/// Run a script and return every `sat` / `unsat` / `unknown` line, in order.
fn verdicts(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(script)
        .expect("script should parse and run");
    out.into_iter()
        .filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .collect()
}

/// Run a script and return every output line (verdicts and values alike).
fn lines(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

// ---------------------------------------------------------------------------
// Direction 1: false `unsat` — leaked branch facts.
// ---------------------------------------------------------------------------

/// Bit-vectors: branch, observe, then pin the *other* branch.
///
/// Model of the final set: `x = #b0101`, `y = #b0111`.  `check_core` reset the
/// BV solver even before the fix, so this is the arm that must stay green
/// rather than one that used to fail — a regression here would mean the rebase
/// broke BV's own reset.
#[test]
fn bv_branch_then_pin_stays_sat() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (assert (or (= x #b0001) (= x #b0101)))
        (assert (or (= y #b0010) (= y #b0111)))
        (check-sat)
        (assert (= x #b0101))
        (check-sat)
        (assert (= y #b0111))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat", "sat"]);
}

/// Pure EUF over an uninterpreted sort: no arithmetic, no bit-vectors, so the
/// only solver that can leak is the congruence closure.
///
/// Final model: `a = c`, `b = d`, `a != b`.
#[test]
fn pure_euf_branch_then_pin_stays_sat() {
    let script = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (declare-const d U)
        (assert (or (= a c) (= a d)))
        (assert (or (= b c) (= b d)))
        (assert (not (= c d)))
        (check-sat)
        (assert (= a c))
        (check-sat)
        (assert (= b d))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat", "sat"]);
}

/// Five interleaved checks, each narrowing the set by one branch.  A leak that
/// only shows up after the *second* rebase — e.g. a seam that is crossed once
/// correctly and then desynchronises — would surface here and not in the
/// two-check reproductions.
///
/// Final model: `x = 5`, `y = 7`, `z = 9`, `w = 11`.
#[test]
fn five_narrowing_checks_stay_sat() {
    let script = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (declare-const w Int)
        (assert (or (= x 1) (= x 5)))
        (assert (or (= y 3) (= y 7)))
        (assert (or (= z 2) (= z 9)))
        (assert (or (= w 4) (= w 11)))
        (check-sat)
        (assert (= x 5))
        (check-sat)
        (assert (= y 7))
        (check-sat)
        (assert (= z 9))
        (check-sat)
        (assert (= w 11))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat", "sat", "sat", "sat"]);
}

/// Nested `push` / `pop` around checks, with a quantifier live throughout.
///
/// Every verdict is `sat`: at depth 2 the set is `x = 5 ∧ y = 7` over the
/// bounded universal `0 <= i <= 3 ⇒ f(i) >= 0`, satisfied by `f ≡ 0`; the pops
/// only remove constraints.
#[test]
fn nested_push_pop_with_quantifier_stays_sat() {
    let script = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (forall ((i Int)) (=> (and (>= i 0) (<= i 3)) (>= (f i) 0))))
        (assert (or (= x 1) (= x 5)))
        (assert (or (= y 2) (= y 7)))
        (check-sat)
        (push 1)
        (assert (= x 5))
        (check-sat)
        (push 1)
        (assert (= y 7))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    assert_eq!(
        verdicts(script),
        vec!["sat", "sat", "sat", "sat", "sat"],
        "every set here is satisfiable; a non-`sat` means leaked scope state"
    );
}

/// Arrays: a `store`/`select` chain forces array-axiom refinement rounds, which
/// are the third rebase seam.  Interposed checks must not change the verdict.
///
/// Final model: `a` arbitrary with `(select a 0) = 7`, `b = (store a 1 9)`,
/// so `(select b 0) = 7` and `(select b 1) = 9`.
#[test]
fn array_refinement_rounds_across_checks_stay_sat() {
    let script = r#"
        (set-logic QF_ALIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= b (store a 1 9)))
        (assert (or (= (select a 0) 7) (= (select a 0) 8)))
        (check-sat)
        (assert (= (select a 0) 7))
        (check-sat)
        (assert (= (select b 1) 9))
        (check-sat)
        (assert (= (select b 0) 7))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat", "sat", "sat"]);
}

/// Mixed theories in one goal: an integer branch, a bit-vector branch and an
/// uninterpreted function, so all three long-lived solvers hold branch state
/// when the first check returns.
///
/// Final model: `i = 5`, `v = #b0111`, `f(5) = 1`.
#[test]
fn mixed_int_bv_uf_multicheck_stays_sat() {
    let script = r#"
        (set-logic QF_UFBV)
        (declare-fun f (Int) Int)
        (declare-const i Int)
        (declare-const v (_ BitVec 4))
        (assert (or (= i 1) (= i 5)))
        (assert (or (= v #b0010) (= v #b0111)))
        (assert (or (= (f i) 1) (= (f i) 2)))
        (check-sat)
        (assert (= i 5))
        (assert (= v #b0111))
        (assert (= (f 5) 1))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat"]);
}

/// Reals with strict inequalities: the branch state lives in the simplex
/// tableau as strict bounds, whose retraction is the case most likely to be
/// mishandled by a partial unwind.
///
/// Final model: `x = 100.0`, `y = 100.0`.
#[test]
fn strict_real_bounds_multicheck_stays_sat() {
    let script = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (or (< x 0.0) (> x 10.0)))
        (assert (or (< y 0.0) (> y 10.0)))
        (check-sat)
        (assert (> x 99.0))
        (check-sat)
        (assert (> y 99.0))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat", "sat"]);
}

// ---------------------------------------------------------------------------
// Direction 2: false `sat` — facts the rebase must not throw away.
// ---------------------------------------------------------------------------

/// The rebase drops every theory-solver fact and re-derives it from the SAT
/// trail.  If a root-level fact is *not* re-derived, an unsatisfiable goal
/// becomes `sat`.  Here the refutation needs the very first assertion
/// (`x = 5`), which must survive an interposed check.
#[test]
fn interposed_check_must_not_lose_a_root_fact() {
    let script = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x 5))
        (assert (or (= y 1) (= y 2)))
        (check-sat)
        (assert (= x 6))
        (check-sat)
    "#;
    assert_eq!(
        verdicts(script),
        vec!["sat", "unsat"],
        "x = 5 and x = 6 are contradictory; a `sat` means the rebase lost the \
         root-level fact instead of replaying it"
    );
}

/// Same, for the bit-vector solver, whose base-level unit facts
/// (`assert_const`) are explicitly named in the rebase doc as state that is
/// dropped and must be re-derived.
#[test]
fn interposed_check_must_not_lose_a_bv_root_fact() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x #x05))
        (assert (or (= y #x01) (= y #x02)))
        (check-sat)
        (assert (= x #x06))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "unsat"]);
}

/// Same, for congruence closure: the refutation needs `f(a) = 1` and `a = b`
/// to combine with `f(b) = 2` across the rebase.
#[test]
fn interposed_check_must_not_lose_a_congruence_fact() {
    let script = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= (f a) 1))
        (assert (= a b))
        (assert (or (= c 3) (= c 4)))
        (check-sat)
        (assert (= (f b) 2))
        (check-sat)
    "#;
    assert_eq!(
        verdicts(script),
        vec!["sat", "unsat"],
        "f(a) = 1, a = b, f(b) = 2 is refuted by congruence"
    );
}

/// A refutation that needs a *quantifier instance* kept from an earlier MBQI
/// round to combine with a fact asserted after an interposed check.  This is
/// the category the rebase reasons about explicitly ("kept lemmas live in the
/// SAT clause database at the root"); if a kept lemma were lost with the
/// theory state, this would answer `sat`.
#[test]
fn interposed_check_must_not_lose_a_kept_instantiation() {
    let script = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const k Int)
        (assert (forall ((i Int)) (=> (and (>= i 0) (<= i 3)) (= (f i) 0))))
        (assert (or (= k 1) (= k 2)))
        (check-sat)
        (assert (= (f 1) 9))
        (assert (= k 1))
        (check-sat)
    "#;
    assert_eq!(
        verdicts(script),
        vec!["sat", "unsat"],
        "the universal forces f(1) = 0, contradicting f(1) = 9"
    );
}

/// Monotonicity across a rebase in the *unsat* direction: once a set is
/// refuted, adding assertions keeps it refuted.  A rebase that resurrected a
/// satisfying assignment from stale state would answer `sat` for the second.
#[test]
fn unsat_stays_unsat_across_further_checks() {
    let script = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 10))
        (assert (< x 5))
        (check-sat)
        (assert (or (= y 1) (= y 2)))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["unsat", "unsat"]);
}

// ---------------------------------------------------------------------------
// Direction 3: the model must survive the rebase, not just the verdict.
// ---------------------------------------------------------------------------

/// The rebase resets the arithmetic solver, which drops the variable interning
/// that `encode` performed once and — because the Tseitin memo is *not*
/// cleared — will never perform again.  If the trail replay does not re-intern
/// a variable, its model value silently degrades to a default.  Here every
/// value is forced, so a default is observable.
#[test]
fn model_values_survive_repeated_checks() {
    let script = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (assert (or (= x 1) (= x 5)))
        (assert (= y 42))
        (assert (= z (+ x y)))
        (check-sat)
        (assert (= x 5))
        (check-sat)
        (get-value (x y z))
    "#;
    let out = lines(script);
    let joined = out.join("\n");
    assert!(
        joined.contains('5') && joined.contains("42") && joined.contains("47"),
        "x = 5, y = 42, z = 47 must all appear after two checks; got:\n{joined}"
    );
}

/// A model produced *after* MBQI rounds have rebased the theory state must
/// still satisfy the ground assertions.
#[test]
fn quantified_model_values_survive_mbqi_rounds() {
    let script = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (assert (forall ((i Int)) (=> (and (>= i 0) (<= i 3)) (>= (f i) 0))))
        (assert (= x 7))
        (check-sat)
        (get-value (x))
    "#;
    let out = lines(script);
    let joined = out.join("\n");
    assert!(
        joined.contains("sat") && joined.contains('7'),
        "x must still evaluate to 7 after the MBQI rounds; got:\n{joined}"
    );
}

// ---------------------------------------------------------------------------
// Direction 4: seams the rebase does *not* cover.
// ---------------------------------------------------------------------------

/// `rebase_theory_state` resets EUF / arithmetic / bit-vector but deliberately
/// not the nonlinear solver, which is scoped by `Solver::push` / `pop` instead.
/// Probe that the nonlinear path is not leaking across checks the same way.
///
/// Final model: `x = 3.0`, `y = 9.0`.
#[test]
fn nonlinear_reals_multicheck_stays_sat() {
    let script = r#"
        (set-logic QF_NRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= y (* x x)))
        (assert (or (= x 2.0) (= x 3.0)))
        (check-sat)
        (assert (= x 3.0))
        (check-sat)
        (assert (= y 9.0))
        (check-sat)
    "#;
    let v = verdicts(script);
    assert!(
        v.iter().all(|r| r == "sat" || r == "unknown"),
        "no `unsat` is admissible here — x = 3, y = 9 is a model; got {v:?}"
    );
    assert_eq!(v.len(), 3);
}

/// Datatypes: `check_dt` runs its own axiom budget outside the CDCL(T) loop,
/// so it is a seam the rebase does not visit.  Interposed checks must still
/// not change the verdict.
#[test]
fn datatype_multicheck_stays_sat() {
    let script = r#"
        (set-logic QF_UFDT)
        (declare-datatypes ((Color 0)) (((red) (green) (blue))))
        (declare-const c Color)
        (declare-const d Color)
        (assert (or (= c red) (= c green)))
        (assert (or (= d green) (= d blue)))
        (check-sat)
        (assert (= c green))
        (check-sat)
        (assert (= d blue))
        (check-sat)
    "#;
    let v = verdicts(script);
    assert!(
        v.iter().all(|r| r == "sat" || r == "unknown"),
        "c = green, d = blue is a model; got {v:?}"
    );
}

/// A first check that forces *many* decisions, so many theory scopes are left
/// open, followed by a check that contradicts nearly all of them.  A rebase
/// that unwound only a bounded number of scopes would fail here and not on the
/// two-variable reproductions.
#[test]
fn deep_decision_stack_then_full_reversal_stays_sat() {
    let mut script = String::from("(set-logic QF_LIA)\n");
    for i in 0..12 {
        script.push_str(&format!("(declare-const v{i} Int)\n"));
        script.push_str(&format!("(assert (or (= v{i} 0) (= v{i} 1)))\n"));
    }
    script.push_str("(check-sat)\n");
    for i in 0..12 {
        script.push_str(&format!("(assert (= v{i} 1))\n"));
    }
    script.push_str("(check-sat)\n");
    for i in 0..12 {
        script.push_str(&format!("(assert (>= v{i} 1))\n"));
    }
    script.push_str("(check-sat)\n");
    assert_eq!(verdicts(&script), vec!["sat", "sat", "sat"]);
}

/// The same deep stack, but the second check is genuinely unsatisfiable: the
/// rebase must not lose so much that a real refutation disappears.
#[test]
fn deep_decision_stack_then_real_contradiction_is_unsat() {
    let mut script = String::from("(set-logic QF_LIA)\n");
    for i in 0..12 {
        script.push_str(&format!("(declare-const v{i} Int)\n"));
        script.push_str(&format!("(assert (or (= v{i} 0) (= v{i} 1)))\n"));
    }
    script.push_str("(check-sat)\n");
    script.push_str("(assert (= v0 1))\n(assert (= v0 0))\n(check-sat)\n");
    assert_eq!(verdicts(&script), vec!["sat", "unsat"]);
}

/// A quantified goal that needs several MBQI rounds, run twice in the same
/// context.  The second `check-sat` starts from a theory state the first left
/// behind *and* re-enters the MBQI loop, exercising both rebase seams in
/// sequence within one script.
#[test]
fn repeated_quantified_checks_stay_sat() {
    let script = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (forall ((i Int)) (=> (and (>= i 0) (<= i 5)) (and (>= (f i) 0) (<= (f i) 10)))))
        (assert (or (= x 0) (= x 3)))
        (assert (or (= y 1) (= y 4)))
        (check-sat)
        (check-sat)
        (assert (= x 3))
        (check-sat)
        (assert (= y 4))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat", "sat", "sat"]);
}

/// `check-sat` under assumptions goes through `Solver::push` / `assert` /
/// `check` / `Solver::pop` — the path whose EUF / arithmetic push was deleted
/// as part of this fix.  Repeating it must not accumulate state.
#[test]
fn repeated_assumption_checks_do_not_accumulate() {
    let script = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (or (= x 1) (= x 5)))
        (assert (or (= y 2) (= y 7)))
        (push 1) (assert (= x 1)) (check-sat) (pop 1)
        (push 1) (assert (= x 5)) (check-sat) (pop 1)
        (push 1) (assert (= y 2)) (check-sat) (pop 1)
        (push 1) (assert (= y 7)) (check-sat) (pop 1)
        (push 1) (assert (= x 1)) (assert (= y 7)) (check-sat) (pop 1)
        (check-sat)
    "#;
    assert_eq!(
        verdicts(script),
        vec!["sat", "sat", "sat", "sat", "sat", "sat"],
        "each branch is individually satisfiable; an `unsat` means a previous \
         assumption survived its `pop`"
    );
}

/// The mirror of the previous test in the `unsat` direction: a genuinely
/// contradictory assumption must still be refuted after several sound ones.
#[test]
fn assumption_checks_still_refute_a_real_contradiction() {
    let script = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (or (= x 1) (= x 5)))
        (push 1) (assert (= x 1)) (check-sat) (pop 1)
        (push 1) (assert (= x 5)) (check-sat) (pop 1)
        (push 1) (assert (= x 9)) (check-sat) (pop 1)
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat", "unsat", "sat"]);
}
