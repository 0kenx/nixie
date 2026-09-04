//! Regression tests for the independently-reimplemented EUF congruence-closure
//! soundness fixes (upstream PR #28) and Bool/EUF encoding fixes (upstream PR
//! #29) against cool-japan/nixie.
//!
//! Lower-level, mechanism-specific tests for the same fixes live next to the
//! code they exercise:
//! * `nixie-theories/src/euf/solver/tests.rs` -- `test_pr28_*` (sig-table
//!   staleness, the disequality watch-list, and the proof-forest spanning-
//!   forest invariant that makes PR28-4's stamped explanations unnecessary
//!   here).
//! * `nixie-solver/src/solver/encode/bool_euf_encoding/tests.rs` -- structural
//!   tests of the two rewrite passes themselves, including the
//!   quantifier-opacity guard and the narrow `encode_nonbool_ite_equality`
//!   backstop in isolation.
//!
//! This file covers the fixes whose defining property is only visible
//! end-to-end: does the *whole solver*, driven exactly as an SMT-LIB2 client
//! would drive it, answer `sat`/`unsat` correctly.

use nixie_solver::Context;

/// Run `script` through a fresh [`Context`], returning its output lines.
fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

/// PR29-2 root cause, reproduced at the shape the mission calls out
/// (`firewire_tree`-style: an `ite` selecting between two uninterpreted-sort
/// constants sits *underneath* a UF application, not as a bare equality
/// operand).
///
/// `g(u1) = f(ite c u2 u3)`, `not c`, so the `ite` must equal `u3`, so
/// congruence forces `g(u1) = f(u3)` -- contradicting a separately asserted
/// `g(u1) != f(u3)`. Left as an opaque EUF leaf, the `ite` breaks that chain
/// and the formula reports a spurious `sat`.
#[test]
fn test_pr29_nonbool_ite_under_uf_argument_false_sat() {
    let mut ctx = Context::new();
    let script = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const u1 U)
        (declare-const u2 U)
        (declare-const u3 U)
        (declare-const c Bool)
        (declare-fun f (U) U)
        (declare-fun g (U) U)
        (assert (= (g u1) (f (ite c u2 u3))))
        (assert (not c))
        (assert (not (= (g u1) (f u3))))
        (check-sat)
    "#;
    let output = ctx.execute_script(script).expect("script should parse");
    assert_eq!(
        output,
        vec!["unsat"],
        "a non-Bool ite nested under a UF argument must not hide the \
         conditional equality from congruence closure"
    );
}

/// Companion satisfiable control for the previous test: flipping `c` to
/// `true` selects `u2` instead, so `g(u1) = f(u2)`, which is consistent with
/// `g(u1) != f(u3)` as long as `u2 != u3`. Guards against the fix
/// over-constraining the formula into an unconditional (wrong) `unsat`.
#[test]
fn test_pr29_nonbool_ite_under_uf_argument_stays_sat_when_consistent() {
    let mut ctx = Context::new();
    let script = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const u1 U)
        (declare-const u2 U)
        (declare-const u3 U)
        (declare-const c Bool)
        (declare-fun f (U) U)
        (declare-fun g (U) U)
        (assert (= (g u1) (f (ite c u2 u3))))
        (assert c)
        (assert (not (= u2 u3)))
        (assert (not (= (g u1) (f u3))))
        (check-sat)
    "#;
    let output = ctx.execute_script(script).expect("script should parse");
    assert_eq!(output, vec!["sat"]);
}

/// PR29-1 + PR29-3 combined: two independent Bool variables the SAT
/// assignment forces to the same truth value must be recognised as EUF-equal
/// so that congruence fires over a Bool-argument-taking UF -- whether that
/// equality reaches EUF via the direct `(= b1 b2)` theory constraint or via
/// Bool completion (both variables merging with the same canonical
/// true/false node), previously *neither* path existed: a Bool-sorted
/// equality was only ever Tseitin-encoded as an iff gate, and a plain Bool
/// `Var` was never registered for completion at all.
#[test]
fn test_pr29_bool_vars_forced_equal_enable_uf_congruence() {
    let mut ctx = Context::new();
    let script = r#"
        (set-logic QF_UF)
        (declare-const b1 Bool)
        (declare-const b2 Bool)
        (declare-fun h (Bool) Int)
        (assert b1)
        (assert b2)
        (assert (= (h b1) 1))
        (assert (not (= (h b2) 1)))
        (check-sat)
    "#;
    let output = ctx.execute_script(script).expect("script should parse");
    assert_eq!(
        output,
        vec!["unsat"],
        "b1 and b2 both forced true must be recognised as EUF-equal, forcing \
         h(b1) = h(b2) by congruence"
    );
}

/// Mechanistic isolation of PR29-1: `(= b1 b2)` must be registered as a real
/// EUF theory constraint, not merely an SAT-level iff gate. `b1`/`b2` here
/// are never SAT-decided to a *concrete* value on their own (nothing forces
/// either one true or false individually), so Bool completion (PR29-3) has
/// nothing to merge them with -- only the direct `Constraint::Eq` on the
/// equality itself can tell EUF `b1 = b2`.
#[test]
fn test_pr29_bool_eq_alone_without_concrete_polarity_enables_congruence() {
    let mut ctx = Context::new();
    let script = r#"
        (set-logic QF_UF)
        (declare-const b1 Bool)
        (declare-const b2 Bool)
        (declare-fun h (Bool) Int)
        (assert (= b1 b2))
        (assert (= (h b1) 1))
        (assert (not (= (h b2) 1)))
        (check-sat)
    "#;
    let output = ctx.execute_script(script).expect("script should parse");
    assert_eq!(
        output,
        vec!["unsat"],
        "(= b1 b2) must reach EUF as a theory constraint so h(b1) = h(b2) \
         follows by congruence"
    );
}

/// PR29-4: a *compound* Bool argument (`(and p q)`, not a plain `Var` or an
/// `Apply`) passed to a UF must be abstracted into a fresh completed
/// variable, or it never participates in Bool completion at all and the
/// congruence with a plain-variable argument of the same truth value is
/// missed.
#[test]
fn test_pr29_compound_bool_uf_argument_abstraction() {
    let mut ctx = Context::new();
    let script = r#"
        (set-logic QF_UF)
        (declare-const p Bool)
        (declare-const q Bool)
        (declare-const b2 Bool)
        (declare-fun h (Bool) Int)
        (assert p)
        (assert q)
        (assert b2)
        (assert (= (h (and p q)) 1))
        (assert (not (= (h b2) 1)))
        (check-sat)
    "#;
    let output = ctx.execute_script(script).expect("script should parse");
    assert_eq!(
        output,
        vec!["unsat"],
        "(and p q), forced true, must be abstracted and completed so it \
         merges with the equally-true b2 in EUF"
    );
}

/// PR29-5 (O(n^2) -> O(n) EUF-to-arith propagation): correctness check, not
/// merely a performance one. `a = b` puts `f(a)` and `f(b)` in the same EUF
/// class by congruence; the arithmetic solver only knows `f(a)`/`f(b)` as
/// opaque Int atoms and needs EUF to propagate that class-membership across,
/// or the contradiction between `f(a) = 5` and `f(b) != 5` is invisible to
/// it. The class-bucketing rewrite must still find this pair.
#[test]
fn test_pr29_euf_to_arith_propagation_still_finds_same_class_pair() {
    let mut ctx = Context::new();
    let script = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const other Int)
        (assert (= a b))
        (assert (= (f a) 5))
        (assert (= other 10))
        (assert (not (= (f b) 5)))
        (check-sat)
    "#;
    let output = ctx.execute_script(script).expect("script should parse");
    assert_eq!(output, vec!["unsat"]);
}

/// Companion control: two arithmetic terms whose EUF classes are genuinely
/// different must *not* have an equality spuriously propagated between them.
/// A class-bucketing bug that puts unrelated terms in one bucket (e.g. an
/// off-by-one on the representative) would show up here as a wrong `unsat`.
#[test]
fn test_pr29_euf_to_arith_propagation_does_not_cross_classes() {
    let mut ctx = Context::new();
    let script = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const c Int)
        (assert (not (= a c)))
        (assert (= (f a) 5))
        (assert (not (= (f c) 5)))
        (check-sat)
    "#;
    let output = ctx.execute_script(script).expect("script should parse");
    assert_eq!(
        output,
        vec!["sat"],
        "a and c are in different EUF classes; f(a) = 5 must not force f(c)"
    );
}

/// PR28-2: the rebuild-and-recheck soundness backstop must not turn a
/// genuinely satisfiable, function-bearing formula into a spurious `unsat`,
/// and the model it leaves behind after replaying the shadow trail must
/// still be one this solver's own model-verification gate accepts (`check`
/// only ever returns `Sat` after verifying the model refutes no assertion --
/// see `Solver::model_refutes_assertions`). Exercised across a `push`/`pop`
/// and a second `check-sat`, so the backstop runs more than once against
/// state that has already been incrementally rebuilt at least once.
#[test]
fn test_pr28_backstop_preserves_sat_with_valid_model_across_push_pop() {
    let mut ctx = Context::new();
    let script = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (declare-fun f (U) U)
        (declare-fun g (U) U)
        (assert (= (f a) b))
        (assert (not (= a c)))
        (push 1)
        (assert (= a b))
        (assert (= (g (f a)) (g b)))
        (check-sat)
        (pop 1)
        (assert (not (= (f a) (f c))))
        (check-sat)
        (get-model)
    "#;
    let output = ctx.execute_script(script).expect("script should parse");
    assert_eq!(
        output[0], "sat",
        "first check-sat (inside the push) must be sat"
    );
    assert_eq!(
        output[1], "sat",
        "second check-sat (after pop, with UF content) must still be sat -- \
         has_app_nodes() gates the backstop on exactly this shape"
    );
    // `get-model` must have produced a real, non-empty model -- not an
    // internal-error placeholder from a corrupted rebuild.
    assert!(
        output.len() > 2 && !output[2].trim().is_empty(),
        "get-model must return a real model after the backstop ran: {output:?}"
    );
}

// ========  ========
// PR28 backstop, lazy theory mode: the rebuild must not run where there is
// no shadow trail to rebuild *from*.
// ========  ========

/// Lazy-mode twin of
/// `pr30_soundness::test_pr30_purified_uf_arg_entailed_equality_false_sat`.
///
/// The PR28 final-check backstop resets EUF/arith/BV and replays
/// `TheoryManager::assignment_trail`. That trail is populated by
/// `on_assignment`'s eager path only: under `:theory-mode lazy`,
/// `on_assignment` returns at its `TheoryMode::Lazy` branch before the
/// trail-append arm ever runs, and the lazy `final_check` loop appends
/// nothing either. Running the backstop there therefore reset the three
/// theory solvers and replayed *nothing*, discarding every fact the lazy
/// loop had just asserted -- and this script, whose refutation needs the
/// arithmetic chain `x = 2`, `y = x + 1` to reach EUF congruence, came back
/// `sat`. The backstop is now gated on eager mode; lazy keeps the
/// incremental behaviour it had before the backstop existed.
#[test]
fn test_pr28_backstop_lazy_mode_keeps_entailed_congruence_unsat() {
    let output = run(r#"
        (set-option :theory-mode lazy)
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x 2))
        (assert (= y (+ x 1)))
        (assert (not (= (f y) (f 3))))
        (check-sat)
    "#);
    assert_eq!(
        output,
        vec!["unsat"],
        "lazy mode must reach the same verdict as eager: arithmetic entails \
         y = 3, so f(y) != f(3) is refuted by congruence"
    );
}

/// Satisfiable control for the gate above: gating the backstop out of lazy
/// mode must not be achieved by making lazy mode over-constrain instead.
/// Here the chain entails `y = 4`, so `f(y) != f(3)` is perfectly consistent
/// and lazy mode must still say `sat` -- with a usable model, proving the
/// theory state survived the final check rather than being wiped.
#[test]
fn test_pr28_backstop_lazy_mode_stays_sat_when_not_entailed() {
    let mut ctx = Context::new();
    let output = ctx
        .execute_script(
            r#"
        (set-option :theory-mode lazy)
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x 2))
        (assert (= y (+ x 2)))
        (assert (not (= (f y) (f 3))))
        (check-sat)
        (get-model)
    "#,
        )
        .expect("script should parse and run");
    assert_eq!(output[0], "sat");
    assert!(
        output.len() > 1 && !output[1].trim().is_empty(),
        "get-model must return a real model in lazy mode: {output:?}"
    );
}

/// Lazy mode must also still find a *purely arithmetic* refutation in the
/// presence of UF content (`has_app_nodes()` is true here, which is what
/// used to send lazy mode down the wiping backstop path). `x >= 1`,
/// `y >= 0` and `x + y <= 0` are jointly infeasible.
#[test]
fn test_pr28_backstop_lazy_mode_keeps_arith_conflict_unsat() {
    let output = run(r#"
        (set-option :theory-mode lazy)
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (<= (+ x y) 0))
        (assert (>= x 1))
        (assert (>= y 0))
        (assert (= (f x) 0))
        (check-sat)
    "#);
    assert_eq!(output, vec!["unsat"]);
}
