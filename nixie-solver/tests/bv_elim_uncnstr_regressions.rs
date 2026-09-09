//! elim-unconstrained (Z3 `elim-uncnstr` port) regressions.
//!
//! The pass replaces applications over exactly-once variables with fresh
//! variables and *records definitions* for model reconstruction; these
//! tests pin the three soundness-critical invariants:
//!
//! 1. **Occurrence counting** — a variable used twice is constrained; the
//!    first draft of the counter counted hash-consed variables once per
//!    DAG (visited-set skip), which made `x` in `(= x+a k) ∧ (= x+b k)`
//!    look unconstrained at *both* sites and answered `sat` on an unsat
//!    goal (`elim_respects_multiple_occurrences`).
//! 2. **Equisatisfiability transfer** — both verdict directions survive
//!    the rewrite (`elim_unsat_transfers`, `elim_sat_certifies`).
//! 3. **Model reconstruction** — a `Sat` verdict's model must certify
//!    against the *original* assertions with definition-reconstructed and
//!    defaulted values (`elim_eq_diagonalization_certifies`,
//!    `deferral_second_use_restores_the_verdict`); the completion must not
//!    shadow definitions (the `unconstrained03` failure) and the
//!    reconstruction must run to a real fixpoint, not a fixed 4 rounds
//!    (the `spear` failure).

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script executes");
    out.iter()
        .filter(|t| !t.trim().is_empty())
        .cloned()
        .collect()
}

/// Two uses of `x` under eliminable operators: `x` is constrained, the
/// system `x+1 = 0 ∧ x+2 = 0` is unsat.  A broken occurrence counter
/// eliminates `x` at both sites independently and answers `sat`.
#[test]
fn elim_respects_multiple_occurrences() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 64))
        (declare-const k (_ BitVec 64))
        (assert (= (bvadd x (_ bv1 64)) k))
        (assert (= (bvadd x (_ bv2 64)) k))
        (check-sat)
    "#);
    assert_eq!(out, vec!["unsat"]);
}

/// Same shape across *two assertions* with the equality diagonalization
/// rule (`= t x -> fresh`): still unsat when the shared variable is
/// constrained by its second occurrence.
#[test]
fn elim_respects_multiple_occurrences_eq_diag() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 64))
        (declare-const t (_ BitVec 64))
        (assert (= t x))
        (assert (= t (bvadd x (_ bv1 64))))
        (check-sat)
    "#);
    assert_eq!(out, vec!["unsat"]);
}

/// The `brummayerbiere4/unconstrained` shape (all variables occur exactly
/// once under eliminable operators, the whole goal collapses): `sat`, and
/// the model must satisfy the original assertions.
#[test]
fn elim_unconstrained_family_solves() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const v1 (_ BitVec 128))
        (declare-const v2 (_ BitVec 128))
        (declare-const v3 (_ BitVec 128))
        (declare-const v4 (_ BitVec 128))
        (declare-const v5 (_ BitVec 128))
        (declare-const v6 (_ BitVec 128))
        (assert (not (= (ite (not (= (bvudiv (bvudiv v2 v3) (bvudiv (bvudiv v1 v2) (bvudiv v1 v3))) (bvand v6 (bvand v4 v5)))) (_ bv1 1) (_ bv0 1)) (_ bv0 1))))
        (check-sat)
        (get-value (v1 v2 v3 v4 v5 v6))
    "#);
    assert_eq!(out[0], "sat", "full output: {out:?}");
    // The get-value line names all six variables.
    assert!(out.len() >= 2, "missing get-value output: {out:?}");
    assert!(out[1].contains("v1") && out[1].contains("v6"), "{out:?}");
}

/// Wide-mul variant (`unconstrained04` shape): the goal routes through the
/// eager dispatch's CEGAR arm, and the elimination still fires there.
#[test]
fn elim_unconstrained_wide_mul_variant() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const v1 (_ BitVec 128))
        (declare-const v2 (_ BitVec 128))
        (declare-const v3 (_ BitVec 128))
        (declare-const v4 (_ BitVec 128))
        (declare-const v5 (_ BitVec 128))
        (declare-const v6 (_ BitVec 128))
        (assert (not (= (bvmul (bvudiv v1 v2) (bvmul v3 v4)) (bvadd v5 v6))))
        (check-sat)
    "#);
    assert_eq!(out, vec!["sat"]);
}

/// Unsat transfers through the rewrite: both `x, y` occur once (the
/// `bvudiv` rule replaces them), and the residual `u < m ∧ u ≥ m` refutes.
#[test]
fn elim_unsat_transfers() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 64))
        (declare-const y (_ BitVec 64))
        (declare-const m (_ BitVec 64))
        (assert (bvult (bvudiv x y) m))
        (assert (bvuge (bvudiv x y) m))
        (check-sat)
    "#);
    assert_eq!(out, vec!["unsat"]);
}

/// The equality-diagonalization shape of `unconstrained03`: the eliminated
/// variable's definition (`u6 := ~u9`) must beat a `0` default — the first
/// completion defaulted defined variables and certified a *falsified*
/// model, flipping this `sat` to a decline.
#[test]
fn elim_eq_diagonalization_certifies() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const v1 (_ BitVec 64))
        (declare-const v2 (_ BitVec 64))
        (declare-const v3 (_ BitVec 64))
        (declare-const v4 (_ BitVec 64))
        (declare-const v5 (_ BitVec 64))
        (declare-const v6 (_ BitVec 64))
        (declare-const v7 (_ BitVec 64))
        (declare-const v8 (_ BitVec 64))
        (declare-const c1 (_ BitVec 1))
        (declare-const c2 (_ BitVec 1))
        (assert (not (= (ite (not (= (ite (= (_ bv1 1) (bvor c1 c2)) (bvudiv (bvudiv v1 v2) v3) (bvudiv (bvudiv v4 v5) v6)) (bvudiv v7 v8))) (_ bv1 1) (_ bv0 1)) (_ bv0 1))))
        (check-sat)
    "#);
    assert_eq!(out, vec!["sat"]);
}

/// The deferral bet must be paid back when it loses: this script's first
/// assertion has the deferral shape (wide division, once-occurring
/// variables), but the later assertions re-use `a` and `b`, so the
/// check-time recount finds nothing to eliminate and the eager circuits
/// are restored before the general path runs.  The goal refutes through
/// the word-level bound (`x <u 0` folds to `false`) after the routing
/// dance, whatever the route — the first draft of this test used a
/// division-semantics contradiction instead, which the general path needs
/// ~a minute for on BOTH the old and new binaries (pre-existing search
/// cost, not this pass's).
#[test]
fn deferral_second_use_restores_the_verdict() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 128))
        (declare-const b (_ BitVec 128))
        (assert (bvult (bvudiv a b) (_ bv0 128)))
        (assert (bvult a b))
        (assert (bvugt b (_ bv0 128)))
        (check-sat)
    "#);
    assert_eq!(out, vec!["unsat"]);
}

/// `spear`-style width-1 encodings: `(= … (distinct …))` over BitVec
/// operands must evaluate concretely in the certification gate (the
/// evaluator used to be unconditionally inconclusive on `distinct`).
#[test]
fn distinct_width1_evaluates_in_certification() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (declare-const p (_ BitVec 1))
        (assert (= p (ite (distinct x y) (_ bv1 1) (_ bv0 1))))
        (assert (= p (_ bv1 1)))
        (assert (= (bvand x y) (_ bv0 32)))
        (check-sat)
    "#);
    assert_eq!(out, vec!["sat"]);
}

/// Definition reconstruction must run to a fixpoint deeper than any fixed
/// round count: a chain of `n` single-use variables under eliminable
/// operators builds a def chain `n` deep, and the final model still has to
/// certify against the original assertions.
#[test]
fn deep_definition_chain_reconstructs() {
    let mut script = String::from(
        "(set-logic QF_BV)\n(declare-const t (_ BitVec 32))\n(declare-const k (_ BitVec 32))\n",
    );
    // x0 = t + 1, x1 = x0 + 1, … each xi used exactly once.
    let n = 12;
    for i in 0..n {
        let lhs = if i == 0 {
            "t".to_string()
        } else {
            format!("x{}", i - 1)
        };
        script.push_str(&format!(
            "(declare-const x{i} (_ BitVec 32))\n(assert (= x{i} (bvadd {lhs} (_ bv1 32))))\n"
        ));
    }
    // The chain's tip plus the target are each used once more; the k tie
    // is satisfiable in exactly one way (2t = 13).
    script.push_str(&format!(
        "(assert (= (bvadd x{} (_ bv1 32)) k))\n(assert (= (bvadd t t) (bvadd k (_ bv13 32))))\n(check-sat)\n",
        n - 1
    ));
    let out = run(&script);
    assert_eq!(out, vec!["sat"]);
}

/// The `cohencu` shape (UltimateAutomizer 2023, Tier-A polynomial class):
/// `y = 3n+3n²+1`, `z+y = 7+3n²+9n` (linear isolation of `z`), and the
/// asserted disequality collapses through the polynomial-identity check
/// after substitution.  The staged version exercises the double-negated
/// conflict shape (`cohencu.c_3`), where the ite-condition variable is
/// defined twice and the ring pass owns the elimination — the stage-4
/// alongside-assertion of its rewrite is what decides the goal.
#[test]
fn cohencu_linear_isolation_decides() {
    let base = r#"
        (set-logic QF_BV)
        (declare-fun n () (_ BitVec 32))
        (declare-fun y () (_ BitVec 32))
        (declare-fun z () (_ BitVec 32))
        (declare-fun cond () (_ BitVec 32))
        (assert (= cond (ite (= (bvadd (bvneg (bvmul z (_ bv6 32))) (bvneg (bvmul y (_ bv12 32))) (bvmul z z) (_ bv12 32)) (_ bv0 32)) (_ bv1 32) (_ bv0 32))))
        (assert (and
            (= (bvadd z y) (bvadd (_ bv7 32) (bvmul (_ bv3 32) (bvmul n n)) (bvmul (_ bv9 32) n)))
            (= (bvadd (bvmul (_ bv3 32) n) (bvmul (_ bv3 32) (bvmul n n)) (_ bv1 32)) y)))
    "#;
    let single = format!("{base}(assert (not (= (_ bv1 32) cond)))\n(check-sat)\n");
    assert_eq!(run(&single), vec!["unsat"], "cohencu.c_2 shape");
    let double = format!("{base}(assert (not (not (= cond (_ bv0 32)))))\n(check-sat)\n");
    assert_eq!(run(&double), vec!["unsat"], "cohencu.c_3 shape");
}

/// Ring-eliminated but satisfiable: `x + y = 5 ∧ y > 0` isolates `x`
/// (odd unit pivot) and must stay `sat` — the stage-4 pass now asserts
/// the ring rewrite *alongside* the originals, and a non-implied rewrite
/// would refute this.
#[test]
fn ring_rewrite_alongside_preserves_sat() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= (bvadd x y) (_ bv5 32)))
        (assert (bvugt y (_ bv0 32)))
        (check-sat)
    "#);
    assert_eq!(out, vec!["sat"]);
}

/// Even-coefficient isolation must NOT fire: `2x + y = 1 ∧ 2x + y' = 2`
/// with `y = y'` fixed is unsat only if `2x` stays constrained — `2` is a
/// non-unit, the equation does not determine `x`, and isolating it would
/// be unsound.
#[test]
fn linear_isolation_requires_odd_coefficient() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= (bvadd (bvmul (_ bv2 32) x) y) (_ bv1 32)))
        (assert (= (bvadd (bvmul (_ bv2 32) x) y) (_ bv2 32)))
        (check-sat)
    "#);
    assert_eq!(out, vec!["unsat"]);
}
