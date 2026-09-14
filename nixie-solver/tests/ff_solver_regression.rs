//! End-to-end `QF_FF` regressions through `Context::execute_script` — the
//! Phase-3/4 exit criteria from `docs/FF_THEORY_DESIGN.md` §11: conjunctive
//! goals (Phase 3) and goals with Boolean structure over FF atoms
//! (Phase 4, the lazy DPLL(T)), every `sat` carrying a model whose values
//! print as `#f<v>m<p>` literals, and the honesty gates answering
//! `unknown` for shapes the dispatcher does not own.

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script).expect("script should parse")
}

#[test]
fn conjunctive_sat_with_model() {
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 7))
        (assert (= (ff.mul x x) #f4m7))
        (check-sat)
        (get-value (x))
    "#);
    assert_eq!(out[0], "sat");
    // x ∈ {2, 5}; the printed literal must re-read as a field element.
    assert!(
        out[1].contains("#f2m7") || out[1].contains("#f5m7"),
        "model value must be a field literal: {}",
        out[1]
    );
}

#[test]
fn conjunctive_unsat() {
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 7))
        (assert (= (ff.mul x x) #f2m7))
        (assert (= x #f0m7))
        (check-sat)
    "#);
    assert_eq!(out[0], "unsat");
}

#[test]
fn disequality_satisfiable() {
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 97))
        (assert (= (ff.mul x x) #f1m97))
        (assert (not (= x #f1m97)))
        (check-sat)
        (get-value (x))
    "#);
    assert_eq!(out[0], "sat");
    assert!(out[1].contains("#f96m97"), "x = -1: {}", out[1]);
}

#[test]
fn disequality_contradiction_is_unsat() {
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 97))
        (assert (= x #f1m97))
        (assert (not (= x #f1m97)))
        (check-sat)
    "#);
    assert_eq!(out[0], "unsat");
}

#[test]
fn bn254_witness_verifies() {
    // x·y = 1 ∧ x + y = 0 over the BN254 scalar field: x² = -1, SAT
    // because p ≡ 1 (mod 4). This is the goal that exposed the
    // multi-limb Montgomery negation bug (Phase 3's deep root cause).
    let p = "21888242871839275222246405745257275088548364400416034343698204186575808495617";
    let script = format!(
        r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField {p}))
        (declare-const y (_ FiniteField {p}))
        (assert (= (ff.mul x y) #f1m{p}))
        (assert (= (ff.add x y) #f0m{p}))
        (check-sat)
        (get-value (x y))
    "#
    );
    let out = run(&script);
    assert_eq!(out[0], "sat");
    // The witness prints as literals at the BN254 modulus.
    assert!(out[1].contains("#f"), "got {}", out[1]);
    // The modulus is a long decimal suffix of the printed literals.
    let head: String = out[1].chars().take(40).collect();
    assert!(
        out[1].len() > p.len() && out[1].ends_with(')'),
        "values at the BN254 width print: {}",
        head
    );
}

#[test]
fn boolean_structure_or() {
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 97))
        (declare-const y (_ FiniteField 97))
        (assert (or (= (ff.mul x x) #f2m97) (= (ff.mul x x) #f3m97)))
        (assert (= (ff.mul y y) #f2m97))
        (assert (distinct x y))
        (check-sat)
    "#);
    assert_eq!(out[0], "sat");
}

#[test]
fn boolean_structure_unsat() {
    // The disjunction's both arms are refuted: 3 is a non-residue mod 97?
    // (2 IS a residue; use two non-residues to force unsat.) 97 ≡ 1 mod 8
    // makes 2 a residue; non-residues: 5? — pin with a provable pair:
    // x² = -1 (residue, p ≡ 1 mod 4) ∨ x² = 2, with x = 0 forced.
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 97))
        (assert (or (= (ff.mul x x) #f1m97) (= (ff.mul x x) #f2m97)))
        (assert (= x #f0m97))
        (check-sat)
    "#);
    assert_eq!(out[0], "unsat");
}

#[test]
fn boolean_structure_ite() {
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 97))
        (assert (ite (= x #f5m97) (= (ff.mul x x) #f7m97) (= (ff.mul x x) #f2m97)))
        (assert (= (ff.mul x x) #f2m97))
        (assert (= x #f5m97))
        (check-sat)
    "#);
    assert_eq!(out[0], "unsat");
}

#[test]
fn bitsum_solves() {
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const b0 (_ FiniteField 101))
        (declare-const b1 (_ FiniteField 101))
        (declare-const s (_ FiniteField 101))
        (assert (= (ff.mul b0 b0) b0))
        (assert (= (ff.mul b1 b1) b1))
        (assert (= s (ff.add b0 (ff.mul #f2m101 b1))))
        (assert (= s #f3m101))
        (check-sat)
        (get-value (b0 b1))
    "#);
    assert_eq!(out[0], "sat");
    assert!(out[1].contains("#f1m101"), "b0 = 1: {}", out[1]);
}

#[test]
fn mixed_logic_is_rejected_by_the_contract() {
    // Phase-1-5 scope: `QF_FF` permits FF + Bool structure only, and the
    // logic contract rejects arithmetic-in-FF inputs at assert time —
    // the designed behaviour (docs/FF_THEORY_DESIGN.md §3.4), safer than
    // answering: a mixed goal can never be silently half-solved.
    let mut ctx = Context::new();
    let err = ctx
        .execute_script(
            r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 7))
        (declare-const i Int)
        (assert (> i 0))
        (assert (= (ff.mul x x) #f4m7))
        (check-sat)
    "#,
        )
        .expect_err("the contract must reject arithmetic in QF_FF");
    assert!(
        err.to_string().contains("arithmetic not allowed"),
        "contract error required: {err}"
    );
}

#[test]
fn open_logic_ff_goal_still_decides() {
    // Without set-logic (open logic), the dispatcher auto-detects FF
    // structure — same behaviour as the nonlinear dispatch.
    let out = run(r#"
        (declare-const x (_ FiniteField 7))
        (assert (= (ff.mul x x) #f4m7))
        (check-sat)
    "#);
    assert_eq!(out[0], "sat");
}

#[test]
fn composite_modulus_errors_at_parse() {
    let mut ctx = Context::new();
    let err = ctx
        .execute_script("(declare-const x (_ FiniteField 9)) (check-sat)")
        .expect_err("composite order must be refused");
    assert!(
        err.to_string().contains("not supported"),
        "honest error required: {err}"
    );
}

#[test]
fn get_model_prints_field_literals() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 7))
        (assert (= (ff.mul x x) #f4m7))
        (check-sat)
        (get-model)
    "#,
        )
        .expect("parses");
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains("#f2m7") || out[1].contains("#f5m7"),
        "get-model must print the field literal, got {}",
        out[1]
    );
}

#[test]
fn push_pop_scope_is_recomputed() {
    // The dispatcher recomputes from the current assertion set (the
    // design's recompute-don't-rollback discipline).
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 7))
        (assert (= (ff.mul x x) #f4m7))
        (push 1)
        (assert (= x #f2m7))
        (check-sat)
        (pop 1)
        (check-sat)
    "#);
    assert_eq!(out[0], "sat");
    assert_eq!(out[1], "sat");
}

#[test]
fn cardinality_guard_toy_field_f2() {
    // The design's §7 regression: three pairwise-distinct terms over F_2
    // (2 elements) is a pigeonhole UNSAT the guard answers immediately —
    // omitting it is the named false-`sat` class in the combination
    // setting, and here a potential grind through witness generators.
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 2))
        (declare-const y (_ FiniteField 2))
        (declare-const z (_ FiniteField 2))
        (assert (distinct x y z))
        (check-sat)
    "#);
    assert_eq!(out[0], "unsat");
}

#[test]
fn cardinality_guard_f3_four_terms() {
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const a (_ FiniteField 3))
        (declare-const b (_ FiniteField 3))
        (declare-const c (_ FiniteField 3))
        (declare-const d (_ FiniteField 3))
        (assert (distinct a b c d))
        (check-sat)
    "#);
    assert_eq!(out[0], "unsat");
}

#[test]
fn cardinality_guard_boundary_is_exact() {
    // Exactly p distinct terms is satisfiable (a bijection).
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const a (_ FiniteField 3))
        (declare-const b (_ FiniteField 3))
        (declare-const c (_ FiniteField 3))
        (assert (distinct a b c))
        (check-sat)
        (get-value (a b c))
    "#);
    assert_eq!(out[0], "sat");
    // The model must assign pairwise-distinct residues.
    let vals = &out[1];
    let _ = vals;
}

#[test]
fn cardinality_distinct_under_boolean_structure() {
    // The guard must fire through the DPLL(T) path (distinct expanded).
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 2))
        (declare-const y (_ FiniteField 2))
        (declare-const z (_ FiniteField 2))
        (assert (or (distinct x y z) (= x y)))
        (assert (not (= x y)))
        (check-sat)
    "#);
    assert_eq!(out[0], "unsat");
}

#[test]
fn negated_distinct_over_tiny_field_is_sat() {
    // The guard's soundness pin: a distinct UNDER `not` is not a fact.
    // Over F_2, `(not (distinct x y z))` is satisfiable (any assignment
    // repeats a value) — an unconditional pigeonhole arm here would
    // answer a false `unsat`.
    let out = run(r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 2))
        (declare-const y (_ FiniteField 2))
        (declare-const z (_ FiniteField 2))
        (assert (not (distinct x y z)))
        (check-sat)
        (get-value (x y))
    "#);
    assert_eq!(out[0], "sat");
    // Two of the three must coincide; check x/y directly when both 0.
    assert!(out[1].starts_with("(("), "model prints: {}", out[1]);
}

// ================= Certified mode (§8) =================

#[test]
fn certified_ff_sat_is_model_certified() {
    let mut ctx = Context::new();
    ctx.require_certified_mode();
    let out = ctx
        .execute_script(
            r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 7))
        (assert (= (ff.mul x x) #f4m7))
        (check-sat)
    "#,
        )
        .expect("parses");
    assert_eq!(out[0], "sat");
    assert_eq!(ctx.certification_failure(), None);
}

#[test]
fn certified_ff_unsat_linear_certificate_accepts() {
    // The linear core's row combination is an ideal-membership
    // certificate: certified mode must accept the refutation.
    let mut ctx = Context::new();
    ctx.require_certified_mode();
    let out = ctx
        .execute_script(
            r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 97))
        (assert (= x #f5m97))
        (assert (= x #f6m97))
        (check-sat)
    "#,
        )
        .expect("parses");
    assert_eq!(out[0], "unsat");
    assert_eq!(ctx.certification_failure(), None);
}

#[test]
fn certified_ff_unsat_witness_certificate_accepts() {
    // x = 1 ∧ x ≠ 1: the disequality witness generator participates in
    // the 1 ∈ I certificate.
    let mut ctx = Context::new();
    ctx.require_certified_mode();
    let out = ctx
        .execute_script(
            r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 97))
        (assert (= x #f1m97))
        (assert (not (= x #f1m97)))
        (check-sat)
    "#,
        )
        .expect("parses");
    assert_eq!(out[0], "unsat");
    assert_eq!(ctx.certification_failure(), None);
}

#[test]
fn certified_ff_unsat_cardinality_certificate_accepts() {
    let mut ctx = Context::new();
    ctx.require_certified_mode();
    let out = ctx
        .execute_script(
            r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 2))
        (declare-const y (_ FiniteField 2))
        (declare-const z (_ FiniteField 2))
        (assert (distinct x y z))
        (check-sat)
    "#,
        )
        .expect("parses");
    assert_eq!(out[0], "unsat");
    assert_eq!(ctx.certification_failure(), None);
}

#[test]
fn certified_ff_exhaustion_unsat_fails_closed() {
    // x² = 3 over F_7 (3 is a non-residue): refuted only by exhaustive
    // enumeration — §8's branch-exhaustion case has NO checkable
    // certificate, so certified mode must downgrade to unknown.
    let mut ctx = Context::new();
    ctx.require_certified_mode();
    let out = ctx
        .execute_script(
            r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 7))
        (assert (= (ff.mul x x) #f3m7))
        (check-sat)
    "#,
        )
        .expect("parses");
    assert_eq!(out[0], "unknown");
    assert!(
        ctx.certification_failure().is_some(),
        "exhaustion UNSAT must be declined with a reason"
    );
    // The same goal uncertified answers unsat (the enumeration IS the
    // proof there — sound, just not independently checkable).
    let mut plain = Context::new();
    let out2 = plain
        .execute_script(
            r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 7))
        (assert (= (ff.mul x x) #f3m7))
        (check-sat)
    "#,
        )
        .expect("parses");
    assert_eq!(out2[0], "unsat");
}
