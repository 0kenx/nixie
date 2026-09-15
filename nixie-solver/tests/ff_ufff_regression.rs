//! End-to-end `QF_UFFF` regressions — the Phase-6-remainder exit
//! criteria from `docs/FF_THEORY_DESIGN.md` §11: FF ⊕ EUF by polite
//! combination, every `sat` carrying a congruence-consistent model,
//! congruence and cardinality refutations answering `unsat`, and the
//! honesty gates (`unknown`) for shapes the combination does not own.
//! Certified mode: `sat` must certify through the independent model
//! evaluator (which re-checks function-hood via
//! `check_application_congruence`); combination `unsat`s have no
//! self-contained certificate and must downgrade to `unknown`.

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    match ctx.execute_script(script) {
        Ok(o) => o,
        // A command error (e.g. a contract violation) is the script's
        // outcome line for these tests.
        Err(e) => vec![format!("(error {e:?})")],
    }
}

#[test]
fn congruence_unsat() {
    // x = y ∧ f(x) = 3 ∧ f(y) ≠ 3: congruence closes the trap.
    let out = run(r#"
        (set-logic QF_UFFF)
        (declare-fun f ((_ FiniteField 7)) (_ FiniteField 7))
        (declare-const x (_ FiniteField 7))
        (declare-const y (_ FiniteField 7))
        (assert (= x y))
        (assert (= (f x) #f3m7))
        (assert (not (= (f y) #f3m7)))
        (check-sat)
    "#);
    assert_eq!(out[0], "unsat");
}

#[test]
fn congruence_through_compound_arguments() {
    // The FF side proves x + y = 5; the arrangement machinery must then
    // know f(x+y) and f(5) are the same function value. This is the
    // case that requires the model-guided case tree (EUF cannot do the
    // arithmetic; the FF model's arrangement supplies it).
    let out = run(r#"
        (set-logic QF_UFFF)
        (declare-fun f ((_ FiniteField 7)) (_ FiniteField 7))
        (declare-const x (_ FiniteField 7))
        (declare-const y (_ FiniteField 7))
        (assert (= (f (ff.add x y)) #f1m7))
        (assert (= x #f2m7))
        (assert (= y #f3m7))
        (assert (not (= (f #f5m7) #f1m7)))
        (check-sat)
    "#);
    assert_eq!(out[0], "unsat");
}

#[test]
fn arithmetic_over_applications_sat() {
    let out = run(r#"
        (set-logic QF_UFFF)
        (declare-fun f ((_ FiniteField 7)) (_ FiniteField 7))
        (declare-const x (_ FiniteField 7))
        (declare-const y (_ FiniteField 7))
        (assert (not (= (f x) (f y))))
        (assert (= (ff.add (f x) (f y)) #f5m7))
        (assert (= x #f1m7))
        (check-sat)
        (get-value (x y (f x) (f y)))
    "#);
    assert_eq!(out[0], "sat");
    // The model must be function-consistent: distinct results imply
    // distinct arguments.
    let vals = &out[1];
    assert!(vals.contains("((x #f1m7)"), "x pinned: {vals}");
    assert!(vals.contains("(y #f0m7)"), "y ≠ x (else f x = f y): {vals}");
    // (f x) + (f y) = 5 with (f x) ≠ (f y): the only pair is {5, 0}.
    assert!(
        (vals.contains("(f x) #f5m7") && vals.contains("(f y) #f0m7"))
            || (vals.contains("(f x) #f0m7") && vals.contains("(f y) #f5m7")),
        "results sum to 5 and differ: {vals}"
    );
}

#[test]
fn function_hood_model_is_consistent() {
    // f(x)=1, f(y)=2 with x, y otherwise unconstrained: a naive
    // per-application model could print x = y with f(x) ≠ f(y) — not a
    // function. The arrangement machinery must keep them apart.
    let out = run(r#"
        (set-logic QF_UFFF)
        (declare-fun f ((_ FiniteField 7)) (_ FiniteField 7))
        (declare-const x (_ FiniteField 7))
        (declare-const y (_ FiniteField 7))
        (assert (= (f x) #f1m7))
        (assert (= (f y) #f2m7))
        (check-sat)
        (get-value (x y (f x) (f y)))
    "#);
    assert_eq!(out[0], "sat");
    let vals = &out[1];
    let xv = value_of(vals, "x");
    let yv = value_of(vals, "y");
    assert_ne!(xv, yv, "equal arguments would break function-hood: {vals}");
}

/// Extract the `#fVmP` literal assigned to `name` in a get-value
/// response (entries are `(name value)` on one or more lines).
fn value_of(get_value_output: &str, name: &str) -> String {
    let pat = format!("({name} #f");
    let start = get_value_output
        .find(&pat)
        .unwrap_or_else(|| panic!("no value for {name} in {get_value_output}"));
    let rest = &get_value_output[start + pat.len()..];
    let end = rest.find('m').unwrap_or(rest.len());
    let after = &rest[end..].find(')').unwrap_or(rest.len());
    format!("#f{}{}", &rest[..end], &rest[end..end + after])
}

#[test]
fn f2_distinct_over_applications_is_unsat() {
    // The toy-field pin from the handoff: three pairwise-distinct
    // values from a two-element field. This is the interface
    // cardinality clause (k ≤ p) — omitting it is a false `sat`.
    let out = run(r#"
        (set-logic QF_UFFF)
        (declare-fun f ((_ FiniteField 2)) (_ FiniteField 2))
        (declare-const x (_ FiniteField 2))
        (declare-const y (_ FiniteField 2))
        (declare-const z (_ FiniteField 2))
        (assert (distinct (f x) (f y) (f z)))
        (check-sat)
    "#);
    assert_eq!(out[0], "unsat");
}

#[test]
fn f2_distinct_under_boolean_structure_is_unsat() {
    // Off-spine (under `or`): the interface cardinality guard fires on
    // the Boolean model that asserts the full family, not on the spine.
    let out = run(r#"
        (set-logic QF_UFFF)
        (declare-fun f ((_ FiniteField 2)) (_ FiniteField 2))
        (declare-const x (_ FiniteField 2))
        (declare-const y (_ FiniteField 2))
        (declare-const z (_ FiniteField 2))
        (assert (or (distinct (f x) (f y) (f z)) (= x #f1m2)))
        (assert (= x #f0m2))
        (check-sat)
    "#);
    assert_eq!(out[0], "unsat");
}

#[test]
fn f2_distinct_satisfiable_when_k_le_p() {
    let out = run(r#"
        (set-logic QF_UFFF)
        (declare-fun f ((_ FiniteField 2)) (_ FiniteField 2))
        (declare-const x (_ FiniteField 2))
        (declare-const y (_ FiniteField 2))
        (assert (distinct (f x) (f y)))
        (check-sat)
        (get-value ((f x) (f y)))
    "#);
    assert_eq!(out[0], "sat");
    let vals = &out[1];
    let fx = value_of(vals, "(f x)");
    let fy = value_of(vals, "(f y)");
    assert_ne!(fx, fy, "the distinct must hold in the model: {vals}");
}

#[test]
fn arity_two_congruence() {
    // h(x, x) = h(y, x) once x = y — but NOT with only one argument
    // equal (the first solve attempt of a buggy congruence check).
    let out = run(r#"
        (set-logic QF_UFFF)
        (declare-fun h ((_ FiniteField 7) (_ FiniteField 7)) (_ FiniteField 7))
        (declare-const x (_ FiniteField 7))
        (declare-const y (_ FiniteField 7))
        (declare-const w (_ FiniteField 7))
        (assert (= x y))
        (assert (= (h x w) #f1m7))
        (assert (not (= (h y w) #f1m7)))
        (check-sat)
    "#);
    assert_eq!(out[0], "unsat");
}

#[test]
fn arity_two_partial_congruence_is_sat() {
    let out = run(r#"
        (set-logic QF_UFFF)
        (declare-fun h ((_ FiniteField 7) (_ FiniteField 7)) (_ FiniteField 7))
        (declare-const x (_ FiniteField 7))
        (declare-const y (_ FiniteField 7))
        (declare-const v (_ FiniteField 7))
        (declare-const w (_ FiniteField 7))
        (assert (= x y))
        (assert (not (= v w)))
        (assert (not (= (h x v) (h y w))))
        (check-sat)
    "#);
    assert_eq!(out[0], "sat");
}

#[test]
fn mixed_fields_multiplex() {
    // A function over two fields: congruence on the 𝔽5 argument, 𝔽7
    // arithmetic on the result.
    let out = run(r#"
        (set-logic QF_UFFF)
        (declare-fun g ((_ FiniteField 5)) (_ FiniteField 7))
        (declare-const a (_ FiniteField 5))
        (declare-const b (_ FiniteField 5))
        (assert (= a b))
        (assert (= (ff.mul (g a) (g b)) #f4m7))
        (check-sat)
        (get-value ((g a) (g b)))
    "#);
    assert_eq!(out[0], "sat");
    let vals = &out[1];
    let ga = value_of(vals, "(g a)");
    let gb = value_of(vals, "(g b)");
    assert_eq!(ga, gb, "a = b ⟹ g(a) = g(b): {vals}");
}

#[test]
fn certified_ufff_sat_model_certifies() {
    let mut ctx = Context::new();
    ctx.execute_script("(set-logic QF_UFFF)").expect("parse");
    ctx.execute_script(
        "(declare-fun f ((_ FiniteField 7)) (_ FiniteField 7))
         (declare-const x (_ FiniteField 7))
         (declare-const y (_ FiniteField 7))
         (assert (= (f x) #f1m7))
         (assert (= (f y) #f2m7))",
    )
    .expect("parse");
    ctx.require_certified_mode();
    let out = ctx.execute_script("(check-sat)").expect("parse");
    // The independent evaluator checks per-application congruence
    // (check_application_congruence): a function-inconsistent candidate
    // would be rejected here.
    assert_eq!(out[0], "sat");
    assert_eq!(ctx.certification_failure(), None);
}

#[test]
fn certified_congruence_unsat_certifies_via_independent_euf_lemmas() {
    // A pure congruence refutation has no FF certificate on the
    // combination path — but certified mode's independent Boolean
    // checker classifies FF equalities as EUF atoms and runs its own
    // VERIFIED congruence-blocking loop (certification.rs's
    // `block_theory_inconsistent_model`), which closes x = y ⟹
    // f(x) = f(y) by itself. The verdict certifies.
    let mut ctx = Context::new();
    ctx.execute_script("(set-logic QF_UFFF)").expect("parse");
    ctx.execute_script(
        "(declare-fun f ((_ FiniteField 7)) (_ FiniteField 7))
         (declare-const x (_ FiniteField 7))
         (declare-const y (_ FiniteField 7))
         (assert (= x y))
         (assert (= (f x) #f3m7))
         (assert (not (= (f y) #f3m7)))",
    )
    .expect("parse");
    ctx.require_certified_mode();
    let out = ctx.execute_script("(check-sat)").expect("parse");
    assert_eq!(out[0], "unsat");
    assert_eq!(ctx.certification_failure(), None);
}

#[test]
fn certified_ff_arithmetic_unsat_in_ufff_downgrades_to_unknown() {
    // A refutation that needs the FIELD arithmetic (not congruence):
    // f(x)² = 2 ∧ f(x) = 0 over 𝔽7 is field-linear unsat, invisible to
    // the checker's EUF-only blocking loop — no certificate exists, so
    // certified mode fails closed by design (the §8 branch-exhaustion /
    // case-tree certificate is future work).
    let mut ctx = Context::new();
    ctx.execute_script("(set-logic QF_UFFF)").expect("parse");
    ctx.execute_script(
        "(declare-fun f ((_ FiniteField 7)) (_ FiniteField 7))
         (declare-const x (_ FiniteField 7))
         (assert (= (ff.mul (f x) (f x)) #f2m7))
         (assert (= (f x) #f0m7))",
    )
    .expect("parse");
    ctx.require_certified_mode();
    let out = ctx.execute_script("(check-sat)").expect("parse");
    assert_eq!(out[0], "unknown");
    assert!(
        ctx.certification_failure().is_some(),
        "the downgrade must be explained"
    );
}

#[test]
fn certified_f2_pigeonhole_certificate_accepts() {
    // The spine cardinality guard carries a checkable pigeonhole
    // certificate — certified mode must ACCEPT this unsat.
    let mut ctx = Context::new();
    ctx.execute_script("(set-logic QF_UFFF)").expect("parse");
    ctx.execute_script(
        "(declare-fun f ((_ FiniteField 2)) (_ FiniteField 2))
         (declare-const x (_ FiniteField 2))
         (declare-const y (_ FiniteField 2))
         (declare-const z (_ FiniteField 2))
         (assert (distinct (f x) (f y) (f z)))",
    )
    .expect("parse");
    ctx.require_certified_mode();
    let out = ctx.execute_script("(check-sat)").expect("parse");
    assert_eq!(out[0], "unsat");
    assert_eq!(ctx.certification_failure(), None);
}

#[test]
fn uf_under_plain_qf_ff_is_a_contract_error() {
    // SMT-LIB: the FF letter does not include UF. A declared function
    // with an FF result sort under QF_FF is a contract violation — a
    // command error, not a silent `unknown`.
    let out = run(r#"
        (set-logic QF_FF)
        (declare-fun f ((_ FiniteField 7)) (_ FiniteField 7))
        (declare-const x (_ FiniteField 7))
        (assert (= (f x) #f1m7))
        (check-sat)
    "#);
    assert!(
        out[0].starts_with("(error"),
        "expected a contract error, got: {}",
        out[0]
    );
}

#[test]
fn honesty_foreign_leaf_is_unknown_without_a_header() {
    // A known logic header makes foreign vocabulary a CONTRACT error
    // (see `uf_under_plain_qf_ff_is_a_contract_error`); without a
    // header the structural routing applies, the combination declines
    // the Int leaf, and the honesty gate answers unknown rather than
    // guessing.
    let out = run(r#"
        (declare-fun f ((_ FiniteField 7)) (_ FiniteField 7))
        (declare-const x (_ FiniteField 7))
        (declare-const i Int)
        (assert (> i 3))
        (assert (= (f x) #f1m7))
        (check-sat)
    "#);
    assert_eq!(out[0], "unknown");
}

#[test]
fn verdicts_are_deterministic() {
    let script = r#"
        (set-logic QF_UFFF)
        (declare-fun f ((_ FiniteField 3)) (_ FiniteField 3))
        (declare-const x (_ FiniteField 3))
        (declare-const y (_ FiniteField 3))
        (assert (or (= (ff.mul (f x) (f x)) #f1m3) (distinct (f x) (f y) x)))
        (assert (not (= (f x) #f0m3)))
        (check-sat)
    "#;
    let a = run(script);
    let b = run(script);
    assert_eq!(a[0], b[0]);
    assert!(a[0] == "sat" || a[0] == "unsat" || a[0] == "unknown");
}
