//! End-to-end binary extension fields, including scopes and certified mode.
use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    Context::new().execute_script(script).expect("valid script")
}

#[test]
fn model_printing_round_trips_and_get_value_evaluates() {
    let out = run("(set-logic QF_FF) (declare-const x (_ BinaryField 7))
        (assert (= (ff.mul x x) (as ff3 (_ BinaryField 7))))
        (check-sat) (get-model) (get-value (x (ff.mul x x) (ff.neg x) (ff.bitsum x x)))");
    assert_eq!(out[0], "sat");
    assert!(out[1].contains("(_ BinaryField 7)"), "{out:?}");
    assert!(out[2].contains("(as ff2 (_ BinaryField 7))"), "{out:?}");
    assert!(out[2].contains("(as ff3 (_ BinaryField 7))"), "{out:?}");
    let script = format!(
        "(set-logic QF_FF) {} (assert (= (ff.mul x x) (as ff3 (_ BinaryField 7)))) (check-sat)",
        out[1]
    );
    // Model output is a parenthesized list of define-fun commands.
    let model = out[1].trim();
    let definitions = model
        .strip_prefix("(model")
        .or_else(|| model.strip_prefix('('))
        .unwrap()
        .strip_suffix(')')
        .unwrap();
    let round = run(&format!(
        "(set-logic QF_FF) {definitions} (assert (= (ff.mul x x) (as ff3 (_ BinaryField 7)))) (check-sat)"
    ));
    assert_eq!(round[0], "sat", "{script}");
}

#[test]
fn boolean_structure_multiple_representations_and_scopes() {
    let out = run("(set-logic QF_FF)
        (declare-const x (_ BinaryField 11)) (declare-const y (_ BinaryField 13))
        (assert (or (= x (as ff2 (_ BinaryField 11))) (= x (as ff3 (_ BinaryField 11)))))
        (assert (= (ff.mul y y) (as ff4 (_ BinaryField 13))))
        (check-sat) (push 1)
        (assert (= (ff.add x x) (as ff1 (_ BinaryField 11)))) (check-sat)
        (pop 1) (check-sat)
        (assert (not (= y (as ff2 (_ BinaryField 13))))) (check-sat)");
    assert_eq!(out, vec!["sat", "unsat", "sat", "unsat"]);
}

#[test]
fn cardinality_uses_order_not_characteristic() {
    let out = run("(set-logic QF_FF) (declare-const a (_ BinaryField 7))
        (declare-const b (_ BinaryField 7)) (declare-const c (_ BinaryField 7))
        (declare-const d (_ BinaryField 7)) (declare-const e (_ BinaryField 7))
        (assert (distinct a b c)) (check-sat) (push 1)
        (assert (distinct a b c d e)) (check-sat) (pop 1) (check-sat)");
    assert_eq!(out, vec!["sat", "unsat", "sat"]);
}

#[test]
fn certified_sat_and_unsupported_arithmetic_refutations() {
    let mut ctx = Context::new();
    ctx.require_certified_mode();
    let out = ctx
        .execute_script(
            "(set-logic QF_FF) (declare-const x (_ BinaryField 7))
        (assert (= (ff.mul x x) (as ff3 (_ BinaryField 7)))) (check-sat)",
        )
        .unwrap();
    assert_eq!(out[0], "sat", "{:?}", ctx.certification_failure());
    let mut ctx = Context::new();
    ctx.require_certified_mode();
    // X^2+X+X_basis has no root in F4 (trace of X_basis is one).
    let out = ctx
        .execute_script(
            "(set-logic QF_FF) (declare-const x (_ BinaryField 7))
        (assert (= (ff.add (ff.mul x x) x) (as ff2 (_ BinaryField 7)))) (check-sat)",
        )
        .unwrap();
    assert_eq!(out[0], "unknown");
    assert!(ctx.certification_failure().is_some());
}

#[test]
fn unsupported_combinations_and_large_search_decline() {
    let out = run("(set-logic QF_UFFF) (declare-const x (_ BinaryField 7))
        (declare-fun f ((_ BinaryField 7)) (_ BinaryField 7))
        (assert (= (f x) x)) (check-sat)");
    assert_eq!(out[0], "unknown");
    let out = run("(set-logic QF_FF) (declare-const x (_ BinaryField 283))
        (declare-const y (_ BinaryField 283)) (declare-const z (_ BinaryField 283))
        (assert (= (ff.mul x y) z)) (check-sat)");
    assert_eq!(out[0], "unknown");
}

// Independent AES-style coefficient convolution; no production field helpers.
fn multiply(a: u32, b: u32, f: u32) -> u32 {
    let mut raw = 0;
    for i in 0..8 {
        for j in 0..8 {
            if (a >> i) & (b >> j) & 1 != 0 {
                raw ^= 1 << (i + j);
            }
        }
    }
    let k = f.ilog2();
    for i in (k..16).rev() {
        if raw >> i & 1 != 0 {
            raw ^= f << (i - k);
        }
    }
    raw
}

#[test]
fn independently_planted_solutions_in_both_f8_representations_and_aes() {
    for f in [11u32, 13, 283] {
        let q = 1 << f.ilog2();
        for seed in 1..=16 {
            let a = (seed * 17 + 3) % q;
            let b = (seed * 29 + 5) % q;
            let target = multiply(a, b, f) ^ a;
            let out = run(&format!(
                "(set-logic QF_FF)
                (declare-const x (_ BinaryField {f})) (declare-const y (_ BinaryField {f}))
                (assert (= x (as ff{a} (_ BinaryField {f}))))
                (assert (= y (as ff{b} (_ BinaryField {f}))))
                (assert (= (ff.add (ff.mul x y) x) (as ff{target} (_ BinaryField {f}))))
                (check-sat)"
            ));
            assert_eq!(out[0], "sat", "f={f} seed={seed}");
        }
    }
}

#[test]
fn exhaustive_two_variable_systems_over_f4() {
    for sum in 0..4 {
        for product in 0..4 {
            let possible =
                (0..4).any(|x| (0..4).any(|y| (x ^ y) == sum && multiply(x, y, 7) == product));
            let out = run(&format!(
                "(set-logic QF_FF)
            (declare-const x (_ BinaryField 7)) (declare-const y (_ BinaryField 7))
            (assert (= (ff.add x y) (as ff{sum} (_ BinaryField 7))))
            (assert (= (ff.mul x y) (as ff{product} (_ BinaryField 7)))) (check-sat)"
            ));
            assert_eq!(out[0], if possible { "sat" } else { "unsat" });
        }
    }
}
