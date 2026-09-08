//! Public regressions for hybrid search and the independently discovered
//! rational conversion defects. Expected conversion values are literal IEEE
//! data, not values obtained from Nixie's folding implementation.
use nixie_solver::Context;

fn verdicts(script: &str) -> Vec<String> {
    Context::new()
        .execute_script(script)
        .expect("valid SMT-LIB")
        .into_iter()
        .filter(|s| matches!(s.trim(), "sat" | "unsat" | "unknown"))
        .collect()
}

#[test]
fn rational_carry_and_inward_overflow_do_not_certify_wrong_data() {
    for (term, correct, wrong) in [
        (
            "((_ to_fp 3 4) RNE (/ 31.0 16.0))",
            "(fp #b0 #b100 #b000)",
            "(fp #b0 #b001 #b000)",
        ),
        (
            "((_ to_fp 3 4) RTZ 16.0)",
            "(fp #b0 #b110 #b111)",
            "(fp #b0 #b010 #b111)",
        ),
    ] {
        let script = format!(
            "(set-logic QF_FP) (assert (= {term} {correct})) (check-sat) (push 1) (assert (= {term} {wrong})) (check-sat)"
        );
        assert_eq!(verdicts(&script), ["sat", "unsat"], "{term}");
        let script = format!("(set-logic QF_FP) (assert (= {term} {wrong})) (check-sat)");
        assert_eq!(
            verdicts(&script),
            ["unsat"],
            "wrong data must not self-verify: {term}"
        );
    }
}

#[test]
fn symbolic_mode_selects_an_exact_arithmetic_branch() {
    let script = "(set-logic QF_FP)
        (declare-const rm RoundingMode)
        (declare-const x (_ FloatingPoint 3 4))
        (assert (distinct rm RNE RNA RTP RTN))
        (assert (= (fp.add rm x x) (fp #b0 #b100 #b100)))
        (assert (fp.isNormal x))
        (check-sat)
        (push 1) (assert (fp.isNegative x)) (check-sat)
        (pop 1) (check-sat)";
    assert_eq!(verdicts(script), ["sat", "unsat", "sat"]);
}

#[test]
fn binary64_symbolic_addition_and_classification() {
    let script = "(set-logic QF_FP)
        (declare-const x Float64)
        (assert (= (fp.add RNE x x) ((_ to_fp 11 53) RNE 3.0)))
        (assert (fp.gt x ((_ to_fp 11 53) RNE 1.0)))
        (assert (fp.lt x ((_ to_fp 11 53) RNE 2.0)))
        (check-sat)";
    assert_eq!(verdicts(script), ["sat"]);
}

#[test]
fn ieee_equality_and_datum_equality_keep_distinct_zero_semantics() {
    let script = "(set-logic QF_FP)
        (declare-const x Float64) (declare-const y Float64)
        (assert (fp.eq x y)) (assert (distinct x y)) (check-sat)
        (push 1) (assert (fp.isNormal x)) (check-sat)
        (pop 1) (check-sat)";
    assert_eq!(verdicts(script), ["sat", "unsat", "sat"]);
}

#[test]
fn symbolic_fp_witness_is_valid_smtlib_and_rechecks() {
    let base = "(set-logic QF_FP)
        (declare-const x (_ FloatingPoint 3 4))
        (assert (= (fp.add RNE x x) (fp #b0 #b100 #b100)))";
    let output = Context::new()
        .execute_script(&format!("{base} (check-sat) (get-value (x))"))
        .expect("solve and print");
    let binding = output
        .iter()
        .find(|s| s.starts_with("((x "))
        .expect("binding");
    let literal = binding
        .strip_prefix("((x ")
        .and_then(|s| s.strip_suffix("))"))
        .expect("FP datum");
    assert_eq!(literal, "(fp #b0 #b011 #b100)");
    assert_eq!(
        verdicts(&format!("{base} (assert (= x {literal})) (check-sat)")),
        ["sat"]
    );
}
