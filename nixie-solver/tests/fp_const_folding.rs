//! Regression: FP constant semantics at the solver level.
//!
//! Covers the two FP rungs landed 2026-09-08 (see
//! `docs/studies/2026-09-08-fp-const-folding.md`):
//!
//! 1. **Bit-pattern value marks on FP literals**: SMT-LIB `=` on floats is
//!    *datum identity* — `(_ +zero e s) ≠ (_ -zero e s)`, distinct finite
//!    literals are never equal — while every NaN of a format is ONE datum.
//!    Equalities between distinct data were previously free Booleans
//!    (false-`sat` class; z3 answered `unsat`).
//! 2. **Constant folding through EUF class pins** (`solver/fp_fold.rs`):
//!    `x = c ∧ y = (fp.op … x …) ∧ y = c2` refutes by unit propagation when
//!    `fold(c) ≠ c2`, including chains and predicates — the unsat direction
//!    the pattern checks and the concrete model builder leave open.
//!
//! Every expectation here is z3-verified (4.16.0).

use nixie_solver::{Context, SolverResult};

fn run_script(script: &str) -> SolverResult {
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(script).unwrap_or_default();
    for tok in outputs.iter().rev() {
        match tok.trim() {
            "sat" => return SolverResult::Sat,
            "unsat" => return SolverResult::Unsat,
            "unknown" => return SolverResult::Unknown,
            _ => {}
        }
    }
    SolverResult::Unknown
}

// ===========================================================================
// `=` on floats is datum identity (value marks)
// ===========================================================================

/// `+0 = -0` is FALSE: asserted true, the formula is unsat (z3: unsat; was a
/// false-`sat`).  Both spellings and the variable-mediated form.
#[test]
fn zero_signs_are_distinct_data() {
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (assert (= (_ +zero 11 53) (_ -zero 11 53)))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (assert (= (fp #b0 #b00000000000 #x0000000000000)
                        (fp #b1 #b00000000000 #x0000000000000)))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const x Float64)
             (assert (= x (_ +zero 11 53)))
             (assert (= x (_ -zero 11 53)))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
}

/// Same value, different spelling: `+0` spelled as bits equals the dedicated
/// literal (z3: sat).
#[test]
fn same_datum_spellings_merge() {
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const x Float64)
             (assert (= x (fp #b0 #b00000000000 #x0000000000000)))
             (assert (= x (_ +zero 11 53)))
             (check-sat)"
        ),
        SolverResult::Sat
    );
}

/// Two distinct finite literals never merge (z3: unsat; was false-`sat`).
#[test]
fn distinct_finite_literals_never_merge() {
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (assert (= (fp #b0 #b11111111111 #b0000000000000000000000000000000000000000000000000000)
                        (fp #b0 #b11111111111 #b0000000000000000000000000000000000000000000000000010)))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
}

/// Every NaN of a format is ONE datum: the payload-less literal, a spelled
/// payload-1 NaN and a spelled payload-2 NaN all `=`-equal (z3: sat each).
#[test]
fn nan_spellings_are_one_datum() {
    for a in ["(_ NaN 11 53)", "(fp #b0 #b11111111111 #x0000000000001)"] {
        for b in [
            "(fp #b0 #b11111111111 #x0000000000001)",
            "(fp #b0 #b11111111111 #x0000000000002)",
            "(fp #b1 #b11111111111 #x0000000000001)",
        ] {
            assert_eq!(
                run_script(&format!(
                    "(set-logic QF_FP)
                     (assert (= {a} {b}))
                     (check-sat)"
                )),
                SolverResult::Sat,
                "({a} = {b}) must be satisfiable: NaN is one datum"
            );
        }
    }
}

/// Infinities: same sign equal, opposite signs distinct (z3: sat / unsat).
#[test]
fn infinity_data_identity() {
    assert_eq!(
        run_script("(set-logic QF_FP) (assert (= (_ +oo 11 53) (_ +oo 11 53))) (check-sat)"),
        SolverResult::Sat
    );
    assert_eq!(
        run_script("(set-logic QF_FP) (assert (= (_ +oo 11 53) (_ -oo 11 53))) (check-sat)"),
        SolverResult::Unsat
    );
}

// ===========================================================================
// Constant folding through EUF class pins
// ===========================================================================

/// The headline shape: `x = c ∧ y = (fp.add RNE x x) ∧ y = c2` with
/// `fold(c, c) ≠ c2` (z3: unsat; was `unknown`).
#[test]
fn fold_refutes_wrong_pinned_sum() {
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const x Float32)
             (declare-const y Float32)
             (assert (= x (fp #b0 #x7f #b00000000000000000000001)))
             (assert (= y (fp.add RNE x x)))
             (assert (= y (fp #b0 #x80 #b00000000000000000000000)))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
    // … and the consistent conclusion keeps the formula satisfiable.
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const x Float32)
             (declare-const y Float32)
             (assert (= x (fp #b0 #x7f #b00000000000000000000001)))
             (assert (= y (fp.add RNE x x)))
             (check-sat)"
        ),
        SolverResult::Sat
    );
}

/// Literal operands fold with no guard: the refutation is a pure unit
/// cascade (z3: unsat; was `unknown`).
#[test]
fn fold_over_literal_operands_is_a_unit_cascade() {
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const x Float64)
             (assert (= x (fp.mul RTN (fp #b1 #b00000000000 #x0000000000001)
                                       (fp #b0 #b00000000000 #x0000000000001))))
             (assert (= x (_ -zero 11 53)))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
    // The CORRECT value (RTN underflow of the negative product is
    // -min_subnormal) is satisfiable (z3: sat).
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const x Float64)
             (assert (= x (fp.mul RTN (fp #b1 #b00000000000 #x0000000000001)
                                       (fp #b0 #b00000000000 #x0000000000001))))
             (assert (= x (fp #b1 #b00000000000 #x0000000000001)))
             (check-sat)"
        ),
        SolverResult::Sat
    );
}

/// Chains: `y = x + x`, `z = y * y` fold transitively; the wrong value
/// refutes, the right one satisfies (z3: unsat / sat).
#[test]
fn folds_chain_through_defined_variables() {
    let base = "(set-logic QF_FP)
         (declare-const x Float64)
         (declare-const y Float64)
         (declare-const z Float64)
         (assert (= x (fp #b0 #b01111111111 #x8000000000000)))
         (assert (= y (fp.add RNE x x)))
         (assert (= z (fp.mul RNE y y)))";
    // 1.5 + 1.5 = 3.0, 3.0 * 3.0 = 9.0.
    assert_eq!(
        run_script(&format!(
            "{base}
             (assert (= z (fp #b0 #b10000000010 #b0010000000000000000000000000000000000000000000000000)))
             (check-sat)"
        )),
        SolverResult::Sat
    );
    assert_eq!(
        run_script(&format!(
            "{base}
             (assert (= z (fp #b0 #b10000000010 #b0100000000000000000000000000000000000000000000000000)))
             (check-sat)"
        )),
        SolverResult::Unsat
    );
}

/// Predicate folds: `fp.isNormal(+oo)` is FALSE, so asserting it true
/// refutes; its negation satisfies (z3: unsat / sat; both were `unknown`).
#[test]
fn predicate_folds_refute_and_satisfy() {
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const x Float64)
             (assert (= x (_ +oo 11 53)))
             (assert (fp.isNormal x))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
    assert_eq!(
        run_script("(set-logic QF_FP) (assert (fp.isNormal (_ +oo 11 53))) (check-sat)"),
        SolverResult::Unsat
    );
    assert_eq!(
        run_script("(set-logic QF_FP) (assert (not (fp.isNormal (_ +oo 11 53)))) (check-sat)"),
        SolverResult::Sat
    );
    // fp.eq(NaN, NaN) is FALSE (IEEE comparison): asserting it true refutes.
    assert_eq!(
        run_script("(set-logic QF_FP) (assert (fp.eq (_ NaN 11 53) (_ NaN 11 53))) (check-sat)"),
        SolverResult::Unsat
    );
    // fp.isNegative of the payload-less NaN literal is FALSE (no sign bit).
    assert_eq!(
        run_script("(set-logic QF_FP) (assert (fp.isNegative (_ NaN 11 53))) (check-sat)"),
        SolverResult::Unsat
    );
}

/// `fp.min(+0,-0) = -0` per the SMT-LIB tie rule (z3: sat; the engine used
/// to return +0 and the fold then refuted the definition).
#[test]
fn min_zero_tie_follows_smtlib() {
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (assert (= (fp.min (_ +zero 11 53) (_ -zero 11 53)) (_ -zero 11 53)))
             (check-sat)"
        ),
        SolverResult::Sat
    );
}

/// Scope safety: the contradiction and its lemmas retract on `pop`.
#[test]
fn fold_lemmas_retract_on_pop() {
    let script = "(set-logic QF_FP)
        (push 1)
        (declare-const x Float32)
        (declare-const y Float32)
        (assert (= x (fp #b0 #x7f #b00000000000000000000001)))
        (assert (= y (fp.add RNE x x)))
        (assert (= y (fp #b0 #x80 #b00000000000000000000000)))
        (check-sat)
        (pop 1)
        (assert (= (_ +zero 11 53) (_ +zero 11 53)))
        (check-sat)";
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(script).unwrap_or_default();
    let verdicts: Vec<&str> = outputs
        .iter()
        .filter(|t| matches!(t.trim(), "sat" | "unsat" | "unknown"))
        .map(|t| t.trim())
        .collect();
    assert_eq!(
        verdicts,
        ["unsat", "sat"],
        "scope 1 must refute, scope 2 must satisfy after pop"
    );
}
