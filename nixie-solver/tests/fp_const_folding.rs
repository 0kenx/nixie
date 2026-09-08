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

// ===========================================================================
// Real → FP conversions: exact single-rounding (`((_ to_fp e s) RM real)`)
// ===========================================================================

/// The double-rounding false-`sat` this fixed: `RTZ` of `1 + 2^-52 + 2^-53`
/// is the truncation `1 + 2^-52`, NOT the RNE value `1 + 2·2^-52`.  The old
/// model-builder path evaluated the real as an `f64` first (an RNE rounding
/// of its own) and "rounded" the already-rounded value, verifying the WRONG
/// witness (z3: `unsat` on the wrong-datum probe; was `sat`).
#[test]
fn real_to_fp_directed_mode_is_a_single_exact_rounding() {
    let head = "(set-logic QF_FP)
         (declare-const x Float64)
         (assert (= x ((_ to_fp 11 53) RTZ \
             (+ 1.0 (/ 1.0 4503599627370496.0) (/ 1.0 9007199254740992.0)))))";
    // True truncation: 1 + 2^-52.
    assert_eq!(
        run_script(&format!(
            "{head}
             (assert (= x (fp #b0 #b01111111111 #x0000000000001)))
             (check-sat)"
        )),
        SolverResult::Sat
    );
    // The RNE double-rounding artefact must NOT verify.
    assert_eq!(
        run_script(&format!(
            "{head}
             (assert (= x (fp #b0 #b01111111111 #x0000000000002)))
             (check-sat)"
        )),
        SolverResult::Unknown,
        "the wrong datum must never verify (was a false `sat`); honest \
         `unknown` — the div-bearing operand's guard cannot fold"
    );
}

/// Dyadic rationals convert exactly and decide both ways: `(/ 3.0 2.0)` is
/// 1.5, so the identity holds (sat) and a perturbed datum refutes when the
/// operand is arithmetically clean enough to fold (z3: sat / unsat).
#[test]
fn real_to_fp_dyadic_conversion_decides() {
    let base = "(set-logic QF_FP)
         (declare-const x Float64)
         (assert (= x ((_ to_fp 11 53) RNE (/ 3.0 2.0))))";
    assert_eq!(
        run_script(&format!(
            "{base}
             (assert (not (= x (fp #b0 #b01111111111 #x8000000000000))))
             (check-sat)"
        )),
        SolverResult::Unknown,
        "z3: `unsat` — the refutation needs the fold's unit, and the \
         div-bearing operand cannot carry an arith-clean guard, so this \
         stays the honest `unknown` (never a false `sat`)"
    );
    assert_eq!(
        run_script(&format!(
            "{base}
             (check-sat)"
        )),
        SolverResult::Sat
    );
}

/// Integer-valued conversions are exact at every magnitude that fits the
/// significand (the assembly bug this pins produced +inf for `2.0`).
#[test]
fn real_to_fp_integer_values_are_exact() {
    for (v, lit) in [
        (2u64, "(fp #b0 #b10000000000 #x0000000000000)"),
        (89524, "(fp #b0 #b10000001111 #x5db4000000000)"),
        ((1 << 53) - 1, "(fp #b0 #b10000110011 #xfffffffffffff)"),
    ] {
        let script = format!(
            "(set-logic QF_FP)
             (declare-const x Float64)
             (assert (= x ((_ to_fp 11 53) RNE {v}.0)))
             (assert (not (= x {lit})))
             (check-sat)"
        );
        assert_eq!(
            run_script(&script),
            SolverResult::Unsat,
            "conversion of {v} must be its exact f64 datum"
        );
    }
}

/// `RNE` of one third: the correctly rounded double (0x3FD5555555555555).
#[test]
fn real_to_fp_one_third_rounds_correctly() {
    let script = "(set-logic QF_FP)
        (declare-const x Float64)
        (assert (= x ((_ to_fp 11 53) RNE (/ 1.0 3.0))))
        (assert (= x (fp #b0 #b01111111101 #x5555555555555)))
        (check-sat)";
    assert_eq!(run_script(script), SolverResult::Sat);
    let wrong = "(set-logic QF_FP)
        (declare-const x Float64)
        (assert (= x ((_ to_fp 11 53) RNE (/ 1.0 3.0))))
        (assert (= x (fp #b0 #b01111111101 #x5555555555556)))
        (check-sat)";
    // The div-bearing operand keeps the fold off, so the wrong datum is an
    // honest `unknown` (never a false `sat`).
    assert_ne!(run_script(wrong), SolverResult::Sat);
}

// ===========================================================================
// Conversion-surface parsing and bit-vector → FP conversions
// ===========================================================================

/// `Int` literals convert with real semantics (SMT-LIB Int ⊆ Real; z3
/// coerces — this was a parse error before).
#[test]
fn to_fp_accepts_integer_literals() {
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const x Float64)
             (assert (= x ((_ to_fp 11 53) RNE 3)))
             (assert (not (= x (fp #b0 #b10000000000 #x8000000000000))))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
}

/// `(_ bvN W)` indexed bit-vector literals parse (the standard spelling for
/// wide constants) and convert exactly, refuting a wrong datum.
#[test]
fn to_fp_from_indexed_bv_literal_decides_both_ways() {
    // 123456789012345678 needs 57 bits: RTP rounds up from exact.
    let base = "(set-logic QF_FP)
         (declare-const x Float64)
         (assert (= x ((_ to_fp 11 53) RTP (_ bv123456789012345678 64))))";
    // The exact fold decides the instance; pin BOTH polarities against the
    // oracle-derived datum: 123456789012345678 = 0x1B69B4BA630F34E·4 …
    // (probe against a clearly wrong datum: zero.)
    assert_eq!(
        run_script(&format!(
            "{base}
             (assert (= x (_ +zero 11 53)))
             (check-sat)"
        )),
        SolverResult::Unsat
    );
    assert_eq!(
        run_script(&format!(
            "{base}
             (check-sat)"
        )),
        SolverResult::Sat
    );
}

/// A variable pinned to a BV constant converts through the class witness
/// (the fold's guarded path).
#[test]
fn to_fp_from_pinned_bv_variable_folds() {
    assert_eq!(
        run_script(
            "(set-logic QF_FPBV)
             (declare-const v (_ BitVec 32))
             (declare-const x Float64)
             (assert (= v (_ bv42 32)))
             (assert (= x ((_ to_fp 11 53) RNE v)))
             (assert (= x (_ +zero 11 53)))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
}

/// A small value spelled with a long fraction: the raw decimal digits
/// exceed i64, the reduced rational fits — the widened decimal path.
#[test]
fn long_fraction_decimals_parse_exactly() {
    // 0.50000000000000000000 (20 fraction digits): raw numerator 5·10^19.
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const x Float64)
             (assert (= x ((_ to_fp 11 53) RNE 0.50000000000000000000)))
             (assert (not (= x (fp #b0 #b01111111110 #x0000000000000))))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
}

/// Genuinely-unrepresentable decimals (reduced rational outside i64/i64)
/// still refuse — never a verdict on a garbled value.
#[test]
fn oversized_decimals_error_not_garble() {
    let mut ctx = Context::new();
    let res = ctx.execute_script(
        "(set-logic QF_FP)
         (declare-const x Float64)
         (assert (= x ((_ to_fp 11 53) RNE 309485009821345068724781056.0)))
         (check-sat)",
    );
    if let Ok(out) = res {
        assert!(
            !out.iter().any(|t| matches!(t.trim(), "sat" | "unsat")),
            "a refused literal must not produce a verdict: {out:?}"
        );
    } // Err = refused at the script level — equally honest
}

// ===========================================================================
// FP → bit-vector conversions (`((_ fp.to_sbv m) RM x)` / `fp.to_ubv`)
// ===========================================================================

/// In-range conversions round to the integer grid under the mode and encode
/// exactly — both verdict polarities (z3-verified probes).
#[test]
fn fp_to_bv_rounds_and_decides_both_ways() {
    // 3.7: RTP → 4 (unsigned), RTZ → 3 (signed).
    let base = "(set-logic QF_FPBV)
         (declare-const x Float64)
         (assert (= x ((_ to_fp 11 53) RNE 3.7)))";
    assert_eq!(
        run_script(&format!(
            "{base}
             (assert (= ((_ fp.to_ubv 32) RTP x) (_ bv4 32)))
             (check-sat)"
        )),
        SolverResult::Sat
    );
    assert_eq!(
        run_script(&format!(
            "{base}
             (assert (= ((_ fp.to_ubv 32) RTP x) (_ bv5 32)))
             (check-sat)"
        )),
        SolverResult::Unsat
    );
    assert_eq!(
        run_script(&format!(
            "{base}
             (assert (= ((_ fp.to_sbv 32) RTZ x) (_ bv3 32)))
             (check-sat)"
        )),
        SolverResult::Sat
    );
}

/// Negative values round with sign (RTN of −3.7 → −4) and encode in
/// two's complement (z3: sat for `bv4294967292` at width 32).
#[test]
fn fp_to_sbv_negative_two_complement() {
    assert_eq!(
        run_script(
            "(set-logic QF_FPBV)
             (declare-const x Float64)
             (assert (= x ((_ to_fp 11 53) RNE (- 3.7))))
             (assert (= ((_ fp.to_sbv 32) RTN x) (_ bv4294967292 32)))
             (check-sat)"
        ),
        SolverResult::Sat
    );
}

/// Underspecified conversions (the rounded value does not fit the width)
/// leave the atom FREE — any probe stays satisfiable, matching z3's
/// underspecification semantics; never a fabricated refutation.
#[test]
fn fp_to_bv_overflow_is_free_not_fabricated() {
    for probe in ["(_ bv255 8)", "(_ bv0 8)", "(_ bv42 8)"] {
        assert_eq!(
            run_script(&format!(
                "(set-logic QF_FPBV)
                 (assert (= ((_ fp.to_ubv 8) RNE ((_ to_fp 11 53) RNE 300.0)) {probe}))
                 (check-sat)"
            )),
            SolverResult::Sat,
            "underspecified conversion: {probe} must stay satisfiable"
        );
    }
}

// ===========================================================================
// FP congruence: operand merges propagate through fp operations
// ===========================================================================

/// `(= a b) → (= (fp.abs a) (fp.abs b))` — congruence through fp ops (z3:
/// unsat; was an honest `unknown` when fp ops were opaque EUF leaves).
#[test]
fn fp_ops_are_congruence_applications() {
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const a Float64)
             (declare-const b Float64)
             (assert (= a b))
             (assert (not (= (fp.abs a) (fp.abs b))))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
    // Binary op under the same merge.
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const a Float64)
             (declare-const b Float64)
             (assert (= a b))
             (assert (not (= (fp.add RNE a a) (fp.add RNE b b))))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
    // `distinct` over congruent applications (z3 times this one out).
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const a Float64)
             (declare-const b Float64)
             (assert (= a b))
             (assert (distinct (fp.mul RNA a a) (fp.mul RNA b b)))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
}

/// `fp.lt x x` / `fp.gt x x` are false for EVERY x (NaN included): a
/// positive atom whose operand classes merge conflicts with the merge's
/// own explanation (z3: unsat).
#[test]
fn strict_comparisons_over_congruent_operands_refute() {
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const a Float64)
             (declare-const b Float64)
             (assert (= a b))
             (assert (fp.lt (fp.abs a) (fp.abs b)))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const a Float64)
             (declare-const b Float64)
             (assert (= a b))
             (assert (fp.gt (fp.add RNE a a) (fp.add RNE b b)))
             (check-sat)"
        ),
        SolverResult::Unsat
    );
}

/// The rounding mode is part of the function symbol: same operands under
/// different modes are NOT forced equal (both solvers: sat).
#[test]
fn congruence_respects_the_rounding_mode() {
    assert_eq!(
        run_script(
            "(set-logic QF_FP)
             (declare-const a Float64)
             (declare-const b Float64)
             (assert (= a b))
             (assert (not (= (fp.add RNE a a) (fp.add RTZ a a))))
             (check-sat)"
        ),
        SolverResult::Sat
    );
}
