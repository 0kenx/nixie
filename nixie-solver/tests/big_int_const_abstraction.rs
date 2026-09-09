//! Regression tests for the too-big `IntConst` linear abstraction (2026-09).
//!
//! The linear parser used to reject any atom mentioning an integer constant
//! outside `i64` (`18446744073709551616` = 2^64), and the
//! `arith_atoms_need_theory` pre-search gate then answered `Unknown` for the
//! *whole goal* – even when the refutation never touched the constant.  Every
//! Verus encoding pins `(uHi 64) = 2^64` (the unsigned upper bound of a
//! 64-bit word), so the entire UFBVDTNIA/UFDTNIA/UFDTLIA Verus families were
//! instant-`unknown` before this fix, with the actual goal often a pure
//! bit-vector identity the solver could refute in milliseconds.
//!
//! The fix abstracts a too-big `IntConst` to its own **shared opaque tableau
//! column** (`extract_linear_terms`): every occurrence of the same
//! hash-consed constant maps to one column, so the parsed system is the
//! original with that constant replaced by a fresh free variable.  That is
//!
//! * exact for **refutation**: a conflict over the column holds for *every*
//!   value of it, in particular the constant's true value, so `unsat` is
//!   sound – `Unsat`-of-abstracted ⇒ ∀c. Unsat ⇒ real `Unsat`;
//! * guarded for **models**: a `Sat` is only a model of the *abstracted*
//!   system (the column's value is some `Rational64`, not the constant), so
//!   `check_with_arith_refinement` accepts it exclusively through the
//!   `BigInt`-exact `model_certify` evaluation and keeps the honest
//!   `Unknown` otherwise (`arith_abstracted_big_const`).

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

/// The minimal shape the old gate nuked: pinning a constant to 2^64 next to
/// an unrelated satisfiable constraint is `sat` (Z3 agrees); the model cannot
/// be `Rational64`-verified, so the honest verdict is `unknown` – but never a
/// wrong decisive one.
#[test]
fn big_const_pin_alone_is_never_wrong() {
    let output = run(r#"
        (set-logic UFLIA)
        (declare-const x Int)
        (assert (= x 18446744073709551616))
        (assert (> x 0))
        (check-sat)
    "#);
    assert_ne!(last_status(&output), "unsat");
}

/// A goal refuted through the *abstracted column itself*: `x = 2^64` and
/// `x > 2^64` conflict identically over the column, so the abstraction's
/// refutation is the real one.
#[test]
fn big_const_self_conflict_is_unsat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const x Int)
        (assert (= x 18446744073709551616))
        (assert (> x 18446744073709551616))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// Two distinct big constants keep their disequality through the shared
/// columns: `2^64` and `2^64 + 1` are different columns, and `x` cannot
/// equal both.
#[test]
fn distinct_big_consts_conflict_is_unsat() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const x Int)
        (assert (= x 18446744073709551616))
        (assert (= x 18446744073709551617))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The Verus shape: the `uHi` pins are units the refutation never needs.
/// The goal below is a pure bit-vector claim over `v` alone, decided
/// without any arithmetic on 2^64 – the old pre-search gate answered
/// `unknown` for exactly this file shape (both solvers: `unsat`).
#[test]
fn verus_uhi_pin_does_not_block_bv_refutation() {
    let output = run(r#"
        (set-logic UFBV)
        (declare-fun uHi (Int) Int)
        (declare-const v (_ BitVec 64))
        (assert (= (uHi 64) 18446744073709551616))
        (assert (= (bvor (bvand v (bvnot ((_ zero_extend 62) (_ bv3 2))))
                         ((_ zero_extend 63) (_ bv1 1)))
                   (bvadd (bvsub v ((_ zero_extend 61) (_ bv4 3)))
                          ((_ zero_extend 63) (_ bv1 1)))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The abstraction must not weaken ordinary arithmetic: a constraint set
/// that is genuinely satisfiable only through the constant's true value
/// stays honest (`unknown`, never a fabricated `sat`, never a false
/// `unsat`).  `x < 5 ∧ x > 2^64` is unsat in the integers; the abstracted
/// system has a model (column := 0, x := 1), so the expected verdict is the
/// gated one.
#[test]
fn big_const_bounds_gap_is_honest() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const x Int)
        (assert (< x 5))
        (assert (> x 18446744073709551616))
        (check-sat)
    "#);
    // Never a wrong decisive answer: z3 says unsat, the abstraction cannot
    // express it, so `unknown` is the only sound verdict available here.
    assert_ne!(last_status(&output), "sat");
}

/// Ordinary `i64`-range arithmetic is untouched: the constant still folds
/// into the tableau's additive term.  (Constants near `i64::MAX` hit a
/// *pre-existing* `Rational64` overflow in debug builds – unrelated to the
/// abstraction – so this uses a 2^62-range value.)
#[test]
fn small_consts_still_fold() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const x Int)
        (assert (= x 4611686018427387903))
        (assert (= x 4611686018427387903))
        (assert (> x 4611686018427387902))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "sat");
}

/// Scope consistency: the abstraction flag is snapshot/restored by
/// `push`/`pop`, so a big constant pinned inside a popped scope stops
/// gating later `sat` verdicts.
#[test]
fn big_const_scope_round_trip() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const x Int)
        (push 1)
        (assert (= x 18446744073709551616))
        (assert (> x 18446744073709551616))
        (check-sat)
        (pop 1)
        (assert (> x 0))
        (check-sat)
    "#);
    let verdicts: Vec<&str> = output
        .iter()
        .filter_map(|l| match l.trim() {
            "sat" | "unsat" | "unknown" => Some(l.trim()),
            _ => None,
        })
        .collect();
    assert_eq!(verdicts, vec!["unsat", "sat"]);
}
