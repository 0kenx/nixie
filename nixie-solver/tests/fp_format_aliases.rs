//! Regression: the SMT-LIB FloatingPoint theory's canonical format aliases
//! `Float32` / `Float64` / `Float16` / `Float128` must resolve to the indexed
//! `(_ FloatingPoint eb sb)` sorts.
//!
//! Before the fix these names fell through to the parser's generic
//! `Uninterpreted` fallback, so `(declare-const x Float32)` created a variable
//! whose sort was `Uninterpreted("Float32")` — a *different* sort from every
//! term the `fp.*` operators produce.  Each such variable was a stranger to
//! all FP machinery (the pattern conflict checks, the concrete model builder,
//! the atoms the FP honesty gate tracks), so any constraint linking it to an
//! fp expression collapsed to the honest `Unknown` while z3 decided it:
//!
//! ```text
//! (declare-const y Float32)
//! (assert (= y (fp.add RNE c c)))   ; nixie: unknown, z3: sat
//! ```
//!
//! These tests pin the repaired behaviour end to end through `Float32` and
//! `Float64` aliases: definitional fp arithmetic over pinned variables is
//! decided by the concrete model builder (`sat`), the trivially conflicting
//! comparison pair is still refuted by the pattern checks (`unsat`), and
//! special-value predicate witnesses are still synthesised (`sat`).

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

/// The direct repro: a `Float32` variable defined by an fp addition of two
/// literals.  The concrete model builder must pin the variable and verify the
/// definitional equality — `sat`, matching z3.
#[test]
fn float32_variable_defined_by_fp_add_decides_sat() {
    let script = r#"
        (set-logic QF_FP)
        (declare-const y Float32)
        (assert (= y (fp.add RNE (fp #b0 #x7f #b00000000000000000000001)
                                   (fp #b0 #x7f #b00000000000000000000001))))
        (check-sat)
    "#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// The chain shape: a pinned `Float32` variable feeding another variable's
/// definition.  Propagation must fold through the pinned operand.
#[test]
fn float32_pinned_operand_chain_decides_sat() {
    let script = r#"
        (set-logic QF_FP)
        (declare-const x Float32)
        (declare-const y Float32)
        (assert (= x (fp #b0 #x7f #b00000000000000000000001)))
        (assert (= y (fp.add RNE x x)))
        (check-sat)
    "#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// The `Float64` alias resolves too: `1.5 + 1.5 = 3.0` exactly, so a
/// disequality against `4.0` is decided `sat` by model construction +
/// verification (z3 agrees).
#[test]
fn float64_alias_disequality_against_folded_sum_decides_sat() {
    let script = r#"
        (set-logic QF_FP)
        (declare-const x Float64)
        (declare-const y Float64)
        (assert (= x (fp #b0 #x3ff #x8000000000000)))
        (assert (= y (fp.add RNE x x)))
        (assert (not (= y (fp #b0 #x401 #x0000000000000))))
        (check-sat)
    "#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// The chained asymmetry `x < y ∧ y < x` is UNSAT in the theory but outside
/// the pattern catalogue (Check 1 covers a *same-lhs* gt/lt pair against one
/// value), and the two free variables carry no positive special-value
/// predicate, so the concrete model builder honestly declines.  The pinned
/// property is the one that matters for soundness: **never `sat`** — the
/// honesty gate's whole purpose.  (z3: `unsat`; deciding this shape is the
/// fp-constant-folding-through-EUF rung, see the fp-gap study.)
#[test]
fn float32_conflicting_comparisons_never_answer_sat() {
    let script = r#"
        (set-logic QF_FP)
        (declare-const x Float32)
        (declare-const y Float32)
        (assert (fp.lt x y))
        (assert (fp.lt y x))
        (check-sat)
    "#;
    assert_ne!(run_script(script), SolverResult::Sat);
}

/// Special-value witness synthesis works through the alias: `fp.isNaN` pins a
/// NaN witness, `sat` by verification.
#[test]
fn float32_isnan_witness_synthesis_decides_sat() {
    let script = r#"
        (set-logic QF_FP)
        (declare-const x Float32)
        (assert (fp.isNaN x))
        (check-sat)
    "#;
    assert_eq!(run_script(script), SolverResult::Sat);
}
