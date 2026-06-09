//! QF_BV soundness regression tests.
//!
//! These tests pin down a soundness fix in `BvSolver::check()` wiring inside
//! `theory_manager.rs`.  Previously the embedded BV SAT check was gated out of
//! the common BV atom paths, so OxiZ answered `sat` for several UNSATISFIABLE
//! QF_BV formulas (false SAT).  The fix consults `bv.check()` whenever a BV
//! equality / disequality / comparison is bit-blasted and asserted.
//!
//! Coverage is bidirectional:
//!   * MUST be UNSAT — the unsoundness fixes (no false SAT).
//!   * MUST stay SAT — proves the fix does not over-correct into false UNSAT.
//!
//! Bit widths are kept small (4 or 8) so the embedded SAT solver stays fast.
//!
//! | Script                                              | Expected |
//! |-----------------------------------------------------|----------|
//! | x = #x00 ∧ x = #x01                                  | UNSAT    |
//! | not(= x x)                                           | UNSAT    |
//! | not(= (bvadd x y) (bvadd y x))                       | UNSAT    |
//! | not(= (bvadd (bvadd x y) z) (bvadd x (bvadd y z)))   | UNSAT    |
//! | not(= (bvmul x (bvadd y z)) ...) (distributivity)   | UNSAT    |
//! | not(= (bvmul #x2 x) (bvadd x x))                     | UNSAT    |
//! | (bvult x y) ∧ (bvult y x)                            | UNSAT    |
//! | (bvule x y) ∧ (bvult y x)                            | UNSAT    |
//! | (bvslt x y) ∧ (bvslt y x)                            | UNSAT    |
//! | (bvsle x y) ∧ (bvslt y x)                            | UNSAT    |
//! | (bvuge x y) ∧ (bvult x y)                            | UNSAT    |
//! | x = #x00 ∧ y = #x01                                  | SAT      |
//! | (= (bvadd x y) #x05)                                 | SAT      |
//! | not(= x y)                                           | SAT      |
//! | (bvult x y)                                          | SAT      |
//! | (bvule x x)                                          | SAT      |
//! | (bvule x y) ∧ (bvule y x)                            | SAT      |
//! | not(= (bvadd x y) #x00)                              | SAT      |
//! | g(a)=#x00 ∧ g(b)=#x01 ∧ a=b  (mixed EUF+BV)          | UNSAT    |
//! | g(a)=#x00 ∧ g(b)=#x01  (a,b free)                    | SAT      |
//! | h(#x00)=#x05 ∧ h(#x01)=#x05                          | SAT      |

use oxiz_solver::{Context, SolverResult};

/// Run a single SMT-LIB2 script and return the solver result.
///
/// The verdict is the last `sat` / `unsat` / `unknown` token in the output.
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

// ─────────────────────────────────────────────────────────────────────────
// MUST be UNSAT — the unsoundness fixes (previously returned false SAT)
// ─────────────────────────────────────────────────────────────────────────

/// Primary bug: a variable forced to two distinct constants.
#[test]
fn bv_const_clash_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x00))
(assert (= x #x01))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// `not(= x x)` is a contradiction for any term.
#[test]
fn bv_not_eq_self_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (not (= x x)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Commutativity of bvadd: negating a valid identity is UNSAT.
#[test]
fn bv_add_commutativity_negation_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (not (= (bvadd x y) (bvadd y x))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Associativity of bvadd: negation is UNSAT.
#[test]
fn bv_add_associativity_negation_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))
(assert (not (= (bvadd (bvadd x y) z) (bvadd x (bvadd y z)))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Distributivity of bvmul over bvadd: negation is UNSAT.  4-bit to stay fast.
#[test]
fn bv_mul_distributivity_negation_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(declare-const z (_ BitVec 4))
(assert (not (= (bvmul x (bvadd y z)) (bvadd (bvmul x y) (bvmul x z)))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// `2*x = x + x` is valid; its negation must be UNSAT.
#[test]
fn bv_mul_two_equals_add_negation_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (not (= (bvmul #x02 x) (bvadd x x))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Unsigned strict order is anti-symmetric: x<y ∧ y<x is UNSAT.
#[test]
fn bv_ult_antisymmetry_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvult x y))
(assert (bvult y x))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// x<=y ∧ y<x is contradictory (unsigned).
#[test]
fn bv_ule_with_reverse_ult_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvule x y))
(assert (bvult y x))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Signed strict order is anti-symmetric: x<y ∧ y<x is UNSAT.
#[test]
fn bv_slt_antisymmetry_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvslt x y))
(assert (bvslt y x))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// x<=y ∧ y<x is contradictory (signed).
#[test]
fn bv_sle_with_reverse_slt_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvsle x y))
(assert (bvslt y x))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// `bvuge` desugars to `NOT bvult`, exercising the negated comparator branch.
/// x>=y ∧ x<y is contradictory.
#[test]
fn bv_uge_with_ult_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvuge x y))
(assert (bvult x y))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// `bvsge` desugars to `NOT bvslt` (negated signed comparator branch).
/// x>=y ∧ x<y is contradictory (signed).
#[test]
fn bv_sge_with_slt_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvsge x y))
(assert (bvslt x y))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

// ─────────────────────────────────────────────────────────────────────────
// MUST stay SAT — proves no over-correction into false UNSAT
// ─────────────────────────────────────────────────────────────────────────

/// Distinct variables bound to distinct constants is satisfiable.
#[test]
fn bv_two_vars_distinct_consts_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= x #x00))
(assert (= y #x01))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// A solvable bvadd equation is SAT.
#[test]
fn bv_add_equals_const_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvadd x y) #x05))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Two distinct (free) variables can differ — SAT.
#[test]
fn bv_not_eq_distinct_vars_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (not (= x y)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// A single strict inequality alone is satisfiable.
#[test]
fn bv_ult_alone_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvult x y))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Reflexive non-strict order: x<=x holds — SAT.
#[test]
fn bv_ule_reflexive_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (bvule x x))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// x<=y ∧ y<=x forces x=y but is satisfiable.
#[test]
fn bv_ule_both_directions_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvule x y))
(assert (bvule y x))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// A non-zero sum is achievable — SAT.
#[test]
fn bv_add_not_zero_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (not (= (bvadd x y) #x00)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

// ─────────────────────────────────────────────────────────────────────────
// Mixed EUF + BV congruence (Defect C): distinct BV constants must be unequal
// ─────────────────────────────────────────────────────────────────────────

/// `g(a)=#x00 ∧ g(b)=#x01 ∧ a=b` is UNSAT: congruence forces `g(a)=g(b)`, but
/// the BV constants `#x00` and `#x01` are distinct.  Requires the EUF layer to
/// know `#x00 != #x01` (the `interned_bv_constants` disequality edges).
#[test]
fn bv_const_congruence_clash_is_unsat() {
    let script = r#"
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= a b))
(assert (= (g a) #x00))
(assert (= (g b) #x01))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Without the forced merge (`a` and `b` free) the same shape is SAT: `g` may
/// map the two arguments to the two distinct constants.
#[test]
fn bv_const_congruence_no_merge_is_sat() {
    let script = r#"
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= (g a) #x00))
(assert (= (g b) #x01))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Two equal constants are consistent: `h(#x00)=#x05 ∧ h(#x01)=#x05` is SAT
/// (proves the disequality edges do not over-constrain distinct arguments that
/// legitimately share a result value).
#[test]
fn bv_const_congruence_same_value_is_sat() {
    let script = r#"
(set-logic QF_UFBV)
(declare-fun h ((_ BitVec 8)) (_ BitVec 8))
(assert (= (h #x00) #x05))
(assert (= (h #x01) #x05))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

// ─────────────────────────────────────────────────────────────────────────
// Multiplier + auxiliary-variable false-UNSAT regression
//
// Second soundness bug in the same area: the embedded BV SAT solver kept its
// satisfying model on the trail across incremental `check()` probes (one model
// choice even ended up pinned, as a `Decision`, at decision level 0).  A later
// `assert_const` on the same variable then contradicted that *arbitrary* model
// value and the solver reported a spurious `trivially_unsat`, turning a
// genuinely-SATISFIABLE multiply formula into a false `Unsat`.
//
// The trigger needs (a) an aux equality binding a fresh var to a `bvmul`
// result, (b) a disequality probe, and (c) a later constant constraint on the
// aux that the first probe's leaked model contradicts — e.g. a disjunction with
// a constant disjunct.  The fix rolls the embedded trail back to the committed
// (asserted) prefix after every probe, so each probe re-derives soundly.
//
// All cases below MUST be SAT; the companions further down MUST stay UNSAT to
// prove the fix does not over-correct.
// ─────────────────────────────────────────────────────────────────────────

/// Script A: `aux = x*3 ∧ aux ≠ x`.  SAT (e.g. x=1 → aux=3 ≠ 1).
#[test]
fn bv_mul_aux_diseq_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const aux (_ BitVec 8))
(assert (= aux (bvmul x #x03)))
(assert (not (= aux x)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Script B: `a = x*3 ∧ b = x ∧ a ≠ b`.  SAT (the extra var `b` aliasing `x`
/// must not corrupt the result).
#[test]
fn bv_mul_aux_alias_diseq_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= a (bvmul x #x03)))
(assert (= b x))
(assert (not (= a b)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Script C (control): direct disequality, no aux.  `(bvmul x 3) ≠ x` is SAT.
#[test]
fn bv_mul_direct_diseq_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (not (= (bvmul x #x03) x)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Script D: two distinct aux muls, `a = x*3 ∧ b = x*5 ∧ a ≠ b`.  SAT (they
/// differ at e.g. x=1: 3 ≠ 5).
#[test]
fn bv_two_mul_aux_diseq_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= a (bvmul x #x03)))
(assert (= b (bvmul x #x05)))
(assert (not (= a b)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// The minimal *reproducer* of the leaked-model false UNSAT (4-bit, fast):
/// `a = x*3 ∧ a ≠ x ∧ (a = x ∨ a = 7)`.  The disequality probe used to leave an
/// arbitrary model for `a` pinned at level 0; the constant disjunct `a = 7`
/// then clashed with it.  SAT — e.g. x=13: 13*3 = 39 ≡ 7 (mod 16), and 7 ≠ 13.
#[test]
fn bv_mul_aux_disjunction_const_is_sat_4bit() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(declare-const a (_ BitVec 4))
(assert (= a (bvmul x #x3)))
(assert (distinct a x))
(assert (or (= a x) (= a #x7)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Same reproducer at 8-bit: x=173 gives 173*3 = 519 ≡ 7 (mod 256), 7 ≠ 173.
#[test]
fn bv_mul_aux_disjunction_const_is_sat_8bit() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const a (_ BitVec 8))
(assert (= a (bvmul x #x03)))
(assert (distinct a x))
(assert (or (= a x) (= a #x07)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// A multiply equation reachable only via a specific witness must stay SAT even
/// when an aux disequality probe ran first: `a = x*3 ∧ a ≠ x ∧ a = 7`.
#[test]
fn bv_mul_aux_diseq_then_const_is_sat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(declare-const a (_ BitVec 4))
(assert (= a (bvmul x #x3)))
(assert (distinct a x))
(assert (= a #x7))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

// — companions that MUST stay UNSAT (no false SAT from the trail-rollback) —

/// Two aux vars bound to the *same* product, asserted distinct: UNSAT.
#[test]
fn bv_same_mul_aux_distinct_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= a (bvmul x #x03)))
(assert (= b (bvmul x #x03)))
(assert (distinct a b))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Commuted operands bind the same product; distinct aux ⇒ UNSAT:
/// `a = 3*x ∧ b = x*3 ∧ a ≠ b`.
#[test]
fn bv_commuted_mul_aux_distinct_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= a (bvmul #x03 x)))
(assert (= b (bvmul x #x03)))
(assert (distinct a b))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// A true equivalence behind aux bindings stays UNSAT:
/// `a = x*2 ∧ b = x+x ∧ a ≠ b`.
#[test]
fn bv_mul_add_equiv_aux_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(declare-const a (_ BitVec 4))
(declare-const b (_ BitVec 4))
(assert (= a (bvmul x #x2)))
(assert (= b (bvadd x x)))
(assert (not (= a b)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// `x*3 = x+x+x` distributivity, no aux: UNSAT.
#[test]
fn bv_mul3_equals_triple_add_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (not (= (bvmul x #x3) (bvadd (bvadd x x) x))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// `2*x = x+x`, no aux: UNSAT.
#[test]
fn bv_two_mul_equals_double_add_is_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (not (= (bvmul #x2 x) (bvadd x x))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}
