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

// ─────────────────────────────────────────────────────────────────────────
// Issue #17 — always-false / always-true strict bit-vector comparisons
//
// `(bvult t #b0)` is false for every `t` (nothing is unsigned-less-than
// zero), and likewise `(bvslt t MIN_SIGNED)`, `(bvugt t MAX_UNSIGNED)` and
// `(bvsgt t MAX_SIGNED)`.  These atoms used to survive unconstrained and the
// solver answered a spurious `sat` with a malformed model value (`#x-1`).
//
// Dually `(bvule #b0 t)`, `(bvuge MAX t)`, `(bvsle MIN t)` and
// `(bvsge MAX_SIGNED t)` are tautologies, while `(bvule t #b0)` and
// `(bvsle t MIN)` remain genuinely satisfiable (only by `0` / `MIN`) — the
// tests below pin both directions so the fix cannot over-correct.
// ─────────────────────────────────────────────────────────────────────────

/// Run a script and return its raw responses (for `get-value` inspection).
fn run_script_outputs(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script).unwrap_or_default()
}

/// Build a single-assertion QF_BV script over one `width`-bit constant `x`.
fn bv_script(width: u32, assertion: &str) -> String {
    format!(
        "(set-logic QF_BV)\n(declare-const x (_ BitVec {width}))\n\
         (assert {assertion})\n(check-sat)\n(get-value (x))\n"
    )
}

/// All-zero literal of `width` bits, e.g. `#x0000` for 16.
fn zero_lit(width: u32) -> String {
    format!("#x{}", "0".repeat((width / 4) as usize))
}

/// Signed-minimum literal (`100…0`) of `width` bits, e.g. `#x8000` for 16.
fn signed_min_lit(width: u32) -> String {
    format!("#x8{}", "0".repeat((width / 4 - 1) as usize))
}

/// Unsigned-maximum literal (`111…1`) of `width` bits.
fn unsigned_max_lit(width: u32) -> String {
    format!("#x{}", "f".repeat((width / 4) as usize))
}

/// Signed-maximum literal (`011…1`) of `width` bits.
fn signed_max_lit(width: u32) -> String {
    format!("#x7{}", "f".repeat((width / 4 - 1) as usize))
}

/// Widths exercised by the issue-17 regressions (the reporter tried 4/8/16/32).
const ISSUE_17_WIDTHS: [u32; 4] = [4, 8, 16, 32];

/// Extract the value literal from a `(get-value (x))` response.
fn model_literal(outputs: &[String]) -> Option<String> {
    let response = outputs.iter().rev().find(|line| line.starts_with("(("))?;
    let inner = response
        .trim()
        .trim_start_matches('(')
        .trim_end_matches(')');
    inner.split_whitespace().nth(1).map(str::to_string)
}

/// Parse a well-formed SMT-LIB bit-vector literal of exactly `width` bits.
///
/// Returns `None` for anything that is not a literal of that exact width —
/// which is what `#x-1` (the value reported in issue #17) hits.
fn parse_bv_literal(literal: &str, width: u32) -> Option<u128> {
    if let Some(digits) = literal.strip_prefix("#x") {
        if digits.len() != (width / 4) as usize {
            return None;
        }
        return u128::from_str_radix(digits, 16).ok();
    }
    if let Some(digits) = literal.strip_prefix("#b") {
        if digits.len() != width as usize {
            return None;
        }
        return u128::from_str_radix(digits, 2).ok();
    }
    None
}

/// `(bvult x 0)` — unsigned-less-than zero — is UNSAT at every width.
#[test]
fn test_issue_17_bvult_zero_unsat() {
    for width in ISSUE_17_WIDTHS {
        let script = bv_script(width, &format!("(bvult x {})", zero_lit(width)));
        assert_eq!(
            run_script(&script),
            SolverResult::Unsat,
            "(bvult x 0) must be unsat at width {width}"
        );
    }
}

/// `(bvslt x MIN_SIGNED)` is UNSAT at every width.
#[test]
fn test_issue_17_bvslt_signed_min_unsat() {
    for width in ISSUE_17_WIDTHS {
        let script = bv_script(width, &format!("(bvslt x {})", signed_min_lit(width)));
        assert_eq!(
            run_script(&script),
            SolverResult::Unsat,
            "(bvslt x MIN_SIGNED) must be unsat at width {width}"
        );
    }
}

/// `(bvsgt MIN_SIGNED x)` is UNSAT at every width.
#[test]
fn test_issue_17_bvsgt_signed_min_unsat() {
    for width in ISSUE_17_WIDTHS {
        let script = bv_script(width, &format!("(bvsgt {} x)", signed_min_lit(width)));
        assert_eq!(
            run_script(&script),
            SolverResult::Unsat,
            "(bvsgt MIN_SIGNED x) must be unsat at width {width}"
        );
    }
}

/// `(bvugt x MAX_UNSIGNED)` and `(bvsgt x MAX_SIGNED)` are the remaining two
/// always-false strict bounds.
#[test]
fn test_issue_17_strict_upper_bounds_unsat() {
    for width in ISSUE_17_WIDTHS {
        for assertion in [
            format!("(bvugt x {})", unsigned_max_lit(width)),
            format!("(bvsgt x {})", signed_max_lit(width)),
            format!("(bvult {} x)", unsigned_max_lit(width)),
            format!("(bvslt {} x)", signed_max_lit(width)),
        ] {
            assert_eq!(
                run_script(&bv_script(width, &assertion)),
                SolverResult::Unsat,
                "{assertion} must be unsat at width {width}"
            );
        }
    }
}

/// The dual tautologies (`0 <=u t`, `t <=u MAX`, `MIN <=s t`, `t <=s MAX_S`)
/// must stay SAT, and their negations must be UNSAT.
#[test]
fn test_issue_17_tautological_bounds() {
    for width in ISSUE_17_WIDTHS {
        for assertion in [
            format!("(bvule {} x)", zero_lit(width)),
            format!("(bvule x {})", unsigned_max_lit(width)),
            format!("(bvsle {} x)", signed_min_lit(width)),
            format!("(bvsle x {})", signed_max_lit(width)),
        ] {
            assert_eq!(
                run_script(&bv_script(width, &assertion)),
                SolverResult::Sat,
                "{assertion} must be sat at width {width}"
            );
            assert_eq!(
                run_script(&bv_script(width, &format!("(not {assertion})"))),
                SolverResult::Unsat,
                "(not {assertion}) must be unsat at width {width}"
            );
        }
    }
}

/// `(bvule x 0)` stays SAT — satisfied only by `x = 0`.  Guards against
/// over-correcting the strict-comparison fix into the non-strict family.
#[test]
fn test_issue_17_bvule_zero_sat() {
    for width in ISSUE_17_WIDTHS {
        let script = bv_script(width, &format!("(bvule x {})", zero_lit(width)));
        let outputs = run_script_outputs(&script);
        assert!(
            outputs.iter().any(|line| line.trim() == "sat"),
            "(bvule x 0) must be sat at width {width}: {outputs:?}"
        );
        let literal = model_literal(&outputs)
            .unwrap_or_else(|| panic!("no model value at width {width}: {outputs:?}"));
        let value = parse_bv_literal(&literal, width)
            .unwrap_or_else(|| panic!("malformed model literal {literal} at width {width}"));
        assert_eq!(value, 0, "(bvule x 0) forces x = 0 at width {width}");
    }
}

/// `(bvsle x MIN_SIGNED)` stays SAT — satisfied only by `x = MIN_SIGNED`.
#[test]
fn test_issue_17_bvsle_signed_min_sat() {
    for width in ISSUE_17_WIDTHS {
        let script = bv_script(width, &format!("(bvsle x {})", signed_min_lit(width)));
        let outputs = run_script_outputs(&script);
        assert!(
            outputs.iter().any(|line| line.trim() == "sat"),
            "(bvsle x MIN_SIGNED) must be sat at width {width}: {outputs:?}"
        );
        let literal = model_literal(&outputs)
            .unwrap_or_else(|| panic!("no model value at width {width}: {outputs:?}"));
        let value = parse_bv_literal(&literal, width)
            .unwrap_or_else(|| panic!("malformed model literal {literal} at width {width}"));
        assert_eq!(
            value,
            1u128 << (width - 1),
            "(bvsle x MIN_SIGNED) forces x = MIN_SIGNED at width {width}"
        );
    }
}

/// Every reported bit-vector model value must be a well-formed literal of the
/// declared width.  Issue #17 printed `#x-1` (a negative integer rendered in
/// decimal behind a `#x` prefix) for `(bvult x #x00)`.
#[test]
fn test_issue_17_bv_model_value_well_formed() {
    for width in ISSUE_17_WIDTHS {
        for assertion in [
            format!(
                "(bvult x {})",
                format_args!("#x{}", "1".repeat((width / 4) as usize))
            ),
            format!("(bvugt x {})", zero_lit(width)),
            format!("(bvule x {})", zero_lit(width)),
            format!("(bvsle x {})", signed_min_lit(width)),
            format!("(bvsge x {})", signed_max_lit(width)),
        ] {
            let outputs = run_script_outputs(&bv_script(width, &assertion));
            if !outputs.iter().any(|line| line.trim() == "sat") {
                continue;
            }
            let literal = model_literal(&outputs).unwrap_or_else(|| {
                panic!("no model value for {assertion} at width {width}: {outputs:?}")
            });
            assert!(
                parse_bv_literal(&literal, width).is_some(),
                "model value {literal} for {assertion} is not a well-formed \
                 {width}-bit literal"
            );
        }
    }
}

/// A comparison between two literals is decided by constant folding, with no
/// free variable involved at all.
#[test]
fn test_issue_17_constant_only_comparison_folds() {
    let unsat_cases = [
        "(bvsgt #x89d8a340 #x00000001)",
        "(bvult #xff #x00)",
        "(bvslt #x7f #x80)",
        "(bvuge #x01 #x02)",
    ];
    for assertion in unsat_cases {
        let script = format!("(set-logic QF_BV)\n(assert {assertion})\n(check-sat)\n");
        assert_eq!(
            run_script(&script),
            SolverResult::Unsat,
            "{assertion} folds to false"
        );
    }
    let sat_cases = [
        "(bvslt #x80 #x7f)",
        "(bvult #x00 #xff)",
        "(bvsge #x7f #x80)",
    ];
    for assertion in sat_cases {
        let script = format!("(set-logic QF_BV)\n(assert {assertion})\n(check-sat)\n");
        assert_eq!(
            run_script(&script),
            SolverResult::Sat,
            "{assertion} folds to true"
        );
    }
}

/// A fact that only holds inside one branch of a disjunction must not be read
/// as an unconditional constraint.  `check_bv.rs`'s conflict collector used to
/// descend through `Or` / `Not`, refuting this satisfiable script.
#[test]
fn test_issue_17_conditional_bv_fact_not_unconditional() {
    let script = r#"
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (or (= (bvurem a b) #x05) (= a #x01)))
(assert (= b #x03))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// A bit-vector fact nested inside a *Boolean* equality is conditional too.
///
/// This AST has no `Iff`: `(= p q)` over two Bool-sorted terms builds a
/// `TermKind::Eq`, so `(= (= r (bvor x y)) p)` is a polarity boundary — it is
/// satisfied just as well with both sides false, and `r = (bvor x y)` need not
/// hold.  `check_bv.rs`'s collector used to recurse into an equality's operands
/// and record the inner bit-vector fact unconditionally, which let the
/// definite-conflict checks refute these satisfiable scripts.
#[test]
fn test_issue_17_bool_eq_polarity_boundary() {
    // Hits the `bvor` result check: 1 | 2 = 3, and r is pinned to 8.
    let or_script = r#"
(set-logic QF_BV)
(declare-const p Bool)
(declare-const r (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (= r (bvor x y)) p))
(assert (not p))
(assert (= x #x01))
(assert (= y #x02))
(assert (= r #x08))
(check-sat)
"#;
    assert_ne!(
        run_script(or_script),
        SolverResult::Unsat,
        "r = (bvor x y) sits behind a Boolean equality asserted false; it must \
         not be collected as an unconditional fact"
    );

    // Hits the remainder-bound check: a bvurem by #x03 can never be #x05.
    let urem_script = r#"
(set-logic QF_BV)
(declare-const p Bool)
(declare-const r (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= (= r (bvurem a b)) p))
(assert (not p))
(assert (= b #x03))
(assert (= r #x05))
(check-sat)
"#;
    assert_ne!(
        run_script(urem_script),
        SolverResult::Unsat,
        "r = (bvurem a b) sits behind a Boolean equality asserted false; the \
         remainder-bound check must not fire on it"
    );
}

/// Wide bit-vector comparison conflicts must be refuted by propagation, not by
/// exhaustive search.  Before the incremental-propagation fix in `oxiz-sat`,
/// this 32-bit conflict took over a minute.
#[test]
fn test_issue_17_wide_comparison_conflict_is_fast() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(assert (and (bvult x #x00000005) (bvugt x #x00000004) (bvugt x #x00000005)))
(check-sat)
"#;
    let start = std::time::Instant::now();
    assert_eq!(run_script(script), SolverResult::Unsat);
    assert!(
        start.elapsed() < std::time::Duration::from_secs(10),
        "32-bit comparison conflict took {:?}; it should be decided by unit \
         propagation in milliseconds",
        start.elapsed()
    );
}

/// `x <=u (x bvxor x)` is satisfiable — `x bvxor x` is zero, so every `x` with
/// `x <=u 0` works, i.e. `x = 0`.
///
/// This is a false-`Unsat` regression guard for the embedded SAT solver's
/// chronological backtracking.  Because chronological backtracking keeps the
/// decisions between the backjump level and the conflict level, the trail stops
/// being sorted by decision level; when the engine mishandled that ordering the
/// bit-blasted encoding of this constraint was refuted outright.  The engine is
/// fixed rather than configured around it, so what this pins is that the default
/// bit-blasting path still answers `Sat` at several widths.
#[test]
fn test_issue_17_bitblasted_xor_bound_is_sat() {
    for width in [4u32, 8, 16] {
        let script = bv_script(width, "(bvule x (bvxor x x))");
        assert_eq!(
            run_script(&script),
            SolverResult::Sat,
            "(bvule x (bvxor x x)) must be sat at width {width}"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Structural bit-vector constant folding.
//
// Issue #17's comparison folding only fires once a bound has actually become
// a literal, so `bvadd`/`bvand`/`bvshl`/... over literal operands have to be
// evaluated at construction time as well.  A ground BV formula carries no BV
// variable at all, so nothing bit-blasts it: an unfolded compound term used to
// survive as an unconstrained Boolean atom and the solver answered a spurious
// `sat`.  Every expected value below was cross-checked against z3 4.15.
// ─────────────────────────────────────────────────────────────────────────

/// A ground (variable-free) BV equality is decided by folding alone.
#[test]
fn test_ground_bv_equalities_are_decided_by_folding() {
    // (script, expected) — each left-hand side folds to the literal quoted in
    // the comment, so the equality is decided outright.
    let cases: [(&str, SolverResult); 10] = [
        // bvlshr by 14 >= width 4 -> #x0; bvadd #xe #x7 -> #x5.
        (
            "(assert (= (bvlshr #xc #xe) (bvadd #xe #x7)))",
            SolverResult::Unsat,
        ),
        ("(assert (= (bvlshr #xc #xe) #x0))", SolverResult::Sat),
        // bvsub #x0 #x4 -> #xc, bvsdiv #x2 #x8 -> #x0, so bvxor -> #xc;
        // bvashr #x6 #xd -> #x0 (non-negative, distance >= width).
        (
            "(assert (= (bvxor (bvsub #x0 #x4) (bvsdiv #x2 #x8)) (bvashr #x6 #xd)))",
            SolverResult::Unsat,
        ),
        // bvor #x7fffffff #x00000001 -> #x7fffffff.
        (
            "(assert (= (bvor #x7fffffff #x00000001) #x7fffffff))",
            SolverResult::Sat,
        ),
        (
            "(assert (not (= (bvor #x7fffffff #x00000001) #x7fffffff)))",
            SolverResult::Unsat,
        ),
        // Division by zero is total.
        ("(assert (= (bvudiv #x07 #x00) #xff))", SolverResult::Sat),
        ("(assert (= (bvurem #x07 #x00) #x07))", SolverResult::Sat),
        ("(assert (= (bvsrem #xf9 #x00) #xf9))", SolverResult::Sat),
        ("(assert (= (bvsmod #xf9 #x00) #xf9))", SolverResult::Sat),
        // bvsdiv by zero is -1 for a non-negative dividend, 1 for a negative one.
        (
            "(assert (and (= (bvsdiv #x07 #x00) #xff) (= (bvsdiv #xf9 #x00) #x01)))",
            SolverResult::Sat,
        ),
    ];
    for (assertion, expected) in cases {
        let script = format!("(set-logic QF_BV)\n{assertion}\n(check-sat)\n");
        assert_eq!(
            run_script(&script),
            expected,
            "ground assertion {assertion} must be {expected:?}"
        );
    }
}

/// A folded compound bound turns a comparison into an always-false (or
/// always-true) atom, which is exactly what issue #17's comparison folding
/// then decides.  Both directions are pinned so the fold cannot over-correct.
#[test]
fn test_folded_bounds_decide_comparisons() {
    for width in ISSUE_17_WIDTHS {
        let zero = zero_lit(width);
        let max = unsigned_max_lit(width);
        // (bvor 0 MAX) folds to MAX, so `x >u MAX` is unsatisfiable ...
        let unsat = bv_script(width, &format!("(bvugt x (bvor {zero} {max}))"));
        assert_eq!(
            run_script(&unsat),
            SolverResult::Unsat,
            "(bvugt x (bvor 0 MAX)) must be unsat at width {width}"
        );
        // ... and (bvand 0 MAX) folds to 0, so `x <u 0` is too.
        let unsat = bv_script(width, &format!("(bvult x (bvand {zero} {max}))"));
        assert_eq!(
            run_script(&unsat),
            SolverResult::Unsat,
            "(bvult x (bvand 0 MAX)) must be unsat at width {width}"
        );
        // The dual bounds stay satisfiable.
        let sat = bv_script(width, &format!("(bvule x (bvor {zero} {max}))"));
        assert_eq!(
            run_script(&sat),
            SolverResult::Sat,
            "(bvule x (bvor 0 MAX)) must be sat at width {width}"
        );
    }
}

/// `((_ extract i j) x)` — the standard SMT-LIB spelling, where the indexed
/// identifier is its own S-expression — must be lowered to a real bit-vector
/// extraction.  It used to degrade to a `Bool`-sorted uninterpreted
/// application, so `(= ((_ extract 3 0) #xab) #xc)` answered `sat` and a
/// `concat` over it could not even determine an operand width.
#[test]
fn test_indexed_extract_application_is_a_bitvector_extraction() {
    let cases: [(&str, SolverResult); 6] = [
        ("(assert (= ((_ extract 3 0) #xab) #xb))", SolverResult::Sat),
        (
            "(assert (= ((_ extract 3 0) #xab) #xc))",
            SolverResult::Unsat,
        ),
        ("(assert (= ((_ extract 7 4) #xab) #xa))", SolverResult::Sat),
        (
            "(assert (= (concat #x0 ((_ extract 3 0) #xab)) #x0b))",
            SolverResult::Sat,
        ),
        (
            "(assert (= (concat #b0000 ((_ extract 3 3) #xab)) #b00001))",
            SolverResult::Sat,
        ),
        (
            "(assert (= (concat #b0000 ((_ extract 3 3) #xab)) #b00000))",
            SolverResult::Unsat,
        ),
    ];
    for (assertion, expected) in cases {
        let width_agnostic = format!("(set-logic QF_BV)\n{assertion}\n(check-sat)\n");
        assert_eq!(
            run_script(&width_agnostic),
            expected,
            "assertion {assertion} must be {expected:?}"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────
// Symbolic operands under the operations the BV dispatch used to drop.
//
// `TheoryManager::process_constraint`'s positive-`Eq` branch dispatched on a
// whitelist of "BV operation" `TermKind`s that named only the arithmetic and
// bitwise ops.  A BV equality whose head was `concat`, `extract`, a shift, or
// a BV-sorted `ite` — which is what `bvsmod`, `bvcomp`, `rotate_*` and
// `zero_extend`/`sign_extend` lower to — matched no case, was never asserted
// into the embedded SAT solver, and survived as a *free boolean*: the solver
// answered `sat` with a model that does not satisfy the formula.  Constant
// folding hides this whenever every operand is a literal, so each test below
// keeps at least one symbolic operand.
//
// A second, independent defect lived in the bit-blasted circuit itself:
// `(bvsdiv s 0)` was pinned to all-ones for both signs of `s`, whereas
// SMT-LIB gives `1` for a negative `s`.  That one produced false `sat` *and*
// false `unsat` verdicts, and only ever with a symbolic dividend.
//
// Every expected verdict below was cross-checked against z3 4.15.4.
// ─────────────────────────────────────────────────────────────────────────

/// Assert a list of `(script-body, expected)` QF_BV cases.
fn assert_bv_cases(cases: &[(&str, SolverResult)]) {
    for (body, expected) in cases {
        let script = format!("(set-logic QF_BV)\n{body}\n(check-sat)\n");
        assert_eq!(
            run_script(&script),
            *expected,
            "QF_BV case must be {expected:?}:\n{body}"
        );
    }
}

/// `(concat CONST y)` pins the high bits to the literal, so a target with a
/// set bit above the symbolic part is unreachable.  This is the reported
/// minimal repro plus the same shape at widths 4/8/16/32.
#[test]
fn test_bv_concat_const_high_symbolic_low_unsat() {
    assert_bv_cases(&[
        // Reported repro: bits 2..7 of `(concat #b000000 w)` are all zero, so
        // it can never equal `#x10` (bit 4 set).
        (
            "(declare-const w (_ BitVec 2))\n(assert (= (concat #b000000 w) #x10))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const y (_ BitVec 2))\n(assert (= (concat #b00 y) #x8))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const y (_ BitVec 4))\n(assert (= (concat #x0 y) #x80))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const y (_ BitVec 8))\n(assert (= (concat #x00 y) #x8000))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const y (_ BitVec 16))\n\
             (assert (= (concat #x0000 y) #x80000000))",
            SolverResult::Unsat,
        ),
        // Nested under an extract, so both dropped kinds appear at once.
        (
            "(declare-const x (_ BitVec 8))\n\
             (assert (= (concat #b0000 ((_ extract 3 0) x)) #x10))",
            SolverResult::Unsat,
        ),
    ]);
}

/// The mirrored shape: `(concat y CONST)` pins the *low* bits, so a target
/// whose low half is non-zero is unreachable.
#[test]
fn test_bv_concat_symbolic_high_const_low_unsat() {
    assert_bv_cases(&[
        (
            "(declare-const y (_ BitVec 2))\n(assert (= (concat y #b00) #x1))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const y (_ BitVec 4))\n(assert (= (concat y #x0) #x01))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const y (_ BitVec 8))\n(assert (= (concat y #x00) #x0001))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const y (_ BitVec 16))\n\
             (assert (= (concat y #x0000) #x00000001))",
            SolverResult::Unsat,
        ),
    ]);
}

/// Control: the same `concat` shapes stay satisfiable when the target *is*
/// reachable, so the fix cannot over-correct into a false UNSAT.
#[test]
fn test_bv_concat_symbolic_controls_stay_sat() {
    assert_bv_cases(&[
        (
            "(declare-const w (_ BitVec 2))\n(assert (= (concat #b000000 w) #x02))",
            SolverResult::Sat,
        ),
        (
            "(declare-const y (_ BitVec 2))\n(assert (= (concat #b00 y) #x1))",
            SolverResult::Sat,
        ),
        (
            "(declare-const y (_ BitVec 4))\n(assert (= (concat #x0 y) #x01))",
            SolverResult::Sat,
        ),
        (
            "(declare-const y (_ BitVec 8))\n(assert (= (concat #x00 y) #x0001))",
            SolverResult::Sat,
        ),
        (
            "(declare-const y (_ BitVec 16))\n\
             (assert (= (concat #x0000 y) #x00000001))",
            SolverResult::Sat,
        ),
        (
            "(declare-const y (_ BitVec 4))\n(assert (= (concat y #x0) #x80))",
            SolverResult::Sat,
        ),
        (
            "(declare-const x (_ BitVec 8))\n\
             (assert (= (concat #b0000 ((_ extract 3 0) x)) #x0a))",
            SolverResult::Sat,
        ),
    ]);
}

/// Both halves of a symbolic word extracted to zero forces the word to zero.
#[test]
fn test_bv_extract_symbolic_operand_is_constrained() {
    assert_bv_cases(&[
        (
            "(declare-const x (_ BitVec 8))\n\
             (assert (= ((_ extract 7 4) x) #x0))\n\
             (assert (= ((_ extract 3 0) x) #x0))\n\
             (assert (not (= x #x00)))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const x (_ BitVec 16))\n\
             (assert (= ((_ extract 15 8) x) #x00))\n\
             (assert (= ((_ extract 7 0) x) #x00))\n\
             (assert (not (= x #x0000)))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const x (_ BitVec 32))\n\
             (assert (= ((_ extract 31 16) x) #x0000))\n\
             (assert (= ((_ extract 15 0) x) #x0000))\n\
             (assert (not (= x #x00000000)))",
            SolverResult::Unsat,
        ),
        // Control: consistent halves stay satisfiable.
        (
            "(declare-const x (_ BitVec 8))\n\
             (assert (= ((_ extract 7 4) x) #x0))\n\
             (assert (= ((_ extract 3 0) x) #xa))",
            SolverResult::Sat,
        ),
    ]);
}

/// Shifts by a literal amount constrain the result's bits exactly: a left
/// shift cannot produce an odd value, a logical right shift cannot set the
/// top bit, and an arithmetic right shift replicates the sign.
#[test]
fn test_bv_shift_symbolic_operand_is_constrained() {
    assert_bv_cases(&[
        (
            "(declare-const x (_ BitVec 4))\n(assert (= (bvshl x #x1) #x7))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const x (_ BitVec 8))\n(assert (= (bvshl x #x01) #x07))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const x (_ BitVec 16))\n(assert (= (bvshl x #x0002) #x0007))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const x (_ BitVec 32))\n\
             (assert (= (bvshl x #x00000002) #x00000007))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const x (_ BitVec 8))\n(assert (= (bvlshr x #x01) #x80))",
            SolverResult::Unsat,
        ),
        // `bvashr` by one duplicates the sign into bits 7 and 6.
        (
            "(declare-const x (_ BitVec 8))\n(assert (= (bvashr x #x01) #x40))",
            SolverResult::Unsat,
        ),
        // A shift also has to reach the BV solver from underneath a
        // *comparison*, not just an equality.
        (
            "(declare-const x (_ BitVec 8))\n\
             (assert (bvult (bvshl x #x08) #x01))\n\
             (assert (not (= (bvshl x #x08) #x00)))",
            SolverResult::Unsat,
        ),
    ]);
}

/// Control: the same shifts stay satisfiable for reachable targets.
#[test]
fn test_bv_shift_controls_stay_sat() {
    assert_bv_cases(&[
        (
            "(declare-const x (_ BitVec 8))\n(assert (= (bvshl x #x01) #x06))",
            SolverResult::Sat,
        ),
        (
            "(declare-const x (_ BitVec 8))\n(assert (= (bvlshr x #x01) #x40))",
            SolverResult::Sat,
        ),
        (
            "(declare-const x (_ BitVec 8))\n(assert (= (bvashr x #x01) #xc0))",
            SolverResult::Sat,
        ),
        (
            "(declare-const x (_ BitVec 32))\n\
             (assert (= (bvshl x #x00000002) #x00000004))",
            SolverResult::Sat,
        ),
    ]);
}

/// `bvsmod` lowers to an `ite` chain, so it exercises the BV-sorted `ite`
/// dispatch.  With a literal divisor of `3` the result's magnitude is below
/// `3` and its sign follows the divisor, so `7` is out of range.
#[test]
fn test_bvsmod_symbolic_divisor_range() {
    assert_bv_cases(&[
        (
            "(declare-const v (_ BitVec 4))\n(assert (= (bvsmod v #x3) #x7))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const v (_ BitVec 8))\n(assert (= (bvsmod v #x03) #x07))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const v (_ BitVec 16))\n\
             (assert (= (bvsmod v #x0003) #x0007))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const v (_ BitVec 32))\n\
             (assert (= (bvsmod v #x00000003) #x00000007))",
            SolverResult::Unsat,
        ),
        // The result's sign follows the *divisor*, not the dividend:
        // `bvsmod(-7, 3) = 2`, never `-1`.
        (
            "(declare-const v (_ BitVec 8))\n(assert (= v #xf9))\n\
             (assert (= (bvsmod v #x03) #xff))",
            SolverResult::Unsat,
        ),
    ]);
}

/// The mirrored `bvsmod` shape, with the dividend a literal and the divisor
/// symbolic — the second reported repro.
#[test]
fn test_bvsmod_symbolic_divisor_operand_unsat() {
    assert_bv_cases(&[
        (
            "(declare-const v (_ BitVec 8))\n(assert (= (bvsmod #xd5 v) #x7f))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const v (_ BitVec 4))\n(assert (= (bvsmod #x5 v) #x7))",
            SolverResult::Unsat,
        ),
    ]);
}

/// Control: `bvsmod` stays satisfiable for in-range targets.
#[test]
fn test_bvsmod_controls_stay_sat() {
    assert_bv_cases(&[
        (
            "(declare-const v (_ BitVec 8))\n(assert (= (bvsmod v #x03) #x02))",
            SolverResult::Sat,
        ),
        (
            "(declare-const v (_ BitVec 8))\n(assert (= (bvsmod #xd5 v) #x00))",
            SolverResult::Sat,
        ),
        (
            "(declare-const v (_ BitVec 8))\n(assert (= v #xf9))\n\
             (assert (= (bvsmod v #x03) #x02))",
            SolverResult::Sat,
        ),
        (
            "(declare-const v (_ BitVec 32))\n\
             (assert (= (bvsmod v #x00000003) #x00000002))",
            SolverResult::Sat,
        ),
    ]);
}

/// `(bvsdiv s 0)` is `-1` for a non-negative `s` and `1` for a negative one —
/// the circuit used to answer all-ones for both, which is a *wrong value*
/// rather than a missing constraint, so it produced false `sat` and false
/// `unsat` alike.
#[test]
fn test_bvsdiv_by_zero_follows_dividend_sign() {
    assert_bv_cases(&[
        (
            "(declare-const x (_ BitVec 4))\n(assert (= x #x9))\n\
             (assert (= (bvsdiv x #x0) #xf))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const x (_ BitVec 8))\n(assert (bvslt x #x00))\n\
             (assert (= (bvsdiv x #x00) #xff))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const x (_ BitVec 16))\n(assert (bvslt x #x0000))\n\
             (assert (= (bvsdiv x #x0000) #xffff))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const x (_ BitVec 32))\n\
             (assert (bvslt x #x00000000))\n\
             (assert (= (bvsdiv x #x00000000) #xffffffff))",
            SolverResult::Unsat,
        ),
        // Dually, a non-negative dividend cannot yield `1`.
        (
            "(declare-const x (_ BitVec 8))\n(assert (bvsge x #x00))\n\
             (assert (= (bvsdiv x #x00) #x01))",
            SolverResult::Unsat,
        ),
    ]);
}

/// Control: the correct divide-by-zero values stay satisfiable at both signs,
/// including with a symbolic divisor forced to zero.
#[test]
fn test_bvsdiv_by_zero_controls_stay_sat() {
    assert_bv_cases(&[
        (
            "(declare-const x (_ BitVec 8))\n(assert (bvslt x #x00))\n\
             (assert (= (bvsdiv x #x00) #x01))",
            SolverResult::Sat,
        ),
        (
            "(declare-const x (_ BitVec 8))\n(assert (bvsge x #x00))\n\
             (assert (= (bvsdiv x #x00) #xff))",
            SolverResult::Sat,
        ),
        (
            "(declare-const x (_ BitVec 8))\n(declare-const d (_ BitVec 8))\n\
             (assert (= d #x00))\n(assert (= x #xf9))\n\
             (assert (= (bvsdiv x d) #x01))",
            SolverResult::Sat,
        ),
        // The non-zero divisor path is unaffected: `bvsdiv(-7, 2) = -3`.
        (
            "(declare-const x (_ BitVec 8))\n(assert (= x #xf9))\n\
             (assert (= (bvsdiv x #x02) #xfd))",
            SolverResult::Sat,
        ),
    ]);
}

/// The remaining kinds that lower to a BV-sorted `ite`, `concat` or
/// `extract`: `ite` itself, `bvcomp`, the extensions and the rotations.
#[test]
fn test_bv_ite_comp_extend_rotate_are_constrained() {
    assert_bv_cases(&[
        (
            "(declare-const x (_ BitVec 8))\n\
             (assert (= (ite (bvult x #x08) #x01 #x02) #x03))",
            SolverResult::Unsat,
        ),
        // `bvcomp x x` is `#b1` for every `x`.
        (
            "(declare-const x (_ BitVec 8))\n(assert (= (bvcomp x x) #b0))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const y (_ BitVec 4))\n\
             (assert (= ((_ zero_extend 4) y) #x10))",
            SolverResult::Unsat,
        ),
        // Sign extension of a 4-bit value never yields `#x0f` (that needs a
        // clear sign bit, which forces the high nibble to zero *and* the low
        // nibble to `f`, i.e. a set sign bit).
        (
            "(declare-const y (_ BitVec 4))\n\
             (assert (= ((_ sign_extend 4) y) #x0f))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const x (_ BitVec 8))\n(assert (= x #x01))\n\
             (assert (= ((_ rotate_left 1) x) #x01))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const x (_ BitVec 8))\n(assert (= x #x01))\n\
             (assert (= ((_ rotate_right 1) x) #x01))",
            SolverResult::Unsat,
        ),
    ]);
}

/// Control: the same `ite` / `bvcomp` / extension / rotation shapes stay
/// satisfiable at their true values.
#[test]
fn test_bv_ite_comp_extend_rotate_controls_stay_sat() {
    assert_bv_cases(&[
        (
            "(declare-const x (_ BitVec 8))\n\
             (assert (= (ite (bvult x #x08) #x01 #x02) #x01))",
            SolverResult::Sat,
        ),
        (
            "(declare-const x (_ BitVec 8))\n(assert (= (bvcomp x x) #b1))",
            SolverResult::Sat,
        ),
        (
            "(declare-const y (_ BitVec 4))\n\
             (assert (= ((_ zero_extend 4) y) #x0a))",
            SolverResult::Sat,
        ),
        (
            "(declare-const y (_ BitVec 4))\n\
             (assert (= ((_ sign_extend 4) y) #xff))",
            SolverResult::Sat,
        ),
        (
            "(declare-const x (_ BitVec 8))\n(assert (= x #x01))\n\
             (assert (= ((_ rotate_left 1) x) #x02))",
            SolverResult::Sat,
        ),
        (
            "(declare-const x (_ BitVec 8))\n(assert (= x #x01))\n\
             (assert (= ((_ rotate_right 1) x) #x80))",
            SolverResult::Sat,
        ),
    ]);
}

/// A BV-sorted `ite` whose selector is a bare boolean *variable* has no
/// circuit of its own inside the embedded BV solver — it gets a fresh, free
/// SAT variable.  Unless that variable is tied to the enclosing search's
/// assignment of the same atom, the embedded solver may take the branch the
/// outer solver has ruled out and both halves look consistent, which is a
/// false `sat`.
#[test]
fn test_bv_ite_bool_variable_condition_tracks_outer_assignment() {
    assert_bv_cases(&[
        // `¬c` forces the else-branch `#x02`, so `x = #x01` is impossible.
        (
            "(declare-const c Bool)\n(declare-const x (_ BitVec 8))\n\
             (assert (= (ite c #x01 #x02) x))\n(assert (not c))\n\
             (assert (= x #x01))",
            SolverResult::Unsat,
        ),
        // Dually with a positive selector.
        (
            "(declare-const c Bool)\n(declare-const x (_ BitVec 8))\n\
             (assert (= (ite c #x01 #x02) x))\n(assert c)\n\
             (assert (= x #x02))",
            SolverResult::Unsat,
        ),
        // Boolean structure above the selector must be respected too.
        (
            "(declare-const c Bool)\n(declare-const d Bool)\n\
             (declare-const x (_ BitVec 8))\n\
             (assert (= (ite (and c d) #x01 #x02) x))\n(assert (not d))\n\
             (assert (= x #x01))",
            SolverResult::Unsat,
        ),
        (
            "(declare-const c Bool)\n(declare-const x (_ BitVec 4))\n\
             (assert (= (ite c #x1 #x2) x))\n(assert (not c))\n\
             (assert (= x #x1))",
            SolverResult::Unsat,
        ),
    ]);
}

/// Control: the same shapes stay satisfiable on the branch the selector
/// actually chooses, and an `ite` under a disjunction must not be forced.
#[test]
fn test_bv_ite_bool_variable_controls_stay_sat() {
    assert_bv_cases(&[
        (
            "(declare-const c Bool)\n(declare-const x (_ BitVec 8))\n\
             (assert (= (ite c #x01 #x02) x))\n(assert (not c))\n\
             (assert (= x #x02))",
            SolverResult::Sat,
        ),
        (
            "(declare-const c Bool)\n(declare-const x (_ BitVec 8))\n\
             (assert (= (ite c #x01 #x02) x))\n(assert c)\n\
             (assert (= x #x01))",
            SolverResult::Sat,
        ),
        // The selector is free here, so both branch values remain reachable.
        (
            "(declare-const c Bool)\n(declare-const x (_ BitVec 8))\n\
             (assert (= (ite c #x01 #x02) x))",
            SolverResult::Sat,
        ),
        (
            "(declare-const c Bool)\n(declare-const x (_ BitVec 8))\n\
             (assert (or (= (ite c #x01 #x02) x) (= x #x09)))",
            SolverResult::Sat,
        ),
    ]);
}
