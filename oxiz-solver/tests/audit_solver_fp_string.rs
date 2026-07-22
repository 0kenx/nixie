//! Regression tests for the solver-fp-string audit findings.
//!
//! These tests pin the *soundness* guarantees established by the audit:
//!
//! 1. String theory atoms (`str.contains`, `str.in_re`, `str.prefixof`, ...) are
//!    mapped to fresh SAT variables and never theory-checked, so the solver must
//!    never report `Sat` for a formula whose satisfiability hinges on one.
//! 2. Floating-point atoms (`fp.lt`, `fp.isNaN`, `fp.div`, ...) are likewise free
//!    Booleans in the CDCL(T) core, so unsupported FP formulas must not be `Sat`.
//! 3. Negated equalities are DISequalities: the FP pre-check must not collect
//!    `(not (= a b))` as `a = b`, which previously produced spurious `Unsat`.
//!
//! The honest answer for the unsupported fragment is `Unknown`. Where the checks
//! *can* soundly detect a genuine contradiction we still expect `Unsat`.

use oxiz_core::ast::{RoundingMode, TermManager};
use oxiz_solver::{Solver, SolverResult};

// ──────────────────────────────────────────────────────────────────
// Finding 1: string atoms must never yield a spurious Sat
// ──────────────────────────────────────────────────────────────────

/// `(= s "abc") ∧ (str.contains s "xyz")` is UNSAT ("abc" does not contain
/// "xyz"). The solver must not report `Sat`.
#[test]
fn str_contains_is_not_free_sat() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let str_sort = manager.sorts.string_sort();
    let s = manager.mk_var("s", str_sort);
    let abc = manager.mk_string_lit("abc");
    let xyz = manager.mk_string_lit("xyz");

    let eq = manager.mk_eq(s, abc);
    let contains = manager.mk_str_contains(s, xyz);
    solver.assert(eq, &mut manager);
    solver.assert(contains, &mut manager);

    let result = solver.check(&mut manager);
    assert_ne!(
        result,
        SolverResult::Sat,
        "str.contains was treated as a free Boolean, giving a spurious Sat"
    );
}

/// `(str.prefixof "z" s) ∧ (= s "abc")` is UNSAT ("abc" does not start with
/// "z"). Must not be `Sat`.
#[test]
fn str_prefixof_is_not_free_sat() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let str_sort = manager.sorts.string_sort();
    let s = manager.mk_var("s", str_sort);
    let abc = manager.mk_string_lit("abc");
    let z = manager.mk_string_lit("z");

    let prefix = manager.mk_str_prefixof(z, s);
    let eq = manager.mk_eq(s, abc);
    solver.assert(prefix, &mut manager);
    solver.assert(eq, &mut manager);

    assert_ne!(solver.check(&mut manager), SolverResult::Sat);
}

/// A lone `(str.contains s t)` over two free string variables is genuinely
/// SATISFIABLE (e.g. `s = t = ""`, since every string contains the empty
/// string — Z3 returns exactly this model). The ground string solver now
/// constructs and *verifies* such a witness, so the honest answer is `Sat`.
///
/// The soundness guarantee this file pins is "no *spurious* `Sat` for an
/// unsatisfiable formula" — covered by `str_contains_is_not_free_sat` and
/// `str_prefixof_is_not_free_sat`, which remain non-`Sat`. Returning a verified
/// `Sat` for a genuinely satisfiable formula strengthens, not weakens, that
/// guarantee.
#[test]
fn lone_satisfiable_string_atom_is_verified_sat() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let str_sort = manager.sorts.string_sort();
    let s = manager.mk_var("s", str_sort);
    let sub = manager.mk_var("t", str_sort);
    let contains = manager.mk_str_contains(s, sub);
    solver.assert(contains, &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}

// ──────────────────────────────────────────────────────────────────
// Finding 2: FP atoms must never yield a spurious Sat
// ──────────────────────────────────────────────────────────────────

/// `fp.lt x y ∧ fp.lt y x` is UNSAT. The generic conflict check only catches
/// `gt × lt`, so both-`lt` slips through; the honesty gate must turn it into a
/// non-`Sat` answer instead of treating the atoms as free Booleans.
#[test]
fn fp_two_lt_is_not_free_sat() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let f32 = manager.sorts.float32_sort();
    let x = manager.mk_var("x", f32);
    let y = manager.mk_var("y", f32);

    let lt_xy = manager.mk_fp_lt(x, y);
    let lt_yx = manager.mk_fp_lt(y, x);
    solver.assert(lt_xy, &mut manager);
    solver.assert(lt_yx, &mut manager);

    assert_ne!(
        solver.check(&mut manager),
        SolverResult::Sat,
        "fp.lt atoms were treated as free Booleans, giving a spurious Sat"
    );
}

/// The sound direct-contradiction check (`x > y ∧ x < y`) must still be caught
/// as `Unsat` — the honesty gate does not mask genuine conflicts.
#[test]
fn fp_gt_and_lt_same_pair_is_unsat() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let f32 = manager.sorts.float32_sort();
    let x = manager.mk_var("x", f32);
    let y = manager.mk_var("y", f32);

    let gt = manager.mk_fp_gt(x, y);
    let lt = manager.mk_fp_lt(x, y);
    solver.assert(gt, &mut manager);
    solver.assert(lt, &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

// ──────────────────────────────────────────────────────────────────
// Finding 3: negated equalities are disequalities (no spurious Unsat)
// ──────────────────────────────────────────────────────────────────

/// `(fp.isZero z) ∧ (not (= y (fp.div RNE z z))) ∧ (not (fp.isNaN y))` is
/// satisfiable (`y` is simply any non-NaN value distinct from `0/0 = NaN`).
///
/// Before the fix the FP pre-check collected the *negated* equality as
/// `y = 0/0`, and Check 3 (0/0 = NaN vs `not isNaN`) fired to report a bogus
/// `Unsat`. The polarity fix means the disequality is no longer recorded, so the
/// result must not be `Unsat`.
#[test]
fn fp_negated_equality_not_collected_as_equality() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let f32 = manager.sorts.float32_sort();
    let y = manager.mk_var("y", f32);
    let zero = manager.mk_fp_plus_zero(8, 24);
    let div = manager.mk_fp_div(RoundingMode::RNE, zero, zero);

    let is_zero = manager.mk_fp_is_zero(zero);
    let eq = manager.mk_eq(y, div);
    let neg_eq = manager.mk_not(eq);
    let is_nan = manager.mk_fp_is_nan(y);
    let neg_nan = manager.mk_not(is_nan);

    solver.assert(is_zero, &mut manager);
    solver.assert(neg_eq, &mut manager);
    solver.assert(neg_nan, &mut manager);

    assert_ne!(
        solver.check(&mut manager),
        SolverResult::Unsat,
        "negated equality was collected as an equality, giving a spurious Unsat"
    );
}

/// Control: the *positive* form `(fp.isZero z) ∧ (= y (fp.div RNE z z)) ∧
/// (not (fp.isNaN y))` genuinely is UNSAT (`0/0 = NaN`, yet `y` is asserted
/// non-NaN while equal to it). Check 3 must still detect it.
#[test]
fn fp_positive_zero_div_nan_is_unsat() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let f32 = manager.sorts.float32_sort();
    let y = manager.mk_var("y", f32);
    let zero = manager.mk_fp_plus_zero(8, 24);
    let div = manager.mk_fp_div(RoundingMode::RNE, zero, zero);

    let is_zero = manager.mk_fp_is_zero(zero);
    let eq = manager.mk_eq(y, div);
    let is_nan = manager.mk_fp_is_nan(y);
    let neg_nan = manager.mk_not(is_nan);

    solver.assert(is_zero, &mut manager);
    solver.assert(eq, &mut manager);
    solver.assert(neg_nan, &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
}

// ──────────────────────────────────────────────────────────────────
// Gate is targeted: non-FP / non-string formulas are unaffected
// ──────────────────────────────────────────────────────────────────

/// A pure Boolean formula with no FP/string atoms must still be decided (`Sat`)
/// — the honesty gate must not over-fire.
#[test]
fn boolean_formula_still_decided() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let p = manager.mk_var("p", manager.sorts.bool_sort);
    solver.assert(p, &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
}
