//! LIA (Linear Integer Arithmetic) Integration Tests
//!
//! These tests verify that the solver correctly handles integer arithmetic constraints,
//! including GCD-based infeasibility detection and cutting planes.

use nixie_solver::{Context, SolverResult};

/// Test GCD-based infeasibility detection for equality constraints
///
/// For the constraint 2x + 2y = 7:
/// - All coefficients have GCD = 2
/// - The constant 7 is not divisible by 2
/// - Therefore, no integer solution exists
///
/// This test ensures the solver detects this infeasibility immediately
/// during assertion, before even invoking the simplex solver.
///
/// Reference: Schrijver, "Theory of Linear and Integer Programming" (1986)
#[test]
fn test_lia_gcd_infeasibility_basic() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_LIA");

    // Create integer variables
    let x = ctx.declare_const("x", ctx.terms.sorts.int_sort);
    let y = ctx.declare_const("y", ctx.terms.sorts.int_sort);

    // Build the constraint: 2x + 2y = 7
    let two = ctx.terms.mk_int(2);
    let seven = ctx.terms.mk_int(7);
    let two_x = ctx.terms.mk_mul(vec![two, x]);
    let two_y = ctx.terms.mk_mul(vec![two, y]);
    let sum = ctx.terms.mk_add(vec![two_x, two_y]);
    let constraint = ctx.terms.mk_eq(sum, seven);

    ctx.assert(constraint);

    // Also add non-negativity constraints (shouldn't matter for GCD check)
    let zero = ctx.terms.mk_int(0);
    let x_nonneg = ctx.terms.mk_ge(x, zero);
    let y_nonneg = ctx.terms.mk_ge(y, zero);
    ctx.assert(x_nonneg);
    ctx.assert(y_nonneg);

    // The result must be UNSAT due to GCD infeasibility
    let result = ctx.check_sat();
    assert!(
        matches!(result, nixie_solver::SolverResult::Unsat),
        "Expected UNSAT for 2x + 2y = 7 (GCD infeasibility), got {:?}",
        result
    );
}

/// Test GCD-based infeasibility with larger GCD
///
/// For 6x + 9y + 12z = 5:
/// - GCD(6, 9, 12) = 3
/// - 5 is not divisible by 3
/// - Therefore UNSAT
#[test]
fn test_lia_gcd_infeasibility_larger_gcd() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_LIA");

    let x = ctx.declare_const("x", ctx.terms.sorts.int_sort);
    let y = ctx.declare_const("y", ctx.terms.sorts.int_sort);
    let z = ctx.declare_const("z", ctx.terms.sorts.int_sort);

    // 6x + 9y + 12z = 5
    let six = ctx.terms.mk_int(6);
    let nine = ctx.terms.mk_int(9);
    let twelve = ctx.terms.mk_int(12);
    let five = ctx.terms.mk_int(5);

    let six_x = ctx.terms.mk_mul(vec![six, x]);
    let nine_y = ctx.terms.mk_mul(vec![nine, y]);
    let twelve_z = ctx.terms.mk_mul(vec![twelve, z]);

    let sum = ctx.terms.mk_add(vec![six_x, nine_y, twelve_z]);
    let constraint = ctx.terms.mk_eq(sum, five);

    ctx.assert(constraint);

    let result = ctx.check_sat();
    assert!(
        matches!(result, nixie_solver::SolverResult::Unsat),
        "Expected UNSAT for 6x + 9y + 12z = 5 (GCD = 3 doesn't divide 5), got {:?}",
        result
    );
}

/// Test that GCD-satisfiable constraints are SAT
///
/// For 2x + 2y = 6:
/// - GCD(2, 2) = 2
/// - 6 is divisible by 2
/// - Therefore SAT (e.g., x=1, y=2 is a solution)
#[test]
fn test_lia_gcd_satisfiable() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_LIA");

    let x = ctx.declare_const("x", ctx.terms.sorts.int_sort);
    let y = ctx.declare_const("y", ctx.terms.sorts.int_sort);

    // 2x + 2y = 6 (SAT: x=1, y=2 works)
    let two = ctx.terms.mk_int(2);
    let six = ctx.terms.mk_int(6);
    let two_x = ctx.terms.mk_mul(vec![two, x]);
    let two_y = ctx.terms.mk_mul(vec![two, y]);
    let sum = ctx.terms.mk_add(vec![two_x, two_y]);
    let constraint = ctx.terms.mk_eq(sum, six);

    ctx.assert(constraint);

    let result = ctx.check_sat();
    assert!(
        matches!(result, nixie_solver::SolverResult::Sat),
        "Expected SAT for 2x + 2y = 6 (GCD-satisfiable), got {:?}",
        result
    );
}

/// Test mixed equality and inequality constraints
///
/// This is a more complex test that combines GCD reasoning with
/// inequality constraints.
#[test]
fn test_lia_mixed_constraints_with_gcd() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_LIA");

    let x = ctx.declare_const("x", ctx.terms.sorts.int_sort);
    let y = ctx.declare_const("y", ctx.terms.sorts.int_sort);

    // Constraint 1: 2x + 2y = 7 (GCD-infeasible)
    let two = ctx.terms.mk_int(2);
    let seven = ctx.terms.mk_int(7);
    let two_x = ctx.terms.mk_mul(vec![two, x]);
    let two_y = ctx.terms.mk_mul(vec![two, y]);
    let sum = ctx.terms.mk_add(vec![two_x, two_y]);
    let eq_constraint = ctx.terms.mk_eq(sum, seven);

    // Constraint 2: x >= 0
    let zero = ctx.terms.mk_int(0);
    let x_nonneg = ctx.terms.mk_ge(x, zero);

    // Constraint 3: y >= 0
    let y_nonneg = ctx.terms.mk_ge(y, zero);

    ctx.assert(eq_constraint);
    ctx.assert(x_nonneg);
    ctx.assert(y_nonneg);

    let result = ctx.check_sat();
    assert!(
        matches!(result, nixie_solver::SolverResult::Unsat),
        "Expected UNSAT (GCD infeasibility should dominate), got {:?}",
        result
    );
}

/// Test that fractional constants in equality are detected as infeasible for LIA
#[test]
fn test_lia_fractional_constant_in_equality() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_LIA");

    let x = ctx.declare_const("x", ctx.terms.sorts.int_sort);

    // x = 3.5 should be UNSAT for integer x
    use num_rational::Rational64;
    let three_point_five = ctx.terms.mk_real(Rational64::new(7, 2));
    let constraint = ctx.terms.mk_eq(x, three_point_five);

    ctx.assert(constraint);

    let result = ctx.check_sat();
    // This should be UNSAT because we can't have an integer equal to 3.5
    assert!(
        matches!(result, nixie_solver::SolverResult::Unsat),
        "Expected UNSAT for x = 3.5 with integer x, got {:?}",
        result
    );
}

// ========  ========
// Integer `div` / `mod` / `abs` defining axioms
//
// The linear solver sees `(div m n)`, `(mod m n)` and the `(ite ...)` that
// `abs` desugars to as opaque atoms.  `Solver::instantiate_arith_axioms`
// supplies their meaning as ground lemmas; without it `(mod i0 7)` was an
// unconstrained variable and `(= (abs (- 9)) (abs (mod i0 7)))` was reported
// `sat` even though `(mod i0 7)` can never leave `[0, 7)`.
//
// The `unsat` cases pin the axioms; the `sat` controls prove they do not
// over-constrain; the zero-divisor cases pin the SMT-LIB rule that `div`/`mod`
// by zero are *uninterpreted* and must therefore stay satisfiable.
// ========  ========

/// Run an SMT-LIB script and return the verdict of its final `check-sat`.
fn run_script(script: &str) -> SolverResult {
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(script).unwrap_or_default();
    for token in outputs.iter().rev() {
        match token.trim() {
            "sat" => return SolverResult::Sat,
            "unsat" => return SolverResult::Unsat,
            "unknown" => return SolverResult::Unknown,
            _ => {}
        }
    }
    SolverResult::Unknown
}

/// Run a script and return *every* `check-sat` verdict, in order.
fn run_script_all(script: &str) -> Vec<SolverResult> {
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(script).unwrap_or_default();
    outputs
        .iter()
        .filter_map(|token| match token.trim() {
            "sat" => Some(SolverResult::Sat),
            "unsat" => Some(SolverResult::Unsat),
            "unknown" => Some(SolverResult::Unknown),
            _ => None,
        })
        .collect()
}

/// The originally reported differential-fuzz defect: `(abs (mod i0 7))` lies in
/// `[0, 7)` and can never equal `(abs (- 9)) = 9`.
#[test]
fn test_abs_of_mod_cannot_reach_nine() {
    let script = r#"
(set-logic QF_AUFLIA)
(declare-const i0 Int)
(assert (= (abs (- 9)) (abs (mod i0 7))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// `0 <= (mod m n) < abs(n)` for a positive constant divisor: both ends.
#[test]
fn test_mod_range_bounds_unsat() {
    let above = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (>= (mod i0 7) 7))
(check-sat)
"#;
    let below = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (< (mod i0 7) 0))
(check-sat)
"#;
    assert_eq!(run_script(above), SolverResult::Unsat);
    assert_eq!(run_script(below), SolverResult::Unsat);
}

/// The remainder range is governed by `abs(n)`, so it holds unchanged for a
/// negative divisor: `(mod i0 (- 7))` still lies in `[0, 7)`.  This is the
/// Euclidean convention – a truncating `%` would allow `-1` here.
#[test]
fn test_mod_negative_divisor_range() {
    let above = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (>= (mod i0 (- 7)) 7))
(check-sat)
"#;
    let negative_value = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (= (mod i0 (- 7)) (- 1)))
(check-sat)
"#;
    assert_eq!(run_script(above), SolverResult::Unsat);
    assert_eq!(run_script(negative_value), SolverResult::Unsat);
}

/// Controls: every value the remainder *can* take must stay reachable, for a
/// positive and a negative divisor alike.
#[test]
fn test_mod_reachable_values_stay_sat() {
    for script in [
        r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (= (mod i0 7) 3))
(check-sat)
"#,
        r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (= (mod i0 7) 0))
(check-sat)
"#,
        r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (= (mod i0 (- 7)) 6))
(check-sat)
"#,
        // A negative dividend still yields a non-negative remainder.
        r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (< i0 0))
(assert (= (mod i0 5) 2))
(check-sat)
"#,
    ] {
        assert_eq!(run_script(script), SolverResult::Sat, "script: {script}");
    }
}

/// `m = n * (div m n) + (mod m n)` for a non-zero constant `n`, both signs.
/// This is what lets the solver relate a `div` term to its `mod` partner
/// instead of treating each as an independent opaque variable.
#[test]
fn test_div_mod_identity() {
    let positive = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (not (= i0 (+ (* 7 (div i0 7)) (mod i0 7)))))
(check-sat)
"#;
    let negative = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (not (= i0 (+ (* (- 7) (div i0 (- 7))) (mod i0 (- 7))))))
(check-sat)
"#;
    assert_eq!(run_script(positive), SolverResult::Unsat);
    assert_eq!(run_script(negative), SolverResult::Unsat);
}

/// Bounds on the dividend propagate to the quotient: `0 <= i0 <= 10` forces
/// `(div i0 3) <= 3`, so demanding `>= 4` is unsatisfiable.
#[test]
fn test_div_bounds_follow_dividend() {
    let script = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (and (>= i0 0) (<= i0 10)))
(assert (>= (div i0 3) 4))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Two independent remainders each live in `[0, 3)`, so their sum is at most 4.
/// The `= 4` control shows the bound is tight rather than over-tightened.
#[test]
fn test_mod_bounds_compose_across_terms() {
    let too_large = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(declare-const i1 Int)
(assert (> (+ (mod i0 3) (mod i1 3)) 4))
(check-sat)
"#;
    let attainable = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(declare-const i1 Int)
(assert (= (+ (mod i0 3) (mod i1 3)) 4))
(check-sat)
"#;
    assert_eq!(run_script(too_large), SolverResult::Unsat);
    assert_eq!(run_script(attainable), SolverResult::Sat);
}

/// SMT-LIB leaves `div`/`mod` by zero *uninterpreted*: any value is allowed, so
/// pinning one to an arbitrary constant must stay satisfiable.  This is the
/// single easiest way to turn the range axiom into an unsoundness, so it is
/// pinned explicitly for both operators and for an open constraint.
#[test]
fn test_mod_zero_divisor_stays_uninterpreted() {
    for script in [
        r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (= (mod i0 0) 5))
(check-sat)
"#,
        r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (= (div i0 0) 5))
(check-sat)
"#,
        // Explicitly *outside* the range the non-zero axiom would impose.
        r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (< (mod i0 0) 0))
(check-sat)
"#,
    ] {
        assert_eq!(run_script(script), SolverResult::Sat, "script: {script}");
    }
}

/// Even uninterpreted, `mod` by zero is a *function* of its dividend: equal
/// dividends force equal results.
#[test]
fn test_mod_zero_divisor_is_congruent() {
    let script = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(declare-const i1 Int)
(assert (= i0 i1))
(assert (not (= (mod i0 0) (mod i1 0))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// A symbolic divisor has no linear defining identity (`m = n*q + r` is a
/// product of two unknowns), so the atom keeps no theory meaning and the
/// solver must stay honest with `Unknown` rather than guess.
#[test]
fn test_mod_symbolic_divisor_is_not_guessed() {
    let script = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(declare-const i1 Int)
(assert (= (mod i0 i1) 100))
(check-sat)
"#;
    assert_ne!(run_script(script), SolverResult::Unsat);
}

/// `(abs t) >= 0` always, and `abs` agrees with the sign of its argument.
#[test]
fn test_abs_is_non_negative() {
    let never_negative = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (< (abs i0) 0))
(check-sat)
"#;
    let matches_sign = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (< i0 0))
(assert (= (abs i0) i0))
(check-sat)
"#;
    let identity_when_non_negative = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(assert (>= i0 0))
(assert (= (abs i0) i0))
(check-sat)
"#;
    assert_eq!(run_script(never_negative), SolverResult::Unsat);
    assert_eq!(run_script(matches_sign), SolverResult::Unsat);
    assert_eq!(run_script(identity_when_non_negative), SolverResult::Sat);
}

/// The defining axioms are asserted at the scope that internalised the term, so
/// a `pop` must retract them together with the assertion that needed them – and
/// a later scope must re-derive them.  Both orders are checked: axioms first
/// then a model, and a model first then the axioms.
#[test]
fn test_mod_axioms_are_scoped_to_their_push() {
    let axiom_then_model = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(push 1)
(assert (>= (mod i0 7) 7))
(check-sat)
(pop 1)
(assert (= (mod i0 7) 3))
(check-sat)
"#;
    let model_then_axiom = r#"
(set-logic QF_LIA)
(declare-const i0 Int)
(push 1)
(assert (= (mod i0 7) 3))
(check-sat)
(pop 1)
(assert (>= (mod i0 7) 7))
(check-sat)
"#;
    assert_eq!(
        run_script_all(axiom_then_model),
        vec![SolverResult::Unsat, SolverResult::Sat]
    );
    assert_eq!(
        run_script_all(model_then_axiom),
        vec![SolverResult::Sat, SolverResult::Unsat]
    );
}

// ========  ========
// Differential test: random small Int formulas containing `div`/`mod`/`abs`,
// checked against a brute-force oracle over a bounded domain.
//
// The formulas bound every variable to `DOMAIN`, so the oracle's exhaustive
// enumeration decides exactly the same problem the solver is given.  The check
// is one-sided in the honest direction: `Unknown` is always acceptable, but a
// `Sat`/`Unsat` that contradicts the oracle is a hard failure.  Guarding
// against *over*-correction is the point – an axiom that is too strong shows up
// as `Unsat` where the oracle found a witness.
//
// Fully deterministic: fixed seed, fixed schedule, no wall-clock dependence.
// ========  ========

/// Inclusive variable domain used by both the generated formula and the oracle.
const DOMAIN: (i64, i64) = (-8, 8);
/// Number of random formulas exercised.
const DIFFERENTIAL_CASES: usize = 400;

/// Expression over the two integer variables `x` and `y`.
#[derive(Clone)]
enum Expr {
    X,
    Y,
    Const(i64),
    Neg(Box<Expr>),
    Abs(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    /// `(mod e d)` – `d` is a non-zero constant or the variable `y`.
    Mod(Box<Expr>, Box<Divisor>),
    /// `(div e d)` – same divisor discipline.
    Div(Box<Expr>, Box<Divisor>),
}

/// A divisor is deliberately never the literal `0`: division by zero is
/// uninterpreted in SMT-LIB and has no oracle value.  A symbolic divisor is
/// accompanied by a `y != 0` guard in the emitted formula, which keeps the
/// oracle exact there too.
#[derive(Clone, Copy)]
enum Divisor {
    Const(i64),
    SymbolicY,
}

/// xorshift64* – a tiny deterministic PRNG so the suite needs no dependency and
/// no entropy source.
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, bound: u64) -> u64 {
        self.next_u64() % bound
    }
}

fn gen_divisor(rng: &mut Rng, allow_symbolic: bool) -> Divisor {
    if allow_symbolic && rng.below(4) == 0 {
        Divisor::SymbolicY
    } else {
        const CHOICES: [i64; 8] = [-5, -4, -3, -2, 2, 3, 4, 5];
        Divisor::Const(CHOICES[rng.below(CHOICES.len() as u64) as usize])
    }
}

fn gen_expr(rng: &mut Rng, depth: u32, uses_symbolic_divisor: &mut bool) -> Expr {
    if depth == 0 {
        return match rng.below(3) {
            0 => Expr::X,
            1 => Expr::Y,
            _ => Expr::Const(rng.below(21) as i64 - 10),
        };
    }
    match rng.below(8) {
        0 => Expr::Neg(Box::new(gen_expr(rng, depth - 1, uses_symbolic_divisor))),
        1 => Expr::Abs(Box::new(gen_expr(rng, depth - 1, uses_symbolic_divisor))),
        2 => Expr::Add(
            Box::new(gen_expr(rng, depth - 1, uses_symbolic_divisor)),
            Box::new(gen_expr(rng, depth - 1, uses_symbolic_divisor)),
        ),
        3 => Expr::Sub(
            Box::new(gen_expr(rng, depth - 1, uses_symbolic_divisor)),
            Box::new(gen_expr(rng, depth - 1, uses_symbolic_divisor)),
        ),
        4..=6 => {
            let divisor = gen_divisor(rng, true);
            if matches!(divisor, Divisor::SymbolicY) {
                *uses_symbolic_divisor = true;
            }
            Expr::Mod(
                Box::new(gen_expr(rng, depth - 1, uses_symbolic_divisor)),
                Box::new(divisor),
            )
        }
        _ => {
            let divisor = gen_divisor(rng, true);
            if matches!(divisor, Divisor::SymbolicY) {
                *uses_symbolic_divisor = true;
            }
            Expr::Div(
                Box::new(gen_expr(rng, depth - 1, uses_symbolic_divisor)),
                Box::new(divisor),
            )
        }
    }
}

fn divisor_smt(divisor: Divisor) -> String {
    match divisor {
        Divisor::Const(c) if c < 0 => format!("(- {})", -c),
        Divisor::Const(c) => c.to_string(),
        Divisor::SymbolicY => "y".to_string(),
    }
}

fn expr_smt(expr: &Expr) -> String {
    match expr {
        Expr::X => "x".to_string(),
        Expr::Y => "y".to_string(),
        Expr::Const(c) if *c < 0 => format!("(- {})", -c),
        Expr::Const(c) => c.to_string(),
        Expr::Neg(a) => format!("(- {})", expr_smt(a)),
        Expr::Abs(a) => format!("(abs {})", expr_smt(a)),
        Expr::Add(a, b) => format!("(+ {} {})", expr_smt(a), expr_smt(b)),
        Expr::Sub(a, b) => format!("(- {} {})", expr_smt(a), expr_smt(b)),
        Expr::Mod(a, d) => format!("(mod {} {})", expr_smt(a), divisor_smt(**d)),
        Expr::Div(a, d) => format!("(div {} {})", expr_smt(a), divisor_smt(**d)),
    }
}

/// Evaluate under `(x, y)` with SMT-LIB (Euclidean) `div`/`mod`.  `None` marks
/// an evaluation that left the oracle's exact range (divisor zero, or an
/// overflow), in which case the whole case is skipped.
fn eval_expr(expr: &Expr, x: i64, y: i64) -> Option<i64> {
    match expr {
        Expr::X => Some(x),
        Expr::Y => Some(y),
        Expr::Const(c) => Some(*c),
        Expr::Neg(a) => eval_expr(a, x, y)?.checked_neg(),
        Expr::Abs(a) => eval_expr(a, x, y)?.checked_abs(),
        Expr::Add(a, b) => eval_expr(a, x, y)?.checked_add(eval_expr(b, x, y)?),
        Expr::Sub(a, b) => eval_expr(a, x, y)?.checked_sub(eval_expr(b, x, y)?),
        Expr::Mod(a, d) => {
            let divisor = eval_divisor(**d, y)?;
            eval_expr(a, x, y)?.checked_rem_euclid(divisor)
        }
        Expr::Div(a, d) => {
            let divisor = eval_divisor(**d, y)?;
            eval_expr(a, x, y)?.checked_div_euclid(divisor)
        }
    }
}

fn eval_divisor(divisor: Divisor, y: i64) -> Option<i64> {
    match divisor {
        Divisor::Const(c) => Some(c),
        // Guarded away by the emitted `(not (= y 0))`, so this is unreachable
        // for the assignments the oracle enumerates.
        Divisor::SymbolicY if y == 0 => None,
        Divisor::SymbolicY => Some(y),
    }
}

#[derive(Clone, Copy)]
enum Cmp {
    Eq,
    Le,
    Ge,
    Lt,
    Gt,
}

impl Cmp {
    fn symbol(self) -> &'static str {
        match self {
            Cmp::Eq => "=",
            Cmp::Le => "<=",
            Cmp::Ge => ">=",
            Cmp::Lt => "<",
            Cmp::Gt => ">",
        }
    }

    fn holds(self, lhs: i64, rhs: i64) -> bool {
        match self {
            Cmp::Eq => lhs == rhs,
            Cmp::Le => lhs <= rhs,
            Cmp::Ge => lhs >= rhs,
            Cmp::Lt => lhs < rhs,
            Cmp::Gt => lhs > rhs,
        }
    }
}

/// A generated case: a conjunction of comparisons plus the domain bounds.
struct Case {
    atoms: Vec<(Expr, Cmp, i64)>,
    guard_y_non_zero: bool,
}

impl Case {
    fn to_smt(&self) -> String {
        let (lo, hi) = DOMAIN;
        let mut script =
            String::from("(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const y Int)\n");
        for var in ["x", "y"] {
            script.push_str(&format!(
                "(assert (and (>= {var} (- {})) (<= {var} {})))\n",
                -lo, hi
            ));
        }
        if self.guard_y_non_zero {
            script.push_str("(assert (not (= y 0)))\n");
        }
        for (expr, cmp, rhs) in &self.atoms {
            let rhs = if *rhs < 0 {
                format!("(- {})", -rhs)
            } else {
                rhs.to_string()
            };
            script.push_str(&format!(
                "(assert ({} {} {}))\n",
                cmp.symbol(),
                expr_smt(expr),
                rhs
            ));
        }
        script.push_str("(check-sat)\n");
        script
    }

    /// Exhaustive oracle over `DOMAIN`.  `None` means some assignment could not
    /// be evaluated exactly, so the case is not usable.
    fn oracle(&self) -> Option<bool> {
        let (lo, hi) = DOMAIN;
        let mut satisfiable = false;
        for x in lo..=hi {
            for y in lo..=hi {
                if self.guard_y_non_zero && y == 0 {
                    continue;
                }
                let mut all_hold = true;
                for (expr, cmp, rhs) in &self.atoms {
                    let value = eval_expr(expr, x, y)?;
                    if !cmp.holds(value, *rhs) {
                        all_hold = false;
                        break;
                    }
                }
                satisfiable |= all_hold;
            }
        }
        Some(satisfiable)
    }
}

/// Random `div`/`mod`/`abs` formulas must never contradict a brute-force
/// enumeration of the same bounded problem.
#[test]
fn test_div_mod_abs_differential_against_brute_force() {
    const COMPARISONS: [Cmp; 5] = [Cmp::Eq, Cmp::Le, Cmp::Ge, Cmp::Lt, Cmp::Gt];
    // Fixed seed: the case set is identical on every run and every machine.
    let mut rng = Rng(0x0d1f_f4e6_5eed_0001);
    let mut mismatches: Vec<String> = Vec::new();
    let mut decided = 0usize;

    for _ in 0..DIFFERENTIAL_CASES {
        let mut guard_y_non_zero = false;
        let atom_count = 1 + rng.below(2) as usize;
        let atoms: Vec<(Expr, Cmp, i64)> = (0..atom_count)
            .map(|_| {
                let expr = gen_expr(&mut rng, 2, &mut guard_y_non_zero);
                let cmp = COMPARISONS[rng.below(COMPARISONS.len() as u64) as usize];
                let rhs = rng.below(17) as i64 - 8;
                (expr, cmp, rhs)
            })
            .collect();
        let case = Case {
            atoms,
            guard_y_non_zero,
        };

        let Some(expected_sat) = case.oracle() else {
            continue;
        };
        let script = case.to_smt();
        let actual = run_script(&script);
        let agrees = match actual {
            // Honest abstention is always allowed.
            SolverResult::Unknown => true,
            SolverResult::Sat => expected_sat,
            SolverResult::Unsat => !expected_sat,
        };
        if actual != SolverResult::Unknown {
            decided += 1;
        }
        if !agrees {
            mismatches.push(format!(
                "oracle={} solver={actual:?}\n{script}",
                if expected_sat { "sat" } else { "unsat" }
            ));
        }
    }

    assert!(
        mismatches.is_empty(),
        "{} differential mismatch(es):\n{}",
        mismatches.len(),
        mismatches.join("\n---\n")
    );
    // Guard against the test silently degenerating into "everything Unknown".
    assert!(
        decided * 2 >= DIFFERENTIAL_CASES,
        "only {decided}/{DIFFERENTIAL_CASES} cases were decided; the div/mod \
         axioms are no longer reaching the solver"
    );
}
