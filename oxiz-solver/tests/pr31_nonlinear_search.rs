//! End-to-end regression tests for the independently-reimplemented nonlinear
//! search work (upstream PR #31 against cool-japan/oxiz).
//!
//! The mechanisms these exercise live in `oxiz-theories` (`nl_eval`,
//! `nl_repair_search`, `nl_ground_reduce`) and `oxiz-solver`
//! (`check_nlsat::adopt_nl_witness`), and each of those modules carries its own
//! unit tests. What only shows up here is the property the whole stack is
//! supposed to have: an SMT-LIB2 client asking a nonlinear question gets a
//! correct verdict *and*, on `sat`, a model whose values actually satisfy the
//! script.
//!
//! Every satisfiable case therefore checks `get-value` as well as the verdict.
//! A `sat` with no usable model would pass a verdict-only test while being
//! useless – and, worse, a `sat` with a *wrong* model would too.

use oxiz_core::ast::TermManager;
use oxiz_solver::{Context, Solver, SolverConfig, SolverResult};

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

// ========  ========
// 1. Model-based repair search: satisfiable nonlinear integer problems that
//    the cell-decomposition core alone leaves undecided.
// ========  ========

/// A product constrained to a composite value, with both factors bounded away
/// from the trivial `1 x n` split. The repair search has to actually solve
/// `x*y = 12` rather than stumble onto a factorisation.
#[test]
fn test_pr31_nia_bounded_product_is_sat_with_model() {
    let output = run(r#"
        (set-logic QF_NIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (* x y) 12))
        (assert (>= x 2))
        (assert (>= y 2))
        (check-sat)
        (get-value (x y))
    "#);
    assert_eq!(output.first().map(String::as_str), Some("sat"));
    let values = output.get(1).expect("get-value must answer after sat");
    let (x, y) = parse_two_ints(values);
    assert_eq!(
        x * y,
        12,
        "the reported model must satisfy x*y = 12: {values}"
    );
    assert!(
        x >= 2 && y >= 2,
        "the reported model must respect the bounds: {values}"
    );
}

/// A square pinned to a perfect square, with the sign fixed to the negative
/// root – so a search that only ever tries non-negative values fails.
#[test]
fn test_pr31_nia_negative_square_root_is_sat_with_model() {
    let output = run(r#"
        (set-logic QF_NIA)
        (declare-const x Int)
        (assert (= (* x x) 49))
        (assert (< x 0))
        (check-sat)
        (get-value (x))
    "#);
    assert_eq!(output.first().map(String::as_str), Some("sat"));
    let values = output.get(1).expect("get-value must answer after sat");
    let x = parse_one_int(values);
    assert_eq!(x, -7, "the only negative root of x*x = 49: {values}");
}

/// Three-variable product with a mixed sign requirement. Nothing here is
/// univariate, so the decomposition core's univariate trust condition cannot
/// certify it either way and the repair search is what has to answer.
#[test]
fn test_pr31_nia_three_way_product_is_sat_with_model() {
    let output = run(r#"
        (set-logic QF_NIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= (* a b c) 30))
        (assert (> a 1))
        (assert (> b 1))
        (assert (> c 1))
        (check-sat)
        (get-value (a b c))
    "#);
    assert_eq!(output.first().map(String::as_str), Some("sat"));
    let values = output.get(1).expect("get-value must answer after sat");
    let numbers = parse_ints(values);
    assert_eq!(numbers.len(), 3, "three values expected: {values}");
    let product: i64 = numbers.iter().product();
    assert_eq!(
        product, 30,
        "the reported model must satisfy a*b*c = 30: {values}"
    );
    assert!(
        numbers.iter().all(|&n| n > 1),
        "every factor must exceed 1: {values}"
    );
}

// ========  ========
// 2. Unsatisfiable controls: the search must never turn one of these `sat`.
// ========  ========

/// A square can never be negative. The repair search cannot prove this – that
/// is the decomposition core's job – but it must not report `sat` either.
#[test]
fn test_pr31_nia_negative_square_is_never_sat() {
    let output = run(r#"
        (set-logic QF_NIA)
        (declare-const x Int)
        (assert (= (* x x) (- 1)))
        (check-sat)
    "#);
    assert_ne!(
        output.first().map(String::as_str),
        Some("sat"),
        "x*x = -1 has no integer solution"
    );
}

/// A product of two bounded factors cannot reach a value larger than the
/// product of their bounds.
#[test]
fn test_pr31_nia_bounded_product_out_of_range_is_never_sat() {
    let output = run(r#"
        (set-logic QF_NIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 1))
        (assert (<= x 3))
        (assert (>= y 1))
        (assert (<= y 3))
        (assert (= (* x y) 11))
        (check-sat)
    "#);
    assert_ne!(
        output.first().map(String::as_str),
        Some("sat"),
        "the largest product in the 1..3 box is 9, so 11 is unreachable"
    );
}

/// Two squares that cannot both hold. A witness-verifying search has no way to
/// produce a model here, so `sat` would be a pure fabrication.
#[test]
fn test_pr31_nia_conflicting_squares_are_never_sat() {
    let output = run(r#"
        (set-logic QF_NIA)
        (declare-const x Int)
        (assert (= (* x x) 4))
        (assert (= (* x x x) 27))
        (check-sat)
    "#);
    assert_ne!(
        output.first().map(String::as_str),
        Some("sat"),
        "x*x = 4 forces x = ±2, neither of which cubes to 27"
    );
}

// ========  ========
// 3. Grammar reduction: arrays and uninterpreted functions in arithmetic
//    positions (QF_ANIA).
// ========  ========

/// Two array reads multiplied together. Without the grammar reduction the
/// product has no polynomial translation, so the atom is invisible to the
/// nonlinear engines and the answer degrades to `unknown`.
#[test]
fn test_pr31_ania_product_of_reads_is_sat_with_model() {
    let output = run(r#"
        (set-logic QF_ANIA)
        (declare-const A (Array Int Int))
        (declare-const B (Array Int Int))
        (declare-const i Int)
        (assert (= (* (select A i) (select B i)) 35))
        (assert (>= (select A i) 3))
        (assert (>= (select B i) 3))
        (check-sat)
        (get-value ((select A i) (select B i)))
    "#);
    assert_eq!(output.first().map(String::as_str), Some("sat"));
    let values = output.get(1).expect("get-value must answer after sat");
    let numbers = parse_ints(values);
    // The response echoes the index terms as well, so pick the two values that
    // multiply to 6 rather than assuming a position.
    assert!(
        numbers
            .iter()
            .any(|&a| numbers.iter().any(|&b| a * b == 35 && a >= 3 && b >= 3)),
        "the model must contain two reads at least 3 whose product is 35: {values}"
    );
}

/// A store pins the read, and the assertion contradicts it. The reduction must
/// not treat the read as a free unknown and report `sat`.
#[test]
fn test_pr31_ania_store_pinned_read_conflict_is_never_sat() {
    let output = run(r#"
        (set-logic QF_ANIA)
        (declare-const A (Array Int Int))
        (assert (= (* (select (store A 3 8) 3) (select (store A 3 8) 3)) 65))
        (check-sat)
    "#);
    assert_ne!(
        output.first().map(String::as_str),
        Some("sat"),
        "the store pins the read to 8, and 8*8 is 64, not 65"
    );
}

/// The satisfiable companion: the store pins the read to 5, whose square is 25.
#[test]
fn test_pr31_ania_store_pinned_read_is_sat() {
    let output = run(r#"
        (set-logic QF_ANIA)
        (declare-const A (Array Int Int))
        (declare-const n Int)
        (assert (= (* (select (store A 3 8) 3) n) 72))
        (check-sat)
        (get-value (n))
    "#);
    eprintln!("[ANIA-DBG] store_pinned output={:?}", output);
    assert_eq!(output.first().map(String::as_str), Some("sat"));
    let values = output.get(1).expect("get-value must answer after sat");
    assert_eq!(
        parse_one_int(values),
        9,
        "8 * n = 72 forces n = 9: {values}"
    );
}

/// Two reads of one array symbol at indices the assertions force equal are one
/// cell, so they cannot take different values. Abstraction alone would allow
/// it; the witness check is what refuses.
#[test]
fn test_pr31_ania_same_cell_read_twice_is_never_sat() {
    let output = run(r#"
        (set-logic QF_ANIA)
        (declare-const A (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (assert (= i j))
        (assert (= (* (select A i) (select A i)) 16))
        (assert (= (select A i) 4))
        (assert (= (select A j) 6))
        (check-sat)
    "#);
    assert_ne!(
        output.first().map(String::as_str),
        Some("sat"),
        "i = j makes both reads the same cell, which cannot hold 4 and 6"
    );
}

// ========  ========
// 4. The searches are budget-gated, and the gate works.
// ========  ========

/// `SolverConfig::nonlinear_model_search` turns the search-based procedures
/// off. Because they can only ever produce `sat`, switching them off can only
/// ever cost completeness – the same goal must degrade to `unknown`, never to
/// a different verdict. Pinning both halves here is what makes the flag a
/// budget control rather than a soundness control.
#[test]
fn test_pr31_model_search_flag_trades_sat_for_unknown() {
    fn solve_bounded_product(search_enabled: bool) -> SolverResult {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let product = manager.mk_mul(vec![x, y]);
        let twelve = manager.mk_int(12);
        let two = manager.mk_int(2);
        let equation = manager.mk_eq(product, twelve);
        let x_bound = manager.mk_ge(x, two);
        let y_bound = manager.mk_ge(y, two);

        let config = SolverConfig {
            nonlinear_model_search: search_enabled,
            ..SolverConfig::default()
        };
        let mut solver = Solver::with_config(config);
        solver.set_logic("QF_NIA");
        solver.assert(equation, &mut manager);
        solver.assert(x_bound, &mut manager);
        solver.assert(y_bound, &mut manager);
        solver.check(&mut manager)
    }

    assert_eq!(
        solve_bounded_product(true),
        SolverResult::Sat,
        "with the searches on, x*y = 12 is solved"
    );
    assert_ne!(
        solve_bounded_product(false),
        SolverResult::Unsat,
        "turning the searches off may cost an answer, but never invert one"
    );
}

// ========  ========
// 5. Depth guard: a pathologically deep assertion must be answered, not
//    crash the process.
// ========  ========

/// Builds a hundred-thousand-deep arithmetic term directly through the term
/// API, bypassing the SMT-LIB reader (whose own nesting limit would reject the
/// input long before the solver saw it) so the *solver's* guards are what is
/// under test.
///
/// Every pre-processing pass that walks an assertion – the grammar reduction
/// and concrete evaluator added for this slice included – must either be
/// iterative or sit behind `Solver::assert`'s depth probe. Otherwise this
/// overflows the native stack instead of returning an answer, which is the
/// one outcome an SMT solver may never have.
#[test]
fn test_pr31_deep_arith_term_answers_instead_of_crashing() {
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let x = manager.mk_var("x", int_sort);
    let one = manager.mk_int(1);

    // `x + 1 + 1 + ... + 1`, a hundred thousand levels deep, built with a
    // loop rather than recursion so the *test* cannot be what overflows.
    let mut tower = x;
    for _ in 0..100_000 {
        tower = manager.mk_add(vec![tower, one]);
    }
    let self_equality = manager.mk_eq(x, tower);

    let mut solver = Solver::new();
    solver.set_logic("QF_NIA");
    // A shallow nonlinear assertion alongside it, so the nonlinear dispatch
    // path is engaged rather than skipped for want of a product.
    let square = manager.mk_mul(vec![x, x]);
    let four = manager.mk_int(4);
    let square_equation = manager.mk_eq(square, four);
    solver.assert(square_equation, &mut manager);
    solver.assert(self_equality, &mut manager);

    let verdict = solver.check(&mut manager);
    // `x = x + 100000` is unsatisfiable, but under an encoding the depth guard
    // deliberately truncated the honest answer is `Unknown`. The forbidden
    // outcomes are `Sat` and not returning at all.
    assert_ne!(
        verdict,
        SolverResult::Sat,
        "x = x + 100000 has no solution, so `sat` is always wrong here"
    );
    assert!(
        matches!(verdict, SolverResult::Unsat | SolverResult::Unknown),
        "a deep term must produce a verdict, got {verdict:?}"
    );
}

// ========  ========
// helpers
// ========  ========

/// Pull every integer literal out of a `get-value` response.
fn parse_ints(response: &str) -> Vec<i64> {
    let mut out = Vec::new();
    let cleaned = response.replace(['(', ')'], " ");
    let mut tokens = cleaned.split_whitespace().peekable();
    while let Some(token) = tokens.next() {
        // `(- 7)` arrives as `-` followed by `7` once the parens are stripped.
        if token == "-" {
            if let Some(next) = tokens.peek()
                && let Ok(value) = next.parse::<i64>()
            {
                out.push(-value);
                tokens.next();
            }
            continue;
        }
        if let Ok(value) = token.parse::<i64>() {
            out.push(value);
        }
    }
    out
}

fn parse_one_int(response: &str) -> i64 {
    let values = parse_ints(response);
    assert_eq!(values.len(), 1, "expected one value in {response}");
    values[0]
}

fn parse_two_ints(response: &str) -> (i64, i64) {
    let values = parse_ints(response);
    assert_eq!(values.len(), 2, "expected two values in {response}");
    (values[0], values[1])
}
