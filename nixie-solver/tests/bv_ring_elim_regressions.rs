//! Ring solve-eqs (`solve_ring_equations`) regressions.
//!
//! The pass eliminates one variable per round; the historical implementation
//! rebuilt, on **every** round, the polynomial of every asserted equality and
//! the variable-occurrence table of every assertion (a full DAG walk each).
//! Definition-dense industrial inputs — the Sydr/Triton `predicate_*` files
//! assert thousands of near-linear equations — offer one eliminable variable
//! per round, so thousands of rounds × thousands of rescans made the pass the
//! entire solve: `20210219-Sydr/master/cjpeg/predicate_2636` spent >390 s
//! inside it and never reached bit-blast.  The incremental rewrite keeps the
//! elimination sequence bit-identical while walking only the substituted
//! assertions per round.
//!
//! These tests pin the invariants that rewrite must preserve:
//!
//! 1. **Verdicts through long elimination chains** — a cyclic chain with an
//!    inconsistent offset is unsat *through* the eliminated links
//!    (`ring_chain_unsat_through_eliminable_links`); the pass may not drop
//!    the cycle constraint when the last link closes over already-eliminated
//!    variables.
//! 2. **Model reconstruction across replayed eliminations** — an open chain
//!    forces `x_1 − x_N ≡ N−1 (mod 2^w)`; the replayed definitions must
//!    produce a model satisfying the *original* equations
//!    (`ring_chain_model_reconstructs_telescope`).
//! 3. **The invertibility gate** — odd coefficients are solved and
//!    substituted; even coefficients are *not* invertible mod 2^w and must
//!    stay constraints (`even_coefficient_is_not_eliminable`: `2x = 1` is
//!    unsat because no solution exists, which requires the equation to have
//!    survived, not been rewritten to `true`).
//! 4. **Preprocess-outcome memoization** — the dispatch/stage-4 cache is
//!    invalidated on new assertions and on `push`/`pop`
//!    (`preprocess_cache_invalidates_on_assert_and_pop`); a stale cache would
//!    answer a *different* assertion set.

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script executes");
    out.iter()
        .filter(|t| !t.trim().is_empty())
        .cloned()
        .collect()
}

/// Build a chain system `x_i + c_i = x_{i+1} + d_i` over width-32 variables.
/// Offsets sum to `N + extra` around the cycle when `close == true`.
fn chain_script(n: u32, close: bool, width: u32) -> String {
    let mut s = format!("(set-logic QF_BV)\n(declare-const x_1 (_ BitVec {width}))\n");
    for i in 2..=n {
        s.push_str(&format!("(declare-const x_{i} (_ BitVec {width}))\n"));
    }
    // One eliminable equation per link: both sides are sums (the plain
    // `= x t` pass cannot take them), each variable occurs in exactly two
    // equations (Z3's `solve_eqs_max_occs`).
    for i in 1..n {
        s.push_str(&format!(
            "(assert (= (bvadd x_{i} (_ bv1 {width})) (bvadd x_{} (_ bv2 {width}))))\n",
            i + 1
        ));
    }
    if close {
        // x_n + 1 = x_1 + 2: telescoping gives x_1 = x_1 + n·(−1) … in
        // total x_1 ≡ x_1 − n (mod 2^w), unsat for 0 < n < 2^w.
        s.push_str(&format!(
            "(assert (= (bvadd x_{n} (_ bv1 {width})) (bvadd x_1 (_ bv2 {width}))))\n"
        ));
    }
    s.push_str("(check-sat)\n");
    s
}

/// Cyclic chain, inconsistent offset: unsat through the eliminated links.
/// The scale (1500 equations) is the shape that made the historical
/// per-round rescan the entire solve; the chain must decide quickly.
#[test]
fn ring_chain_unsat_through_eliminable_links() {
    let out = run(&chain_script(1500, true, 32));
    assert_eq!(out.last().map(String::as_str), Some("unsat"));
}

/// Open chain: sat, and the replayed ring definitions must satisfy the
/// original equations — telescoping forces `x_1 − x_N ≡ N−1 (mod 2^32)`.
#[test]
fn ring_chain_model_reconstructs_telescope() {
    const N: u32 = 600;
    let mut script = chain_script(N, false, 32);
    script.push_str("(get-value (x_1 x_N))\n");
    // `x_N` does not exist (the generator names x_1..x_n); rename tail.
    let script = script.replace("x_N", &format!("x_{N}"));
    let out = run(&script);
    assert_eq!(out[0], "sat", "open chain must be sat: {out:?}");
    // Output shape: `((x_1 #x........)\n (x_n #x........))` — collect the
    // `#x…` value tokens in declaration order.
    let vals: Vec<&str> = out[1]
        .split_whitespace()
        .filter(|t| t.starts_with("#x"))
        .collect();
    assert!(vals.len() == 2, "get-value output: {out:?}");
    let parse = |tok: &str| -> u32 {
        let hex = tok.trim_matches(|c: char| c == ')' || c == ',');
        let hex = hex.trim_start_matches("#x");
        u32::from_str_radix(hex, 16).unwrap_or_else(|_| panic!("hex value {tok:?}"))
    };
    let (v1, vn) = (parse(vals[0]), parse(vals[1]));
    // (x_1 - x_n) mod 2^32 == N-1: each equation i reads
    // x_i = x_{i+1} + 1, so x_1 = x_n + (N-1).
    let diff = v1.wrapping_sub(vn);
    assert_eq!(diff, N - 1, "telescope broken: x_1={v1:#x} x_n={vn:#x}");
}

/// Odd coefficient: `3x = 9 ∧ x = 4` is unsat *through* the solved
/// definition `x = 3⁻¹·9 = 3`; a pass that dropped the equation or solved
/// over an even inverse answers sat.
#[test]
fn odd_coefficient_solves_to_contradiction() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (assert (= (bvmul (_ bv3 32) x) (_ bv9 32)))
        (assert (= x (_ bv4 32)))
        (check-sat)
    "#);
    assert_eq!(out.last().map(String::as_str), Some("unsat"));
}

/// Even coefficient: `2x = 1` has no solution mod 2^32, and 2 is not a
/// unit — the equation must stay a constraint (an elimination that divides
/// by the non-unit 2 would call it sat).
#[test]
fn even_coefficient_is_not_eliminable() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (assert (= (bvmul (_ bv2 32) x) (_ bv1 32)))
        (check-sat)
    "#);
    assert_eq!(out.last().map(String::as_str), Some("unsat"));
}

/// The preprocess outcome is memoized across the dispatch/stage-4 boundary;
/// new assertions and `pop` must invalidate it.  A stale cache answers the
/// *previous* assertion set (wrong verdict at step 3/5).
#[test]
fn preprocess_cache_invalidates_on_assert_and_pop() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (declare-const y (_ BitVec 32))
        (assert (= (bvadd x (_ bv1 32)) (bvadd y (_ bv2 32))))
        (check-sat)
        (assert (= x (bvadd y (_ bv3 32))))
        (check-sat)
        (push 1)
        (assert (= x (bvadd y (_ bv9 32))))
        (check-sat)
        (pop 1)
        (check-sat)
    "#);
    let verdicts: Vec<&str> = out.iter().map(String::as_str).collect();
    // Step 1: one equation, two unknowns — sat.
    // Step 2: x = y+1 ∧ x = y+3 — unsat.
    // Step 3: the pushed equation is implied by neither; still unsat
    //         (the step-2 assertions are still live under the push).
    // Step 4: back to the step-2 set — unsat, *not* the stale sat of step 1.
    assert_eq!(
        verdicts,
        vec!["sat", "unsat", "unsat", "unsat"],
        "verdict sequence: {out:?}"
    );
}

/// Same invalidation across the *double-run* boundary the cache exists for:
/// a definition-dense goal routes through the dispatch's preprocessing
/// trial and then the stage-4 parity pass — both must see the same
/// assertion set, and a second `check-sat` with more assertions must
/// recompute (not replay) the memoized outcome.
#[test]
fn preprocess_cache_double_run_stays_correct() {
    let mut script = String::from("(set-logic QF_BV)\n");
    for i in 1..=40 {
        script.push_str(&format!("(declare-const x_{i} (_ BitVec 32))\n"));
    }
    for i in 1..40 {
        script.push_str(&format!(
            "(assert (= (bvadd x_{i} (_ bv7 32)) (bvadd x_{} (_ bv9 32))))\n",
            i + 1
        ));
    }
    script.push_str("(check-sat)\n"); // open chain: sat
    // Close it inconsistently: x_40 + 7 = x_1 + 8 telescopes to
    // x_1 = x_1 − 39 ≢ x_1 (mod 2^32).
    script.push_str("(assert (= (bvadd x_40 (_ bv7 32)) (bvadd x_1 (_ bv8 32))))\n");
    script.push_str("(check-sat)\n"); // unsat
    let out = run(&script);
    let verdicts: Vec<&str> = out.iter().map(String::as_str).collect();
    assert_eq!(verdicts, vec!["sat", "unsat"], "sequence: {out:?}");
}
