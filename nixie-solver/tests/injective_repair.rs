//! Regression tests for the distinct-semantics guard clauses (the
//! census-driven fix; see
//! docs/studies/2026-09-07-memory-alias-arrangement-gap.md).
//!
//! The conflict census measured that CDCL learns the falsity of read-over-
//! write guard atoms `(= t_i t_j)` between a live distinct's arguments one
//! conflict at a time (23k of 58k theory lemmas on memory-alias-s0-large).
//! The guard clauses `¬distinct ∨ ¬(t_i = t_j)` are theorems; with the
//! distinct a level-0 unit they falsify every existing guard atom by unit
//! propagation at descent start.

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}


// ---------------------------------------------------------------------------
// Distinct-semantics guard clauses (the census-driven fix; see the
// arrangement-gap study's conflict census).
// ---------------------------------------------------------------------------

/// The guard clause `¬distinct ∨ ¬(t_i = t_j)` is a theorem for every pair
/// of a live spec's arguments.  With the distinct asserted at the top
/// level, the guard atoms are falsified by unit propagation at descent
/// start — the census found CDCL learning exactly that falsity one conflict
/// at a time (23k of 58k theory lemmas on memory-alias-s0-large).
#[test]
fn distinct_guard_clause_decides_eq_atom() {
    // `distinct x y` and `(= x y)` both asserted: unsat outright (z3 agrees),
    // and the guard clause makes it a unit-propagation refutation.
    let script = concat!(
        "(set-logic QF_UFLIA)\n",
        "(declare-fun x () Int)\n(declare-fun y () Int)\n",
        "(declare-fun z () Int)\n",
        "(assert (distinct x y))\n",
        "(assert (= x y))\n",
        "(assert (> z 0))\n",
        "(check-sat)\n",
    );
    assert_eq!(run(script), vec!["unsat"]);
}

/// A CONDITIONAL distinct (under ite): the guard clause is valid
/// regardless of the distinct's polarity — when the distinct is false, the
/// clause is satisfied through its first literal; when true, the eq atom
/// must be false.  Both polarities must decide correctly.
#[test]
fn conditional_distinct_with_guard_clause_is_sound() {
    // c chooses: (distinct x y) and (x = y) cannot both hold on the c branch.
    let unsat_shape = concat!(
        "(set-logic QF_UFLIA)\n",
        "(declare-fun x () Int)\n(declare-fun y () Int)\n",
        "(declare-fun c () Bool)\n",
        "(assert c)\n",
        "(assert (ite c (distinct x y) (> x y)))\n",
        "(assert (= x y))\n",
        "(check-sat)\n",
    );
    assert_eq!(run(unsat_shape), vec!["unsat"]);
    // Without c: the ite can take the (> x y) branch and x = y fails there,
    // so the formula is satisfiable via ¬c.
    let sat_shape = concat!(
        "(set-logic QF_UFLIA)\n",
        "(declare-fun x () Int)\n(declare-fun y () Int)\n",
        "(declare-fun c () Bool)\n",
        "(assert (ite c (distinct x y) (> x y)))\n",
        "(assert (ite c (= x y) (= x y)))\n",
        "(check-sat)\n",
    );
    // ¬c: (> x y) branch with x = y forced elsewhere — contradiction there
    // too; the c branch: distinct + x=y — contradiction.  Both branches
    // refute: unsat (z3 agrees).
    assert_eq!(run(sat_shape), vec!["unsat"]);
}

/// The storecomm shape the census measured: the guard clauses must not
/// change the verdict, only the cost.
#[test]
fn memory_alias_shape_with_guard_clauses_both_polarities() {
    let n = 10u32;
    let mut script = String::from("(set-logic QF_AUFLIA)\n");
    for i in 0..n {
        script.push_str(&format!("(declare-fun idx{i} () Int)\n"));
    }
    script.push_str("(declare-fun v9 () Int)\n(declare-fun v4 () Int)\n");
    script.push_str("(assert (distinct");
    for i in 0..n {
        if i != 4 {
            script.push_str(&format!(" idx{i}"));
        }
    }
    script.push_str("))\n");
    script.push_str("(assert (= idx9 idx4))\n");
    script.push_str("(assert (= v9 7))\n(assert (= v4 9))\n");
    script.push_str("(declare-fun b () (Array Int Int))\n");
    let mut a1 = "b".to_string();
    let mut a2 = "b".to_string();
    for i in 0..n {
        let w1 = if i == 9 { "v9" } else if i == 4 { "v4" } else { "100" };
        let w2 = if i == 9 { "v4" } else if i == 4 { "v9" } else { "100" };
        a1 = format!("(store {a1} idx{i} {w1})");
        a2 = format!("(store {a2} idx{i} {w2})");
    }
    script.push_str(&format!(
        "(declare-fun a1 () (Array Int Int))\n(assert (= a1 {a1}))\n"
    ));
    script.push_str(&format!(
        "(declare-fun a2 () (Array Int Int))\n(assert (= a2 {a2}))\n"
    ));
    script.push_str("(assert (distinct (select a1 idx9) (select a2 idx9)))\n(check-sat)\n");
    assert_eq!(run(&script), vec!["sat"], "different anchors differ at the aliased cell");
    let unsat = script
        .replace("(assert (= v9 7))", "(assert (= v9 5))")
        .replace("(assert (= v4 9))", "(assert (= v4 5))");
    assert_eq!(run(&unsat), vec!["unsat"], "equal anchors agree everywhere");
}
