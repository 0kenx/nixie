//! A string equality used as an `ite` **condition** is not decided — false `sat`.
//!
//! No TLA+ here: the terms are built straight onto `nixie-core`, so this is a
//! solver-level reproducer. Found by the TLA+ arena encoding, where
//! `Cardinality` is a sum of `ite`s guarded by element equalities.
//!
//! Run: `cargo run -p nixie-tla-check --example strite`
//!
//! Each line asserts a formula that is **unsatisfiable**, so every one should
//! print `Unsat`. The controls are the point: they place the defect precisely
//! by showing what *does* work.

use nixie_core::{SortKind, TermId, TermManager};
use nixie_solver::{Solver, SolverResult};

/// Assert the given formulas and report the verdict against what it must be.
fn probe(label: &str, expect: SolverResult, build: impl FnOnce(&mut TermManager) -> Vec<TermId>) {
    let mut tm = TermManager::new();
    let asserts = build(&mut tm);
    let mut solver = Solver::new();
    for a in asserts {
        solver.assert(a, &mut tm);
    }
    let got = solver.check(&mut tm);
    let mark = if got == expect { "ok" } else { "<-- WRONG" };
    println!("{label:56} {got:?}  {mark}");
}

fn main() {
    // ---- controls: the string theory itself works ----

    probe(
        "x=\"a\" /\\ y=\"b\" /\\ x=y            [asserted atom]",
        SolverResult::Unsat,
        |tm| {
            let ss = tm.sorts.string_sort();
            let x = tm.mk_var("x", ss);
            let y = tm.mk_var("y", ss);
            let a = tm.mk_string_lit("a");
            let b = tm.mk_string_lit("b");
            let (e1, e2) = (tm.mk_eq(x, a), tm.mk_eq(y, b));
            let e3 = tm.mk_eq(x, y);
            vec![e1, e2, e3]
        },
    );

    probe(
        "\"a\"=\"b\" /\\ TRUE                  [boolean connective]",
        SolverResult::Unsat,
        |tm| {
            let a = tm.mk_string_lit("a");
            let b = tm.mk_string_lit("b");
            let eq = tm.mk_eq(a, b);
            let t = tm.mk_bool(true);
            vec![tm.mk_and([eq, t])]
        },
    );

    // ---- control: the same `ite` shape over integers works ----

    probe(
        "i=1 /\\ j=2 /\\ ite(i=j,1,0) # 0     [int condition]",
        SolverResult::Unsat,
        |tm| {
            let is = tm.sorts.int_sort;
            let (i, j) = (tm.mk_var("i", is), tm.mk_var("j", is));
            let (one, two, zero) = (tm.mk_int(1), tm.mk_int(2), tm.mk_int(0));
            let (e1, e2) = (tm.mk_eq(i, one), tm.mk_eq(j, two));
            let eq = tm.mk_eq(i, j);
            let ite = tm.mk_ite(eq, one, zero);
            let e = tm.mk_eq(ite, zero);
            let n = tm.mk_not(e);
            vec![e1, e2, n]
        },
    );

    // ---- the defect: a string equality as an `ite` condition ----
    // Variables pinned to distinct literals, so no constant folding is
    // possible and the equality can only be settled by the theory.

    probe(
        "x=\"a\" /\\ y=\"b\" /\\ ite(x=y,1,0) # 0  [int branches]",
        SolverResult::Unsat,
        |tm| {
            let ss = tm.sorts.string_sort();
            let (x, y) = (tm.mk_var("x", ss), tm.mk_var("y", ss));
            let a = tm.mk_string_lit("a");
            let b = tm.mk_string_lit("b");
            let (e1, e2) = (tm.mk_eq(x, a), tm.mk_eq(y, b));
            let eq = tm.mk_eq(x, y);
            let (one, zero) = (tm.mk_int(1), tm.mk_int(0));
            let ite = tm.mk_ite(eq, one, zero);
            let e = tm.mk_eq(ite, zero);
            let n = tm.mk_not(e);
            vec![e1, e2, n]
        },
    );

    // The same, with BOOLEAN branches: this rules arithmetic out entirely.
    probe(
        "x=\"a\" /\\ y=\"b\" /\\ ~ite(x=y,F,T)     [bool branches]",
        SolverResult::Unsat,
        |tm| {
            let ss = tm.sorts.string_sort();
            let (x, y) = (tm.mk_var("x", ss), tm.mk_var("y", ss));
            let a = tm.mk_string_lit("a");
            let b = tm.mk_string_lit("b");
            let (e1, e2) = (tm.mk_eq(x, a), tm.mk_eq(y, b));
            let eq = tm.mk_eq(x, y);
            let (t, f) = (tm.mk_bool(true), tm.mk_bool(false));
            let ite = tm.mk_ite(eq, f, t);
            let n = tm.mk_not(ite);
            vec![e1, e2, n]
        },
    );

    // The shape the TLA+ arena actually builds, for the record.
    probe(
        "1 + ite(\"b\"=\"a\",0,1) # 2           [cardinality shape]",
        SolverResult::Unsat,
        |tm| {
            let a = tm.mk_string_lit("a");
            let b = tm.mk_string_lit("b");
            let eq = tm.mk_eq(b, a);
            let (one, zero, two) = (tm.mk_int(1), tm.mk_int(0), tm.mk_int(2));
            let ite = tm.mk_ite(eq, zero, one);
            let sum = tm.mk_add([one, ite]);
            let e = tm.mk_eq(sum, two);
            let n = tm.mk_not(e);
            vec![n]
        },
    );

    // A sanity case that is genuinely satisfiable, so a fix cannot be a
    // blanket "assume the condition is false".
    probe(
        "ite(p=q,1,0) # 0, p q uninterpreted   [really Sat]",
        SolverResult::Sat,
        |tm| {
            let nm = tm.intern_str("U");
            let us = tm.sorts.intern(SortKind::Uninterpreted(nm));
            let (p, q) = (tm.mk_var("p", us), tm.mk_var("q", us));
            let eq = tm.mk_eq(p, q);
            let (one, zero) = (tm.mk_int(1), tm.mk_int(0));
            let ite = tm.mk_ite(eq, one, zero);
            let e = tm.mk_eq(ite, zero);
            let n = tm.mk_not(e);
            vec![n]
        },
    );
}
