//! Runs the solver core as compiled without `std`.
//!
//! ```sh
//! cargo run -p nixie-nostd-smoke
//! ```
//!
//! This binary links `std` (it prints the verdict); the solver underneath is
//! compiled without it: nothing in this crate's dependency graph turns the
//! library crates' `std` feature on, so `nixie-core`, `nixie-math`,
//! `nixie-sat` and `nixie-theories` build as `no_std` + `alloc` too. Without
//! the feature there is no SMT-LIB parser and no environment (`NIXIE_*` knobs
//! all read as unset), so the formula is built through `TermManager`.
//!
//! What must not change is the solving. Linear integer arithmetic with
//! push/pop and uninterpreted functions with congruence closure answer what
//! they answer under `std`; `just verify` runs this so that a `no_std`
//! configuration that merely compiles never passes for one that works.

use nixie_core::ast::TermManager;
use nixie_solver::{Solver, SolverResult};

fn main() {
    let mut tm = TermManager::new();
    let mut solver = Solver::new();

    // 5 <= x <= 10 is satisfiable; adding x < 5 is not; popping restores.
    let x = tm.mk_var("x", tm.sorts.int_sort);
    let five = tm.mk_int(5);
    let ten = tm.mk_int(10);
    solver.assert(tm.mk_ge(x, five), &mut tm);
    solver.assert(tm.mk_le(x, ten), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    solver.push();
    solver.assert(tm.mk_lt(x, five), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    solver.pop();
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);

    // f(f(x)) = x and f(f(f(x))) = x force f(x) = x: f(f(f(x))) is f(x) by
    // the first equation applied to f(x), hence x by the second.
    let int_sort = tm.sorts.int_sort;
    let fx = tm.mk_apply("f", [x], int_sort);
    let ffx = tm.mk_apply("f", [fx], int_sort);
    let fffx = tm.mk_apply("f", [ffx], int_sort);
    solver.push();
    solver.assert(tm.mk_eq(ffx, x), &mut tm);
    solver.assert(tm.mk_eq(fffx, x), &mut tm);
    solver.assert(tm.mk_distinct([fx, x]), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    solver.pop();

    println!("no_std solver: LIA push/pop and EUF congruence answer as under std");
}
