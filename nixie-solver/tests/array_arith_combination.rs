//! A **wrong `sat`**: an index equality that only *arithmetic* entails never
//! reaches the array theory.
//!
//! See `docs/studies/2026-09-14-array-index-equality-from-arithmetic.md`. The
//! guard below is `#[ignore]`d because it currently fails: it is checked in so
//! the reproducer is not lost and so the fix has something to turn green, not
//! to pass today.
//!
//! Found from the most ordinary TLA+ there is — a function read at a state
//! variable's value —
//!
//! ```tla
//! f[k \in 0..3] == IF k <= 0 THEN 0 ELSE 1
//! Init == n = 0 /\ s = f[n]      Next == n' = n + 1 /\ s' = f[n']
//! Inv  == s < 100
//! ```
//!
//! which has no counterexample and is reported as violated.

use nixie_core::TermManager;
use nixie_solver::{Solver, SolverResult};

/// `n1 = n0 + 1`, `n0 = 0`, so `n1` is `1` and `store(base, 1, 7)[n1]` is `7`.
/// Asserting it is `2` is unsatisfiable. The solver answers `Sat`.
#[test]
#[ignore = "known wrong `sat`: see docs/studies/2026-09-14-array-index-equality-from-arithmetic.md"]
fn select_at_an_arithmetically_equal_index() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let arr = tm.sorts.array(int, int);
    let base = tm.mk_var("base", arr);
    let n0 = tm.mk_var("n0", int);
    let n1 = tm.mk_var("n1", int);
    let zero = tm.mk_int(0);
    let one = tm.mk_int(1);
    let seven = tm.mk_int(7);
    let two = tm.mk_int(2);
    let stored = tm.mk_store(base, one, seven);
    let at = tm.mk_select(stored, n1);
    let mut s = Solver::new();
    let c0 = tm.mk_eq(n0, zero);
    let sum = tm.mk_add([n0, one]);
    let c1 = tm.mk_eq(n1, sum);
    let c2 = tm.mk_eq(at, two);
    s.assert(c0, &mut tm);
    s.assert(c1, &mut tm);
    s.assert(c2, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// The same read with the index equality given **directly** is decided
/// correctly, which is what localises the gap. Not ignored: this one passes,
/// and it is the control that keeps the diagnosis honest.
#[test]
fn select_at_a_directly_equal_index_is_decided() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let arr = tm.sorts.array(int, int);
    let base = tm.mk_var("base", arr);
    let n1 = tm.mk_var("n1", int);
    let one = tm.mk_int(1);
    let seven = tm.mk_int(7);
    let two = tm.mk_int(2);
    let stored = tm.mk_store(base, one, seven);
    let at = tm.mk_select(stored, n1);
    let mut s = Solver::new();
    let c1 = tm.mk_eq(n1, one);
    let c2 = tm.mk_eq(at, two);
    s.assert(c1, &mut tm);
    s.assert(c2, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// And so is an equality **chain** through EUF, with no arithmetic in it.
#[test]
fn select_through_an_equality_chain_is_decided() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let arr = tm.sorts.array(int, int);
    let base = tm.mk_var("base", arr);
    let n0 = tm.mk_var("n0", int);
    let n1 = tm.mk_var("n1", int);
    let one = tm.mk_int(1);
    let seven = tm.mk_int(7);
    let two = tm.mk_int(2);
    let stored = tm.mk_store(base, one, seven);
    let at = tm.mk_select(stored, n1);
    let mut s = Solver::new();
    let a = tm.mk_eq(n1, n0);
    let b = tm.mk_eq(n0, one);
    let c = tm.mk_eq(at, two);
    s.assert(a, &mut tm);
    s.assert(b, &mut tm);
    s.assert(c, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// And the arithmetic alone is decided: `n0 = 0`, `n1 = n0 + 1`, `n1 # 1` is
/// unsatisfiable without an array anywhere near it.
#[test]
fn the_arithmetic_alone_is_decided() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let n0 = tm.mk_var("n0", int);
    let n1 = tm.mk_var("n1", int);
    let zero = tm.mk_int(0);
    let one = tm.mk_int(1);
    let sum = tm.mk_add([n0, one]);
    let a = tm.mk_eq(n1, sum);
    let b = tm.mk_eq(n0, zero);
    let eq1 = tm.mk_eq(n1, one);
    let ne = tm.mk_not(eq1);
    let mut s = Solver::new();
    s.assert(a, &mut tm);
    s.assert(b, &mut tm);
    s.assert(ne, &mut tm);
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}
