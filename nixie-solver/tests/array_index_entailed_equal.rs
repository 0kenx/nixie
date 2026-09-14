//! A **wrong `sat`**: an array index a *variable* whose equality to a constant
//! index only arithmetic entails.
//!
//! `select(A, 0) = 0`, `select(A, 1) = 1`, `n = 1`, `select(A, n) = 5` is
//! unsatisfiable: congruence gives `select(A, n) = select(A, 1) = 1`. With
//! `n = 1` asserted directly it was decided correctly. With `n = 1` *entailed*
//! (`n0 = 0`, `n = n0 + 1`) it answered `Sat`.
//!
//! No array *lemma* is involved — there is no store, so nothing mints the
//! index-equality atom. What was missing is one step earlier:
//! `nelson_oppen_combine`'s model-equal probe pairs terms that are both EUF
//! application arguments *and* arithmetic interface terms, and a constant
//! array index was never made an interface term. `purify_numeric_uf_args`
//! pinned constant arguments of `Apply` (the `pr30#3` fix) but walked past
//! `Select`/`Store`.
//!
//! Found from Apalache's `Rec3.tla` — a recursive `Fib` over `0..15` read at a
//! state variable, `Fib[n']` — which was reported violated with `Fib[1] = 2`.

use nixie_core::TermManager;
use nixie_solver::{Solver, SolverResult};

/// The index equality given **directly**: the control. Congruence alone
/// decides it, and it was always correct.
#[test]
fn a_directly_equal_index_is_decided() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let arr = tm.sorts.array(int, int);
    let a = tm.mk_var("A", arr);
    let n = tm.mk_var("n", int);
    let (z, o, five) = (tm.mk_int(0), tm.mk_int(1), tm.mk_int(5));
    let s0 = tm.mk_select(a, z);
    let s1 = tm.mk_select(a, o);
    let sn = tm.mk_select(a, n);
    let mut s = Solver::new();
    let c1 = tm.mk_eq(s0, z);
    let c2 = tm.mk_eq(s1, o);
    let c3 = tm.mk_eq(n, o);
    let c4 = tm.mk_eq(sn, five);
    for c in [c1, c2, c3, c4] {
        s.assert(c, &mut tm);
    }
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// The same read with `n = 1` entailed only by **arithmetic**. This is the
/// one that answered `Sat`.
#[test]
fn an_arithmetically_equal_index_is_decided() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let arr = tm.sorts.array(int, int);
    let a = tm.mk_var("A", arr);
    let n0 = tm.mk_var("n0", int);
    let n = tm.mk_var("n", int);
    let (z, o, five) = (tm.mk_int(0), tm.mk_int(1), tm.mk_int(5));
    let s0 = tm.mk_select(a, z);
    let s1 = tm.mk_select(a, o);
    let sn = tm.mk_select(a, n);
    let mut s = Solver::new();
    let c1 = tm.mk_eq(s0, z);
    let c2 = tm.mk_eq(s1, o);
    let c3 = tm.mk_eq(n0, z);
    let sum = tm.mk_add([n0, o]);
    let c4 = tm.mk_eq(n, sum);
    let c5 = tm.mk_eq(sn, five);
    for c in [c1, c2, c3, c4, c5] {
        s.assert(c, &mut tm);
    }
    assert_eq!(s.check(&mut tm), SolverResult::Unsat);
}

/// The satisfiable side of the same shape, so the fix cannot be a blanket
/// refutation: with `n = n0 + 2` the read is at index `2`, which nothing
/// constrains, so `5` is a perfectly good value.
#[test]
fn an_unconstrained_index_stays_sat() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let arr = tm.sorts.array(int, int);
    let a = tm.mk_var("A", arr);
    let n0 = tm.mk_var("n0", int);
    let n = tm.mk_var("n", int);
    let (z, o, two, five) = (tm.mk_int(0), tm.mk_int(1), tm.mk_int(2), tm.mk_int(5));
    let s0 = tm.mk_select(a, z);
    let s1 = tm.mk_select(a, o);
    let sn = tm.mk_select(a, n);
    let mut s = Solver::new();
    let c1 = tm.mk_eq(s0, z);
    let c2 = tm.mk_eq(s1, o);
    let c3 = tm.mk_eq(n0, z);
    let sum = tm.mk_add([n0, two]);
    let c4 = tm.mk_eq(n, sum);
    let c5 = tm.mk_eq(sn, five);
    for c in [c1, c2, c3, c4, c5] {
        s.assert(c, &mut tm);
    }
    assert_eq!(s.check(&mut tm), SolverResult::Sat);
}
