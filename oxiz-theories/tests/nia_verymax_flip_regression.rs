//! Regression tests for the QF_NIA "VeryMax flip" class (510/489 shape).
//!
//! Background (see the 0.3.2 QF_NIA parity investigation): industrial
//! VeryMax/T2 termination goals mix
//!
//!   * unit-bounded integer variables and defining equalities,
//!   * a **rank-function disjunction** – `∨ᵢ (v ≥ cᵢ)` with dozens of
//!     bound alternatives,
//!   * a **Boolean guard interface** – `(= (= b true) φ)` constraining a
//!     free Boolean without defining it,
//!   * bilinear monomials (`z*z`),
//!
//! and their witnesses sit far from the linear-relaxation vertex.  Two bugs
//! made these goals flip `sat ↔ unknown` on the *same input*:
//!
//! 1. `ground_bool_interface_eqs` collected `(= b φ)` equalities from
//!    **nested** positions (e.g. the LHS of `(= (= b true) ψ)`), treating a
//!    constraint on `b` as a *definition*: substituting `b := φ` pinned the
//!    variable, strengthened the goal and hid the real model (the witness
//!    below wants `b = false`, the bogus grounding forced `b = true`).
//! 2. The model-based search had no case-split for falsified *non-`or`*
//!    conjuncts (disequalities, constant-sided Boolean equalities) and no
//!    bound-chain collapse for rank disjunctions, so whether the witness was
//!    found depended on which simplex vertex the relaxation happened to land
//!    on – a pivot-order change silently flipped the verdict.
//!
//! These tests pin the *procedure*: each formula must be decided by
//! `dispatch_nia_constraints` (model-based NIA search), not by luck.

use oxiz_core::ast::{TermId, TermManager};
use oxiz_theories::nlsat::{NlDispatchResult, dispatch_nia_constraints};

/// Build the shared variable skeleton for the flip shape.
struct FlipShape {
    x: TermId,
    y: TermId,
    z: TermId,
    b: TermId,
}

fn declare(tm: &mut TermManager) -> FlipShape {
    let int_sort = tm.sorts.int_sort;
    let bool_sort = tm.sorts.bool_sort;
    FlipShape {
        x: tm.mk_var("x", int_sort),
        y: tm.mk_var("y", int_sort),
        z: tm.mk_var("z", int_sort),
        b: tm.mk_var("b", bool_sort),
    }
}

/// Unit bounds: `-1 ≤ x ≤ 1`, `y ≥ 0`, `0 ≤ z ≤ 3`.
fn unit_bounds(tm: &mut TermManager, s: &FlipShape) -> TermId {
    let one = tm.mk_int(1);
    let m1 = tm.mk_int(-1);
    let z0 = tm.mk_int(0);
    let z3 = tm.mk_int(3);
    let gx = tm.mk_ge(s.x, m1);
    let lx = tm.mk_le(s.x, one);
    let gy = tm.mk_ge(s.y, z0);
    let gz = tm.mk_ge(s.z, z0);
    let lz = tm.mk_le(s.z, z3);
    tm.mk_and([gx, lx, gy, gz, lz])
}

/// The Boolean guard interface `(= (= b true) (not (= z 0)))` – a constraint
/// on `b`, *not* a definition of it (the satisfying model has `b = false`,
/// `z = 0`).
fn bool_guard(tm: &mut TermManager, s: &FlipShape) -> TermId {
    let z0 = tm.mk_int(0);
    let eq_z = tm.mk_eq(s.z, z0);
    let neq = tm.mk_not(eq_z);
    let b_true = tm.mk_eq(s.b, tm.mk_true());
    tm.mk_eq(b_true, neq)
}

/// The bilinear coupling `z*z = 4*z` (forces `z ∈ {0, 4}`, i.e. `z = 0`
/// inside the unit box).
fn bilinear(tm: &mut TermManager, s: &FlipShape) -> TermId {
    let four = tm.mk_int(4);
    let zz = tm.mk_mul([s.z, s.z]);
    let fz = tm.mk_mul([four, s.z]);
    tm.mk_eq(zz, fz)
}

/// Rank-function disjunction `∨_{i=1..n} (y ≥ i)` in the encoder shape
/// VeryMax emits: `(<= (+ (* (- 1) y) 0 i) 0)`.
fn rank_disjunction(tm: &mut TermManager, s: &FlipShape, n: i64) -> TermId {
    let m1 = tm.mk_int(-1);
    let z0 = tm.mk_int(0);
    let zero = tm.mk_int(0);
    let disjuncts: Vec<TermId> = (1..=n)
        .map(|i| {
            let i_term = tm.mk_int(i);
            let prod = tm.mk_mul([m1, s.y]);
            let sum = tm.mk_add([prod, z0, i_term]);
            tm.mk_le(sum, zero)
        })
        .collect();
    tm.mk_or(disjuncts)
}

/// Linear coupling `2*y + 3*x = 12` (with `x ∈ {-1,0,1}` the only integer
/// solution is `x = 0, y = 6` – far from the relaxation's `y = 0` vertex).
fn linear_coupling(tm: &mut TermManager, s: &FlipShape) -> TermId {
    let two = tm.mk_int(2);
    let three = tm.mk_int(3);
    let twelve = tm.mk_int(12);
    let ty = tm.mk_mul([two, s.y]);
    let tx = tm.mk_mul([three, s.x]);
    let sum = tm.mk_add([ty, tx]);
    tm.mk_eq(sum, twelve)
}

/// The full flip shape: guard + bounds + bilinear + rank disjunction +
/// linear coupling. Satisfiable exactly at `x=0, y=6, z=0, b=false`.
/// Pre-fix this answered `unknown` (the bogus `b := true` grounding forced
/// `z ≠ 0`, contradicting `z*z = 4*z` inside the box).
#[test]
fn flip_shape_with_bool_guard_is_sat() {
    let mut tm = TermManager::new();
    let s = declare(&mut tm);
    let parts = [
        unit_bounds(&mut tm, &s),
        bool_guard(&mut tm, &s),
        bilinear(&mut tm, &s),
        rank_disjunction(&mut tm, &s, 8),
        linear_coupling(&mut tm, &s),
    ];
    let assertion = tm.mk_and(parts);
    assert!(
        matches!(
            dispatch_nia_constraints(&[assertion], &mut tm, true, true),
            Some(NlDispatchResult::Sat(_))
        ),
        "x=0, y=6, z=0, b=false satisfies the flip shape"
    );
}

/// Same shape without the Boolean guard (pure arithmetic): the rank
/// disjunction plus the linear coupling must still reach `y = 6`.
#[test]
fn flip_shape_rank_disjunction_is_sat() {
    let mut tm = TermManager::new();
    let s = declare(&mut tm);
    let parts = [
        unit_bounds(&mut tm, &s),
        bilinear(&mut tm, &s),
        rank_disjunction(&mut tm, &s, 8),
        linear_coupling(&mut tm, &s),
    ];
    let assertion = tm.mk_and(parts);
    assert!(
        matches!(
            dispatch_nia_constraints(&[assertion], &mut tm, true, true),
            Some(NlDispatchResult::Sat(_))
        ),
        "x=0, y=6, z=0 satisfies the arithmetic flip shape"
    );
}

/// A *long* rank chain (60 alternatives) must not regress: the bound-chain
/// collapse in `try_alternatives` reduces `∨ᵢ (y ≥ i)` to `y ≥ 1`, so the
/// chain length must not matter.
#[test]
fn flip_shape_long_rank_chain_is_sat() {
    let mut tm = TermManager::new();
    let s = declare(&mut tm);
    let parts = [
        unit_bounds(&mut tm, &s),
        bilinear(&mut tm, &s),
        rank_disjunction(&mut tm, &s, 60),
        linear_coupling(&mut tm, &s),
    ];
    let assertion = tm.mk_and(parts);
    assert!(matches!(
        dispatch_nia_constraints(&[assertion], &mut tm, true, true),
        Some(NlDispatchResult::Sat(_))
    ));
}

/// The unsatisfiable twin: `y ≥ 9` plus the coupling `2y + 3x = 12` with
/// `|x| ≤ 1` caps `y ≤ 7`. The dispatcher must never answer `Sat` here
/// (honest `None`/`Unsat` both acceptable – the relaxation-infeasible case
/// is deliberately uncertified).
#[test]
fn flip_shape_unsat_twin_never_sat() {
    let mut tm = TermManager::new();
    let s = declare(&mut tm);
    let y9 = tm.mk_int(9);
    let gy9 = tm.mk_ge(s.y, y9);
    let parts = [
        unit_bounds(&mut tm, &s),
        bool_guard(&mut tm, &s),
        bilinear(&mut tm, &s),
        gy9,
        linear_coupling(&mut tm, &s),
    ];
    let assertion = tm.mk_and(parts);
    let res = dispatch_nia_constraints(&[assertion], &mut tm, true, true);
    assert!(
        !matches!(res, Some(NlDispatchResult::Sat(_))),
        "y ≥ 9 ∧ 2y + 3x = 12 ∧ |x| ≤ 1 is unsatisfiable"
    );
}

/// The guard must be honored in *both* directions: pinning the guard's
/// Boolean true (`b = true ⇒ z ≠ 0`) makes the bilinear coupling
/// unsatisfiable inside the box (`z ∈ {0,4}` ∩ `[0,3] ∩ {≠0} = ∅`). The
/// dispatcher must not report `Sat` when every model needs `z ≠ 0`.
#[test]
fn flip_shape_guard_true_branch_is_not_sat() {
    let mut tm = TermManager::new();
    let s = declare(&mut tm);
    let b_true = tm.mk_eq(s.b, tm.mk_true());
    let parts = [
        unit_bounds(&mut tm, &s),
        b_true,
        bool_guard(&mut tm, &s),
        bilinear(&mut tm, &s),
        rank_disjunction(&mut tm, &s, 8),
        linear_coupling(&mut tm, &s),
    ];
    let assertion = tm.mk_and(parts);
    let res = dispatch_nia_constraints(&[assertion], &mut tm, true, true);
    assert!(
        !matches!(res, Some(NlDispatchResult::Sat(_))),
        "b = true forces z ≠ 0, contradicting z*z = 4*z within [0,3]"
    );
}
