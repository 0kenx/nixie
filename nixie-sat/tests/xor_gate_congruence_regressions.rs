//! Tests for the corrected XOR-gate congruence (2026-09-18, second landing):
//! sign-complete extraction (all four input-sign presentations per base
//! clause — the signs-as-written scan found zero of bv_ILA's 2,534 complete
//! parity sets) and the signed-input presentation algebra in the closure.
//!
//! The pinned bug (minimized from fuzz seed 500089 to 56 clauses): the
//! first XOR closure keyed the affine relation over all three gate vars,
//! so one parity definition read three ways (any var as the output) merged
//! its inputs with its outputs — `37 ≡ 41 ≡ 122 ≡ 123` from a single
//! `122 ↔ 37⊕41` / `123 ↔ ¬(37⊕41)` pair — a false UNSAT.  A second
//! variant parity-folded the input signs into the key, merging a
//! definition's `o` with its own `¬o`.  The sound algebra mirrors ITE:
//! `f = a⊕b` has presentations `(a,b)` and `(¬a,¬b)`; `¬f` has `(¬a,b)`
//! and `(a,¬b)`; canonical = min per family; duplicate polarity readings
//! self-cancel.

use nixie_sat::{Lit, Solver, SolverConfig, SolverResult, Var};

fn v(i: usize) -> Var {
    Var::new(i as u32)
}

fn l(i: usize, positive: bool) -> Lit {
    if positive {
        Lit::pos(v(i))
    } else {
        Lit::neg(v(i))
    }
}

/// Force `a ≡ b` in DIMACS literal terms.
fn force_equal_dimacs(s: &mut Solver, a: i32, b: i32) {
    s.add_clause_dimacs(&[-a, b]);
    s.add_clause_dimacs(&[a, -b]);
}

/// Force `a ≢ b` (the opposite of [`force_equal_dimacs`]).
#[allow(dead_code)]
fn force_distinct_dimacs(s: &mut Solver, a: i32, b: i32) {
    s.add_clause_dimacs(&[a, b]);
    s.add_clause_dimacs(&[-a, -b]);
}

/// Emit the 4-clause parity set for `o ↔ (a ⊕ b)` with `flip` selecting the
/// constant (`false`: XOR, `true`: XNOR — both are complete presentations
/// the extractor must recognize).
fn add_parity_gate(s: &mut Solver, o: usize, a: usize, b: usize, flip: bool) {
    let (o, a, b) = (l(o, true), l(a, true), l(b, true));
    if flip {
        s.add_clause([o, a.negate(), b.negate()]);
        s.add_clause([o.negate(), a.negate(), b]);
        s.add_clause([o.negate(), a, b.negate()]);
        s.add_clause([o, a, b]);
    } else {
        s.add_clause([o.negate(), a, b]);
        s.add_clause([o.negate(), a.negate(), b.negate()]);
        s.add_clause([o, a.negate(), b]);
        s.add_clause([o, a, b.negate()]);
    }
}

fn congruence_solver(num_vars: usize) -> Solver {
    let cfg = SolverConfig {
        enable_equiv_substitution: true,
        enable_gate_congruence: true,
        enable_inprocessing: true,
        presearch_collapse: true,
        enable_lucky: false,
        ..SolverConfig::default()
    };
    let mut s = Solver::with_config(cfg);
    for _ in 0..num_vars {
        s.new_var();
    }
    s
}

#[test]
fn xor_congruent_twins_fold() {
    let mut s = congruence_solver(8);
    add_parity_gate(&mut s, 6, 0, 1, false);
    add_parity_gate(&mut s, 7, 0, 1, false);
    // o6 ≠ o7 must be UNSAT (identical functions).
    s.add_clause([l(6, true), l(7, true)]);
    s.add_clause([l(6, false), l(7, false)]);
    assert_eq!(s.solve(), SolverResult::Unsat); // distinct-break, correct polarity
}

#[test]
fn xor_xnor_presentation_extraction_folds() {
    // One definition as XOR, its twin as XNOR over the same inputs: the
    // twins are COMPLEMENTS (o7 ≡ ¬o6).  Forcing them equal is UNSAT.
    // The signs-as-written scan found neither gate (xor=0 on bv_ILA).
    let mut s = congruence_solver(8);
    add_parity_gate(&mut s, 6, 0, 1, false);
    add_parity_gate(&mut s, 7, 0, 1, true);
    s.add_clause([l(6, false), l(7, true)]);
    s.add_clause([l(6, true), l(7, false)]);
    assert_eq!(s.solve(), SolverResult::Unsat);
}

#[test]
fn xor_single_definition_does_not_merge_own_vars() {
    // THE pinned bug shape: one parity definition must never merge its
    // inputs with its outputs (the three-way reading).  The formula is
    // satisfiable; a false closure makes it UNSAT.
    let mut s = congruence_solver(6);
    add_parity_gate(&mut s, 5, 0, 1, false);
    assert_eq!(s.solve(), SolverResult::Sat);
    // And its complement twin: still satisfiable, o5 ≢ o4 but o5 ≡ ¬o4.
    let mut s2 = congruence_solver(6);
    add_parity_gate(&mut s2, 5, 0, 1, false);
    add_parity_gate(&mut s2, 4, 0, 1, true);
    assert_eq!(s2.solve(), SolverResult::Sat);
}

#[test]
fn xor_complement_output_polarity_readings_self_cancel() {
    // The parity-folded-key variant of the bug: a definition whose output
    // literal is recorded negated (equivalent presentation) must not merge
    // o with ¬o.  Equivalent presentations of one relation over two vars.
    let mut s = congruence_solver(6);
    add_parity_gate(&mut s, 5, 0, 1, false);
    // Same relation, output negated and inputs flipped: ¬5 ↔ (¬0)⊕(¬1).
    add_parity_gate(&mut s, 4, 2, 3, false);
    // 0≡2 and 1≡3 make gate4 the same function as gate5 with o4 ≡ ¬o5.
    s.add_clause([l(0, false), l(2, false)]);
    s.add_clause([l(0, true), l(2, true)]);
    s.add_clause([l(1, false), l(3, false)]);
    s.add_clause([l(1, true), l(3, true)]);
    assert_eq!(s.solve(), SolverResult::Sat);
    // o4 ≡ o5 must be UNSAT (with gate4 an XNOR over congruent inputs,
    // o4 ≡ ¬(2⊕3) ≡ ¬o5 — complements).
    let mut s2 = congruence_solver(6);
    add_parity_gate(&mut s2, 5, 0, 1, false);
    add_parity_gate(&mut s2, 4, 2, 3, true);
    s2.add_clause([l(0, false), l(2, false)]);
    s2.add_clause([l(0, true), l(2, true)]);
    s2.add_clause([l(1, false), l(3, false)]);
    s2.add_clause([l(1, true), l(3, true)]);
    s2.add_clause([l(4, false), l(5, true)]);
    s2.add_clause([l(4, true), l(5, false)]);
    assert_eq!(s2.solve(), SolverResult::Unsat);
}

#[test]
fn xor_false_unsat_regression_minimized() {
    // Verbatim from fuzz seed 500089 (delta-debugged to the parity pair +
    // noise): must stay SAT.  The buggy closure answered unsat via the
    // fabricated class {37, 41, 122, 123}.
    let clauses: [&[i32]; 8] = [
        &[-122, 37, 41],
        &[-122, -37, -41],
        &[122, -37, 41],
        &[122, 37, -41],
        &[123, 37, 41],
        &[123, -37, -41],
        &[-123, 37, -41],
        &[-123, -37, 41],
    ];
    let mut s = congruence_solver(124);
    for c in clauses {
        s.add_clause_dimacs(c);
    }
    assert_eq!(s.solve(), SolverResult::Sat);
    // And the true relation the closure may derive: 122 ≡ ¬123 — so
    // forcing 122 ≡ 123 must be UNSAT.
    let mut s2 = congruence_solver(124);
    for c in clauses {
        s2.add_clause_dimacs(c);
    }
    force_equal_dimacs(&mut s2, 122, 123);
    assert_eq!(s2.solve(), SolverResult::Unsat);
}
