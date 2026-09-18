//! Regression tests for ITE gate-congruence extraction and folding
//! (`solver/congruence.rs`, landed 2026-09-18 after the kissat
//! `congruence.c` reference).
//!
//! The properties under test:
//!
//! 1. **Soundness of the extraction.** A four-clause ITE definition is only
//!    recorded when all four clauses are present; the derived equivalences
//!    must therefore be entailed. The 2026-09-18 prototyping bug this file
//!    pins: the canonical presentation of `(c ? t : e)` is
//!    `(¬c ? e : t)` — then/else SWAPPED, not negated. Negating all three
//!    inputs produces the *complement's* swap form, which made the closure
//!    merge an output with the output of a *different* function (a false
//!    UNSAT on `6s299b685_Iter22`, caught by kissat disagreement).
//! 2. **The three merge rules** (same function, same complement, and the
//!    cross rule where one gate's positive triple is another's complement).
//! 3. **The trivial-ITE shortcut** (`c ? t : t` proves `o ≡ t`) including
//!    when `t` is not itself a gate output.
//!
//! Black-box whole-solver checks in the `pr26_inprocessing_regressions`
//! style: verdicts plus total models satisfying the *original* clauses.

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

/// Force `a ≡ b` (an inconsistent demand when the congruence proved `a ≡ ¬b`).
fn force_equal(s: &mut Solver, a: usize, b: usize) {
    s.add_clause([l(a, false), l(b, true)]);
    s.add_clause([l(a, true), l(b, false)]);
}

/// Force `a ≠ b` (an inconsistent demand when the congruence proved `a ≡ b`).
fn force_distinct(s: &mut Solver, a: usize, b: usize) {
    s.add_clause([l(a, true), l(b, true)]);
    s.add_clause([l(a, false), l(b, false)]);
}

/// Add the four clauses defining `o ↔ (c ? t : e)` with per-literal polarity.
#[allow(clippy::too_many_arguments)]
fn add_ite_gate(
    s: &mut Solver,
    o: usize,
    c: usize,
    t: usize,
    e: usize,
    ot: bool,
    ct: bool,
    tt: bool,
    et: bool,
) {
    let (o, c, t, e) = (l(o, ot), l(c, ct), l(t, tt), l(e, et));
    // (¬o ∨ ¬c ∨ t), (¬o ∨ c ∨ e), (o ∨ ¬c ∨ ¬t), (o ∨ c ∨ ¬e)
    s.add_clause([o.negate(), c.negate(), t]);
    s.add_clause([o.negate(), c, e]);
    s.add_clause([o, c.negate(), t.negate()]);
    s.add_clause([o, c, e.negate()]);
}

fn assert_model_satisfies(solver: &Solver, clauses: &[&[Lit]], num_vars: usize) {
    for (i, clause) in clauses.iter().enumerate() {
        let sat = clause.iter().any(|&lit| {
            let val = solver.model_value(lit.var());
            (val == nixie_sat::LBool::True) == lit.is_pos()
        });
        assert!(sat, "clause #{i} {clause:?} unsatisfied by the model");
    }
    for i in 0..num_vars {
        assert_ne!(
            solver.model_value(v(i)),
            nixie_sat::LBool::Undef,
            "variable {i} must be concrete in a Sat model"
        );
    }
}

/// Solver with ELS + gate congruence armed the way the inprocessing round
/// runs it (the fold is what consumes the congruence edges).
fn congruence_solver(num_vars: usize) -> Solver {
    let cfg = SolverConfig {
        enable_equiv_substitution: true,
        enable_gate_congruence: true,
        enable_inprocessing: true,
        // Conflict scheduling (the default) fires the fold on the
        // elimination clock, which tiny instances never reach; the
        // pre-search path does.
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

/// Two ITE gates over identical inputs have equivalent outputs: forcing
/// `o1 ≠ o2` must be UNSAT, and the base formula (without the break) SAT.
#[test]
fn ite_congruent_twins_fold() {
    // vars: 0..5 inputs, 6/7 outputs, 8 breaker
    let mut s = congruence_solver(9);
    add_ite_gate(&mut s, 6, 0, 1, 2, true, true, true, true);
    add_ite_gate(&mut s, 7, 0, 1, 2, true, true, true, true);
    force_distinct(&mut s, 6, 7);
    assert_eq!(s.solve(), SolverResult::Unsat);
}

/// Complementary gates: `o2 ↔ ¬f(o1)` (both branch literals flipped). The
/// 2026-09-18 canonicalization bug merged these as EQUAL — turning this SAT
/// family into a false UNSAT. With the fix, `o1 ≠ o2` is UNSAT (o2 ≡ ¬o1)
/// and the unbroken formula is SAT.
#[test]
fn ite_complement_twins_fold_as_negation_not_equality() {
    // o6 ↔ (c0 ? t1 : e2);  o7 ↔ (c0 ? ¬t1 : ¬e2)
    let mut s = congruence_solver(9);
    add_ite_gate(&mut s, 6, 0, 1, 2, true, true, true, true);
    add_ite_gate(&mut s, 7, 0, 1, 2, true, true, false, false);
    // o6 = o7 forced: UNSAT, because the congruence proved o7 ≡ ¬o6.
    force_equal(&mut s, 6, 7);
    assert_eq!(s.solve(), SolverResult::Unsat);

    // And the positive statement: o6 ≠ o7 holds — the formula with the
    // break removed must be SAT with a total model.
    let mut s2 = congruence_solver(8);
    add_ite_gate(&mut s2, 6, 0, 1, 2, true, true, true, true);
    add_ite_gate(&mut s2, 7, 0, 1, 2, true, true, false, false);
    let r = s2.solve();
    assert_eq!(r, SolverResult::Sat);
}

/// The same function presented the two ways the canonicalization must
/// identify: `(c ? t : e)` and `(¬c ? e : t)`. Forcing their outputs apart
/// must be UNSAT.
#[test]
fn ite_swap_presentation_is_the_same_function() {
    // o6 ↔ (c0 ? t1 : e2);  o7 ↔ (¬c0 ? e2 : t1)
    let mut s = congruence_solver(9);
    add_ite_gate(&mut s, 6, 0, 1, 2, true, true, true, true);
    add_ite_gate(&mut s, 7, 0, 2, 1, true, false, true, true);
    force_distinct(&mut s, 6, 7);
    assert_eq!(s.solve(), SolverResult::Unsat);
}

/// Trivial ITE `o ↔ (c ? t : t)` forces `o ≡ t`, including when `t` is not
/// itself any gate's output (the case where the equivalence would otherwise
/// be lost because class materialization only names gate outputs).
#[test]
fn ite_trivial_gate_proves_output_equals_branch() {
    let mut s = congruence_solver(8);
    // o6 ↔ (c0 ? t1 : t1): four clauses with e == t.
    add_ite_gate(&mut s, 6, 0, 1, 1, true, true, true, true);
    // o6 ≠ t1 must be UNSAT (the trivial gate proves o6 ≡ t1).
    force_distinct(&mut s, 6, 1);
    assert_eq!(s.solve(), SolverResult::Unsat);
}

/// The real-world false-UNSAT shape from `6s299b685_Iter22`: an output
/// defined as the complement function via a differently-presented gate. The
/// formula is SAT; a bogus same-function merge of the two outputs makes it
/// UNSAT. This is the minimized form of the bug the differential fuzzer and
/// kissat disagreement caught on 2026-09-18.
#[test]
fn ite_false_unsat_regression_complement_vs_plain_presentation() {
    // Gate A: o6 ↔ (c0 ? x3 : e4)
    // Gate B: o7 ↔ (c0 ? ¬x3 : ¬e4)   [= ¬o6, the Iter22 shape]
    // Constraints: c0 and (x3 ∨ e4) — satisfiable; any model works.
    // A buggy closure merging o6 ≡ o7 (instead of o6 ≡ ¬o7) plus the
    // equality clauses below flips the verdict to a false UNSAT.
    let mut s = congruence_solver(9);
    add_ite_gate(&mut s, 6, 0, 3, 4, true, true, true, true);
    add_ite_gate(&mut s, 7, 0, 3, 4, true, true, false, false);
    s.add_clause([l(0, true)]);
    s.add_clause([l(3, true), l(4, true)]);
    // o6 ≡ o7 forced: genuinely UNSAT (they are complements).
    force_equal(&mut s, 6, 7);
    assert_eq!(s.solve(), SolverResult::Unsat);

    // Without the break: SAT, model total and satisfying every original
    // clause (checks the fold did not corrupt reconstruction).
    fn add_tracked(s: &mut Solver, clauses: &mut Vec<Vec<Lit>>, lits: &[Lit]) {
        clauses.push(lits.to_vec());
        s.add_clause(lits.iter().copied());
    }
    fn quad(s: &mut Solver, clauses: &mut Vec<Vec<Lit>>, o: Lit, c: Lit, t: Lit, e: Lit) {
        add_tracked(s, clauses, &[o.negate(), c.negate(), t]);
        add_tracked(s, clauses, &[o.negate(), c, e]);
        add_tracked(s, clauses, &[o, c.negate(), t.negate()]);
        add_tracked(s, clauses, &[o, c, e.negate()]);
    }
    let mut s2 = congruence_solver(8);
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    quad(
        &mut s2,
        &mut clauses,
        l(6, true),
        l(0, true),
        l(3, true),
        l(4, true),
    );
    quad(
        &mut s2,
        &mut clauses,
        l(7, true),
        l(0, true),
        l(3, false),
        l(4, false),
    );
    add_tracked(&mut s2, &mut clauses, &[l(0, true)]);
    add_tracked(&mut s2, &mut clauses, &[l(3, true), l(4, true)]);
    assert_eq!(s2.solve(), SolverResult::Sat);
    let refs: Vec<&[Lit]> = clauses.iter().map(|c| c.as_slice()).collect();
    assert_model_satisfies(&s2, &refs, 8);
}

/// Sanity: gates over DIFFERENT inputs never merge. Forcing the outputs
/// apart must stay SAT.
#[test]
fn ite_distinct_gates_do_not_fold() {
    let mut s = congruence_solver(9);
    add_ite_gate(&mut s, 6, 0, 1, 2, true, true, true, true);
    add_ite_gate(&mut s, 7, 0, 1, 3, true, true, true, true); // different else
    force_distinct(&mut s, 6, 7);
    // e2 ≠ e3 makes the two functions genuinely different; o6 ≠ o7 is then
    // satisfiable.
    force_distinct(&mut s, 2, 3);
    assert_eq!(s.solve(), SolverResult::Sat);
}

/// An ITE whose branches make it an XOR (`c ? t : ¬t`) is left to the XOR
/// arm (kissat parity) — it must still be handled soundly: two such gates
/// over the same inputs fold as XOR outputs.
#[test]
fn ite_xor_shaped_gate_is_sound() {
    let mut s = congruence_solver(8);
    // o6 ↔ (c0 ? t1 : ¬t1)
    add_ite_gate(&mut s, 6, 0, 1, 1, true, true, true, false);
    // o7 ↔ (c0 ? t1 : ¬t1)
    add_ite_gate(&mut s, 7, 0, 1, 1, true, true, true, false);
    force_distinct(&mut s, 6, 7);
    assert_eq!(s.solve(), SolverResult::Unsat);
}
