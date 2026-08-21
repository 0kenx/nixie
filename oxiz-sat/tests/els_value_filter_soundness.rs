//! ELS rewrite soundness regression: value-filtered substitution.
//!
//! `substitute_equivalent_literals_round` used to keep level-0-falsified
//! literals in rewritten clauses and rely on the post-pass watch rebuild +
//! one `propagate()` to re-establish the fixpoint. But a watch only fires
//! when its literal *becomes* false: watches freshly parked on literals that
//! were **already** false at level 0 never fire again, so a rewritten clause
//! could sit with both watches dead – no unit propagation, no conflict –
//! until the full-assignment guard caught a falsified live clause
//! (`constraints_17_0.4_1` answered `Unknown` under `enable_equiv_substitution`;
//! without the guard this is a false-`Sat` class).
//!
//! The fix mirrors cadical `decompose.cpp`: while rewriting, drop literals
//! false at level 0 and retire clauses satisfied at level 0, so every
//! surviving literal (hence every rebuilt watch) is unassigned.
//!
//! The hand-built tests below pin the *behavior* of the value filter
//! (collapsed clauses become units; a fully-falsified rewrite reports UNSAT).
//! The dead-watch shape itself needs mid-search state (learned binaries
//! feeding the SCC plus level-0 units accumulated during search) – every
//! purely pre-search construction is self-healing, because the two watches
//! are alive until the rewrite swaps them onto already-false literals – so
//! the historical reproducer lives in the ignored test at the bottom.

use oxiz_sat::{LBool, Lit, Solver, SolverConfig, SolverResult, Var};

fn v(i: u32) -> Var {
    Var::new(i)
}

#[test]
fn els_rewrite_does_not_strand_dead_watches_sat() {
    // Vars: x=0, y=1, a=2, b=3.
    // Units: ¬x, ¬y (level 0). Equivalence: a ≡ b. Victim: (x ∨ y ∨ b).
    //
    // Formula is SAT: x=y=false forces b=true (hence a=true) through the
    // victim clause. With the value filter the victim rewrites to the unit
    // `b` and the model carries b (and a) true; assert both so a regression
    // to "keep the false literals, decide the rest" is visible in the model.
    let mut solver = Solver::with_config(SolverConfig {
        enable_inprocessing: false,
        enable_equiv_substitution: true,
        presearch_collapse: true,
        ..SolverConfig::default()
    });
    for _ in 0..4 {
        solver.new_var();
    }
    solver.add_clause(vec![Lit::neg(v(0))]); // ¬x
    solver.add_clause(vec![Lit::neg(v(1))]); // ¬y
    solver.add_clause(vec![Lit::neg(v(2)), Lit::pos(v(3))]); // ¬a ∨ b
    solver.add_clause(vec![Lit::pos(v(2)), Lit::neg(v(3))]); // a ∨ ¬b
    solver.add_clause(vec![Lit::pos(v(0)), Lit::pos(v(1)), Lit::pos(v(3))]); // x ∨ y ∨ b  (victim)

    assert_eq!(solver.solve(), SolverResult::Sat);
    // The victim clause forces b (and thus a) true.
    let model = solver.model();
    assert_eq!(
        model[3],
        LBool::True,
        "b must be true: victim clause is unit after ¬x, ¬y"
    );
    assert_eq!(model[2], LBool::True, "a must be true: a ≡ b");
}

#[test]
fn els_rewrite_detects_falsified_clause_as_unsat() {
    // Same shape, plus the unit ¬a: the victim clause (x∨y∨b) rewrites
    // through the equivalence to a side contradicted by ¬a at level 0 →
    // the instance is UNSAT and ELS must report it (a fully-falsified
    // rewrite is a level-0 refutation, cadical `learn_empty_clause`).
    let mut solver = Solver::with_config(SolverConfig {
        enable_inprocessing: false,
        enable_equiv_substitution: true,
        presearch_collapse: true,
        ..SolverConfig::default()
    });
    for _ in 0..4 {
        solver.new_var();
    }
    solver.add_clause(vec![Lit::neg(v(0))]); // ¬x
    solver.add_clause(vec![Lit::neg(v(1))]); // ¬y
    solver.add_clause(vec![Lit::neg(v(2))]); // ¬a
    solver.add_clause(vec![Lit::neg(v(2)), Lit::pos(v(3))]); // ¬a ∨ b
    solver.add_clause(vec![Lit::pos(v(2)), Lit::neg(v(3))]); // a ∨ ¬b
    solver.add_clause(vec![Lit::pos(v(0)), Lit::pos(v(1)), Lit::pos(v(3))]); // x ∨ y ∨ b

    assert_eq!(solver.solve(), SolverResult::Unsat);
}

/// The historical reproducer (satcomp2024 `constraints_17_0.4_1`, SAT):
/// with `enable_equiv_substitution` the mid-search ELS round rewrote clauses
/// through equivalences built from learned binaries while level-0 units had
/// accumulated, parking fresh watches on already-false literals. The search
/// then reached a full assignment over a falsified live clause and the
/// full-assignment guard honestly returned `Unknown` on a SATISFIABLE
/// instance (before that guard existed this was the false-`Sat` shape).
///
/// Slow (tens of seconds in debug): run explicitly with
/// `cargo nextest run -p oxiz-sat --runignored only --test els_value_filter_soundness`.
#[test]
#[ignore = "slow: full solve of a 2720-var instance; run with --runignored"]
fn els_constraints_17_mid_search_rewrite_answers_sat_not_unknown() {
    use oxiz_sat::DimacsParser;
    let mut solver = Solver::with_config(SolverConfig {
        enable_inprocessing: true,
        enable_bve: true,
        enable_equiv_substitution: true,
        ..SolverConfig::default()
    });
    let mut parser = DimacsParser::new();
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../satcomp2024/bench/8e720686372c5037f30b4fc7b1c71d48-constraints_17_0.4_1.sanitized.cnf"
    );
    parser.parse_file(path, &mut solver).expect("parse");
    let result = solver.solve();
    assert_eq!(
        result,
        SolverResult::Sat,
        "constraints_17 is SAT (CaDiCaL model verified); `Unknown` means an \
         inprocessing pass stranded dead watches on level-0-false literals"
    );
}
