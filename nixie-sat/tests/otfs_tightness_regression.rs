//! Soundness regression: the OTFS arm's trigger tightness (2026-09-12).
//!
//! The first `NIXIE_OTFS` implementation fired on a cheap size comparison
//! (`counter + learnt < |A|`) that undercounts the accumulated resolvent —
//! resolved-away conflict-level pivots leave both accumulators while staying
//! `seen` — so the arm rewrote antecedents the partial resolvent had NOT been
//! absorbed into, and the "strengthened" clause was not entailed.  The corpus
//! screen caught it as direct verdict contradictions on model-verified SAT
//! files: `constraints_17` (false `unsat` at 956 conflicts; baseline
//! model-checked `sat` at 44 381), `frb65-12-2`, `mp1-klieber2017s`
//! (false `unsat` ~1.3 k conflicts), `g2-slp`, all three summle files,
//! `si2-b03m`, `j3037_10_mdd_b` — 57 rejected cells, 13 files.
//!
//! The fix gates the fire on the exact cadical condition: every marked
//! literal except ¬p must already be a literal of the antecedent (forcing
//! the merged resolvent to BE `A \ {p}`), computed over the analysis's
//! actual marked set.  These tests pin each false-`unsat` file: the buggy
//! build answered `unsat` comfortably inside the budget, so `!= Unsat` is
//! the assertion (reaching the true `sat` within the budget is welcome but
//! not required).  Gated behind `NIXIE_SLOW_REGRESSIONS=1`.
use nixie_sat::{Lit, Solver, SolverConfig, SolverResult, Var};

fn load_dimacs(text: &str, config: SolverConfig) -> Solver {
    let mut solver = Solver::with_config(config);
    for line in text.lines() {
        let t = line.trim();
        if t.is_empty() || t.starts_with('c') {
            continue;
        }
        if t.starts_with('p') {
            let declared = t
                .split_whitespace()
                .nth(2)
                .and_then(|s| s.parse().ok())
                .unwrap_or(0);
            for _ in 0..declared {
                solver.new_var();
            }
            continue;
        }
        let clause: Vec<Lit> = t
            .split_whitespace()
            .map(|s| s.parse::<i32>().expect("int"))
            .take_while(|&x| x != 0)
            .map(|x| {
                let idx = x.unsigned_abs() - 1;
                while idx as usize >= solver.num_vars() {
                    solver.new_var();
                }
                if x > 0 {
                    Lit::pos(Var::new(idx))
                } else {
                    Lit::neg(Var::new(idx))
                }
            })
            .collect();
        solver.add_clause(clause);
    }
    solver
}

fn assert_not_unsat(rel: &str, budget: u64) {
    let text = nixie_testcorpus::read_or_skip!(rel);
    let mut on = load_dimacs(&text, SolverConfig::default());
    on.set_otfs(true);
    on.set_max_conflicts(Some(budget));
    let result = on.solve();
    assert_ne!(
        result,
        SolverResult::Unsat,
        "{rel}: OTFS arm claimed UNSAT on a satisfiable instance (trigger-tightness regression)"
    );
    assert!(
        on.stats().otfs_strengthened > 0,
        "{rel}: OTFS never fired inside the budget - the regression no longer exercises the arm"
    );
}

#[test]
fn otfs_not_unsat_on_constraints_17() {
    if std::env::var("NIXIE_SLOW_REGRESSIONS").ok().as_deref() != Some("1") {
        eprintln!("skipping (set NIXIE_SLOW_REGRESSIONS=1 to run)");
        return;
    }
    // False `unsat` at 956 conflicts on the buggy build; baseline
    // model-checked `sat` at 44 381.
    assert_not_unsat(
        "precompile/corpus-sc24f/8e720686372c5037f30b4fc7b1c71d48-constraints_17_0.4_1.sanitized.cnf",
        20_000,
    );
}

#[test]
fn otfs_not_unsat_on_mp1_klieber() {
    if std::env::var("NIXIE_SLOW_REGRESSIONS").ok().as_deref() != Some("1") {
        eprintln!("skipping (set NIXIE_SLOW_REGRESSIONS=1 to run)");
        return;
    }
    assert_not_unsat(
        "precompile/corpus-sc24f/0876c518e5653369e20fb1ee0bb8db40-mp1-klieber2017s-0500-023-t12.cnf",
        20_000,
    );
}

#[test]
fn otfs_not_unsat_on_frb65() {
    if std::env::var("NIXIE_SLOW_REGRESSIONS").ok().as_deref() != Some("1") {
        eprintln!("skipping (set NIXIE_SLOW_REGRESSIONS=1 to run)");
        return;
    }
    assert_not_unsat(
        "precompile/corpus-sc24f/a38affaa741c958fc32769d5fe89b06c-frb65-12-2.used-as.sat04-874.cnf",
        20_000,
    );
}
