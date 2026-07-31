#![allow(clippy::unwrap_used)]

//! Solve a CNF and, on SAT, verify the returned model satisfies EVERY original
//! clause. Catches substitution (or any inprocessing) bugs that produce an
//! invalid model. Usage: validate_model <file.cnf>  (EQUIV env honored).
use oxiz_sat::{DimacsParser, Lit, Solver, SolverConfig};

fn main() {
    let path = std::env::args().nth(1).unwrap();
    let mut cfg = SolverConfig::default();
    cfg.enable_equiv_substitution = std::env::var("EQUIV").map_or(true, |v| v != "0");
    let mut p = DimacsParser::new();
    let mut s = Solver::with_config(cfg);
    if let Err(e) = p.parse_file(&path, &mut s) {
        eprintln!("parse error: {e}");
        std::process::exit(2);
    }
    // Snapshot the original clauses BEFORE solving (substitution rewrites them).
    let (_nv, original) = s.export_problem_dimacs();

    let r = s.solve();
    match r {
        oxiz_sat::SolverResult::Unsat => println!("UNSAT (no model to validate)"),
        oxiz_sat::SolverResult::Unknown => println!("UNKNOWN"),
        oxiz_sat::SolverResult::Sat => {
            let model = s.model();
            let mut bad = 0usize;
            let mut checked = 0usize;
            for clause in &original {
                if clause.is_empty() {
                    continue;
                }
                checked += 1;
                let sat = clause.iter().any(|&v| {
                    let vi = v.unsigned_abs() as usize - 1;
                    let val = model.get(vi).copied().unwrap_or(oxiz_sat::LBool::Undef);
                    if v > 0 { val.is_true() } else { val.is_false() }
                });
                if !sat {
                    bad += 1;
                    if bad <= 3 {
                        eprintln!("UNSATISFIED clause: {:?}", clause);
                    }
                }
            }
            let _ = Lit::pos(oxiz_sat::Var::new(0));
            if bad == 0 {
                println!("SAT model VALID ({checked} clauses satisfied)");
            } else {
                println!("SAT model INVALID: {bad}/{checked} clauses unsatisfied");
                std::process::exit(1);
            }
        }
    }
}
