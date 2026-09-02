#![allow(clippy::unwrap_used)]

//! DIMACS SAT solver with DRAT/LRAT proof logging.
//!
//! Standard SAT-competition-style entry point:
//!
//! ```text
//! oxiz-sat-lrat <input.cnf> [--lrat PATH] [--lrat-binary PATH] [--drat PATH]
//! ```
//!
//! Prints the `s SATISFIABLE` / `s UNSATISFIABLE` / `s UNKNOWN` line. When a
//! proof path is given, the solver streams a DRAT or LRAT proof there (LRAT
//! for `--lrat`/`--lrat-binary`, DRAT for `--drat`). Verify an LRAT proof with:
//!
//! ```text
//! lrat-check <input.cnf> <out.lrat>          # text
//! lrat-check <input.cnf> <decoded.lrat>      # binary: decode .clrat→.lrat first
//! ```
use oxiz_sat::{DimacsParser, Solver, SolverConfig};
use std::env;

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    let cnf = args.iter().find(|a| !a.starts_with('-')).cloned();
    let lrat = flag_value(&args, "--lrat");
    let lrat_binary = flag_value(&args, "--lrat-binary");
    let drat = flag_value(&args, "--drat");
    let bare = args.iter().any(|a| a == "--bare");
    let bve = args.iter().any(|a| a == "--bve");

    let Some(cnf) = cnf else {
        eprintln!(
            "usage: {} <input.cnf> [--lrat PATH] [--lrat-binary PATH] [--drat PATH] [--bare]",
            env::args().next().unwrap_or_else(|| "oxiz-sat-lrat".into())
        );
        std::process::exit(2);
    };

    let mut config = SolverConfig::default();
    // BVE+ELS under an attached proof (proof-compatible elimination): the
    // study arm for LRAT-with-elimination measurement.
    if bve {
        config.enable_bve = true;
    }
    if args.iter().any(|a| a == "--els") {
        config.enable_equiv_substitution = true;
    }
    if bare {
        config.enable_chronological_backtrack = false;
        config.enable_lucky = false;
        config.enable_stabilize = false;
        config.reuse_trail = false;
        config.use_vmtf = false;
    }
    let mut solver = Solver::with_config(config);
    let diag = std::env::var("OXIZ_DIAG").is_ok();

    // Connect the proof tracer *before* parsing so original clauses draw ids
    // 1..K in file order (matching the checker's CNF numbering).
    if let Some(p) = &lrat_binary {
        solver.enable_lrat_proof_binary(p).unwrap();
    } else if let Some(p) = &lrat {
        solver.enable_lrat_proof(p).unwrap();
    } else if let Some(p) = &drat {
        solver.enable_drat_proof(p).unwrap();
    }

    if let Err(e) = DimacsParser::new().parse_file(&cnf, &mut solver) {
        eprintln!("parse error: {e}");
        std::process::exit(2);
    }
    let result = solver.solve();
    solver.disable_proof();

    if diag {
        let st = solver.stats();
        eprintln!(
            "DIAG conflicts={} learned={} deleted={} lucky={}/{} bve_elim={} subst={}",
            st.conflicts,
            st.learned_clauses,
            st.deleted_clauses,
            st.lucky_succeeded,
            st.lucky_tried,
            st.bve_eliminated,
            st.substitutions
        );
    }
    match result {
        oxiz_sat::SolverResult::Sat => println!("s SATISFIABLE"),
        oxiz_sat::SolverResult::Unsat => println!("s UNSATISFIABLE"),
        oxiz_sat::SolverResult::Unknown => println!("s UNKNOWN"),
    }
}

fn flag_value(args: &[String], flag: &str) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == flag {
            return it.next().cloned();
        }
        if let Some(v) = a.strip_prefix(&format!("{flag}=")) {
            return Some(v.to_string());
        }
    }
    None
}
