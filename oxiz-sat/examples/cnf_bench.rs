//! In-process CNF benchmark: solve every `.cnf` under a directory (recursively)
//! and report total/mean SOLVE time (parsing timed separately), so per-process
//! startup does not pollute the measurement. Also reports aggregate conflicts.
//!
//! ```text
//! cargo run --release --example cnf_bench -- /path/to/cnf/dir
//! ```

use oxiz_sat::{DimacsParser, Solver, SolverResult};
use std::env;
use std::path::{Path, PathBuf};
use std::time::Instant;

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = std::fs::read_dir(dir) {
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().and_then(|s| s.to_str()) == Some("cnf") {
                out.push(p);
            }
        }
    }
}

fn main() {
    let root = env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: cnf_bench <dir>");
        std::process::exit(2);
    });

    let mut files = Vec::new();
    walk(Path::new(&root), &mut files);
    files.sort();

    let mut total_solve_ns: u128 = 0;
    let mut total_parse_ns: u128 = 0;
    let mut conflicts: u64 = 0;
    let mut decisions: u64 = 0;
    let mut propagations: u64 = 0;
    let mut n = 0usize;
    let mut sat = 0usize;
    let mut unsat = 0usize;

    for f in &files {
        let mut parser = DimacsParser::new();
        let mut solver = Solver::new();

        let t0 = Instant::now();
        if let Err(e) = parser.parse_file(f, &mut solver) {
            eprintln!("skip {}: {e}", f.display());
            continue;
        }
        total_parse_ns += t0.elapsed().as_nanos();

        let t1 = Instant::now();
        let r = solver.solve();
        total_solve_ns += t1.elapsed().as_nanos();

        let s = solver.stats();
        conflicts += s.conflicts;
        decisions += s.decisions;
        propagations += s.propagations;

        match r {
            SolverResult::Sat => sat += 1,
            SolverResult::Unsat => unsat += 1,
            SolverResult::Unknown => {}
        }
        n += 1;
    }

    let solve_ms = total_solve_ns as f64 / 1e6;
    let parse_ms = total_parse_ns as f64 / 1e6;
    eprintln!(
        "files={n} sat={sat} unsat={unsat} | parse={parse_ms:.1}ms solve={solve_ms:.1}ms \
         (mean {:.3}ms/file) | conflicts={conflicts} decisions={decisions} propagations={propagations} \
         ({:.2}M props/s)",
        solve_ms / n.max(1) as f64,
        propagations as f64 / (solve_ms / 1000.0).max(1e-9) / 1e6
    );
}
