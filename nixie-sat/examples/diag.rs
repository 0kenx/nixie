#![allow(clippy::unwrap_used)]

//! Diagnostic: solve one CNF and dump detailed search stats.
use nixie_sat::{DimacsParser, Solver, SolverConfig};

fn main() {
    let path = std::env::args().nth(1).unwrap();
    let cfg = if std::env::var("NOSTABLE").is_ok() {
        SolverConfig {
            enable_stabilize: false,
            ..SolverConfig::default()
        }
    } else {
        SolverConfig::default()
    };
    let mut p = DimacsParser::new();
    let mut s = Solver::with_config(cfg);
    p.parse_file(&path, &mut s).unwrap();
    let t0 = std::time::Instant::now();
    let r = s.solve();
    let el = t0.elapsed();
    let st = s.stats();
    println!(
        "result={:?} time={:.3}s vars={} conflicts={} decisions={} props={} restarts={}\n\
         learned={} unit={} binary={} deleted={} alive={}\n\
         total_lbd={} avg_lbd={:.3} minimizations={} lits_removed={}\n\
         chrono_bt={} nonchrono_bt={}",
        r,
        el.as_secs_f64(),
        s.num_vars(),
        st.conflicts,
        st.decisions,
        st.propagations,
        st.restarts,
        st.learned_clauses,
        st.unit_clauses,
        st.binary_clauses,
        st.deleted_clauses,
        st.learned_clauses.saturating_sub(st.deleted_clauses),
        st.total_lbd,
        st.avg_lbd(),
        st.minimizations,
        st.literals_removed,
        st.chrono_backtracks,
        st.non_chrono_backtracks,
    );
}
