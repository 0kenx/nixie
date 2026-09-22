//! Controlled benchmark client for the four exact heap optimizations.
mod heap_perf_next_driver;

use nixie_solver::heap::{HeapOptimizations, HeapSolver};
use std::error::Error;

fn configure(mode: &str, solver: &mut HeapSolver) -> Result<(), Box<dyn Error>> {
    let mut options = HeapOptimizations {
        anchor_coverage: true,
        equality_propagation: true,
        cache_templates: true,
        lazy_boolean: true,
    };
    match mode {
        "all" => {}
        "no_coverage" => options.anchor_coverage = false,
        "no_equalities" => options.equality_propagation = false,
        "no_cache" => options.cache_templates = false,
        "eager" => options.lazy_boolean = false,
        "none" => options = HeapOptimizations::NONE,
        _ => return Err("unsupported optimization arm".into()),
    }
    solver.set_optimizations(options)?;
    Ok(())
}

fn diagnostics(solver: &HeapSolver) {
    let stats = solver.statistics();
    println!(
        "optimization {} {} {} {}",
        stats.template_builds, stats.template_hits, stats.integer_rewrites, stats.refinement_rounds
    );
}

fn main() -> Result<(), Box<dyn Error>> {
    heap_perf_next_driver::run(configure, diagnostics)
}
