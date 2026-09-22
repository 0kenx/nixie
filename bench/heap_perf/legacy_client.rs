//! Compile the identical workload interpreter against the unmodified baseline.
#[path = "../../nixie-solver/examples/heap_perf_next_driver/mod.rs"]
mod driver;

use nixie_solver::heap::HeapSolver;
use std::error::Error;

fn configure(mode: &str, _: &mut HeapSolver) -> Result<(), Box<dyn Error>> {
    if mode != "baseline" { return Err("baseline client requires baseline mode".into()); }
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    driver::run(configure, |_| {})
}
