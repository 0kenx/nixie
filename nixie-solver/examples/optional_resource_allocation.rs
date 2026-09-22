//! Allocate an eight-GPU cluster to a mandatory service and optional batches.
//! Run with `cargo run -p nixie-solver --example optional_resource_allocation`.
use nixie_core::ast::TermManager;
use nixie_solver::{Solver, SolverConfig, SolverResult};
use nixie_theories::cp::{CpModel, OptionalTask};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let training = tm.mk_var("accept_training", tm.sorts.bool_sort);
    let analytics = tm.mk_var("accept_analytics", tm.sorts.bool_sort);
    // Slots are hours after 18:00. The service uses four GPUs throughout
    // the six-hour window. Each accepted batch needs four GPUs for two hours.
    let mut tasks = Vec::new();
    for (name, presence, starts, duration) in [
        ("service", tm.mk_true(), vec![0], 6),
        ("training", training, vec![0, 1, 2, 3, 4], 2),
        ("analytics", analytics, vec![0, 1, 2, 3, 4], 2),
    ] {
        let entries = starts
            .into_iter()
            .map(|hour| {
                let atom = tm.mk_var(&format!("{name}_starts_at_{hour}"), tm.sorts.bool_sort);
                (hour.into(), atom)
            })
            .collect();
        tasks.push(OptionalTask {
            presence,
            start: cp.variable(entries, &mut tm)?,
            duration: duration.into(),
            demand: 4.into(),
        });
    }
    cp.cumulative_optional(tasks, 8.into(), &mut tm)?;
    let mut solver = Solver::with_config(SolverConfig::default().certified());
    solver.register_cp(cp, &mut tm)?;
    // Admission policy is ordinary Boolean logic. Requiring both batches
    // makes cumulative find nonoverlapping two-hour windows for them.
    solver.assert(training, &mut tm);
    solver.push();
    solver.assert(analytics, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    println!("Both batches fit alongside the mandatory service.");
    solver.pop();
    // Cancellation removes only scheduling usage; analytics retains its
    // declared finite start domain, available to other application constraints.
    solver.assert(tm.mk_not(analytics), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    println!("Training also fits when analytics is cancelled.");
    Ok(())
}
