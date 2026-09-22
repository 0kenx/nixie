//! Reproducible optional cumulative callback and public-solver workload.
//! See bench/cp_perf/README.md for counter collection and experimental controls.
use nixie_core::ast::TermManager;
use nixie_solver::{Solver, SolverConfig, SolverResult};
use nixie_theories::cp::{CpModel, OptionalTask};
use nixie_theories::user_propagator::UserPropagatorManager;
use num_bigint::BigInt;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 7 {
        return Err(
            "usage: cp_scheduling_perf callback|solver|certified FAMILY TASKS WIDTH SEED REPEATS"
                .into(),
        );
    }
    let mode = args[1].as_str();
    let family = args[2].as_str();
    let count: usize = args[3].parse()?;
    let width: usize = args[4].parse()?;
    let seed: usize = args[5].parse()?;
    let repeats: usize = args[6].parse()?;
    if count == 0 || width == 0 || !matches!(mode, "callback" | "solver" | "certified") {
        return Err("invalid workload dimensions or mode".into());
    }
    if !matches!(
        family,
        "unknown" | "present" | "absent" | "shared" | "blocked" | "wide" | "sparse"
    ) {
        return Err("unknown family".into());
    }
    let mut tm = TermManager::new();
    let mut cp = CpModel::new(&tm);
    let shared = tm.mk_var("shared", tm.sorts.bool_sort);
    let offset = if family == "wide" {
        BigInt::from(1) << 140
    } else {
        BigInt::from(0)
    };
    let mut tasks = Vec::new();
    let mut presences = Vec::new();
    for i in 0..count {
        let presence = if family == "shared" {
            shared
        } else {
            tm.mk_var(&format!("p{i}"), tm.sorts.bool_sort)
        };
        presences.push(presence);
        let entries = (0..width)
            .map(|j| {
                // Rotate declared values without changing the time window. Seeds
                // change candidate order; the solver also receives this exact seed.
                let value = (j + seed % width) % width;
                let atom = tm.mk_var(&format!("s{i}_{j}"), tm.sorts.bool_sort);
                (&offset + BigInt::from(value), atom)
            })
            .collect();
        tasks.push(OptionalTask {
            presence,
            start: cp.variable(entries, &mut tm)?,
            duration: if family == "blocked" {
                width.into()
            } else {
                1.into()
            },
            demand: 1.into(),
        });
    }
    if family == "sparse" {
        for i in 0..count * 4 {
            let entries = (0..width)
                .map(|j| {
                    let atom = tm.mk_var(&format!("unrelated{i}_{j}"), tm.sorts.bool_sort);
                    (j.into(), atom)
                })
                .collect();
            cp.variable(entries, &mut tm)?;
        }
    }
    // Blocked jobs exceed capacity individually: every unknown admission must
    // be rejected. Other families have an explicit all-present feasible schedule.
    let capacity = if family == "blocked" { 0 } else { count };
    cp.cumulative_optional(tasks, capacity.into(), &mut tm)?;
    if mode == "callback" {
        let (_, watches, callback) = cp.into_propagator();
        let mut manager = UserPropagatorManager::new();
        manager.register_propagator(callback);
        for watch in watches {
            manager.watch_term(watch);
        }
        for iteration in 0..repeats {
            manager.push();
            if family == "present" || family == "absent" {
                for &presence in &presences {
                    manager.notify_fixed(presence, tm.mk_bool(family == "present"));
                }
            }
            println!("round {iteration} {:?}", manager.final_check());
            for consequence in manager.get_consequences() {
                // Include order and complete explanations, not merely a count.
                println!("{consequence:?}");
            }
            manager.pop(1);
            if manager.has_consequences() {
                return Err("scope leaked consequences".into());
            }
        }
        // Partial callback states deliberately have no SAT verdict.
        println!("unknown");
    } else {
        let mut config = SolverConfig::default();
        if mode == "certified" {
            config = config.certified();
        }
        let mut solver = Solver::with_config(config);
        solver.set_random_seed(seed as u64);
        solver.register_cp(cp, &mut tm)?;
        for iteration in 0..repeats {
            solver.push();
            if family == "present" || family == "absent" {
                for &presence in &presences {
                    let literal = if family == "present" {
                        presence
                    } else {
                        tm.mk_not(presence)
                    };
                    solver.assert(literal, &mut tm);
                }
            }
            let result = solver.check(&mut tm);
            if result != SolverResult::Sat {
                return Err(format!("expected verified SAT, got {result:?}").into());
            }
            let stats = solver.stats();
            println!(
                "round {iteration} {result:?} {} {} {}",
                stats.conflicts, stats.decisions, stats.propagations
            );
            solver.pop();
        }
        println!("sat");
    }
    Ok(())
}
