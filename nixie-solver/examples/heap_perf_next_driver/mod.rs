//! Shared workload interpreter, restricted to the heap API available at cb50c87e.
//! Both baseline and candidate clients compile this identical file.

use nixie_solver::heap::{Formula, HeapError, HeapSolver, Heaplet};
use nixie_solver::{SolverConfig, SolverResult};
use std::error::Error;

#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn next<T: std::str::FromStr>(
    words: &mut std::str::SplitWhitespace<'_>,
) -> Result<T, Box<dyn Error>> {
    words
        .next()
        .ok_or("missing token")?
        .parse()
        .map_err(|_| "invalid token".into())
}

fn report(
    solver: &mut HeapSolver,
    index: usize,
    diagnostics: fn(&HeapSolver),
) -> Result<(), Box<dyn Error>> {
    let result = solver.check();
    if result == SolverResult::Sat {
        solver.validate_model(solver.model().ok_or(HeapError("missing heap model"))?)?;
    }
    println!("begin {index}");
    println!(
        "{}",
        match result {
            SolverResult::Sat => "sat",
            SolverResult::Unsat => "unsat",
            SolverResult::Unknown => "unknown",
        }
    );
    let stats = solver.statistics();
    println!(
        "sizes {} {} {}",
        stats.heaplets, stats.original_nodes, stats.backend_terms
    );
    println!("definitions {}", stats.definition_assertions);
    println!("comparisons {}", stats.heap_comparisons);
    println!(
        "search {} {} {}",
        stats.conflicts, stats.decisions, stats.propagations
    );
    diagnostics(solver);
    if let Some(reason) = solver.reason_unknown() {
        println!("reason {reason}");
    }
    if let Some(model) = solver.model() {
        for (name, value) in &model.integers {
            println!("var {name} {value}");
        }
        for (location, value) in &model.cells {
            println!("cell {location} {value}");
        }
    }
    println!("end {index}");
    Ok(())
}

type Configure = fn(&str, &mut HeapSolver) -> Result<(), Box<dyn Error>>;

pub fn run(configure: Configure, diagnostics: fn(&HeapSolver)) -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 4 {
        return Err("usage: heap_perf_next CASE SEED MODE".into());
    }
    let seed: u64 = args[2].parse()?;
    let input = std::fs::read_to_string(&args[1])?;
    let mut words = input.split_whitespace();
    if words.next() != Some("vars") {
        return Err("expected vars".into());
    }
    let count: usize = next(&mut words)?;
    let mut solver = HeapSolver::with_config(SolverConfig {
        max_conflicts: 10_000,
        max_decisions: 100_000,
        timeout_ms: 0,
        ..SolverConfig::default()
    });
    configure(&args[3], &mut solver)?;
    solver.set_random_seed(seed);
    let mut terms: Vec<_> = (0..count)
        .map(|i| solver.int_var(&format!("x{i}")))
        .collect();
    let mut formulas: Vec<Formula> = Vec::new();
    let mut checks = 0;
    while let Some(op) = words.next() {
        match op {
            "offset" => {
                let base: usize = next(&mut words)?;
                let delta: i64 = next(&mut words)?;
                let delta = solver.integer(delta);
                terms.push(solver.add(terms.get(base).ok_or("invalid term")?, &delta)?);
            }
            "heap" | "heapv" => {
                let count: usize = next(&mut words)?;
                let mut heap = Heaplet::emp();
                for _ in 0..count {
                    let location: usize = next(&mut words)?;
                    let value = if op == "heapv" {
                        let value: usize = next(&mut words)?;
                        terms.get(value).ok_or("invalid value term")?.clone()
                    } else {
                        solver.integer(next::<i64>(&mut words)?)
                    };
                    heap = heap.star(Heaplet::points_to(
                        terms.get(location).ok_or("invalid location")?,
                        &value,
                    ));
                }
                formulas.push(solver.reify(heap)?);
            }
            "bound" => {
                let term: usize = next(&mut words)?;
                let lower = solver.integer(next::<i64>(&mut words)?);
                let upper = solver.integer(next::<i64>(&mut words)?);
                let term = terms.get(term).ok_or("invalid bound term")?;
                let lower = solver.le(&lower, term)?;
                let upper = solver.le(term, &upper)?;
                solver.assert(&lower)?;
                solver.assert(&upper)?;
            }
            "eq" => {
                let left: usize = next(&mut words)?;
                let right: usize = next(&mut words)?;
                let equality = solver.eq(
                    terms.get(left).ok_or("invalid equality")?,
                    terms.get(right).ok_or("invalid equality")?,
                )?;
                solver.assert(&equality)?;
            }
            "not" => {
                let index: usize = next(&mut words)?;
                formulas.push(solver.not(formulas.get(index).ok_or("invalid negation")?)?);
            }
            "or" | "and" => {
                let count: usize = next(&mut words)?;
                let mut children = Vec::with_capacity(count);
                for _ in 0..count {
                    let index: usize = next(&mut words)?;
                    children.push(formulas.get(index).ok_or("invalid connective")?.clone());
                }
                formulas.push(if op == "or" {
                    solver.or(&children)?
                } else {
                    solver.and(&children)?
                });
            }
            "assert" => {
                let index: usize = next(&mut words)?;
                let polarity: u8 = next(&mut words)?;
                let formula = formulas.get(index).ok_or("invalid assertion")?;
                match polarity {
                    1 => solver.assert(formula)?,
                    0 => {
                        let negative = solver.not(formula)?;
                        solver.assert(&negative)?;
                    }
                    _ => return Err("invalid polarity".into()),
                }
            }
            "push" => solver.push(),
            "pop" => solver.pop()?,
            "check" => {
                report(&mut solver, checks, diagnostics)?;
                checks += 1;
            }
            _ => return Err("unsupported workload command".into()),
        }
    }
    if checks == 0 {
        report(&mut solver, 0, diagnostics)?;
    }
    Ok(())
}
