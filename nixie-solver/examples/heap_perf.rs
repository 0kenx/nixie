//! Driver for `bench/heap_perf/run.py`; input format and protocol are in its README.
use nixie_solver::heap::{HeapError, HeapSolver, Heaplet};
use nixie_solver::{SolverConfig, SolverResult};
use std::error::Error;
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};

#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

struct Counter {
    phase: String,
    control: Option<(File, File)>,
}

impl Counter {
    fn new(phase: String) -> Result<Self, Box<dyn Error>> {
        let control = match (
            std::env::var("HEAP_PERF_CONTROL"),
            std::env::var("HEAP_PERF_ACK"),
        ) {
            (Ok(control), Ok(ack)) => Some((
                OpenOptions::new().write(true).open(control)?,
                File::open(ack)?,
            )),
            (Err(_), Err(_)) if phase == "total" => None,
            _ => return Err("phase measurement requires both perf control FIFOs".into()),
        };
        Ok(Self { phase, control })
    }

    fn command(&mut self, phase: &str, command: &str) -> Result<(), Box<dyn Error>> {
        if self.phase == phase
            && let Some((control, ack)) = &mut self.control
        {
            writeln!(control, "{command}")?;
            control.flush()?;
            // perf sends the terminating NUL as part of its FIFO protocol.
            let mut message = [0; 5];
            ack.read_exact(&mut message)?;
            if &message != b"ack\n\0" {
                return Err("invalid perf acknowledgement".into());
            }
        }
        Ok(())
    }
}

fn next<T: std::str::FromStr>(
    words: &mut std::str::SplitWhitespace<'_>,
) -> Result<T, Box<dyn Error>> {
    words
        .next()
        .ok_or("missing input token")?
        .parse()
        .map_err(|_| "invalid input token".into())
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 4 {
        return Err("usage: heap_perf CASE SEED total|encode|solve|validate".into());
    }
    let seed: u64 = args[2].parse()?;
    if !["total", "encode", "solve", "validate"].contains(&args[3].as_str()) {
        return Err("invalid phase".into());
    }
    let mut counter = Counter::new(args[3].clone())?;
    counter.command("encode", "enable")?;
    let input = std::fs::read_to_string(&args[1])?;
    let mut words = input.split_whitespace();
    if words.next() != Some("vars") {
        return Err("case must start with vars".into());
    }
    let count: usize = next(&mut words)?;
    let mut solver = HeapSolver::with_config(SolverConfig {
        max_conflicts: 10_000,
        max_decisions: 100_000,
        timeout_ms: 0,
        ..SolverConfig::default()
    });
    solver.set_random_seed(seed);
    match std::env::var("HEAP_PERF_UNFOLDED") {
        Ok(value) if value == "1" => solver.set_definition_simplification(false)?,
        Ok(value) if value == "0" => {}
        Err(std::env::VarError::NotPresent) => {}
        _ => return Err("HEAP_PERF_UNFOLDED must be 0 or 1".into()),
    }
    let vars: Vec<_> = (0..count)
        .map(|i| solver.int_var(&format!("x{i}")))
        .collect();
    let mut atoms = Vec::new();
    while let Some(op) = words.next() {
        match op {
            "heap" => {
                let cells: usize = next(&mut words)?;
                let mut heaplet = Heaplet::emp();
                for _ in 0..cells {
                    let loc: usize = next(&mut words)?;
                    let val: i64 = next(&mut words)?;
                    let loc = vars.get(loc).ok_or("invalid location variable")?;
                    let val = solver.integer(val);
                    heaplet = heaplet.star(Heaplet::points_to(loc, &val));
                }
                atoms.push(solver.reify(heaplet)?);
            }
            "bound" => {
                let var: usize = next(&mut words)?;
                let lo: i64 = next(&mut words)?;
                let hi: i64 = next(&mut words)?;
                let var = vars.get(var).ok_or("invalid bound variable")?;
                let lo = solver.integer(lo);
                let hi = solver.integer(hi);
                let lower = solver.le(&lo, var)?;
                let upper = solver.le(var, &hi)?;
                solver.assert(&lower)?;
                solver.assert(&upper)?;
            }
            "eq" => {
                let a: usize = next(&mut words)?;
                let b: usize = next(&mut words)?;
                let eq = solver.eq(
                    vars.get(a).ok_or("invalid equality variable")?,
                    vars.get(b).ok_or("invalid equality variable")?,
                )?;
                solver.assert(&eq)?;
            }
            "assert" => {
                let atom: usize = next(&mut words)?;
                let polarity: u8 = next(&mut words)?;
                let atom = atoms.get(atom).ok_or("invalid heap atom")?;
                match polarity {
                    1 => solver.assert(atom)?,
                    0 => {
                        let negated = solver.not(atom)?;
                        solver.assert(&negated)?;
                    }
                    _ => return Err("invalid heap polarity".into()),
                }
            }
            _ => return Err("unrecognized case instruction".into()),
        }
    }
    let encoded = solver.statistics();
    counter.command("encode", "disable")?;
    counter.command("solve", "enable")?;
    let verdict = solver.check();
    counter.command("solve", "disable")?;
    counter.command("validate", "enable")?;
    if verdict == SolverResult::Sat {
        solver.validate_model(solver.model().ok_or(HeapError("missing heap model"))?)?;
    }
    counter.command("validate", "disable")?;
    let stats = solver.statistics();

    println!(
        "{}",
        match verdict {
            SolverResult::Sat => "sat",
            SolverResult::Unsat => "unsat",
            SolverResult::Unknown => "unknown",
        }
    );
    println!(
        "definitions {} {}",
        stats.definition_assertions, stats.backend_terms
    );
    if let Some(reason) = solver.reason_unknown() {
        println!("reason {reason}");
    }
    println!(
        "sizes {} {} {}",
        encoded.heaplets, encoded.original_nodes, encoded.backend_terms
    );
    println!(
        "search {} {} {}",
        stats.conflicts, stats.decisions, stats.propagations
    );
    if let Some(model) = solver.model() {
        for (name, value) in &model.integers {
            println!("var {name} {value}");
        }
        for (loc, value) in &model.cells {
            println!("cell {loc} {value}");
        }
    }
    Ok(())
}
