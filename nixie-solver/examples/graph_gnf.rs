//! GNF (graph DIMACS) driver — differential-testing harness against MonoSAT.
//!
//! Reads the unweighted directed subset of MonoSAT's GNF format and solves
//! it with the integrated graph constraints (`nixie_theories::graph`):
//!
//! - `p cnf <vars> <clauses>` header,
//! - `digraph [int] <nodes> <edges> <id>` declarations,
//! - `edge <gid> <from> <to> <var> [`weight`]` (weights ignored, must be int),
//! - `reach <gid> <from> <to> <var>` for `from != to` (MonoSAT's reflexive
//!   semantics coincide with Nixie's strict semantics exactly when
//!   `from != to`; self-pair reach is rejected),
//! - `acyclic <gid> <var>`,
//! - DIMACS clauses over the variables (each theory element owns a unique
//!   variable, per GNF rules; the campaign maps each to its edge/atom term).
//!
//! Anything outside this subset is rejected with exit code 2 so a campaign
//! fails loudly rather than comparing mismatched semantics. Prints the
//! standard `s SATISFIABLE` / `s UNSATISFIABLE` line for diffing.
//!
//! Usage: `cargo run -p nixie-solver --example graph_gnf -- file.gnf`

use std::collections::HashMap;
use std::env;
use std::fs;

use nixie_core::ast::TermManager;
use nixie_solver::{Solver, SolverResult};
use nixie_theories::graph::{GraphModel, VertexId};

/// Match the production CLI's allocator (see `nixie-cli/src/main.rs`):
/// without this, throughput examples measure glibc malloc instead of the
/// solver.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// A parsed GNF instance over the supported subset.
struct Gnf {
    clauses: Vec<Vec<i64>>,
    /// (graph id, from, to, var)
    edges: Vec<(u64, u64, u64, i64)>,
    /// (graph id, from, to, var), from != to
    reach: Vec<(u64, u64, u64, i64)>,
    /// (graph id, var)
    acyclic: Vec<(u64, i64)>,
    /// (graph id, node count)
    graphs: Vec<(u64, u64)>,
}

fn parse_gnf(text: &str) -> Result<Gnf, String> {
    let mut gnf = Gnf {
        clauses: Vec::new(),
        edges: Vec::new(),
        reach: Vec::new(),
        acyclic: Vec::new(),
        graphs: Vec::new(),
    };
    for (lineno, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        let tokens: Vec<&str> = line.split_whitespace().collect();
        let malformed = || format!("line {}: malformed GNF: {line}", lineno + 1);
        match tokens[0] {
            "p" => {
                if tokens.len() != 4 || tokens[1] != "cnf" {
                    return Err(malformed());
                }
            }
            "digraph" => {
                // `digraph [weight] nodes edges id`; the weight type is
                // optional and must be `int` when present.
                let body = &tokens[1..];
                let nums_tokens: &[&str] = if body.len() == 4 {
                    if body[0] != "int" {
                        return Err(format!(
                            "line {}: only unweighted / int graphs are supported",
                            lineno + 1
                        ));
                    }
                    &body[1..]
                } else if body.len() == 3 {
                    body
                } else {
                    return Err(malformed());
                };
                let nums: Vec<u64> = nums_tokens
                    .iter()
                    .map(|t| t.parse::<u64>().map_err(|_| malformed()))
                    .collect::<Result<_, _>>()?;
                gnf.graphs.push((nums[2], nums[0]));
            }
            "edge" => {
                if tokens.len() != 5 && tokens.len() != 6 {
                    return Err(malformed());
                }
                let gid: u64 = tokens[1].parse().map_err(|_| malformed())?;
                let from: u64 = tokens[2].parse().map_err(|_| malformed())?;
                let to: u64 = tokens[3].parse().map_err(|_| malformed())?;
                let var: i64 = tokens[4].parse().map_err(|_| malformed())?;
                if var <= 0 {
                    return Err(format!("line {}: edge vars must be positive", lineno + 1));
                }
                gnf.edges.push((gid, from, to, var));
            }
            "reach" => {
                if tokens.len() != 5 {
                    return Err(malformed());
                }
                let gid: u64 = tokens[1].parse().map_err(|_| malformed())?;
                let from: u64 = tokens[2].parse().map_err(|_| malformed())?;
                let to: u64 = tokens[3].parse().map_err(|_| malformed())?;
                let var: i64 = tokens[4].parse().map_err(|_| malformed())?;
                if var <= 0 {
                    return Err(format!("line {}: reach vars must be positive", lineno + 1));
                }
                if from == to {
                    return Err(format!(
                        "line {}: self-pair reach has different semantics in MonoSAT (reflexive) and Nixie (strict); excluded from the campaign",
                        lineno + 1
                    ));
                }
                gnf.reach.push((gid, from, to, var));
            }
            "acyclic" => {
                if tokens.len() != 3 {
                    return Err(malformed());
                }
                let gid: u64 = tokens[1].parse().map_err(|_| malformed())?;
                let var: i64 = tokens[2].parse().map_err(|_| malformed())?;
                if var <= 0 {
                    return Err(format!(
                        "line {}: acyclic vars must be positive",
                        lineno + 1
                    ));
                }
                gnf.acyclic.push((gid, var));
            }
            _ => {
                // DIMACS clause.
                let mut clause: Vec<i64> = Vec::new();
                for t in &tokens {
                    let lit: i64 = t.parse().map_err(|_| malformed())?;
                    if lit == 0 {
                        break;
                    }
                    clause.push(lit);
                }
                if clause.is_empty() {
                    return Err(malformed());
                }
                gnf.clauses.push(clause);
            }
        }
    }
    // Every theory element must own a distinct variable (GNF rule), so the
    // mapping below is unambiguous.
    let mut seen: Vec<i64> = gnf
        .edges
        .iter()
        .map(|e| e.3)
        .chain(gnf.reach.iter().map(|r| r.3))
        .chain(gnf.acyclic.iter().map(|a| a.1))
        .collect();
    seen.sort_unstable();
    seen.dedup();
    let total = gnf.edges.len() + gnf.reach.len() + gnf.acyclic.len();
    if seen.len() != total {
        return Err("theory elements must own distinct variables".to_string());
    }
    Ok(gnf)
}

/// Terms for clause-only variables are minted up front so clause building
/// never needs the manager mutably at assert time.
fn auxiliary_terms(
    clauses: &[Vec<i64>],
    owned: &HashMap<i64, nixie_core::TermId>,
    tm: &mut TermManager,
) -> HashMap<i64, nixie_core::TermId> {
    let mut all: HashMap<i64, nixie_core::TermId> = HashMap::new();
    for clause in clauses {
        for &lit in clause {
            let var = lit.abs();
            if !owned.contains_key(&var) && !all.contains_key(&var) {
                let term = tm.mk_var(&format!("gnf_var_{var}"), tm.sorts.bool_sort);
                all.insert(var, term);
            }
        }
    }
    all
}

fn main() {
    let path = match env::args().nth(1) {
        Some(p) => p,
        None => {
            eprintln!("usage: graph_gnf <file.gnf>");
            std::process::exit(2);
        }
    };
    let text = match fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("error reading {path}: {e}");
            std::process::exit(2);
        }
    };
    let t0 = std::time::Instant::now();
    let gnf = match parse_gnf(&text) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("parse error: {e}");
            std::process::exit(2);
        }
    };
    let t_parse = t0.elapsed();

    // Presize the term manager: the manager's tables otherwise grow
    // through repeated rehash/copy cycles while the driver mints the edge
    // atoms, their negations, the or-clauses, and the auxiliary atoms
    // (table-growth copies profiled as a quarter of a pure-Boolean goal's
    // assertion pipeline; the hint changes nothing semantically).
    let clause_literals: usize = gnf.clauses.iter().map(|c| c.len()).sum();
    let expected_terms = (gnf.edges.len()
        + gnf.reach.len()
        + gnf.acyclic.len()
        + clause_literals
        + gnf.clauses.len())
    .saturating_mul(2);
    let mut tm = TermManager::with_capacity(expected_terms);
    let mut model = GraphModel::new(&tm);
    // GNF graph ids are arbitrary non-negative integers; remap them to
    // consecutive GraphHandles in declaration order (`new_graph` hands out
    // exactly those indices).
    let mut handle_of: HashMap<u64, nixie_theories::graph::GraphHandle> = HashMap::new();
    for (i, &(gid, _)) in gnf.graphs.iter().enumerate() {
        let handle = model.new_graph();
        debug_assert_eq!(handle.index(), i);
        handle_of.insert(gid, handle);
    }
    // graph id -> Vec<VertexId>
    let mut vertices: HashMap<u64, Vec<VertexId>> = HashMap::new();
    for &(gid, nodes) in &gnf.graphs {
        let handle = match handle_of.get(&gid) {
            Some(&h) => h,
            None => {
                eprintln!("graph {gid} lost its handle");
                std::process::exit(2);
            }
        };
        let mut vs = Vec::new();
        for _ in 0..nodes {
            match model.add_vertex(handle) {
                Ok(v) => vs.push(v),
                Err(e) => {
                    eprintln!("construction error: {e}");
                    std::process::exit(2);
                }
            }
        }
        vertices.insert(gid, vs);
    }

    // var -> term
    let mut terms: HashMap<i64, nixie_core::TermId> = HashMap::new();
    for &(gid, from, to, var) in &gnf.edges {
        let handle = match handle_of.get(&gid) {
            Some(&h) => h,
            None => {
                eprintln!("edge references undeclared graph {gid}");
                std::process::exit(2);
            }
        };
        let vs = match vertices.get(&gid) {
            Some(v) => v,
            None => {
                eprintln!("edge references undeclared graph {gid}");
                std::process::exit(2);
            }
        };
        let (u, v) = match (vs.get(from as usize), vs.get(to as usize)) {
            (Some(&u), Some(&v)) => (u, v),
            _ => {
                eprintln!("edge {from}->{to} out of range for graph {gid}");
                std::process::exit(2);
            }
        };
        let atom = tm.mk_var(&format!("gnf_edge_{var}"), tm.sorts.bool_sort);
        match model.add_edge(handle, u, v, atom, &mut tm) {
            Ok(t) => {
                terms.insert(var, t);
            }
            Err(e) => {
                eprintln!("construction error: {e}");
                std::process::exit(2);
            }
        }
    }
    for &(gid, from, to, var) in &gnf.reach {
        let handle = match handle_of.get(&gid) {
            Some(&h) => h,
            None => {
                eprintln!("reach references undeclared graph {gid}");
                std::process::exit(2);
            }
        };
        let vs = match vertices.get(&gid) {
            Some(v) => v,
            None => {
                eprintln!("reach references undeclared graph {gid}");
                std::process::exit(2);
            }
        };
        let (u, v) = match (vs.get(from as usize), vs.get(to as usize)) {
            (Some(&u), Some(&v)) => (u, v),
            _ => {
                eprintln!("reach {from}->{to} out of range for graph {gid}");
                std::process::exit(2);
            }
        };
        match model.reach(handle, u, v, &mut tm) {
            Ok(t) => {
                terms.insert(var, t);
            }
            Err(e) => {
                eprintln!("construction error: {e}");
                std::process::exit(2);
            }
        }
    }
    for &(gid, var) in &gnf.acyclic {
        let handle = match handle_of.get(&gid) {
            Some(&h) => h,
            None => {
                eprintln!("acyclic references undeclared graph {gid}");
                std::process::exit(2);
            }
        };
        match model.acyclic(handle, &mut tm) {
            Ok(t) => {
                terms.insert(var, t);
            }
            Err(e) => {
                eprintln!("construction error: {e}");
                std::process::exit(2);
            }
        }
    }

    let auxiliary = auxiliary_terms(&gnf.clauses, &terms, &mut tm);
    let t1 = std::time::Instant::now();
    let mut solver = Solver::new();
    if let Err(e) = solver.register_graph(model, &mut tm) {
        eprintln!("registration error: {e}");
        std::process::exit(2);
    }
    let t_register = t1.elapsed();
    for clause in &gnf.clauses {
        let mut lits: Vec<nixie_core::TermId> = Vec::new();
        for &lit in clause {
            let var = lit.abs();
            let term = match terms.get(&var).or_else(|| auxiliary.get(&var)) {
                Some(&t) => t,
                None => {
                    eprintln!("clause references unowned variable {var}");
                    std::process::exit(2);
                }
            };
            let literal = if lit < 0 { tm.mk_not(term) } else { term };
            lits.push(literal);
        }
        let clause_term = tm.mk_or(lits);
        solver.assert(clause_term, &mut tm);
    }
    let t_assert = t1.elapsed() - t_register;
    let t2 = std::time::Instant::now();
    let result = solver.check(&mut tm);
    if std::env::var_os("TIMING").is_some() {
        eprintln!(
            "c timing parse={:?} register={:?} assert={:?} check={:?}",
            t_parse,
            t_register,
            t_assert,
            t2.elapsed()
        );
    }
    match result {
        SolverResult::Sat => println!("s SATISFIABLE"),
        SolverResult::Unsat => println!("s UNSATISFIABLE"),
        SolverResult::Unknown => {
            println!("s UNKNOWN");
            std::process::exit(1);
        }
    }
    // STATS=1 prints the deterministic solver counters on stderr so A/B
    // builds can be verified bit-identical (the propagator optimizations
    // must be semantics-inert: same propagations, same conflicts).
    if std::env::var_os("STATS").is_some() {
        let stats = solver.stats();
        eprintln!(
            "c conflicts={} decisions={} propagations={}",
            stats.conflicts, stats.decisions, stats.propagations
        );
    }
}
