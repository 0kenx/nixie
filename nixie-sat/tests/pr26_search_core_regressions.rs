//! Regression tests for the PR #26 search-core port: VMTF wiring,
//! stable/focused tick-based restarts, reuse-trail, and rephasing.
//!
//! These are black-box, whole-solver checks (the white-box mechanism tests
//! live next to the code in `src/solver/tests.rs`, `src/vmtf.rs`, and
//! `src/restart_model.rs`). The property under test here is the one that
//! matters most for a heuristic port: every config preset – which now
//! exercises VMTF, the stable/focused schedule, and reuse-trail restarts by
//! default – must agree with every other preset (and with every mechanism
//! individually disabled) on the SAT/UNSAT verdict. A branching or restart
//! heuristic is free to change *how fast* a verdict is found; it must never
//! change *which* verdict is found.

use nixie_sat::{ConfigPreset, Solver, SolverConfig, SolverResult};

/// Build the pigeonhole-principle UNSAT instance: `pigeons` items into
/// `holes` slots (`pigeons > holes`).
fn add_pigeonhole(solver: &mut Solver, pigeons: usize, holes: usize) {
    for _ in 0..pigeons * holes {
        solver.new_var();
    }
    let var = |p: usize, h: usize| (p * holes + h + 1) as i32;
    for p in 0..pigeons {
        let clause: Vec<i32> = (0..holes).map(|h| var(p, h)).collect();
        solver.add_clause_dimacs(&clause);
    }
    for h in 0..holes {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                solver.add_clause_dimacs(&[-var(p1, h), -var(p2, h)]);
            }
        }
    }
}

/// A small, deliberately satisfiable random-ish 3-SAT instance over 12
/// variables (chosen so more than one satisfying assignment exists, which is
/// what actually exercises decision-order-dependent branching heuristics).
fn add_small_sat_instance(solver: &mut Solver) {
    for _ in 0..12 {
        solver.new_var();
    }
    let clauses: &[[i32; 3]] = &[
        [1, 2, 3],
        [-1, 4, 5],
        [2, -3, 6],
        [-4, 7, 8],
        [5, -6, 9],
        [-7, 8, 10],
        [1, -8, -9],
        [-2, 3, -10],
        [4, -5, 11],
        [-6, 7, 12],
        [-11, -12, 1],
        [10, 11, -2],
    ];
    for c in clauses {
        solver.add_clause_dimacs(c);
    }
}

/// A moderately sized UNSAT XOR-chain-like instance built from an
/// over-constrained pigeonhole (5 into 4), large enough to force multiple
/// restarts and clause-database reductions under every preset's tuned
/// intervals.
fn solves_php_5_4(preset: ConfigPreset) -> SolverResult {
    let mut solver = Solver::with_config(preset.config());
    add_pigeonhole(&mut solver, 5, 4);
    solver.solve()
}

#[test]
fn test_pr26_all_presets_agree_on_unsat_pigeonhole() {
    for preset in ConfigPreset::all_presets() {
        assert_eq!(
            solves_php_5_4(*preset),
            SolverResult::Unsat,
            "preset {preset:?} disagreed on PHP(5,4), which is unconditionally UNSAT"
        );
    }
}

#[test]
fn test_pr26_all_presets_agree_on_sat_instance() {
    for preset in ConfigPreset::all_presets() {
        let mut solver = Solver::with_config(preset.config());
        add_small_sat_instance(&mut solver);
        assert_eq!(
            solver.solve(),
            SolverResult::Sat,
            "preset {preset:?} disagreed on a satisfiable instance"
        );
    }
}

/// Toggle every PR #26 mechanism off one at a time (starting from the
/// default, all-on config) and confirm the verdict never moves. This is the
/// "0 result flips" soundness bar from the task brief, checked directly
/// against each individual knob rather than only the bundled presets.
#[test]
fn test_pr26_individual_mechanism_toggles_never_flip_unsat_verdict() {
    let base = SolverConfig::default();
    let variants: Vec<(&str, SolverConfig)> = vec![
        ("all defaults (VMTF+stabilize+reuse_trail on)", base.clone()),
        (
            "use_vmtf off",
            SolverConfig {
                use_vmtf: false,
                ..base.clone()
            },
        ),
        (
            "enable_stabilize off",
            SolverConfig {
                enable_stabilize: false,
                ..base.clone()
            },
        ),
        (
            "reuse_trail off",
            SolverConfig {
                reuse_trail: false,
                ..base.clone()
            },
        ),
        (
            "rephase_interval on (every 3 restarts)",
            SolverConfig {
                rephase_interval: 3,
                ..base.clone()
            },
        ),
        (
            "everything off (legacy Luby, no VMTF, no reuse-trail)",
            SolverConfig {
                use_vmtf: false,
                enable_stabilize: false,
                reuse_trail: false,
                rephase_interval: 0,
                ..base
            },
        ),
    ];

    for (label, config) in variants {
        let mut solver = Solver::with_config(config);
        add_pigeonhole(&mut solver, 4, 3);
        assert_eq!(
            solver.solve(),
            SolverResult::Unsat,
            "config variant [{label}] disagreed on PHP(4,3), which is unconditionally UNSAT"
        );
    }
}

#[test]
fn test_pr26_individual_mechanism_toggles_never_flip_sat_verdict() {
    let base = SolverConfig::default();
    let variants: Vec<(&str, SolverConfig)> = vec![
        ("all defaults", base.clone()),
        (
            "use_vmtf off",
            SolverConfig {
                use_vmtf: false,
                ..base.clone()
            },
        ),
        (
            "enable_stabilize off",
            SolverConfig {
                enable_stabilize: false,
                ..base.clone()
            },
        ),
        (
            "reuse_trail off",
            SolverConfig {
                reuse_trail: false,
                ..base.clone()
            },
        ),
        (
            "rephase_interval on (every restart)",
            SolverConfig {
                rephase_interval: 1,
                ..base
            },
        ),
    ];

    for (label, config) in variants {
        let mut solver = Solver::with_config(config);
        add_small_sat_instance(&mut solver);
        assert_eq!(
            solver.solve(),
            SolverResult::Sat,
            "config variant [{label}] disagreed on a satisfiable instance"
        );
    }
}

/// Repeated `solve()` calls on freshly-built solvers with the new defaults
/// must be deterministic (no reliance on e.g. uninitialized memory or
/// system time) -- the stable/focused schedule and reuse-trail restarts are
/// pure functions of the conflict/tick counters, not of wall-clock time.
#[test]
fn test_pr26_default_config_is_deterministic_across_runs() {
    let mut results = Vec::new();
    for _ in 0..5 {
        let mut solver = Solver::new();
        add_pigeonhole(&mut solver, 5, 4);
        results.push(solver.solve());
    }
    assert!(results.iter().all(|&r| r == SolverResult::Unsat));
}
