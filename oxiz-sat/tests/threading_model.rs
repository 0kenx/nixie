//! Pins the crate's threading and cancellation contract (see the
//! "Threading and cancellation model" section of the crate docs):
//!
//! 1. **Reentrant across solver instances** – independent `Solver`s may be
//!    driven from different threads concurrently with bit-identical results.
//!    The solver is deterministic, so any shared-mutable-state regression
//!    (a global counter, a shared cache) shows up as a divergent trajectory,
//!    not just a flaky timing: the concurrent results must equal the
//!    sequential ones *exactly*.
//! 2. **Asynchronous termination is cooperative cancellation** – a flag set
//!    from another thread mid-search yields `Unknown` (never a wrong
//!    verdict), and the instance remains usable once the flag is cleared.
//!    A flag raised before `solve()` abandons before preprocessing.

use oxiz_sat::{Lit, Solver, SolverResult, Var};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;

/// Pigeonhole `pigeons > holes` (UNSAT); the (10,9) size is the cancellation
/// test's workhorse: ~3 s of deterministic search, so a flag set at 300 ms
/// lands mid-search with a wide margin, and a broken cancellation mechanism
/// fails the test in seconds rather than hanging.
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

/// A small satisfiable instance with a non-trivial search.
fn add_sat_instance(solver: &mut Solver) {
    for _ in 0..14 {
        solver.new_var();
    }
    // Hand-built 3-SAT skeleton that is SAT (x1 = x2 = ... = true works).
    for i in 0..12u32 {
        let a = Var::new(i);
        let b = Var::new(i + 1);
        let c = Var::new(i + 2);
        solver.add_clause([Lit::neg(a), Lit::pos(b), Lit::pos(c)]);
        solver.add_clause([Lit::pos(a), Lit::neg(b), Lit::pos(c)]);
    }
    solver.add_clause([Lit::pos(Var::new(0)), Lit::pos(Var::new(13))]);
}

fn build(kind: u32) -> (Solver, SolverResult) {
    let mut solver = Solver::new();
    match kind % 3 {
        0 => {
            add_pigeonhole(&mut solver, 7, 6);
            (solver, SolverResult::Unsat)
        }
        1 => {
            add_sat_instance(&mut solver);
            (solver, SolverResult::Sat)
        }
        _ => {
            // Mixed: a SAT pigeonhole (pigeons <= holes) plus constraints.
            add_pigeonhole(&mut solver, 6, 6);
            solver.add_clause([Lit::neg(Var::new(0)), Lit::neg(Var::new(1))]);
            (solver, SolverResult::Sat)
        }
    }
}

/// Reentrancy: 4 threads × 3 instance kinds, each thread building and
/// solving its own `Solver`s concurrently, must reproduce the sequential
/// results exactly (verdict + final conflict count – the deterministic
/// trajectory fingerprint).
#[test]
fn reentrant_across_solver_instances() {
    const THREADS: u32 = 4;

    // Sequential ground truth: (kind, verdict, conflicts).
    let expected: Vec<(u32, SolverResult, u64)> = (0..3)
        .map(|kind| {
            let (mut solver, expected_result) = build(kind);
            let result = solver.solve();
            assert_eq!(result, expected_result, "sequential solve kind {kind}");
            (kind, result, solver.stats().conflicts)
        })
        .collect();

    let expected = Arc::new(expected);
    let mut handles = Vec::new();
    for t in 0..THREADS {
        let expected = Arc::clone(&expected);
        handles.push(thread::spawn(move || {
            // Each thread iterates all kinds (including the same kind other
            // threads are running concurrently) so instance construction and
            // search genuinely interleave.
            for (kind, want_result, want_conflicts) in expected.iter() {
                let (mut solver, _) = build(*kind);
                let result = solver.solve();
                assert_eq!(
                    result, *want_result,
                    "thread {t} kind {kind}: concurrent verdict diverged"
                );
                assert_eq!(
                    solver.stats().conflicts,
                    *want_conflicts,
                    "thread {t} kind {kind}: concurrent trajectory diverged \
                     (shared mutable state in the library?)"
                );
            }
        }));
    }
    for h in handles {
        h.join().expect("reentrancy worker thread must not panic");
    }
}

/// A flag raised *before* `solve()` abandons before any search work: the
/// verdict is `Unknown` and not a single conflict is spent (pre-search gate).
#[test]
fn pre_raised_interrupt_abandons_before_preprocessing() {
    let flag = Arc::new(AtomicBool::new(false));
    let mut solver = Solver::new();
    add_pigeonhole(&mut solver, 7, 6);
    solver.set_interrupt(Arc::clone(&flag));
    flag.store(true, Ordering::SeqCst);
    assert_eq!(solver.solve(), SolverResult::Unknown);
    assert_eq!(
        solver.stats().conflicts,
        0,
        "a pre-raised interrupt must not burn conflicts before abandoning"
    );
    // Caller-owned flag: clearing it restores normal solving.
    flag.store(false, Ordering::SeqCst);
    assert_eq!(solver.solve(), SolverResult::Unsat);
}

/// A flag set by another thread *mid-search* cancels: `Unknown`, never a
/// wrong verdict, and the same instance solves correctly afterwards.
#[test]
fn asynchronous_termination_from_another_thread() {
    let flag = Arc::new(AtomicBool::new(false));
    let mut solver = Solver::new();
    // ~3 s of deterministic UNSAT search at release speed; see
    // `add_pigeonhole`.
    add_pigeonhole(&mut solver, 10, 9);
    solver.set_interrupt(Arc::clone(&flag));

    let setter = Arc::clone(&flag);
    let canceller = thread::spawn(move || {
        thread::sleep(std::time::Duration::from_millis(300));
        setter.store(true, Ordering::SeqCst);
    });
    let result = solver.solve();
    canceller.join().expect("canceller thread");

    assert_eq!(
        result,
        SolverResult::Unknown,
        "cancellation must yield Unknown, never a verdict; php(10,9) is UNSAT \
         and would have taken seconds more, so anything else here is a bug"
    );

    // The instance remains usable: clear the caller-owned flag and solve to
    // completion on the same solver object.
    flag.store(false, Ordering::SeqCst);
    assert_eq!(solver.solve(), SolverResult::Unsat);
}
