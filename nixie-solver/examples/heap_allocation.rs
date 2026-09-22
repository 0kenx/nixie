//! Run with `cargo run -p nixie-solver --example heap_allocation`.
use nixie_solver::SolverResult;
use nixie_solver::heap::{HeapError, HeapSolver, Heaplet};

fn main() -> Result<(), HeapError> {
    let mut solver = HeapSolver::new();
    let x = solver.int_var("x");
    let y = solver.int_var("y");
    let seven = solver.integer(7);
    let nine = solver.integer(9);
    let allocated =
        solver.reify(Heaplet::points_to(&x, &seven).star(Heaplet::points_to(&y, &nine)))?;
    let alias = solver.eq(&x, &y)?;

    // A symbolic post-allocation state with two exclusively owned cells.
    solver.assert(&allocated)?;
    assert_eq!(solver.check(), SolverResult::Sat);
    let model = solver.model().ok_or(HeapError("missing heap model"))?;
    println!("Allocated heap: {:?}", model.cells);

    // Verify allocated => x != y by looking for a counterexample:
    // allocated AND NOT(x != y), i.e. allocated AND x = y.
    solver.push();
    solver.assert(&alias)?;
    assert_eq!(solver.check(), SolverResult::Unsat);
    println!("No aliasing counterexample exists.");
    solver.pop()?;
    assert_eq!(solver.check(), SolverResult::Sat);
    Ok(())
}
