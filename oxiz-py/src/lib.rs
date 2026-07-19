//! OxiZ Python Bindings
//!
//! Provides Python bindings for the OxiZ SMT solver via PyO3/maturin.
//!
//! # Quick start
//!
//! ```python
//! import oxiz
//!
//! ctx = oxiz.Context()
//! solver = oxiz.Solver()
//!
//! x = ctx.int_const("x")
//! y = ctx.int_const("y")
//!
//! solver.add(x + y > ctx.int_val(0), ctx.tm)
//! solver.add(x < ctx.int_val(10), ctx.tm)
//!
//! result = solver.check(ctx.tm)
//! if result.is_sat:
//!     print(solver.model())
//! ```

pub mod builtins;
pub mod context;
pub mod optimizer;
pub mod results;
pub mod solver_py;
pub mod term;
pub mod theories;

use pyo3::prelude::*;

/// OxiZ SMT Solver Python module
#[pymodule]
fn oxiz(m: &Bound<'_, PyModule>) -> PyResult<()> {
    // Core term and sort types
    m.add_class::<term::PyTerm>()?;
    m.add_class::<term::PyTermManager>()?;
    m.add_class::<term::PySort>()?;

    // Solver result enumerations
    m.add_class::<results::PySolverResult>()?;
    m.add_class::<results::PyOptimizationResult>()?;

    // High-level context (z3-python parity API)
    m.add_class::<context::PyContext>()?;

    // Solver and optimizer
    m.add_class::<solver_py::PySolver>()?;
    m.add_class::<optimizer::PyOptimizer>()?;

    // FP rounding-mode sentinel class
    m.add_class::<theories::PyFPRoundingMode>()?;

    // Module-level boolean / arithmetic combinators
    m.add_function(wrap_pyfunction!(builtins::And, m)?)?;
    m.add_function(wrap_pyfunction!(builtins::Or, m)?)?;
    m.add_function(wrap_pyfunction!(builtins::Not, m)?)?;
    m.add_function(wrap_pyfunction!(builtins::Implies, m)?)?;
    m.add_function(wrap_pyfunction!(builtins::If, m)?)?;

    // Explicit-TM variants (for users who work with bare TermManager)
    m.add_function(wrap_pyfunction!(builtins::and_tm, m)?)?;
    m.add_function(wrap_pyfunction!(builtins::or_tm, m)?)?;
    m.add_function(wrap_pyfunction!(builtins::not_tm, m)?)?;

    // String theory combinators
    m.add_function(wrap_pyfunction!(theories::StringVal, m)?)?;
    m.add_function(wrap_pyfunction!(theories::StringSort, m)?)?;
    m.add_function(wrap_pyfunction!(theories::Concat, m)?)?;
    m.add_function(wrap_pyfunction!(theories::Length, m)?)?;
    m.add_function(wrap_pyfunction!(theories::Contains, m)?)?;
    m.add_function(wrap_pyfunction!(theories::PrefixOf, m)?)?;
    m.add_function(wrap_pyfunction!(theories::SuffixOf, m)?)?;

    // Array theory combinators
    m.add_function(wrap_pyfunction!(theories::ArraySort, m)?)?;

    // Sort constructors for base sorts
    m.add_function(wrap_pyfunction!(theories::IntSort, m)?)?;
    m.add_function(wrap_pyfunction!(theories::BoolSort, m)?)?;

    // Floating-point sort and value constructors
    m.add_function(wrap_pyfunction!(theories::FPSort, m)?)?;
    m.add_function(wrap_pyfunction!(theories::FPVal, m)?)?;

    // Floating-point arithmetic combinators
    m.add_function(wrap_pyfunction!(theories::fp_add, m)?)?;
    m.add_function(wrap_pyfunction!(theories::fp_sub, m)?)?;
    m.add_function(wrap_pyfunction!(theories::fp_mul, m)?)?;
    m.add_function(wrap_pyfunction!(theories::fp_div, m)?)?;

    // Quantifier combinators
    m.add_function(wrap_pyfunction!(theories::ForAll, m)?)?;
    m.add_function(wrap_pyfunction!(theories::Exists, m)?)?;

    // Version metadata
    m.add("__version__", env!("CARGO_PKG_VERSION"))?;

    Ok(())
}
