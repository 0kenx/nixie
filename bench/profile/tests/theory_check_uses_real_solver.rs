//! Regression test for `bench_theory_check` in `benches/profile_benchmarks.rs`.
//!
//! The `TheoryCheck` profiling category used to be benchmarked against a
//! `MockTheory` whose `check_sat` unconditionally returned `Sat` (and whose
//! `assert_formula` did nothing at all), so the benchmark measured only
//! `TheoryCoordinator` dispatch bookkeeping, never real theory reasoning.
//! `bench_theory_check` now drives a real `Simplex` (linear-arithmetic)
//! solver through the same `TheorySolver` interface.
//!
//! This test does not re-run the benchmark itself (criterion benches use
//! `harness = false`, which disables `#[test]` support in that binary).
//! Instead it exercises the identical pattern -- a `Simplex`-backed
//! `TheorySolver` registered with a real `TheoryCoordinator` -- against both
//! a satisfiable and an unsatisfiable constraint set. A stub theory (like
//! the old `MockTheory`) would report `Sat` for both; only a solver that
//! actually checks the asserted constraints can tell them apart, which is
//! exactly the property this guards against regressing.

use nixie_solver::combination::coordinator::{
    SatResult, TheoryCoordinator, TheoryId, TheorySolver,
};
use nixie_theories::arithmetic::{LinExpr, Simplex, VarId};
use num_rational::Rational64;

/// Minimal `Simplex`-backed `TheorySolver`, mirroring
/// `SimplexTheory` in `benches/profile_benchmarks.rs`: `assert_formula`'s
/// `formula: usize` argument (`TheoryCoordinator`'s placeholder `TermId`)
/// selects which of two fixed bound constraints on a single variable to
/// add to the underlying `Simplex`.
struct BoundsTheory {
    simplex: Simplex,
    var: VarId,
    /// `(lower, upper)` bound the two representative "formulas" set.
    bounds: (Rational64, Rational64),
}

impl BoundsTheory {
    fn new(lower: Rational64, upper: Rational64) -> Self {
        let mut simplex = Simplex::new();
        let var = simplex.new_var();
        Self {
            simplex,
            var,
            bounds: (lower, upper),
        }
    }
}

impl TheorySolver for BoundsTheory {
    fn theory_id(&self) -> TheoryId {
        TheoryId::Arithmetic
    }

    fn assert_formula(&mut self, formula: usize) -> Result<(), String> {
        match formula % 2 {
            0 => {
                let mut expr = LinExpr::new();
                expr.add_term(self.var, Rational64::new(1, 1));
                expr.add_constant(-self.bounds.0);
                self.simplex.add_ge(expr, formula as u32);
            }
            _ => {
                let mut expr = LinExpr::new();
                expr.add_term(self.var, Rational64::new(1, 1));
                expr.add_constant(-self.bounds.1);
                self.simplex.add_le(expr, formula as u32);
            }
        }
        Ok(())
    }

    fn check_sat(&mut self) -> Result<SatResult, String> {
        match self.simplex.check() {
            Ok(()) => Ok(SatResult::Sat),
            Err(_conflict) => Ok(SatResult::Unsat),
        }
    }

    fn get_model(&self) -> Option<rustc_hash::FxHashMap<usize, usize>> {
        Some(rustc_hash::FxHashMap::default())
    }

    fn get_conflict(&self) -> Option<Vec<usize>> {
        None
    }

    fn backtrack(&mut self, _level: usize) -> Result<(), String> {
        Ok(())
    }

    fn get_implied_equalities(&self) -> Vec<(usize, usize)> {
        Vec::new()
    }

    fn notify_equality(&mut self, _lhs: usize, _rhs: usize) -> Result<(), String> {
        Ok(())
    }
}

fn run(lower: Rational64, upper: Rational64) -> SatResult {
    let mut coordinator = TheoryCoordinator::new(Default::default());
    coordinator.register_theory(Box::new(BoundsTheory::new(lower, upper)));
    coordinator
        .assert_formula(0, TheoryId::Arithmetic)
        .expect("lower bound formula");
    coordinator
        .assert_formula(1, TheoryId::Arithmetic)
        .expect("upper bound formula");
    coordinator.check_sat().expect("check_sat")
}

/// `0 <= x <= 10` is satisfiable: the coordinator must report `Sat`.
#[test]
fn satisfiable_bounds_report_sat() {
    let result = run(Rational64::new(0, 1), Rational64::new(10, 1));
    assert_eq!(result, SatResult::Sat);
}

/// `10 <= x <= 0` is a contradiction: the coordinator must report `Unsat`.
/// A stub theory that always answers `Sat` regardless of what was asserted
/// (like the benchmark's old `MockTheory`) would fail this assertion --
/// that is precisely the gap this regression test closes.
#[test]
fn contradictory_bounds_report_unsat() {
    let result = run(Rational64::new(10, 1), Rational64::new(0, 1));
    assert_eq!(result, SatResult::Unsat);
}
