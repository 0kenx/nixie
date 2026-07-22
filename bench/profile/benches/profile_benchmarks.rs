use bench_profile::{parser_script, run_script, sat_propagation_script, theory_check_script};
use criterion::{Criterion, criterion_group, criterion_main};
use num_rational::Rational64;
use oxiz_core::RewriteContext;
use oxiz_core::ast::{TermId, TermManager};
use oxiz_core::profiling::{ProfilingCategory, ProfilingStats};
use oxiz_core::rewrite::{CombinedRewriter, Rewriter};
use oxiz_proof::ProofRecorder;
use oxiz_sat::{Lit, Solver as SatSolver};
use oxiz_solver::combination::coordinator::{SatResult, TheoryCoordinator, TheoryId, TheorySolver};
use oxiz_theories::Theory;
use oxiz_theories::arithmetic::{LinExpr, Simplex, VarId};
use oxiz_theories::array::ArraySolver;
use oxiz_theories::bv::{Constraint as BvConstraint, Interval, WordLevelPropagator};
use oxiz_theories::euf::{EufSolver, FunctionProperties};
use oxiz_theories::string::{ConstraintAutomaton, Dfa};
use std::hint::black_box;

fn print_snapshot(category: ProfilingCategory) {
    let snapshot = ProfilingStats::snapshot();
    println!(
        "{} => count={} total_ns={}",
        category,
        snapshot.count(category),
        snapshot.total_ns(category)
    );
}

fn bench_sat_propagation(c: &mut Criterion) {
    let mut group = c.benchmark_group(ProfilingCategory::SatPropagation.as_str());
    group.bench_function("solve", |b| {
        b.iter(|| {
            let mut solver = SatSolver::new();
            let a = solver.new_var();
            let b_var = solver.new_var();
            let c_var = solver.new_var();
            solver.add_clause([Lit::pos(a), Lit::pos(b_var)]);
            solver.add_clause([Lit::neg(a), Lit::pos(c_var)]);
            solver.add_clause([Lit::neg(b_var), Lit::pos(c_var)]);
            solver.add_clause([Lit::neg(c_var)]);
            black_box(solver.solve())
        });
    });
    group.finish();
    print_snapshot(ProfilingCategory::SatPropagation);
}

/// Adapts a real [`Simplex`] linear-arithmetic solver to the
/// `TheorySolver` interface, so `bench_theory_check` measures genuine
/// theory reasoning end to end through `TheoryCoordinator` instead of only
/// coordinator dispatch bookkeeping -- all the previous `MockTheory` (whose
/// `check_sat` unconditionally returned `Sat` without ever touching a
/// solver, and whose `assert_formula` did nothing at all) actually
/// exercised.
///
/// `TheoryCoordinator`'s `TermId` is a dispatch-only placeholder (`pub type
/// TermId = usize`, see `combination::coordinator`) carrying no term
/// content of its own, so `assert_formula` resolves the id against a small,
/// fixed, representative constraint set built in `new`: five variables
/// bounded in `[0, 20]`, chained by four pairwise upper bounds plus one
/// constraint tying all five together. The system is jointly satisfiable
/// but not decidable from any single bound in isolation, so `check_sat`
/// must actually run the simplex tableau (see `Simplex::check`) to confirm
/// it -- mirroring how a real theory (e.g. `LinearArithmeticTheory` in
/// `oxiz-solver`) is driven by the coordinator in production.
struct SimplexTheory {
    simplex: Simplex,
    vars: [VarId; 5],
}

impl SimplexTheory {
    fn new() -> Self {
        let mut simplex = Simplex::new();
        let vars = [
            simplex.new_var(),
            simplex.new_var(),
            simplex.new_var(),
            simplex.new_var(),
            simplex.new_var(),
        ];
        for (i, &v) in vars.iter().enumerate() {
            simplex.set_lower(v, Rational64::new(0, 1), i as u32);
            simplex.set_upper(v, Rational64::new(20, 1), 10 + i as u32);
        }
        Self { simplex, vars }
    }

    /// The `n`-th representative constraint: `x_n + x_{n+1} <= 10` for `n`
    /// in `0..4` (four overlapping pairwise bounds), and at `n == 4` the
    /// cross-cutting `x0 + x1 + x2 + x3 + x4 >= 5` that ties every variable
    /// together. Returns the built expression and whether it is a `>=`
    /// constraint (`false` means `<=`).
    fn build(&self, n: usize) -> (LinExpr, bool) {
        let v = &self.vars;
        if n < 4 {
            let mut expr = LinExpr::new();
            expr.add_term(v[n], Rational64::new(1, 1));
            expr.add_term(v[n + 1], Rational64::new(1, 1));
            expr.add_constant(Rational64::new(-10, 1));
            (expr, false)
        } else {
            let mut expr = LinExpr::new();
            for &var in v {
                expr.add_term(var, Rational64::new(1, 1));
            }
            expr.add_constant(Rational64::new(-5, 1));
            (expr, true)
        }
    }

    /// Number of distinct representative constraints `assert_formula` can
    /// resolve an id to (see [`Self::build`]).
    const NUM_CONSTRAINTS: usize = 5;
}

impl TheorySolver for SimplexTheory {
    fn theory_id(&self) -> TheoryId {
        TheoryId::Arithmetic
    }

    fn assert_formula(&mut self, formula: usize) -> Result<(), String> {
        let (expr, is_ge) = self.build(formula % Self::NUM_CONSTRAINTS);
        if is_ge {
            self.simplex.add_ge(expr, formula as u32);
        } else {
            self.simplex.add_le(expr, formula as u32);
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
        // The theory-combination model interface here is keyed on the same
        // placeholder `usize` ids `assert_formula` receives, which carry no
        // correspondence to `Simplex`'s real `VarId`/`Rational64` values
        // (those are exercised directly by `bench_simplex_pivot`), so there
        // is nothing meaningful to report through this particular
        // interface without fabricating one.
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

fn bench_theory_check(c: &mut Criterion) {
    let mut group = c.benchmark_group(ProfilingCategory::TheoryCheck.as_str());
    group.bench_function("coordinator", |b| {
        b.iter(|| {
            let mut coordinator = TheoryCoordinator::new(Default::default());
            coordinator.register_theory(Box::new(SimplexTheory::new()));
            for formula in 0..SimplexTheory::NUM_CONSTRAINTS {
                coordinator
                    .assert_formula(formula, TheoryId::Arithmetic)
                    .expect("registered theory accepts a formula it was built to resolve");
            }
            black_box(coordinator.check_sat())
        });
    });
    group.finish();
    print_snapshot(ProfilingCategory::TheoryCheck);
}

fn bench_egraph_merge(c: &mut Criterion) {
    let mut group = c.benchmark_group(ProfilingCategory::EGraphMerge.as_str());
    group.bench_function("merge", |b| {
        b.iter(|| {
            // Exercise the production EufSolver on a realistic congruence-closure workload:
            //   - 10 leaf terms: x_0..x_4 and y_0..y_4
            //   - Function symbol 0 (f, commutative): 5 binary apps f(x_i, y_i)
            //   - Function symbol 1 (g, plain): 5 unary apps g(x_i) and 5 unary apps g(y_i)
            //   - Merge x_i = y_i for i in 0..5; congruence must derive g(x_i) = g(y_i)
            //   - black_box the equality checks so the optimizer cannot elide the work
            let mut solver = EufSolver::new();

            // Register f as commutative so canonicalize_args fires (exercises hot path).
            solver.register_function(
                0,
                FunctionProperties {
                    associative: false,
                    commutative: true,
                    has_identity: false,
                },
            );
            // g (symbol 1) has no special properties.

            const N: u32 = 5;

            // Intern leaf terms: x_i => TermId 1..=5, y_i => TermId 6..=10
            let mut xs = [0u32; N as usize];
            let mut ys = [0u32; N as usize];
            for i in 0..N {
                xs[i as usize] = solver.intern(TermId::new(1 + i));
                ys[i as usize] = solver.intern(TermId::new(1 + N + i));
            }

            // Intern app terms:
            //   f(x_i, y_i): TermId 11..=15
            //   g(x_i):      TermId 16..=20
            //   g(y_i):      TermId 21..=25
            let mut gxs = [0u32; N as usize];
            let mut gys = [0u32; N as usize];
            for i in 0..N {
                let _fxy =
                    solver.intern_app(TermId::new(11 + i), 0, [xs[i as usize], ys[i as usize]]);
                gxs[i as usize] = solver.intern_app(TermId::new(16 + i), 1, [xs[i as usize]]);
                gys[i as usize] = solver.intern_app(TermId::new(21 + i), 1, [ys[i as usize]]);
            }

            // Merge x_i = y_i; congruence closure must derive g(x_i) = g(y_i).
            for i in 0..N {
                solver
                    .merge(xs[i as usize], ys[i as usize], TermId::new(100 + i))
                    .expect("euf merge");
            }

            // Observe congruence results so the optimizer cannot elide the work.
            let mut all_equal = true;
            for i in 0..N {
                all_equal &= solver.are_equal(gxs[i as usize], gys[i as usize]);
            }
            black_box(all_equal)
        });
    });
    group.finish();
    print_snapshot(ProfilingCategory::EGraphMerge);
}

fn build_simplex() -> Simplex {
    let mut simplex = Simplex::new();
    let x0 = simplex.new_var();
    let x1 = simplex.new_var();
    simplex.set_lower(x0, Rational64::new(0, 1), 0);
    simplex.set_upper(x0, Rational64::new(2, 1), 1);
    simplex.set_lower(x1, Rational64::new(0, 1), 2);
    simplex.set_upper(x1, Rational64::new(2, 1), 3);
    let mut expr = LinExpr::new();
    expr.add_term(x0, Rational64::new(1, 1));
    expr.add_term(x1, Rational64::new(1, 1));
    expr.add_constant(Rational64::new(-3, 1));
    simplex.add_ge(expr, 4);
    simplex
}

fn bench_simplex_pivot(c: &mut Criterion) {
    let mut group = c.benchmark_group(ProfilingCategory::SimplexPivot.as_str());
    group.bench_function("check", |b| {
        b.iter(|| {
            let mut simplex = build_simplex();
            black_box(simplex.check())
        });
    });
    group.finish();
    print_snapshot(ProfilingCategory::SimplexPivot);
}

fn bench_bv_propagation(c: &mut Criterion) {
    let mut group = c.benchmark_group(ProfilingCategory::BvPropagation.as_str());
    group.bench_function("propagate", |b| {
        b.iter(|| {
            let mut propagator = WordLevelPropagator::new();
            let a = TermId::new(1);
            let b_term = TermId::new(2);
            let c_term = TermId::new(3);
            propagator.set_interval(a, Interval::new(1, 3, 8));
            propagator.set_interval(b_term, Interval::new(2, 4, 8));
            propagator.add_constraint(BvConstraint::Add(c_term, a, b_term));
            black_box(propagator.propagate())
        });
    });
    group.finish();
    print_snapshot(ProfilingCategory::BvPropagation);
}

fn bench_string_automata(c: &mut Criterion) {
    let mut group = c.benchmark_group(ProfilingCategory::StringAutomata.as_str());
    group.bench_function("accepts", |b| {
        b.iter(|| {
            let mut dfa = Dfa::new();
            let accepting = dfa.add_state();
            dfa.add_transition(0, 'a', accepting);
            dfa.add_default_transition(accepting, accepting);
            dfa.accepting.insert(accepting);
            let automaton = ConstraintAutomaton::from_dfa(dfa).with_prefix("a".to_string());
            black_box(automaton.accepts("aaaa"))
        });
    });
    group.finish();
    print_snapshot(ProfilingCategory::StringAutomata);
}

fn bench_array_extensionality(c: &mut Criterion) {
    let mut group = c.benchmark_group(ProfilingCategory::ArrayExtensionality.as_str());
    group.bench_function("check", |b| {
        b.iter(|| {
            let mut solver = ArraySolver::new();
            let array = solver.intern_array(TermId::new(1));
            let index = solver.intern(TermId::new(2));
            let value = solver.intern(TermId::new(3));
            let store = solver.intern_store(TermId::new(4), array, index, value);
            let _ = solver.intern_select(TermId::new(5), store, index);
            black_box(solver.check())
        });
    });
    group.finish();
    print_snapshot(ProfilingCategory::ArrayExtensionality);
}

fn bench_proof_generation(c: &mut Criterion) {
    let mut group = c.benchmark_group(ProfilingCategory::ProofGeneration.as_str());
    group.bench_function("record", |b| {
        b.iter(|| {
            let mut recorder = ProofRecorder::new();
            let premise = recorder.record_input("p");
            black_box(recorder.record_derived("unit-resolution", &[premise], "p"))
        });
    });
    group.finish();
    print_snapshot(ProfilingCategory::ProofGeneration);
}

fn bench_parser(c: &mut Criterion) {
    let mut group = c.benchmark_group(ProfilingCategory::Parser.as_str());
    group.bench_function("parse_script", |b| {
        b.iter(|| black_box(run_script(parser_script())))
    });
    group.finish();
    print_snapshot(ProfilingCategory::Parser);
}

fn bench_cache_miss(c: &mut Criterion) {
    let mut group = c.benchmark_group(ProfilingCategory::CacheMiss.as_str());
    group.bench_function("rewrite_unique_terms", |b| {
        b.iter(|| {
            let mut manager = TermManager::new();
            let mut ctx = RewriteContext::new();
            let mut rewriter = CombinedRewriter::new();
            let x = manager.mk_var("x", manager.sorts.int_sort);
            for offset in 0..8 {
                let cst = manager.mk_int(offset);
                let term = manager.mk_add(vec![x, cst]);
                let _ = rewriter.rewrite(term, &mut ctx, &mut manager);
            }
            black_box(rewriter.stats().cache_misses)
        });
    });
    group.finish();
    print_snapshot(ProfilingCategory::CacheMiss);
}

fn bench_context_scripts(c: &mut Criterion) {
    let mut group = c.benchmark_group("ContextScripts");
    group.bench_function("sat_script", |b| {
        b.iter(|| black_box(run_script(sat_propagation_script())))
    });
    group.bench_function("theory_script", |b| {
        b.iter(|| black_box(run_script(theory_check_script())))
    });
    group.finish();
}

criterion_group!(
    profile_benches,
    bench_sat_propagation,
    bench_theory_check,
    bench_egraph_merge,
    bench_simplex_pivot,
    bench_bv_propagation,
    bench_string_automata,
    bench_array_extensionality,
    bench_proof_generation,
    bench_parser,
    bench_cache_miss,
    bench_context_scripts,
);
criterion_main!(profile_benches);
