//! Regression tests for the opt-p2 audit findings:
//!
//! 1. `oxiz-opt/src/maxsat/algorithms.rs`: the default weighted (stratified)
//!    MaxSAT path must respect weights and report the true weighted optimum
//!    (WPM1), not just any Fu-Malik-style minimal-violation-count solution.
//! 2. `oxiz-opt/src/preprocess.rs`: unit propagation must never treat a SOFT
//!    unit clause as a hard fact.
//! 3. `oxiz-opt/src/context.rs`: `OptContext::optimize()` must not coerce
//!    rational weights to 1, and must not report `Optimal` when the inner
//!    solver ever answers `Unknown`.

use oxiz_opt::{
    MaxSatAlgorithm, MaxSatConfig, MaxSatResult, MaxSatSolver, OptContext, Preprocessor, Weight,
};
use oxiz_sat::{Lit, Var};

fn lit(v: u32, neg: bool) -> Lit {
    if neg {
        Lit::neg(Var(v))
    } else {
        Lit::pos(Var(v))
    }
}

/// hard: x0 \/ x1
/// soft: ~x0  weight 3
/// soft: ~x1  weight 1
///
/// The only way to satisfy the hard clause is x0=true or x1=true (or both).
/// True weighted optimum: x0=false, x1=true -> ~x0 satisfied (cost 0),
/// ~x1 violated (cost 1). Total cost = 1. A solver that ignores weights
/// (plain Fu-Malik/MSU3 minimal-violation-count) could instead report
/// cost 3 (e.g. x0=true, x1=false) while still claiming `Optimal`.
fn build_adversarial_instance(config: MaxSatConfig) -> MaxSatSolver {
    let mut solver = MaxSatSolver::with_config(config);
    solver.add_hard([lit(0, false), lit(1, false)]);
    solver.add_soft_weighted([lit(0, true)], Weight::from(3i64));
    solver.add_soft_weighted([lit(1, true)], Weight::from(1i64));
    solver
}

#[test]
fn weighted_maxsat_default_stratified_path_is_weight_optimal() {
    // Default config: stratified = true, which is the path under audit.
    let mut solver = build_adversarial_instance(MaxSatConfig::default());
    let result = solver.solve().expect("solve should not error");
    assert_eq!(result, MaxSatResult::Optimal);
    assert_eq!(
        solver.cost(),
        Weight::from(1i64),
        "weighted MaxSAT must minimize total weight, not violation count"
    );
}

#[test]
fn weighted_maxsat_wmax_algorithm_is_weight_optimal() {
    let config = MaxSatConfig::builder()
        .algorithm(MaxSatAlgorithm::WMax)
        .stratified(true)
        .build();
    let mut solver = build_adversarial_instance(config);
    let result = solver.solve().expect("solve should not error");
    assert_eq!(result, MaxSatResult::Optimal);
    assert_eq!(solver.cost(), Weight::from(1i64));
}

#[test]
fn weighted_maxsat_larger_instance_finds_true_weighted_optimum() {
    // hard: x0 \/ x1 \/ x2
    // soft ~x0 w=10, soft ~x1 w=10, soft ~x2 w=1
    // Optimal: x2=false (pay 1), x0=true, x1=true -> cost 1.
    let mut solver = MaxSatSolver::new();
    solver.add_hard([lit(0, false), lit(1, false), lit(2, false)]);
    solver.add_soft_weighted([lit(0, true)], Weight::from(10i64));
    solver.add_soft_weighted([lit(1, true)], Weight::from(10i64));
    solver.add_soft_weighted([lit(2, true)], Weight::from(1i64));

    let result = solver.solve().expect("solve should not error");
    assert_eq!(result, MaxSatResult::Optimal);
    assert_eq!(solver.cost(), Weight::from(1i64));
}

#[test]
fn weighted_maxsat_two_overlapping_cores() {
    // hard: (x0 \/ x1), (x1 \/ x2)
    // soft: ~x0 w=1, ~x1 w=100, ~x2 w=1
    // Setting x1=true satisfies both hard clauses cheaply, paying only the
    // weight-100 soft clause's violation... but setting x0=true AND x2=true
    // (x1=false) pays only 1+1=2, which is cheaper than paying 100.
    let mut solver = MaxSatSolver::new();
    solver.add_hard([lit(0, false), lit(1, false)]);
    solver.add_hard([lit(1, false), lit(2, false)]);
    solver.add_soft_weighted([lit(0, true)], Weight::from(1i64));
    solver.add_soft_weighted([lit(1, true)], Weight::from(100i64));
    solver.add_soft_weighted([lit(2, true)], Weight::from(1i64));

    let result = solver.solve().expect("solve should not error");
    assert_eq!(result, MaxSatResult::Optimal);
    assert_eq!(solver.cost(), Weight::from(2i64));
}

/// Preprocessing must never treat a SOFT unit clause as a hard fact: the
/// exact audit example (soft (x) w=1, soft (~x) w=5) must survive
/// preprocessing untouched, in full, with both weights intact.
#[test]
fn preprocess_never_treats_soft_unit_as_fact() {
    use oxiz_opt::{PreprocessConfig, SoftClause, SoftId};

    // Bounded variable elimination is a separate preprocessing pass (not
    // part of this audit's unit-propagation finding) with its own,
    // independent soft-clause-resolution soundness caveats; disable it so
    // this test isolates the unit-propagation fix under audit.
    let config = PreprocessConfig {
        bounded_variable_elimination: false,
        ..PreprocessConfig::default()
    };
    let mut prep = Preprocessor::with_config(config);
    let soft = vec![
        SoftClause::new(SoftId::new(0), [lit(0, false)], Weight::from(1i64)),
        SoftClause::new(SoftId::new(1), [lit(0, true)], Weight::from(5i64)),
    ];

    let (result, hard) = prep.preprocess(&soft);

    assert!(hard.is_empty());
    assert_eq!(result.len(), 2, "neither soft unit may be dropped");
    let total_weight: i64 = result.iter().filter_map(|c| c.weight.to_i64()).sum();
    assert_eq!(
        total_weight, 6,
        "no weight may be lost during preprocessing"
    );
}

/// End-to-end: feeding the adversarial preprocessing example through the
/// preprocessor and then the real weighted solver must still produce the
/// true optimum (cost 1), proving the preprocessing fix doesn't just avoid
/// a crash but preserves solvability to the correct answer.
#[test]
fn preprocess_then_solve_finds_true_optimum() {
    use oxiz_opt::{PreprocessConfig, SoftClause, SoftId};

    // See `preprocess_never_treats_soft_unit_as_fact` for why BVE is
    // disabled here: it is a separate pass with its own soundness caveats,
    // outside the scope of the unit-propagation finding under audit.
    let config = PreprocessConfig {
        bounded_variable_elimination: false,
        ..PreprocessConfig::default()
    };
    let mut prep = Preprocessor::with_config(config);
    let soft = vec![
        SoftClause::new(SoftId::new(0), [lit(0, false)], Weight::from(1i64)),
        SoftClause::new(SoftId::new(1), [lit(0, true)], Weight::from(5i64)),
    ];
    let (soft, hard) = prep.preprocess(&soft);

    let mut solver = MaxSatSolver::new();
    for h in hard {
        solver.add_hard(h.iter().copied());
    }
    for c in &soft {
        solver.add_soft_weighted(c.lits.iter().copied(), c.weight.clone());
    }

    let result = solver.solve().expect("solve should not error");
    assert_eq!(result, MaxSatResult::Optimal);
    assert_eq!(solver.cost(), Weight::from(1i64));
}

/// `OptContext::optimize()` must not coerce rational weights to 1: with hard
/// constraints forcing *exactly one* of p, q true (p ∨ q, and ¬p ∨ ¬q – an
/// XOR, so there is a genuine trade-off), soft `p` weight 3/2 (rational) vs
/// soft `q` weight 1 (integer), the true optimum sacrifices the *cheaper*
/// integer weight (p=true, q=false => cost 1, satisfying soft `p` and
/// violating soft `q`), not whichever the coercion-to-1 bug would make
/// artificially tie/dominate.
///
/// Soft terms are plain variables (not `¬p`/`¬q`) because
/// `OptContext::is_soft_satisfied` looks the soft term up directly in the
/// model map, which only contains base-variable assignments – a
/// pre-existing, separate limitation unrelated to the weight-coercion fix
/// under test here.
#[test]
fn optctx_rational_weight_is_not_coerced_to_one() {
    let mut ctx = OptContext::new();

    let bool_sort = ctx.terms.sorts.bool_sort;
    let p = ctx.terms.mk_var("p_rat", bool_sort);
    let q = ctx.terms.mk_var("q_rat", bool_sort);
    let p_or_q = ctx.terms.mk_or([p, q]);
    let not_p = ctx.terms.mk_not(p);
    let not_q = ctx.terms.mk_not(q);
    let not_both = ctx.terms.mk_or([not_p, not_q]);

    ctx.add_hard(p_or_q);
    ctx.add_hard(not_both);
    let soft_p = ctx.add_soft_weighted(p, Weight::from((3i64, 2i64))); // 1.5
    let soft_q = ctx.add_soft_weighted(q, Weight::from(1i64));

    let result = ctx.optimize().expect("optimize should not error");
    assert!(matches!(
        result,
        oxiz_opt::OptResult::Optimal | oxiz_opt::OptResult::Satisfiable
    ));

    // True optimum has cost exactly 1 (only the integer-weighted soft
    // clause violated: p=true satisfies hard + soft `p`, q=false violates
    // soft `q`). Coercing the rational weight to 1 would create a spurious
    // tie between the two options and could let the strictly worse
    // (cost 1.5, q=true/p=false) assignment win.
    assert_eq!(ctx.cost(), Weight::from(1i64));
    assert!(ctx.is_soft_satisfied(soft_p));
    assert!(!ctx.is_soft_satisfied(soft_q));
}

/// Sanity check that plain integer weights still behave exactly as before
/// the scaling fix (scale factor of 1 when no rational weights are
/// present).
#[test]
fn optctx_integer_weights_unaffected_by_scaling_fix() {
    let mut ctx = OptContext::new();

    let bool_sort = ctx.terms.sorts.bool_sort;
    let p = ctx.terms.mk_var("p_int", bool_sort);
    let q = ctx.terms.mk_var("q_int", bool_sort);
    let p_or_q = ctx.terms.mk_or([p, q]);
    let not_p = ctx.terms.mk_not(p);
    let not_q = ctx.terms.mk_not(q);
    let not_both = ctx.terms.mk_or([not_p, not_q]);

    ctx.add_hard(p_or_q);
    ctx.add_hard(not_both);
    ctx.add_soft_weighted(p, Weight::from(3i64));
    let soft_q = ctx.add_soft_weighted(q, Weight::from(1i64));

    let result = ctx.optimize().expect("optimize should not error");
    assert!(matches!(
        result,
        oxiz_opt::OptResult::Optimal | oxiz_opt::OptResult::Satisfiable
    ));
    assert_eq!(ctx.cost(), Weight::from(1i64));
    assert!(!ctx.is_soft_satisfied(soft_q));
}
