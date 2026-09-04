//! The verdict cache's contract with its callers.
//!
//! Three things have to hold for [`super::GoalFingerprint`] to be allowed to
//! short-circuit a search, and each gets a pin here:
//!
//! 1. **A hit answers the question that was asked.**  The cached verdict must
//!    agree with what a solver that never saw the earlier call would say.
//! 2. **A settings change is not "nothing happened".**  Every mutator of
//!    something a `check` reads must make the next `check` run for real –
//!    mechanically, so a setter added later cannot quietly opt out.
//! 3. **The observable consequences of a re-run actually arrive.**  A verdict is
//!    not the only output: turning unsat-core production on after a cached
//!    `Unsat`, or raising a budget after a cached `Unknown`, has to produce the
//!    core and the real answer rather than replay the old verdict.
//!
//! (2) and (3) are the same defect seen from two sides, and both were live:
//! before this, the fingerprint carried `max_conflicts` and `max_decisions` and
//! nothing else from a `SolverConfig` with eighteen fields.

use crate::Context;
use crate::solver::{Solver, SolverConfig, SolverResult, TheoryMode};
use nixie_core::ast::TermManager;

/// A small unsatisfiable LIA goal: `x > 0 && x < 0`.
fn assert_unsat_goal(solver: &mut Solver, manager: &mut TermManager) {
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let zero = manager.mk_int(0);
    let positive = manager.mk_gt(x, zero);
    let negative = manager.mk_lt(x, zero);
    solver.assert(positive, manager);
    solver.assert(negative, manager);
}

/// Every mutator of a solver *setting* must drop the cached verdict.
///
/// # Why this is a table and not a handful of scenarios
///
/// The rule stated in `solver::config` is mechanical – *every* `&mut self`
/// method there ends by calling `Solver::settings_changed` – precisely because
/// the failure it prevents is silent.  A setter that skips it produces no error,
/// no warning and no wrong answer on the goal it was tested with; it produces a
/// stale answer later, on somebody else's session, to a question that was never
/// asked.  Pinning the rule itself is the only form of test that a setter added
/// next year cannot pass by accident.
///
/// Each entry re-establishes the cache first, so a mutator that fails to drop it
/// fails here even if a previous entry already dropped it.
#[test]
fn every_settings_mutator_drops_the_cached_verdict() {
    type Mutator = (&'static str, fn(&mut Solver));

    let mutators: &[Mutator] = &[
        ("set_config", |s| {
            let mut config = s.config().clone();
            config.theory_mode = TheoryMode::Lazy;
            s.set_config(config);
        }),
        ("set_timeout", |s| {
            s.set_timeout(core::time::Duration::from_millis(1234));
        }),
        ("set_conflict_limit", |s| s.set_conflict_limit(4321)),
        ("set_decision_limit", |s| s.set_decision_limit(4321)),
        ("set_theory_aware_branching", |s| {
            s.set_theory_aware_branching(!s.theory_aware_branching());
        }),
        ("set_produce_unsat_cores", |s| {
            s.set_produce_unsat_cores(true)
        }),
        ("set_random_seed", |s| s.set_random_seed(4242)),
        ("set_logic", |s| s.set_logic("QF_LIA")),
    ];

    for (name, mutate) in mutators {
        let mut solver = Solver::new();
        let mut manager = TermManager::new();
        assert_unsat_goal(&mut solver, &mut manager);

        assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
        assert!(
            solver.last_check.is_some(),
            "{name}: precondition – the check above must have left a cached verdict"
        );

        mutate(&mut solver);
        assert!(
            solver.last_check.is_none(),
            "{name}: a setting a `check` reads has just changed, so the previous \
             verdict no longer answers the next call; every mutator in \
             `solver::config` owes a `Solver::settings_changed`"
        );
    }
}

/// The fingerprint alone – with the invalidation hook out of the picture –
/// still refuses a verdict computed under different settings.
///
/// The hook above and the fingerprint are deliberately redundant.  This pin is
/// what makes that claim testable rather than decorative: it puts the cached
/// verdict back by hand after the mutator has dropped it, exactly as a future
/// setter that forgot to announce itself would leave things, and requires the
/// fingerprint to catch it anyway.
#[test]
fn the_fingerprint_alone_rejects_a_verdict_from_different_settings() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    assert_unsat_goal(&mut solver, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);

    let stale = solver
        .last_check
        .clone()
        .expect("the check above cached a verdict");

    let mut config = solver.config().clone();
    config.timeout_ms = 999_999;
    solver.set_config(config);

    // Undo the hook's work, leaving only the fingerprint standing.
    solver.last_check = Some(stale);
    assert!(
        solver.cached_verdict(&solver.goal_fingerprint()).is_none(),
        "the fingerprint carries the whole `SolverConfig` by value precisely so \
         that a settings change it was never told about still misses"
    );
}

/// A cache hit must agree with a solver that never saw the earlier call.
///
/// The property that makes the optimisation legitimate at all.  Checked against
/// a *fresh* `Context` replaying the same script rather than against a forced
/// re-run on the same solver, because a re-run is deliberately not idempotent
/// (it keeps what it learned) whereas a fresh solver is the definition of the
/// right answer.
#[test]
fn a_cache_hit_agrees_with_a_solver_that_never_saw_the_first_call() {
    const SESSIONS: &[(&str, &str)] = &[
        (
            "unsat-lia",
            "(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))(assert (< x 0))",
        ),
        (
            "sat-lia",
            "(set-logic QF_LIA)(declare-const x Int)(assert (> x 0))(assert (< x 10))",
        ),
        (
            "quantified",
            "(set-logic UFLIA)(declare-fun f (Int) Int)(declare-const a Int)\
             (assert (forall ((i Int)) (> (f i) 0)))(assert (<= (f a) 0))",
        ),
        (
            "arrays",
            "(set-logic QF_AUFLIA)(declare-const a (Array Int Int))(declare-const i Int)\
             (assert (= (select (store a i 5) i) 6))",
        ),
    ];

    for (name, script) in SESSIONS {
        let mut incremental = Context::new();
        incremental
            .execute_script(script)
            .expect("session should parse and run");

        let mut verdicts = Vec::new();
        for _ in 0..4 {
            let out = incremental
                .execute_script("(check-sat)")
                .expect("check-sat should run");
            verdicts.push(out.last().cloned().unwrap_or_default());
        }

        let mut fresh = Context::new();
        fresh
            .execute_script(script)
            .expect("session should parse and run");
        let reference = fresh
            .execute_script("(check-sat)")
            .expect("check-sat should run")
            .last()
            .cloned()
            .unwrap_or_default();

        assert!(
            verdicts.iter().all(|v| *v == reference),
            "{name}: every repeat, cached or not, must answer what a solver \
             starting from scratch on the same goal answers; got {verdicts:?} \
             against {reference}"
        );
    }
}

/// A cache hit must not search; a settings change must make the next check
/// search again.
///
/// # How "did it actually search?" is observed
///
/// Through the cumulative propagation counter.  It is the one output of a
/// `check` that a cache hit provably cannot move – a hit returns before the
/// solve loop – and that a real search on a non-trivial goal provably does move.
/// Verdict equality cannot distinguish the two cases, which is exactly why the
/// staleness holes this pins were invisible: the replayed answer was the *right*
/// answer for the old settings.
///
/// The interleaved mutation is `:timeout`.  It was the sharpest of the holes:
/// the solve loop honours `SolverConfig::timeout_ms`, an `Unknown` produced by
/// exhausting it is a statement about the budget rather than about the goal, and
/// before this the fingerprint carried `max_conflicts` and `max_decisions` and
/// nothing else – so `(check-sat)` → `unknown` → `(set-option :timeout ...)` →
/// `(check-sat)` handed the same `unknown` straight back out of the cache
/// without re-searching.
#[test]
fn a_settings_change_between_checks_makes_the_next_check_search_again() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    // All but one of the assignments to four Booleans excluded by a clause
    // each: satisfiable, by exactly one model, and only reachable by
    // propagating.  Satisfiable on purpose – a refuted goal keeps its
    // level-0 conflict, so a re-run of *that* would exit before doing enough
    // work to be visible here, and this pin would then be measuring nothing.
    const BITS: usize = 4;
    let vars: Vec<_> = (0..BITS)
        .map(|i| manager.mk_var(&format!("p{i}"), manager.sorts.bool_sort))
        .collect();
    for assignment in 1..(1u32 << BITS) {
        let clause: Vec<_> = vars
            .iter()
            .enumerate()
            .map(|(i, &v)| {
                if assignment & (1 << i) == 0 {
                    v
                } else {
                    manager.mk_not(v)
                }
            })
            .collect();
        let excluded = manager.mk_or(clause);
        solver.assert(excluded, &mut manager);
    }

    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    let after_first = solver.get_statistics().propagations;
    assert!(
        after_first > 0,
        "precondition: the first check must do some work, or this pin cannot \
         tell a search from a cache hit"
    );

    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    assert_eq!(
        solver.get_statistics().propagations,
        after_first,
        "nothing changed between the two calls, so the second must have been \
         answered from the cached verdict rather than re-searched"
    );

    solver.set_timeout(core::time::Duration::from_secs(600));
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    assert!(
        solver.get_statistics().propagations > after_first,
        "the caller changed a limit the solve loop honours; the previous verdict \
         describes a search under the old limit, so this call owes a real one"
    );
}

/// Turning unsat-core production on after a cached `Unsat` must produce a core –
/// a *named* one.
///
/// The verdict is the same either way, which is exactly why this hole was
/// invisible: the cache hit returned the right answer while `unsat_core` stayed
/// `None`, so `(get-unsat-core)` silently yielded nothing.
///
/// # Two independent causes, both pinned here
///
/// Fixing the cache alone left the symptom in place at script level, because
/// `Solver::assert_named` *also* only wrote the assertion's name down when the
/// flag was already on – so a session that asserted first and enabled the option
/// afterwards got a re-run and an anonymous core.  That is the same defect one
/// layer down (state captured under one setting, read under another), and the
/// names asserted below are what distinguish the two: `is_some()` alone would
/// pass with the second cause still live.
#[test]
fn enabling_unsat_cores_after_a_cached_unsat_produces_a_named_core() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();

    let x = manager.mk_var("x", manager.sorts.int_sort);
    let zero = manager.mk_int(0);
    let positive = manager.mk_gt(x, zero);
    let negative = manager.mk_lt(x, zero);
    solver.assert_named(positive, "pos", &mut manager);
    solver.assert_named(negative, "neg", &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
    assert!(
        solver.get_unsat_core().is_none(),
        "precondition: core production is off, so there is no core yet"
    );

    solver.set_produce_unsat_cores(true);
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
    let core = solver
        .get_unsat_core()
        .expect(
            "the caller turned core production on and asked again; answering from \
             a verdict computed while it was off leaves nothing for \
             `(get-unsat-core)`",
        )
        .clone();
    assert!(
        core.names.iter().any(|n| n == "pos") && core.names.iter().any(|n| n == "neg"),
        "the core must name the assertions the caller named, not merely exist – \
         an option that arrives after the assertions must still be honoured; \
         got {:?}",
        core.names
    );
}

/// The same ordering, driven through SMT-LIB as a caller would write it.
#[test]
fn setting_produce_unsat_cores_after_the_assertions_still_yields_a_core() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_LIA)\
             (declare-const x Int)\
             (assert (! (> x 0) :named pos))\
             (assert (! (< x 0) :named neg))\
             (check-sat)\
             (set-option :produce-unsat-cores true)\
             (check-sat)\
             (get-unsat-core)",
        )
        .expect("script should parse and run");

    let core_line = out.last().cloned().unwrap_or_default();
    assert!(
        core_line.contains("pos") && core_line.contains("neg"),
        "`:produce-unsat-cores` set between two checks must be honoured by the \
         second one; got {out:?}"
    );
}

/// `SolverConfig`'s equality is what the fingerprint's coverage rests on.
///
/// Comparing the struct whole is the reason a field added to `SolverConfig`
/// later is covered the day it is added.  This pin fails if someone reaches for
/// a hand-written `PartialEq` that ignores fields, which would restore exactly
/// the hand-picked-subset bug this replaced.
#[test]
fn solver_config_equality_notices_every_field() {
    let base = SolverConfig::default();

    let mut differs = base.clone();
    differs.timeout_ms = base.timeout_ms.wrapping_add(1);
    assert_ne!(base, differs, "timeout_ms must be part of the comparison");

    let mut differs = base.clone();
    differs.simplify = !base.simplify;
    assert_ne!(base, differs, "simplify must be part of the comparison");

    let mut differs = base.clone();
    differs.finite_expansion_budget = base.finite_expansion_budget.wrapping_add(1);
    assert_ne!(
        base, differs,
        "finite_expansion_budget must be part of the comparison"
    );

    assert_eq!(base, base.clone(), "a clone must compare equal");
}
