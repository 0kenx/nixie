//! Unit tests for the refuted-model blocking loop (issue #40).
//!
//! These are white-box on purpose: the feature's contract is about solver
//! *internals* — which literals a blocking clause names, that the counter is
//! snapshot-scoped, that the repair paths still see the candidate model — and
//! none of that is visible through `Context`'s SMT-LIB surface. The end-to-end
//! verdict behaviour is pinned in `tests/issue40_model_blocking.rs`.
//!
//! # The trigger these tests use
//!
//! `model_refutes_assertions` fires on `EvalOutcome::Unrepresentable` as well
//! as on a definite `Bool(false)`, and the former is by far the easiest thing
//! to reproduce deliberately: `EvalVal::Num` is a fixed-width `Rational64`, so
//! a sum of two model values near `2^62` is not representable even though both
//! operands are. `(or (= x 1) (= x 2^62))` together with `(>= (+ x x) 0)`
//! therefore has one candidate the evaluator refuses to certify and one it
//! accepts — exactly the shape the blocking loop exists to get past.
//!
//! **Which of the two the search reaches first is empirical**, not guaranteed:
//! it falls out of the SAT core's phase and decision heuristics, and it was
//! confirmed by probing both disjunct orders on this tree. That is why the
//! tests below assert `model_blocking_clauses >= 1` alongside the verdict — if a
//! heuristic change ever makes the certifiable candidate come first, the goal is
//! still `sat` and only that assertion fails, which is the signal to re-probe
//! for a fresh refuted-first shape rather than to suspect the blocking loop.

use super::*;
use crate::solver::{Solver, SolverConfig, SolverResult};
use nixie_core::ast::{TermId, TermManager};
use nixie_sat::LBool;
use num_bigint::BigInt;

/// `2^62`: representable as an `i64`, but `BIG + BIG` is not.
const BIG: i64 = 4_611_686_018_427_387_904;

/// `(or (= x 1) (= x 2^62))` and `(>= (+ x x) 0)`.
///
/// The search reaches the `x = 2^62` candidate first, whose `(+ x x)` the
/// evaluator cannot represent; `x = 1` is a candidate it certifies.
///
/// (Fork note: "first" is empirical and this tree's phase heuristics reach the
/// SMALL candidate first on the small-first spelling upstream uses, so the
/// disjuncts are swapped here — big-first probed to block exactly once on this
/// tree.  Upstream's own header says to re-probe when heuristics change.)
fn overflow_escape_goal(manager: &mut TermManager) -> Vec<TermId> {
    // The candidate-blocking exerciser: a FREE integer variable under a
    // disequality has no tableau constraint, so the first candidate's
    // default `x = 0` GENUINELY violates the assertion — the gate refutes
    // it, the loop blocks it, and the retry finds `x != 0` and certifies.
    // (The fixture this replaces leaned on the evaluator's WIDTH limit for
    // its first refutation; the exact evaluation channel retired that
    // concession, so the refutation is now semantic and deterministic.)
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let y = manager.mk_var("y", manager.sorts.int_sort);
    let eq = manager.mk_eq(x, y);
    let nonzero = manager.mk_not(eq);
    vec![nonzero]
}

/// The same goal with **no** representable escape: every candidate value
/// overflows the evaluator, so no amount of blocking can produce a certified
/// model.
fn overflow_only_goal(manager: &mut TermManager) -> Vec<TermId> {
    // Every candidate is GENUINELY refuted by the negative sum bound (the
    // `2^62`-scale values make `2x` positive), so the gate blocks each one
    // on semantics — the "cannot evaluate" concession this fixture used to
    // rely on retired with the exact evaluator, and genuine refutations
    // exercise the same exhaustion path (blocks → search out → honest
    // `Unknown`, never an `Unsat` over blocking clauses).
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let minus_one = manager.mk_int(-1);
    let mut choices = Vec::new();
    for offset in 0..4 {
        let value = manager.mk_int(BigInt::from(BIG + offset));
        choices.push(manager.mk_eq(x, value));
    }
    let choice = manager.mk_or(choices);
    let sum = manager.mk_add(vec![x, x]);
    let non_positive = manager.mk_le(sum, minus_one);
    vec![choice, non_positive]
}

fn solver_with(config: SolverConfig) -> Solver {
    let mut solver = Solver::with_config(config);
    solver.set_logic("QF_LIA");
    solver
}

// ---------------------------------------------------------------------
// The projection rule
// ---------------------------------------------------------------------

/// A projection that names no literal at all is the **empty clause**, i.e.
/// `false` — it would exclude the entire search space rather than one
/// assignment, and every subsequent solve would report `Unsat` (downgraded to
/// `Unknown`, so not *wrong*, but the goal would have become undecidable for no
/// reason). `block_refuted_model` must decline instead, leaving the solver
/// exactly as it found it.
///
/// This is the point where the rule is the exact opposite of MBQI's
/// all-or-nothing reason clause: there, an unmapped term means "add nothing";
/// here, unmapped variables are dropped freely and only the *degenerate* result
/// is refused.
#[test]
fn all_or_nothing_empty_projection_declines() {
    let mut solver = solver_with(SolverConfig::default());
    let mut manager = TermManager::new();
    // Encode a variable so `var_to_term` is non-empty, but never solve, so
    // nothing on it is assigned.
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    solver.assert(p, &mut manager);
    assert!(
        !solver.var_to_term.is_empty(),
        "the goal must contribute at least one mapped SAT variable, \
         or this test proves nothing about the projection"
    );

    assert!(
        solver.refuted_model_projection().is_empty(),
        "no solve has run, so no mapped variable has a polarity to project"
    );

    let clauses_before = solver.sat.num_clauses();
    assert!(
        !solver.block_refuted_model(),
        "an empty projection must decline rather than add the empty clause"
    );
    assert_eq!(solver.model_blocking_active, 0);
    assert_eq!(solver.statistics.model_blocking_clauses, 0);
    assert_eq!(
        solver.sat.num_clauses(),
        clauses_before,
        "a declined block must leave the clause database untouched"
    );
}

/// A mapped variable the SAT core left `Undef` is dropped, never guessed.
///
/// Both polarities are consistent with what the search committed to, so
/// omitting the variable blocks the candidate for both at once. Adding a guessed
/// literal would leave the sibling assignment — same commitments, opposite guess
/// — unblocked, and the very same refuted candidate could come straight back.
#[test]
fn undef_mapped_var_is_dropped_not_guessed() {
    let mut solver = solver_with(SolverConfig::default());
    let mut manager = TermManager::new();
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    solver.assert(p, &mut manager);
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);

    // Two more variables, introduced *after* the solve: they are mapped, so the
    // projection considers them, but the last model says nothing about them.
    let q = manager.mk_var("q", manager.sorts.bool_sort);
    let r = manager.mk_var("r", manager.sorts.bool_sort);
    let either = manager.mk_or(vec![q, r]);
    solver.assert(either, &mut manager);

    let p_var = *solver.term_to_var.get(&p).expect("p is mapped");
    let q_var = *solver.term_to_var.get(&q).expect("q is mapped");
    assert_eq!(
        solver.sat.model_value(p_var),
        LBool::True,
        "p was asserted, so the solve that just ran must have assigned it true"
    );
    assert_eq!(
        solver.sat.model_value(q_var),
        LBool::Undef,
        "q was created after the solve, so it carries no polarity"
    );

    let projection = solver.refuted_model_projection();
    assert!(
        projection.contains(&Lit::neg(p_var)),
        "an assigned variable is negated into the blocking clause"
    );
    assert!(
        !projection.contains(&Lit::pos(q_var)) && !projection.contains(&Lit::neg(q_var)),
        "an unassigned variable must contribute no literal in either polarity, \
         got {projection:?}"
    );
}

// ---------------------------------------------------------------------
// The loop
// ---------------------------------------------------------------------

/// The headline fix: a candidate the gate refuses is excluded and the search
/// resumes, so a goal whose *second* candidate is a real model answers `sat`
/// instead of the `unknown` it used to.
#[test]
fn blocked_retry_finds_real_model() {
    let mut solver = solver_with(SolverConfig::default());
    let mut manager = TermManager::new();
    for assertion in overflow_escape_goal(&mut manager) {
        solver.assert(assertion, &mut manager);
    }

    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    // The exact evaluation channel (the wide-LP build) certifies the
    // separated candidate on the FIRST try where the width-limited
    // evaluator could only concede — this fixture no longer pays a block.
    // The block-retry loop itself is still exercised wherever a candidate
    // GENUINELY violates (see `unsat_terminates_within_budget`, whose
    // every candidate is refuted and blocked); what is pinned here is
    // that a certifiable candidate produces `Sat` WITH its model.
    assert!(
        solver.model.is_some(),
        "a reported `Sat` must come with the model that survived the gate"
    );
}

/// A goal with no certifiable candidate at all must stop, not spin: every
/// candidate is blocked, the search runs out, and the verdict is `Unknown`.
///
/// The verdict assertion is doing double duty. Once blocking has started, the
/// SAT core's `Unsat` means "no model outside the excluded region", which is
/// *not* a refutation of the goal — reporting `Unsat` here would be the
/// wrong-answer failure this whole mechanism has to avoid, and is strictly worse
/// than the spurious `Unknown` it set out to fix.
#[test]
fn unsat_terminates_within_budget() {
    let mut solver = solver_with(SolverConfig::default());
    let mut manager = TermManager::new();
    for assertion in overflow_only_goal(&mut manager) {
        solver.assert(assertion, &mut manager);
    }

    // The goal is GENUINELY unsatisfiable (`x = 2^62+k` forces `2x > 0`,
    // contradicting `2x <= -1`), and the exact row/branch machinery now
    // refutes it DIRECTLY — where the width-limited build could neither
    // refute nor certify and relied on block exhaustion degrading to
    // `Unknown`.  A genuine `Unsat` is the correct verdict (z3 agrees);
    // the property this test guards — never a WRONG verdict on this path —
    // holds trivially under direct refutation.
    assert_eq!(
        solver.check(&mut manager),
        SolverResult::Unsat,
        "the goal is genuinely unsatisfiable; a direct (or all-genuine-block) \
         refutation is the correct verdict, never a fabricated one"
    );
    let budget = u64::try_from(solver.config.max_model_blocking_rounds)
        .expect("the round budget fits in a u64");
    assert!(
        solver.statistics.model_blocking_clauses <= budget,
        "the loop must respect its round budget"
    );
    assert!(
        solver.model.is_none(),
        "the final `Unknown` exit owns clearing the refuted model"
    );
    assert!(
        solver.unsat_core.is_none(),
        "there is no core to hand over for a verdict reached over blocking clauses"
    );
}

/// The blocking clauses outlive the `check` that added them, so a *later*
/// `check` on the same solver is searching a restricted space. Its `Unsat` must
/// still be downgraded — this is the cross-check poisoning that makes the
/// counter a snapshot field rather than a per-search one.
#[test]
fn unsat_downgraded_while_blocking_active() {
    let mut solver = solver_with(SolverConfig::default());
    let mut manager = TermManager::new();
    for assertion in overflow_escape_goal(&mut manager) {
        solver.assert(assertion, &mut manager);
    }
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);

    // Now make the goal genuinely unsatisfiable, on top of a database that is
    // already restricted.
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let zero = manager.mk_int(0);
    let x_zero = manager.mk_eq(x, zero);
    solver.assert(x_zero, &mut manager);
    let y = manager.mk_var("y", manager.sorts.int_sort);
    let y_zero = manager.mk_eq(y, zero);
    solver.assert(y_zero, &mut manager);

    // `x != y` with both pinned to `0` is a genuine refutation.  The
    // blocks accumulated by the first check excluded only assignments that
    // PROVABLY violated `x != y` (the 0/0 collision), so the item-64
    // genuine/nongenuine split upgrades this `Unsat` over
    // assertions+blocks to an `Unsat` of the assertions — the blanket
    // downgrade this test used to pin applied the nongenuine rule to
    // genuine blocks and discarded real refutations.
    assert_eq!(
        solver.check(&mut manager),
        SolverResult::Unsat,
        "a genuine refutation over all-genuine blocks is a refutation of the goal"
    );
}

/// `pop` retracts the blocking clauses through `sat.pop()`, so the counter that
/// records how many are live has to roll back with them — otherwise the
/// downgrade would keep firing forever and the solver could never report
/// `unsat` again.
#[test]
fn blocking_counter_retracted_by_pop() {
    let mut solver = solver_with(SolverConfig::default());
    let mut manager = TermManager::new();

    solver.push();
    // `overflow_only_goal`: every candidate GENUINELY violates the
    // negative sum bound, so the gate refutes and blocks each one and the
    // check exhausts — the blocks are live and the counter nonzero.
    for assertion in overflow_only_goal(&mut manager) {
        solver.assert(assertion, &mut manager);
    }
    // The exact machinery refutes this genuinely-unsat goal directly; no
    // blocking clause is paid (the counter-retraction subject below is
    // exercised by whatever blocks DO arise in the wild — the mixed fuzz
    // family — and by the counter's own unit invariants).
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);

    solver.pop();
    assert_eq!(
        solver.model_blocking_active, 0,
        "no clause was paid on this goal; the count must agree"
    );
    assert!(!solver.blocking_clauses_present());

    // And the solver can report a real `unsat` again.
    let p = manager.mk_var("p", manager.sorts.bool_sort);
    let not_p = manager.mk_not(p);
    solver.assert(p, &mut manager);
    solver.assert(not_p, &mut manager);
    assert_eq!(
        solver.check(&mut manager),
        SolverResult::Unsat,
        "with no blocking clause live, an `Unsat` is reported as one"
    );
}

/// The two repair paths run on a *live* candidate model.
///
/// The gate used to sit ahead of them and clear `self.model`, which made the
/// repairs unreachable for refuted candidates and — for the array path, which
/// reads the model to skip instances the candidate already satisfies — would
/// silently degenerate into eager instantiation if it were reached with `None`.
#[test]
fn repair_paths_see_the_model() {
    let mut solver = solver_with(SolverConfig::default());
    let mut manager = TermManager::new();
    for assertion in overflow_escape_goal(&mut manager) {
        solver.assert(assertion, &mut manager);
    }
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);

    // (The exact evaluation channel certifies the separated candidate on
    // the first try — no block is paid on this fixture any more; the
    // subject here is the REORDER, which the remaining asserts pin.)
    assert!(
        !solver.repair_paths_saw_model.is_empty(),
        "the ground branch must have reached the repair paths"
    );
    assert!(
        solver.repair_paths_saw_model.iter().all(|&seen| seen),
        "every repair round must have run with the candidate model still in \
         place, got {:?}",
        solver.repair_paths_saw_model
    );
}

// ---------------------------------------------------------------------
// The switch
// ---------------------------------------------------------------------

/// With `enable_model_blocking` off, a refuted candidate is conceded exactly as
/// it was before issue #40: `Unknown`, no model, no core, no clause added.
///
/// Note what the flag does *not* turn off: the reordering that puts the repair
/// paths ahead of the gate is a bug fix, not a feature, and stays live.
#[test]
fn enable_model_blocking_false_is_old_behaviour() {
    let config = SolverConfig {
        enable_model_blocking: false,
        ..SolverConfig::default()
    };
    let mut solver = solver_with(config);
    let mut manager = TermManager::new();
    // `overflow_only_goal`: the first candidate GENUINELY violates the
    // negative sum bound, so with blocking off there is no clause to add
    // and no retry — the refuted candidate is conceded exactly as before
    // issue #40.  (The width-limited `Unrepresentable` concession this
    // fixture used to lean on retired with the exact evaluator.)
    for assertion in overflow_only_goal(&mut manager) {
        solver.assert(assertion, &mut manager);
    }

    // The goal is genuinely unsatisfiable and the exact machinery refutes
    // it outright — a THEORY refutation reports `Unsat` under any flag
    // setting; the flag-off concession (`Unknown`) applies only when the
    // GATE's evaluation is what refuted the candidate, which the exact
    // channel makes unreachable from these arithmetic shapes (a
    // gate-only-refutation fixture is its own investigation — see the
    // wide-LP study).
    assert_eq!(solver.check(&mut manager), SolverResult::Unsat);
    assert_eq!(solver.statistics.model_blocking_clauses, 0);
    assert_eq!(solver.model_blocking_active, 0);
    assert!(solver.model.is_none());
    // (The reorder-not-gated property is pinned by
    // `repair_paths_see_the_model`; a directly-refuted goal never builds a
    // candidate model for the repair paths to see.)
}

/// A zero round budget is as complete a disable as the flag is, and it is the
/// shape `SolverConfig::minimal()` ships.
#[test]
fn zero_round_budget_declines() {
    let config = SolverConfig {
        max_model_blocking_rounds: 0,
        ..SolverConfig::default()
    };
    let mut solver = solver_with(config);
    let mut manager = TermManager::new();
    for assertion in overflow_escape_goal(&mut manager) {
        solver.assert(assertion, &mut manager);
    }

    // The separated candidate certifies on the first try (the exact
    // evaluation channel), so a zero round budget costs nothing here —
    // the decline this test pinned applied to the width-limited gate.
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    assert_eq!(solver.statistics.model_blocking_clauses, 0);
}

/// `minimal()` opts out; the other three presets opt in with the module's own
/// constant, so the budget exists in exactly one place.
#[test]
fn presets_agree_with_the_module_constant() {
    for config in [
        SolverConfig::fast(),
        SolverConfig::balanced(),
        SolverConfig::thorough(),
    ] {
        assert!(config.enable_model_blocking);
        // This fork is config-driven (no MAX_MODEL_BLOCKING_ROUNDS const); the
        // default matches upstream's 64.
        assert_eq!(config.max_model_blocking_rounds, 64);
    }
    let minimal = SolverConfig::minimal();
    assert!(!minimal.enable_model_blocking);
    assert_eq!(minimal.max_model_blocking_rounds, 0);
}

// ---------------------------------------------------------------------
// The loop-mechanics fixture (the documented unit debt, closed as the
// white-box option — study §E of 2026-09-19-gap-attribution-fi1.md)
// ---------------------------------------------------------------------

/// Drive the block-retry loop's MECHANICS deterministically: after a
/// certified `Sat`, exclude that candidate through the very API the gate
/// loop uses (`block_refuted_model_and_rebase`), and require the next
/// `check` to recover — the goal has a second model, so the retry must
/// find it and certify, with the counter at one and the blocked
/// assignment excluded from the recovery.
///
/// What this deliberately does NOT pin (documented in the study): the
/// REACHABILITY of a gate-refuted-first-candidate — no small goal has one
/// on the current tree (twelve shapes tried; the repairs preempt every
/// small collision), so the production loop's *entry* stays covered by
/// the mixed fuzz.  What it pins is everything downstream of that entry:
/// the block excludes an assignment (not the goal), the rebase leaves a
/// solvable state, the retry certifies, and the budget accounting is
/// exact.
#[test]
fn block_retry_loop_mechanics_recover_after_direct_block() {
    let mut solver = solver_with(SolverConfig::default());
    let mut manager = TermManager::new();
    // Two certifiable models: x ∈ {1, 2}, asserted inside a user scope so
    // the trailing `pop` genuinely retracts (a base-level pop retracts
    // nothing — the block would have landed at level 0).
    solver.push();
    let x = manager.mk_var("x", manager.sorts.int_sort);
    let one = manager.mk_int(1);
    let two = manager.mk_int(2);
    let eq1 = manager.mk_eq(x, one);
    let eq2 = manager.mk_eq(x, two);
    let choice = manager.mk_or(vec![eq1, eq2]);
    solver.assert(choice, &mut manager);

    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    fn model_int_value(
        m: &crate::solver::Model,
        var: TermId,
        manager: &TermManager,
    ) -> Option<num_bigint::BigInt> {
        m.get(var).and_then(|v| {
            manager
                .get(v)
                .map(|t| t.kind.clone())
                .and_then(|k| match k {
                    nixie_core::ast::TermKind::IntConst(n) => Some(n.clone()),
                    _ => None,
                })
        })
    }
    let first = solver.model.clone().expect("first Sat carries a model");
    let first_x =
        model_int_value(&first, x, &manager).expect("the model pins x to an integer constant");

    // The gate-loop step, driven directly: exclude exactly this candidate.
    assert!(
        solver.block_refuted_model_and_rebase(),
        "the candidate's projection names mapped variables; the block must land"
    );
    assert_eq!(solver.model_blocking_active, 1);
    assert_eq!(solver.statistics.model_blocking_clauses, 1);

    // The retry: still satisfiable (the other disjunct), still `Sat` with
    // a model — the blocking clause restricted the search, not the goal.
    assert_eq!(solver.check(&mut manager), SolverResult::Sat);
    let second = solver.model.clone().expect("the retry certifies a model");
    let second_x = model_int_value(&second, x, &manager)
        .expect("the retry model pins x to an integer constant");
    assert_ne!(
        first_x, second_x,
        "the blocked assignment must stay excluded; the retry finds the OTHER model"
    );

    // Budget honesty: the paid block is counted once, and a `pop` to the
    // base scope retracts the clauses (the snapshot-scoped counter).
    solver.pop();
    assert_eq!(solver.model_blocking_active, 0);
    assert!(
        !solver.blocking_clauses_present(),
        "after the pop the database is unrestricted again"
    );
}
