//! Reproductions for task **#26** — theory-solver scope leakage across
//! `TheoryManager` lifetimes produces a **false `unsat`**.
//!
//! # The leak
//!
//! `Solver::check_core` drives a CDCL(T) search through a [`TheoryManager`] that
//! borrows the *long-lived* EUF / arithmetic / bit-vector solvers.  Every theory
//! scope is opened and closed through `TheoryManager::push_theory_scope` /
//! `pop_theory_scope`, one per SAT decision level, and the manager decides how
//! many to pop from its own `level_stack`:
//!
//! ```text
//! fn on_backtrack(&mut self, level: u32) {
//!     while self.level_stack.len() > (level as usize + 1) { self.pop_theory_scope(); }
//! }
//! ```
//!
//! A search that ends `Sat` **never backtracks**, so it leaves the theory
//! solvers several scopes deep, holding every assertion the winning branch made.
//! A new `TheoryManager` is then built — for the next MBQI round, or for the
//! next `check-sat` — and it starts with `level_stack == vec![0]`.  From that
//! moment the leaked scopes are *unreachable*: `level_stack.len()` is already 1,
//! so no `on_backtrack(0)` can ever pop them, and the assertions inside them are
//! committed for the lifetime of the `Solver`.  Meanwhile the new manager
//! replays the whole SAT trail into the theory solvers at what it believes is
//! base level, physically stacking the new facts on top of the leaked ones.
//!
//! Instrumenting `push_theory_scope` / `pop_theory_scope` with the solver-owned
//! absolute depth counter (`DerivedReasons`) next to the manager's own
//! `level_stack` makes the mismatch visible.  For
//! [`mbqi_round_scope_leak_causes_false_unsat`] below, with `f(1) = 100`,
//! `x ∈ {1, 5}` and `y ∈ {2, 7}`:
//!
//! ```text
//! [assert] abs_depth=0 stack=1  f(1) = 100
//! [scope]  push abs_depth=1 stack=2
//! [assert] abs_depth=1 stack=2  y = 7
//! [scope]  push abs_depth=2 stack=3
//! [assert] abs_depth=2 stack=3  y != 2
//! [scope]  push abs_depth=3 stack=4
//! [assert] abs_depth=3 stack=4  x != 5
//! [assert] abs_depth=3 stack=4  x  = 1        <-- retracted branch, scope 3
//! [round]  end of mbqi round 1: abs theory depth = 3, sat decision level = 0
//! [assert] abs_depth=3 stack=1  f(1) = 100    <-- fresh manager, believes base
//! [assert] abs_depth=3 stack=1  x != 1        <-- lands on top of `x = 1`
//! ```
//!
//! The MBQI lemma `f(1) = 100 ⇒ x ≠ 1` is added with `Solver::add_clause`, which
//! calls `backtrack_to_root()` **without notifying the theory manager** — hence
//! `sat decision level = 0` against `abs theory depth = 3`.  Round 2 asserts
//! `x ≠ 1` into a tableau that still contains `x = 1` from the branch the lemma
//! just retracted, the arithmetic solver refutes it at SAT decision level 0, and
//! `solve_with_theory` returns `Unsat` before conflict analysis can even run.
//! The leaked bound of a retracted branch has refuted a satisfiable formula.
//!
//! # Why the honesty nets did not catch it
//!
//! `conflict_clause.rs`'s `reason_literal_is_live` check guarded only the
//! *derived-equality* expansion path (case 2 of `terms_to_conflict_clause`).
//! The leaked assertion here is tagged with an ordinary atom that still has a
//! SAT variable, so it took case 1 and was emitted unchecked; and when the
//! conflict lands at decision level 0, `solve_with_theory` returns `Unsat`
//! before conflict analysis examines the clause at all.  Nothing was loud; the
//! answer was simply wrong.  Case 1 now applies the same liveness test — see
//! *Status* below.
//!
//! # Status — fixed
//!
//! Every test below asserts the **correct** answer, and every one of them failed
//! before the task-#26 fix.  They are now the regression pins for it.
//!
//! The remedy is `Solver::rebase_theory_state` (`solver/mod.rs`), called at the
//! two seams this file exercises — `check_core` entry and the MBQI round
//! boundary.  It drops the SAT trail to the root and re-derives the EUF /
//! arithmetic / bit-vector state from it, so the next round starts from exactly
//! the facts it is entitled to: the ground assertions plus every kept
//! instantiation lemma, all of which live in the SAT clause database with their
//! unit consequences committed at the root, and none of the branch decisions.
//!
//! Popping the leaked scopes instead was tried and diverges — see the doc
//! comment on `rebase_theory_state` for why the SAT trail and the theory scope
//! stack have to be re-aligned together.
//!
//! The honesty net was extended at the same time: case (1) of
//! `terms_to_conflict_clause` now applies `reason_literal_is_live`, so a reason
//! atom the SAT core no longer has assigned trips a `debug_assert!` and falls
//! back to the conservative lemma instead of being emitted silently.  With the
//! fix reverted, [`leaked_order_bounds_cause_a_false_unsat`] trips exactly that
//! assertion — the net is live, not quiet by exemption.

use oxiz_solver::Context;

/// Run a script and return every `sat` / `unsat` / `unknown` line, in order.
fn verdicts(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(script)
        .expect("script should parse and run");
    out.into_iter()
        .filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .collect()
}

/// The two-branch core shared by the multi-`check-sat` reproductions.
///
/// `x ∈ {1, 5}` and `y ∈ {2, 7}` force the SAT core to take decisions, so a
/// `Sat` verdict leaves theory scopes open holding the branch it chose.
const TWO_BRANCH_CORE: &str = r#"
    (set-logic QF_LIA)
    (declare-const x Int)
    (declare-const y Int)
    (assert (or (= x 1) (= x 5)))
    (assert (or (= y 2) (= y 7)))
"#;

// ---------------------------------------------------------------------------
// Control: green today and after the fix.
// ---------------------------------------------------------------------------

/// The differential control arm: the very assertion set that the reproductions
/// end up with, checked **once**, is satisfiable and answered `sat`.
///
/// This is what makes the reproductions below evidence of a *leak* rather
/// than of an ordinary incompleteness: nothing about the final assertion set is
/// hard.  Only the history leading to it differs.
#[test]
fn control_same_assertions_checked_once_are_sat() {
    let script = format!("{TWO_BRANCH_CORE}\n(assert (= x 5))\n(assert (= y 7))\n(check-sat)\n");
    assert_eq!(
        verdicts(&script),
        vec!["sat"],
        "x = 5, y = 7 satisfies both disjunctions"
    );
}

// ---------------------------------------------------------------------------
// (a) End-to-end false `unsat` — the MBQI-round leak inside a single check.
// ---------------------------------------------------------------------------

/// **Task #26, the flagged hazard itself.** A single `check-sat` on a
/// satisfiable UFLIA goal answers `unsat`, because an MBQI lemma retracts the
/// branch round 1 decided on while the arithmetic solver keeps that branch's
/// `x = 1` committed in a scope the round-2 manager cannot reach.
///
/// The goal is plainly satisfiable: take `x = 5`, `y = 2`, `f(1) = 100` and
/// `f(5) = 0`.  The universal then reads `f(i) = 100 ⇒ x ≠ i`, whose only
/// relevant instance is `i = 1`, and `x = 5 ≠ 1` discharges it.
///
/// See the module documentation for the annotated scope trace of this exact
/// script.
#[test]
fn mbqi_round_scope_leak_causes_false_unsat() {
    let script = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (or (= x 1) (= x 5)))
        (assert (or (= y 2) (= y 7)))
        (assert (= (f 1) 100))
        (assert (forall ((i Int)) (=> (= (f i) 100) (not (= x i)))))
        (check-sat)
    "#;
    assert_eq!(
        verdicts(script),
        vec!["sat"],
        "x = 5, y = 2, f(1) = 100, f(5) = 0 is a model; the `unsat` comes from \
         the round-1 branch assertion `x = 1` surviving in an unreachable \
         theory scope"
    );
}

// ---------------------------------------------------------------------------
// (a) End-to-end false `unsat` — the same leak across `check-sat` calls.
// ---------------------------------------------------------------------------

/// The purest statement of the bug: **interposing a `(check-sat)` changes the
/// answer**.
///
/// Both halves finish with the identical assertion set, and
/// [`control_same_assertions_checked_once_are_sat`] shows that set is `sat`.
/// Adding a `(check-sat)` before the last two assertions can only *observe*, it
/// cannot constrain — yet it turns the verdict into `unsat`, because the first
/// check left `x = 1` and `y = 7` committed in scopes the second check's
/// manager can never pop.  (`Solver::check_core` resets only the bit-vector
/// solver between checks; EUF and arithmetic carry over by design.)
#[test]
fn interposed_check_sat_must_not_change_the_verdict() {
    let script = format!(
        "{TWO_BRANCH_CORE}\n(check-sat)\n(assert (= x 5))\n(assert (= y 7))\n(check-sat)\n"
    );
    assert_eq!(
        verdicts(&script),
        vec!["sat", "sat"],
        "a preceding (check-sat) must not make a satisfiable goal unsat"
    );
}

/// One pinning assertion is enough: the second check contradicts only the
/// leaked `x = 1`, and `y` is left free.  Guards against a fix that merely
/// happens to work when every leaked variable is re-pinned.
#[test]
fn one_leaked_bound_is_enough_for_a_false_unsat() {
    let script = format!("{TWO_BRANCH_CORE}\n(check-sat)\n(assert (= x 5))\n(check-sat)\n");
    assert_eq!(verdicts(&script), vec!["sat", "sat"]);
}

/// The leak is not specific to integer equalities: order bounds leak the same
/// way.  Round 1 decides `x <= 0`; the second check's `x >= 10` then meets a
/// tableau that still holds the retracted upper bound.
#[test]
fn leaked_order_bounds_cause_a_false_unsat() {
    let script = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (or (<= x 0) (>= x 10)))
        (assert (or (<= y 0) (>= y 10)))
        (check-sat)
        (assert (>= x 10))
        (assert (>= y 10))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat"]);
}

/// Reals leak identically — the branch state lives in the shared simplex
/// tableau, not in anything integer-specific.
#[test]
fn leaked_real_bounds_cause_a_false_unsat() {
    let script = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (or (= x 1.0) (= x 5.0)))
        (assert (or (= y 2.0) (= y 7.0)))
        (check-sat)
        (assert (= x 5.0))
        (assert (= y 7.0))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat"]);
}

/// Uninterpreted function applications leak through the same seam: the branch
/// equalities on `f(0)` / `f(1)` survive in EUF's leaked scopes.
#[test]
fn leaked_uf_branch_equalities_cause_a_false_unsat() {
    let script = r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (assert (or (= (f 0) 1) (= (f 0) 5)))
        (assert (or (= (f 1) 2) (= (f 1) 7)))
        (check-sat)
        (assert (= (f 0) 5))
        (assert (= (f 1) 7))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat"]);
}

// ---------------------------------------------------------------------------
// (a) The quantified fragments the MBQI parity suites cover.
// ---------------------------------------------------------------------------

/// UFLIA: the same leak with a bounded-box universal in play, i.e. inside the
/// fragment `tests/mbqi_sat_certification.rs` certifies.
#[test]
fn quantified_uflia_multicheck_false_unsat() {
    let script = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (forall ((i Int)) (=> (and (>= i 0) (<= i 3)) (>= (f i) 0))))
        (assert (or (= x 1) (= x 5)))
        (assert (or (= y 2) (= y 7)))
        (check-sat)
        (assert (= x 5))
        (assert (= y 7))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat"]);
}

/// AUFLIA: array-init universal plus two branching integers.
#[test]
fn quantified_auflia_multicheck_false_unsat() {
    let script = r#"
        (set-logic AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (declare-const y Int)
        (assert (forall ((i Int)) (=> (and (>= i 0) (< i 3)) (= (select a i) 0))))
        (assert (or (= x 1) (= x 5)))
        (assert (or (= y 2) (= y 7)))
        (check-sat)
        (assert (= x 5))
        (assert (= y 7))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat"]);
}

/// UFLRA: range-bounded universal plus two branching reals.
#[test]
fn quantified_uflra_multicheck_false_unsat() {
    let script = r#"
        (set-logic UFLRA)
        (declare-fun f (Real) Real)
        (declare-const x Real)
        (declare-const y Real)
        (assert (forall ((v Real)) (and (>= (f v) 0.0) (<= (f v) 1.0))))
        (assert (or (= x 1.0) (= x 5.0)))
        (assert (or (= y 2.0) (= y 7.0)))
        (check-sat)
        (assert (= x 5.0))
        (assert (= y 7.0))
        (check-sat)
    "#;
    assert_eq!(verdicts(script), vec!["sat", "sat"]);
}

// ---------------------------------------------------------------------------
// (a) The self-contradictory sequence: unsat, then sat, from a *weaker* state.
// ---------------------------------------------------------------------------

/// The leak survives `push`, and `pop` cures it — which is visible from the
/// outside as an impossible answer sequence.
///
/// `Solver::pop` resets EUF and arithmetic wholesale (see the comment on
/// `Solver::pop`), so it happens to sweep the leak away.  The middle check
/// therefore answers `unsat` for an assertion set that is *strictly stronger*
/// than the one the final check answers `sat` for — the final check's set is a
/// subset of the middle one.  A monotone solver cannot do that; only leaked
/// state can.
#[test]
fn push_pop_exposes_the_leak_as_a_non_monotone_answer_sequence() {
    let script = format!(
        "{TWO_BRANCH_CORE}
        (check-sat)
        (push 1)
        (assert (= x 5))
        (assert (= y 7))
        (check-sat)
        (pop 1)
        (check-sat)
    "
    );
    assert_eq!(
        verdicts(&script),
        vec!["sat", "sat", "sat"],
        "the middle check's assertions are a superset of the last check's; \
         `unsat` there with `sat` here can only come from leaked state"
    );
}
