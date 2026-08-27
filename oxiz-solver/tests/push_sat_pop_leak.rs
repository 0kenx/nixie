//! Soundness guards for the `push / check-sat (sat) / pop / assert / check-sat`
//! incremental leak — a **pre-existing base-solver bug found during the
//! upstream-v0.3.3 port** and fixed by journalling the clause-dedup memos on
//! the undo trail (`TrailOp::NumericEqSplitPairAdded`,
//! `TrailOp::ArithConstAxiomPairAdded`).
//!
//! # The shape
//!
//! ```text
//! (assert A)          ; base — includes a numeric equality atom
//! (push 1)
//! (check-sat)         ; answers sat (correctly)
//! (pop 1)
//! (assert B)          ; B refutes the base under the atom's semantics
//! (check-sat)         ; MUST be unsat; the bug answers sat
//! ```
//!
//! # Evidence trail (2026-08-27 session, `docs/studies/2026-08-27-v0.3.3-port.md`)
//!
//! * Reproduces on **pristine main** (`845c53b`) — not a port regression.
//! * Pure-Bool shapes (no arithmetic) are **correct** — the SAT core's
//!   push/solve/pop path is fine (verified with a standalone `oxiz-sat`
//!   driver replaying the same clause/unit sequence, binary and ternary
//!   forms: `r1=Sat r2=Unsat`).
//! * The failing second `check` answers `sat` with **zero decisions**: the
//!   level-0 prefix satisfies every live clause, so the refutation has to
//!   come from theory propagation of the numeric equality atom — and none
//!   fires.
//! The fix (all repros below now pass):
//!   `numeric_eq_split_pairs` (the trichotomy-clause dedup memo) survived
//!   `pop` while the clauses it deduped were emitted into the popped SAT
//!   scope, so the trichotomy clauses were never re-emitted (their atoms
//!   disappeared from the second check's variable legend). The memo is now
//!   journalled (`TrailOp::NumericEqSplitPairAdded`) and retracted by `pop`.
//!   An initially-suspected "stale watch" theory in `oxiz_sat::Solver::pop`
//!   was disproved: a standalone replay of the same clause/unit sequence
//!   through the public `oxiz-sat` API answers correctly, and the memo fix
//!   alone repairs every repro once the binary is genuinely rebuilt (an
//!   intermediate "still failing" observation was a stale binary from a
//!   disk-full build failure).
//! * Second instance of the same class, found by sweeping:
//!   `arith_const_axiom_pairs` ("already axiomatized in a prior `check`
//!   whose clauses survived (no retracting `pop`)" — the parenthetical is
//!   false) is journalled the same way. `care_split_pairs` and
//!   `arith_defined_terms` were already journalled.

use oxiz_solver::Context;

fn verdicts(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script).expect("script must execute")
}

/// Minimal shape: the asserted `(= x 5)` after the pop must force `p` true
/// (via `p = (x = 5)`) and conflict with `(not p)`.
#[test]
fn sat_in_scope_then_pop_loses_arith_atom() {
    let out = verdicts(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (declare-const p Bool)
         (assert (= p (= x 5)))
         (assert (not p))
         (push 1)
         (check-sat)
         (pop 1)
         (assert (= x 5))
         (check-sat)",
    );
    assert_eq!(out, vec!["sat".to_string(), "unsat".to_string()]);
}

/// The no-push/pop control: identical assertions, correct `unsat`.
#[test]
fn the_same_assertions_without_push_pop_are_unsat() {
    let out = verdicts(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (declare-const p Bool)
         (assert (= p (= x 5)))
         (assert (not p))
         (assert (= x 5))
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat".to_string()]);
}

/// An `unsat` verdict inside the scope does NOT poison the next check
/// (the corruption is specific to a `sat` leaf).
#[test]
fn unsat_in_scope_then_pop_stays_correct() {
    let out = verdicts(
        "(set-logic QF_LIA)
         (declare-const x Int)
         (declare-const p Bool)
         (assert (= p (= x 5)))
         (assert (not p))
         (push 1)
         (assert (= x 5))
         (check-sat)
         (pop 1)
         (assert (= x 5))
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat".to_string(), "unsat".to_string()]);
}

/// UF-application form (the shape the `define-fun-rec` driver reaches it
/// through): two rounds of instance assertions around a pop.
#[test]
fn uf_chain_around_pop_is_unsat() {
    let out = verdicts(
        "(declare-fun f (Int) Int)
         (declare-const p Bool)
         (assert (= p (= (f 5) 120)))
         (assert (not p))
         (push 1)
         (check-sat)
         (pop 1)
         (assert (= (f 5) (* 5 (f 4))))
         (assert (= (f 4) (* 4 (f 3))))
         (assert (= (f 3) (* 3 (f 2))))
         (assert (= (f 2) (* 2 (f 1))))
         (assert (= (f 1) (f 0)))
         (assert (= 1 (f 0)))
         (check-sat)",
    );
    assert_eq!(out, vec!["sat".to_string(), "unsat".to_string()]);
}
