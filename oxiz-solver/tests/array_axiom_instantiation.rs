//! Regression tests for lazy array-axiom instantiation in the CDCL(T) loop.
//!
//! These pin the behaviour of the read-over-write / extensionality /
//! select-congruence lemmas added by `Solver::instantiate_array_axioms`.  Every
//! case here is one the syntactic array pre-checks (`check_array.rs`) cannot
//! decide on their own: without in-loop axiom instantiation the solver would
//! either return a spurious `Sat` (an unsound result) or an over-cautious
//! `Unknown`.

use oxiz_solver::{Context, SolverResult};

/// Run an SMT-LIB script and return the verdict of the final `check-sat`.
fn run_script(script: &str) -> SolverResult {
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(script).unwrap_or_default();
    for tok in outputs.iter().rev() {
        match tok.trim() {
            "sat" => return SolverResult::Sat,
            "unsat" => return SolverResult::Unsat,
            "unknown" => return SolverResult::Unknown,
            _ => {}
        }
    }
    SolverResult::Unknown
}

/// Read-over-write case 2 (different index) drives a conflict: with `i != j`,
/// `select(store(a,i,v),j)` must equal `select(a,j)`, so `5` and `7` clash.
///
/// The syntactic pre-check only handles the *same*-index read-over-write; the
/// disequality-driven case is decided solely by the in-loop RoW-2 axiom.
#[test]
fn row2_different_index_is_unsat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const v Int)
(assert (not (= i j)))
(assert (= (select (store a i v) j) 5))
(assert (= (select a j) 7))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// The same RoW-2 shape but consistent (`select(a,j) = 5`) must stay `Sat`,
/// proving the axiom does not over-constrain.
#[test]
fn row2_different_index_consistent_is_sat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const v Int)
(assert (not (= i j)))
(assert (= (select (store a i v) j) 5))
(assert (= (select a j) 5))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Two nested stores at three pairwise-distinct indices: reading at `k` skips
/// both writes and must reduce to `select(a,k)`.  Requires two rounds of RoW-2
/// (outer store, then inner store), i.e. genuine saturation over the lemma the
/// first round introduces.
#[test]
fn nested_store_read_skips_both_writes_is_unsat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const k Int)
(declare-const v1 Int)
(declare-const v2 Int)
(assert (not (= i k)))
(assert (not (= j k)))
(assert (= (select (store (store a i v1) j v2) k) 5))
(assert (= (select a k) 9))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Nested-store read where the outer write *does* land on the query index:
/// `select(store(store(a,i,v1),j,v2), j) = v2` regardless of `i`.  Asserting a
/// different value for `v2` is unsat via same-index RoW-1 at the outer store.
#[test]
fn nested_store_read_hits_outer_write_is_unsat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (= (select (store (store a i 1) j 2) j) 3))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Extensionality witness: `a != b` while every *named* read agrees.  A witness
/// index (distinct from `0` and `1`) can differ, so the formula is satisfiable —
/// the extensionality lemma must introduce such a witness rather than force a
/// spurious `Unsat`, and the solver must not report `Unknown`.
#[test]
fn extensionality_witness_is_sat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(assert (not (= a b)))
(assert (= (select a 0) (select b 0)))
(assert (= (select a 1) (select b 1)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Select congruence over an asserted array equality: `a = b` forces
/// `select(a,0) = select(b,0)`, so pinning them to `5` and `7` is unsat.
#[test]
fn select_congruence_over_equality_is_unsat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(assert (= a b))
(assert (= (select a 0) 5))
(assert (= (select b 0) 7))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Store equality via extensionality on a disequality that is genuinely
/// contradictory: `a != store(a,i,v)` yet `select(a,i) = v` (so the store is a
/// no-op and the arrays are actually equal at every index) — the witness index
/// must collapse onto `i`, making the disequality unsatisfiable.
#[test]
fn store_noop_disequality_is_unsat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const v Int)
(assert (= (select a i) v))
(assert (not (= a (store a i v))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// A plain disequality of two unconstrained arrays with no shared reads is
/// trivially satisfiable and must remain `Sat` (extensionality adds a witness
/// but never over-constrains).
#[test]
fn unconstrained_array_disequality_is_sat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(assert (not (= a b)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Read-over-write with a store to a base array that itself is aliased through
/// an equality: `B = store(a,i,v)` and reading `B` at a different index must go
/// to `a`.  Exercises the alias-guarded RoW instantiation.
#[test]
fn aliased_store_read_over_write_is_unsat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const v Int)
(assert (= b (store a i v)))
(assert (not (= i j)))
(assert (= (select b j) 5))
(assert (= (select a j) 7))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Issue #22 (reduced): an equality between two *independent* read-over-write
/// reads whose indices are arithmetic compounds.
///
/// Both base arrays are unconstrained, so a model exists trivially (choose the
/// arrays so the two reads agree).  Nothing here entails a conflict, yet the
/// index terms (`+`, `div`) are not syntactically comparable — the case that
/// stresses the RoW instantiation's "index relationship unknown" path.  The
/// axiom layer must leave such a read unresolved (`eval_read` → `None`) rather
/// than committing to a value and manufacturing a disequality conflict.
#[test]
fn test_issue_22_read_over_write_arith_index() {
    let script = r#"
(set-logic QF_AUFLIA)
(declare-const a0 (Array Int Int))
(declare-const a1 (Array Int Int))
(declare-const i0 Int)
(declare-const i1 Int)
(declare-const i2 Int)
(assert (= (select (store a1 1 2) (+ 2 i1))
           (select (store a0 i0 (div i1 8)) (div i2 10))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Issue #22 (verbatim reproducer): read-over-write with `div`, `mod`, `abs`,
/// `ite` and `+` in the index/value positions, wrapped in `(not (distinct …))`.
///
/// `z3` answers `sat`; this pins that oxiz agrees.  The Euclidean constants
/// involved — `(div 7 7) = 1`, `(mod (- 3) (- 5)) = 2`, `(abs 7) = 7` — are
/// covered independently by `oxiz-core/tests/audit_div_semantics.rs`.
#[test]
fn test_issue_22_full_reproducer() {
    let script = r#"
(set-logic QF_AUFLIA)
(declare-const a0 (Array Int Int))
(declare-const a1 (Array Int Int))
(declare-const i0 Int)
(declare-const i1 Int)
(declare-const i2 Int)
(assert (not (distinct
  (select (store a1 (div 7 7) (mod (- 3) (- 5))) (+ 2 i1))
  (select (store a0 (ite (<= (mod (abs 7) 2) (- 3)) (- 9) i0) (div i1 8)) (div i2 10)))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

// ──────────────────────────────────────────────────────────────────
// Polarity boundary: facts must be unconditionally asserted
// ──────────────────────────────────────────────────────────────────

/// `(not (and A B))` is `(or (not A) (not B))`, so neither conjunct is
/// entailed.  The array pre-check's collector tracked polarity but passed it
/// straight through its `And` arm, so a single `(not (and …))` handed every
/// conjunct to the definite-conflict maps at negative polarity.
///
/// Here `(= (select (store a 3 5) 3) 5)` is a *true* read-over-write, so
/// recording it as a negated select assertion made the axiom evaluation agree
/// with the "negated" value and fire a conflict.  The formula is satisfiable
/// with `p = false` (`z3` answers `sat`).
#[test]
fn test_array_bool_eq_polarity_boundary() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const p Bool)
(assert (not (and (= (select (store a 3 5) 3) 5) p)))
(check-sat)
"#;
    assert_ne!(
        run_script(script),
        SolverResult::Unsat,
        "conjuncts of a negated And are disjunctive; they must not be collected \
         as unconditional read-over-write facts"
    );

    // Double negation reaches the store=store extensionality collector, which
    // had the same pass-through: the inner disequality flips back to positive
    // polarity and was recorded as an asserted `(= (store a 0 1) (store b 0 2))`.
    // Satisfiable with `p = false` — the inner disequality is in fact valid, so
    // the assertion reduces to `(not p)`.
    let double_negation = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(declare-const p Bool)
(assert (not (and (not (= (store a 0 1) (store b 0 2))) p)))
(check-sat)
"#;
    assert_ne!(
        run_script(double_negation),
        SolverResult::Unsat,
        "a doubly-negated equality under a negated And is not asserted; the \
         store extensionality check must not fire on it"
    );
}

/// Control: the same store=store equality asserted *unconditionally* really is
/// unsatisfiable, so the fix above must not have disabled the check.
#[test]
fn test_array_store_extensionality_still_fires_when_asserted() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(assert (= (store a 0 1) (store b 0 2)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}
