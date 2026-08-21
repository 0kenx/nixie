//! Regression: constant-function arrays and select-over-select
//! (read-modify-write heaps) in the array theory.
//!
//! Two lazy-lemma gaps closed together (found via the QF_ANIA `avg40`
//! false-SAT; see
//! `docs/studies/2026-08-arithmetic-negated-atoms-false-sat.md`):
//!
//! 1. **Constant-function arrays**: `((as const S) v)` parses as a qualified
//!    `Apply` — an opaque array term unless recognized.  The axiom
//!    `select((as const S) v, i) = v` holds for every index; one unit per
//!    observed read makes the stored value visible.  Without it even the
//!    fully ground `(select ((as const (Array Int Int)) 162) 7)` was left
//!    free and wrong verdicts followed.
//! 2. **select-over-select** (read-modify-write): `select(select(A, j), i)`
//!    where `A`'s store chain stores at `j` — the Ultimate/UltimateAutomizer
//!    heap-update shape (`store(mem, base, store(select(mem, base), off,
//!    v))`).  The array operand of the outer read is itself a read; it is
//!    resolved through A's (aliased) store chain so the outer read twins to
//!    a read of the stored value.
//!
//! Every UNSAT case here is z3-verified; the SAT cases guard against
//! over-eager lemma fabrication.

use oxiz_solver::{Context, SolverResult};

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

/// Fully ground constant-array read: `select(const 162, 7) = 162`.
#[test]
fn ground_const_array_select_is_the_constant() {
    let script = r#"
        (set-logic QF_ANIA)
        (declare-const a (Array Int Int))
        (assert (not (= (select ((as const (Array Int Int)) 162) 7) 162)))
        (check-sat)
    "#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Constant array bound to a variable, read at a variable index.
#[test]
fn const_array_read_through_binding() {
    let script = r#"
        (set-logic QF_ANIA)
        (declare-const a (Array Int Int))
        (declare-const v Int)
        (declare-const i Int)
        (assert (= a ((as const (Array Int Int)) 162)))
        (assert (= v (select a i)))
        (assert (not (= v 162)))
        (check-sat)
    "#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Consistent constant-array model stays SAT (no fabricated conflicts).
#[test]
fn const_array_consistent_stays_sat() {
    let script = r#"
        (set-logic QF_ANIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (= a ((as const (Array Int Int)) 5)))
        (assert (= (select a i) 5))
        (check-sat)
    "#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// 2-level read-modify-write through a store of a constant inner array:
/// `select(select(store(mem, base, const 162), base), 0) = 162`.
#[test]
fn select_over_select_const_value() {
    let script = r#"
        (set-logic QF_ANIA)
        (declare-const mem (Array Int (Array Int Int)))
        (declare-const base Int)
        (declare-const v Int)
        (declare-const mem2 (Array Int (Array Int Int)))
        (assert (= mem2 (store mem base ((as const (Array Int Int)) 162))))
        (assert (= v (select (select mem2 base) 0)))
        (assert (not (= v 162)))
        (check-sat)
    "#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// The canonical RMW shape: read the heap at `base`, write at `off`, store
/// back, then read the updated cell.
#[test]
fn read_modify_write_heap_update() {
    let script = r#"
        (set-logic QF_ANIA)
        (declare-const mem (Array Int (Array Int Int)))
        (declare-const base Int)
        (declare-const off Int)
        (declare-const v Int)
        (declare-const mem2 (Array Int (Array Int Int)))
        (assert (= mem2 (store mem base (store (select mem base) off 5))))
        (assert (= v (select (select mem2 base) off)))
        (assert (not (= v 5)))
        (check-sat)
    "#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// RMW at a DIFFERENT offset leaves the untouched offset's read free (SAT —
/// the value at `off2` comes from the base heap, unconstrained here).
#[test]
fn read_modify_write_other_offset_stays_sat() {
    let script = r#"
        (set-logic QF_ANIA)
        (declare-const mem (Array Int (Array Int Int)))
        (declare-const base Int)
        (declare-const off1 Int)
        (declare-const off2 Int)
        (declare-const v Int)
        (declare-const mem2 (Array Int (Array Int Int)))
        (assert (= mem2 (store mem base (store (select mem base) off1 5))))
        (assert (= v (select (select mem2 base) off2)))
        (assert (not (= off1 off2)))
        (assert (not (= v 5)))
        (check-sat)
    "#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Sequential RMW chain (12 levels): the final read at the written offset
/// sees the newest value.
#[test]
fn read_modify_write_chain() {
    let mut script = String::from(
        "(set-logic QF_ANIA)\n\
         (declare-const mem (Array Int (Array Int Int)))\n\
         (declare-const base Int)\n\
         (declare-const off Int)\n",
    );
    let mut prev = String::from("mem");
    let n = 12;
    for k in 0..n {
        script.push_str(&format!(
            "(declare-const m{k} (Array Int (Array Int Int)))\n\
             (assert (= m{k} (store {prev} base (store (select {prev} base) off {k}))))\n"
        ));
        prev = format!("m{k}");
    }
    let last = n - 1;
    script.push_str(&format!(
        "(declare-const v Int)\n\
         (assert (= v (select (select {prev} base) off)))\n\
         (assert (not (= v {last})))\n\
         (check-sat)\n"
    ));
    assert_eq!(run_script(&script), SolverResult::Unsat);
}
