//! Regression: the pure-BV dispatch's blastable-fragment memo must be
//! solver-owned, never thread-local.
//!
//! TermIds are manager-relative: two `Context`s on one thread assign the
//! same ids to unrelated terms.  When the memo was a `thread_local!` set,
//! solver A (a pure QF_BV script) populated it with ids *it* had proven
//! blastable; solver B – a fresh manager reusing those ids for a
//! UF-bearing formula – then read A's entries as positives, the
//! `all_assertions_bv_fragment` flag stayed up, and the pure-BV dispatch
//! received an unblastable assertion whose UF atoms the blast encoder
//! cannot represent.  This test is that exact shape: if the memo leaks
//! across managers, B answers `sat` to an unsat formula.
//!
//! (Landed with the fix that moved the memo onto `Solver`
//! (`blastable_memo`), where one solver = one manager makes
//! cross-manager reads impossible.)

use nixie_solver::Context;

#[test]
fn blastable_memo_does_not_leak_across_contexts_on_one_thread() {
    // Solver A: several bit-vector terms – with a thread-local memo this
    // caches ids 0..~6 as proven blastable.
    let mut a = Context::new();
    let a_script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (bvadd x #x01) y))
        (assert (= (bvmul x y) #x06))
        (assert (bvult (bvand x #x0f) #x10))
        (check-sat)
    "#;
    let a_responses = a
        .execute_script(a_script)
        .unwrap_or_else(|e| panic!("solver A script failed: {e:?}"));
    assert!(
        a_responses.iter().any(|r| r.eq_ignore_ascii_case("sat")),
        "solver A (pure QF_BV) did not answer sat: {a_responses:?}"
    );

    // Solver B, same thread, fresh manager: ids restart at zero, so B's
    // `(f #x01)` application would land on an id A proved blastable.  The
    // formula is unsat through the UF equality; a leaked memo routes it to
    // the pure-BV dispatch, the encoder cannot blast `f`, and the atoms
    // drop – answering `sat`.
    let mut b = Context::new();
    let b_script = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (assert (= (f #x01) #x01))
        (assert (distinct (f #x01) #x01))
        (check-sat)
    "#;
    let b_responses = b
        .execute_script(b_script)
        .unwrap_or_else(|e| panic!("solver B script failed: {e:?}"));
    let out = b_responses
        .last()
        .unwrap_or_else(|| panic!("solver B produced no answer"))
        .to_ascii_lowercase();
    assert_eq!(
        out, "unsat",
        "solver B answered {out}: the blastable-fragment memo leaked from \
         solver A (thread-local TermId collision across managers)"
    );

    // And interleaved re-checks keep both answers stable (the memo is
    // consulted again on later asserts; no cross-poisoning may appear
    // after B has populated its own memo either).
    let a_again = a
        .execute_script("(check-sat)")
        .unwrap_or_else(|e| panic!("solver A recheck failed: {e:?}"));
    let a_out = a_again
        .last()
        .unwrap_or_else(|| panic!("solver A produced no answer on recheck"))
        .to_ascii_lowercase();
    assert_eq!(
        a_out, "sat",
        "solver A changed its answer after solver B ran: {a_out}"
    );
}
