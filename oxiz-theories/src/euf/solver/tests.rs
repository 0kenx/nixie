//! Unit tests for the EUF congruence-closure solver.
//!
//! Split out of `euf/solver.rs` so that neither file approaches the 2000-line
//! ceiling.  Being a child module of `solver`, it still sees the private
//! fields and helpers the older tests inspect directly.

use super::*;

#[test]
fn test_euf_basic() {
    let mut solver = EufSolver::new();

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));

    assert!(!solver.are_equal(a, b));

    solver.merge(a, b, TermId::new(0)).unwrap_or(());
    assert!(solver.are_equal(a, b));

    solver.merge(b, c, TermId::new(0)).unwrap_or(());
    assert!(solver.are_equal(a, c));
}

#[test]
fn test_euf_diseq_conflict() {
    let mut solver = EufSolver::new();

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));

    // Assert a != b
    solver.assert_diseq(a, b, TermId::new(10));
    assert!(solver.check_conflicts().is_none());

    // Then assert a = b -> conflict
    solver.merge(a, b, TermId::new(11)).unwrap_or(());
    assert!(solver.check_conflicts().is_some());
}

// Audit regression (theories-euf): `Theory::assert_false` used to call
// `assert_diseq(node, node, term)` -- a node asserted disequal to
// ITSELF, which is unconditionally false in any congruence closure.
// That made every `assert_false` call an instant, fabricated
// contradiction regardless of what the term actually meant. It must no
// longer poison the solver this way.
#[test]
fn audit_assert_false_does_not_fabricate_self_contradiction() {
    use crate::theory::Theory;

    let mut solver = EufSolver::new();
    let term = TermId::new(1);

    let result = solver
        .assert_false(term)
        .expect("assert_false must not error");
    assert!(
        matches!(result, TheoryResult::Sat),
        "assert_false must not itself report Unsat"
    );

    // And `check()` afterward must not find a fabricated conflict
    // either -- previously it always did, for any term.
    let checked = solver.check().expect("check must not error");
    assert!(
        matches!(checked, TheoryResult::Sat),
        "check() after assert_false(term) must not be a fabricated Unsat; got {checked:?}"
    );
}

#[test]
fn test_euf_congruence() {
    let mut solver = EufSolver::new();

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));

    // f(a) and f(b)
    let fa = solver.intern_app(TermId::new(3), 0, [a]);
    let fb = solver.intern_app(TermId::new(4), 0, [b]);

    assert!(!solver.are_equal(fa, fb));

    // Merge a and b -> f(a) = f(b) by congruence
    solver.merge(a, b, TermId::new(0)).unwrap_or(());
    assert!(solver.are_equal(fa, fb));
}

#[test]
fn test_use_list_append_undone_by_pop() {
    // Regression (audit theories-p3, deferral a): an application interned in a
    // scope appends its index to the use-list of its pre-existing argument;
    // pop() must remove that entry so a reused node index cannot corrupt
    // congruence later.
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let before = solver.use_list[a as usize].len();

    solver.push();
    let _fa = solver.intern_app(TermId::new(2), 0, [a]);
    assert_eq!(
        solver.use_list[a as usize].len(),
        before + 1,
        "interning f(a) must extend a's use-list"
    );
    solver.pop();
    assert_eq!(
        solver.use_list[a as usize].len(),
        before,
        "pop() must undo the use-list append on the pre-existing arg"
    );
}

#[test]
fn test_use_list_merge_extension_undone_by_pop() {
    // Regression (audit theories-p3, deferral a): merge() splices one class's
    // use-list into the survivor's. A scoped merge must be fully undone by
    // pop(), including the use-list extension on the pre-existing root.
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let _fa = solver.intern_app(TermId::new(3), 0, [a]);
    let _fb = solver.intern_app(TermId::new(4), 0, [b]);

    let la = solver.use_list[a as usize].len();
    let lb = solver.use_list[b as usize].len();

    solver.push();
    solver
        .merge(a, b, TermId::new(0))
        .expect("merge must not error");
    solver.pop();

    assert_eq!(solver.use_list[a as usize].len(), la);
    assert_eq!(solver.use_list[b as usize].len(), lb);
    // After pop the merge is fully retracted: a and b are distinct again.
    assert!(!solver.are_equal(a, b));
}

#[test]
fn test_euf_explanation_simple() {
    let mut solver = EufSolver::new();

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));

    // Assert a = b (reason 10)
    solver.merge(a, b, TermId::new(10)).unwrap_or(());

    // Assert b = c (reason 11)
    solver.merge(b, c, TermId::new(11)).unwrap_or(());

    // Assert a != c (reason 12)
    solver.assert_diseq(a, c, TermId::new(12));

    // Now check - should have conflict with explanation containing reasons 10, 11, 12
    let conflict = solver.check_conflicts();
    assert!(conflict.is_some());

    if let Some(reasons) = conflict {
        // Should contain the disequality reason
        assert!(reasons.contains(&TermId::new(12)));
        // Should contain at least one of the equality reasons
        assert!(reasons.len() >= 2);
    }
}

#[test]
fn test_euf_explanation_congruence() {
    let mut solver = EufSolver::new();

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));

    // f(a) and f(b)
    let fa = solver.intern_app(TermId::new(3), 0, [a]);
    let fb = solver.intern_app(TermId::new(4), 0, [b]);

    // Assert f(a) != f(b) (reason 20)
    solver.assert_diseq(fa, fb, TermId::new(20));

    // Assert a = b (reason 21) -> causes f(a) = f(b) by congruence
    solver.merge(a, b, TermId::new(21)).unwrap_or(());

    // Check - should have conflict
    let conflict = solver.check_conflicts();
    assert!(conflict.is_some());

    if let Some(reasons) = conflict {
        // Should contain the disequality reason
        assert!(reasons.contains(&TermId::new(20)));
        // Should contain the equality reason that caused congruence
        assert!(reasons.contains(&TermId::new(21)));
    }
}

#[test]
fn test_euf_transitivity_explanation() {
    let mut solver = EufSolver::new();

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));
    let d = solver.intern(TermId::new(4));

    // Assert a = b (reason 100)
    solver.merge(a, b, TermId::new(100)).unwrap_or(());

    // Assert b = c (reason 101)
    solver.merge(b, c, TermId::new(101)).unwrap_or(());

    // Assert c = d (reason 102)
    solver.merge(c, d, TermId::new(102)).unwrap_or(());

    // Assert a != d (reason 103)
    solver.assert_diseq(a, d, TermId::new(103));

    // Check - should have conflict
    let conflict = solver.check_conflicts();
    assert!(conflict.is_some());

    if let Some(reasons) = conflict {
        // Should contain the disequality reason
        assert!(reasons.contains(&TermId::new(103)));
        // Should have multiple reasons from the equality chain
        assert!(reasons.len() >= 2);
    }
}

#[test]
fn test_commutative_function() {
    let mut solver = EufSolver::new();

    // Register a commutative function (e.g., addition)
    solver.register_function(
        0,
        FunctionProperties {
            associative: false,
            commutative: true,
            has_identity: false,
        },
    );

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));

    // f(a, b) and f(b, a) are congruent under commutativity.
    let fab = solver.intern_app(TermId::new(3), 0, [a, b]);
    let fba = solver.intern_app(TermId::new(4), 0, [b, a]);

    // They must be *equal*, not the same node. `intern_app` deliberately gives
    // every new term its own node and records the congruence as a retractable
    // merge; sharing the index would make the equality outlive the argument
    // classes that justify it (see `intern_app`'s docs).
    assert_ne!(fab, fba, "each term gets its own node");
    assert!(
        solver.are_equal(fab, fba),
        "f(a,b) and f(b,a) must be merged by commutative congruence"
    );
}

#[test]
fn test_associative_function() {
    let mut solver = EufSolver::new();

    // Register an associative function (e.g., addition)
    solver.register_function(
        0,
        FunctionProperties {
            associative: true,
            commutative: false,
            has_identity: false,
        },
    );

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));

    // f(a, b)
    let fab = solver.intern_app(TermId::new(10), 0, [a, b]);

    // f(f(a, b), c) should be flattened to f(a, b, c)
    let fab_c = solver.intern_app(TermId::new(11), 0, [fab, c]);

    // Verify that the node has 3 arguments (flattened)
    let node = &solver.nodes[fab_c as usize];
    assert_eq!(node.args.len(), 3);
}

#[test]
fn test_associative_commutative_function() {
    let mut solver = EufSolver::new();

    // Register an associative and commutative function (e.g., addition)
    solver.register_function(
        0,
        FunctionProperties {
            associative: true,
            commutative: true,
            has_identity: false,
        },
    );

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));

    // f(a, b)
    let fab = solver.intern_app(TermId::new(10), 0, [a, b]);

    // f(c, f(a, b)) should be flattened and canonicalized
    let c_fab = solver.intern_app(TermId::new(11), 0, [c, fab]);

    // f(f(b, a), c) should be flattened and canonicalized to the same thing
    let fba = solver.intern_app(TermId::new(12), 0, [b, a]);
    let fba_c = solver.intern_app(TermId::new(13), 0, [fba, c]);

    // Due to commutativity and associativity, they are congruent — and so are
    // merged into one class rather than collapsed onto one node.
    assert_ne!(c_fab, fba_c, "each term gets its own node");
    assert!(
        solver.are_equal(c_fab, fba_c),
        "f(c, f(a,b)) and f(f(b,a), c) must be merged by AC congruence"
    );
}

#[test]
fn test_fingerprint_basic() {
    // Same func and args should produce the same fingerprint
    let fp1 = ENodeFingerprint::compute(0, &[1, 2, 3]);
    let fp2 = ENodeFingerprint::compute(0, &[1, 2, 3]);
    assert_eq!(fp1, fp2);

    // Different args should (almost certainly) produce different fingerprints
    let fp3 = ENodeFingerprint::compute(0, &[1, 2, 4]);
    assert_ne!(fp1, fp3);

    // Different func should produce different fingerprint
    let fp4 = ENodeFingerprint::compute(1, &[1, 2, 3]);
    assert_ne!(fp1, fp4);
}

#[test]
fn test_fingerprint_empty_args() {
    let fp1 = ENodeFingerprint::compute(5, &[]);
    let fp2 = ENodeFingerprint::compute(5, &[]);
    assert_eq!(fp1, fp2);

    let fp3 = ENodeFingerprint::compute(6, &[]);
    assert_ne!(fp1, fp3);
}

#[test]
fn test_congruence_with_fingerprint_prefilter() {
    // Verify congruence closure still works correctly with fingerprint optimization
    let mut solver = EufSolver::new();

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));

    // g(a, c) and g(b, c)
    let gac = solver.intern_app(TermId::new(10), 1, [a, c]);
    let gbc = solver.intern_app(TermId::new(11), 1, [b, c]);

    assert!(!solver.are_equal(gac, gbc));

    // Merge a and b -> g(a,c) = g(b,c) by congruence
    solver.merge(a, b, TermId::new(50)).unwrap_or(());
    assert!(solver.are_equal(gac, gbc));
}

#[test]
fn test_fingerprint_table_populated() {
    let mut solver = EufSolver::new();

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));

    let _fa = solver.intern_app(TermId::new(3), 0, [a]);
    let _fb = solver.intern_app(TermId::new(4), 0, [b]);

    // There should be entries in the fingerprint table
    assert!(solver.fingerprint_table_len() > 0);
}

#[test]
fn test_push_pop_rebuilds_fingerprint_table() {
    use crate::theory::Theory;

    let mut solver = EufSolver::new();

    let a = solver.intern(TermId::new(1));

    solver.push();

    let b = solver.intern(TermId::new(2));
    let _fa = solver.intern_app(TermId::new(3), 0, [a]);
    let _fb = solver.intern_app(TermId::new(4), 0, [b]);

    let fp_count_before = solver.fingerprint_table_len();
    assert!(fp_count_before > 0);

    solver.pop();

    // After pop, fingerprint table should be rebuilt (possibly smaller)
    let fp_count_after = solver.fingerprint_table_len();
    assert!(fp_count_after <= fp_count_before);
}

#[test]
fn test_batch_sig_updates_correctness() {
    // Test that batch signature updates produce correct congruence results
    // with multiple function applications
    let mut solver = EufSolver::new();

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));
    let d = solver.intern(TermId::new(4));

    // f(a, c) and f(b, d)
    let fac = solver.intern_app(TermId::new(10), 0, [a, c]);
    let fbd = solver.intern_app(TermId::new(11), 0, [b, d]);

    assert!(!solver.are_equal(fac, fbd));

    // Merge a=b and c=d -> should trigger congruence f(a,c) = f(b,d)
    solver.merge(a, b, TermId::new(50)).unwrap_or(());
    solver.merge(c, d, TermId::new(51)).unwrap_or(());
    assert!(solver.are_equal(fac, fbd));
}

#[test]
fn test_reset_clears_fingerprint_table() {
    use crate::theory::Theory;

    let mut solver = EufSolver::new();

    let a = solver.intern(TermId::new(1));
    let _fa = solver.intern_app(TermId::new(2), 0, [a]);

    assert!(solver.fingerprint_table_len() > 0);

    solver.reset();

    assert_eq!(solver.fingerprint_table_len(), 0);
}

/// Test that the fingerprint pre-filter does not cause false negatives:
/// - Merging unrelated args must NOT produce spurious congruence merges.
/// - Merging the right args MUST still produce congruence merges.
#[test]
fn test_fingerprint_prefilter_short_circuits() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));
    let f_sym = 100u32;
    let fa = solver.intern_app(TermId::new(10), f_sym, [a]);
    let fb = solver.intern_app(TermId::new(11), f_sym, [b]);

    // Merge a = c (NOT a = b)
    solver.merge(a, c, TermId::new(20)).unwrap_or(());
    // f(a) and f(b) should NOT be merged (root(a) != root(b))
    assert!(
        !solver.are_equal(fa, fb),
        "f(a) and f(b) should not be merged without a=b"
    );

    // Now merge a = b (so root(a) == root(b))
    solver.merge(a, b, TermId::new(21)).unwrap_or(());
    // After a=b, congruence should derive f(a)=f(b)
    assert!(
        solver.are_equal(fa, fb),
        "f(a) and f(b) should be merged after a=b"
    );
}

/// Test the critical invariant: multi-step merges that route through an
/// intermediate shared root must still produce congruence.
/// This catches the bug where Change A's `continue` skips the fingerprint-table
/// update, leaving the invariant broken for subsequent merges.
#[test]
fn test_fingerprint_prefilter_invariant_multi_merge() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));
    let f_sym = 200u32;
    let fa = solver.intern_app(TermId::new(10), f_sym, [a]);
    let fb = solver.intern_app(TermId::new(11), f_sym, [b]);

    // merge(a, c): fa re-canonicalizes to f([c]); new fp may not be in table yet.
    // The pre-filter must still update fingerprint_table so the next step works.
    solver.merge(a, c, TermId::new(20)).unwrap_or(());
    assert!(
        !solver.are_equal(fa, fb),
        "f(a) and f(b) should not be merged yet"
    );

    // merge(b, c): fb re-canonicalizes to f([c]); fp IS now in table; congruence fires.
    solver.merge(b, c, TermId::new(21)).unwrap_or(());
    assert!(
        solver.are_equal(fa, fb),
        "f(a) and f(b) should be merged after a=c and b=c (both share root c)"
    );
}

/// Verify that using the reusable canon_buf (Change A) does not corrupt results
/// when two different intern_app calls with different arities share the same solver.
/// The buffer is cleared and refilled each iteration, so results must remain correct
/// even across applications with different argument lists.
#[test]
fn test_canonicalize_buf_is_reused() {
    let mut solver = EufSolver::new();

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));

    let f_sym = 300u32;

    // Two applications with different argument sets
    let fab = solver.intern_app(TermId::new(10), f_sym, [a, b]);
    let fbc = solver.intern_app(TermId::new(11), f_sym, [b, c]);

    // Neither should be equal to each other initially
    assert!(!solver.are_equal(fab, fbc));

    // Merging a = b triggers propagate, which exercises the reused canon_buf
    // on use-list entries for both f(a,b) and f(b,c).
    solver.merge(a, b, TermId::new(50)).unwrap_or(());

    // f(a,b) has canonical args [root(a), root(b)] = [r, r]; if root(b) = root(c) differs
    // they must still be distinct.
    assert!(!solver.are_equal(fab, fbc));

    // Now merge b = c so the solver exercises propagate again with the same buf
    solver.merge(b, c, TermId::new(51)).unwrap_or(());

    // After a=b and b=c, a=b=c.  f(a,b) canonical = [root, root], f(b,c) = [root, root]
    // so congruence must unify them.
    assert!(
        solver.are_equal(fab, fbc),
        "f(a,b) and f(b,c) must be equal once a=b=c"
    );
}

/// Verify that the incremental sig_trail correctly restores sig_table and
/// fingerprint_table to exactly the pre-push state, matching what a full
/// rebuild would have produced.
#[test]
fn test_incremental_sig_trail_matches_rebuild() {
    use crate::theory::Theory;

    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let f_sym = 100u32;
    let fa = solver.intern_app(TermId::new(10), f_sym, [a]);
    // Capture state BEFORE push
    let sig_before = solver.sig_table_len();
    let fp_before = solver.fingerprint_table_len();

    solver.push();
    let c = solver.intern(TermId::new(3));
    let fc = solver.intern_app(TermId::new(11), f_sym, [c]);
    solver.merge(a, c, TermId::new(20)).expect("merge a=c");
    // Now pop — should restore to pre-push state
    solver.pop();

    let sig_after = solver.sig_table_len();
    let fp_after = solver.fingerprint_table_len();
    assert_eq!(
        sig_before, sig_after,
        "sig_table size should match pre-push state after pop"
    );
    assert_eq!(
        fp_before, fp_after,
        "fingerprint_table size should match pre-push state after pop"
    );
    // The merge done during the push scope must be undone
    assert!(
        !solver.are_equal(fa, fc),
        "terms merged during push scope should not be equal after pop"
    );
    let _ = (b, fc);
}

/// Verify that a 3-level push/pop stack completely rewinds all sig/fp state.
#[test]
fn test_push_pop_stack_depth_3() {
    use crate::theory::Theory;

    let mut solver = EufSolver::new();
    let f = 100u32;
    let a = solver.intern(TermId::new(1));

    // Level 1
    solver.push();
    let b = solver.intern(TermId::new(2));
    let fab = solver.intern_app(TermId::new(10), f, [a, b]);

    // Level 2
    solver.push();
    let c = solver.intern(TermId::new(3));
    let fbc = solver.intern_app(TermId::new(11), f, [b, c]);
    solver.merge(a, b, TermId::new(20)).expect("merge a=b");

    // Level 3
    solver.push();
    let d = solver.intern(TermId::new(4));
    solver.merge(b, c, TermId::new(21)).expect("merge b=c");

    // Pop all three levels
    solver.pop(); // back to level 2 state
    solver.pop(); // back to level 1 state
    solver.pop(); // back to initial state

    // After all pops, no merges should remain
    assert!(
        !solver.are_equal(a, b),
        "a and b should not be equal after full pop"
    );
    let _ = (fab, fbc, c, d);
}

#[test]
fn test_function_application_entries_basic() {
    // f(a) and g(b) with func ids 7 and 8 respectively.
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let _fa = solver.intern_app(TermId::new(3), 7, [a]);
    let _gb = solver.intern_app(TermId::new(4), 8, [b]);

    // Only the application of func 7 is reported.
    let entries = solver.function_application_entries(7);
    assert_eq!(entries.len(), 1, "exactly one application of func 7");
    let e = &entries[0];
    assert_eq!(e.arg_reps.len(), 1);
    // The argument class of a contains a's TermId (1).
    assert!(e.arg_class_terms[0].contains(&TermId::new(1)));
    // The result class contains the application term itself (3).
    assert!(e.result_class_terms.contains(&TermId::new(3)));

    // A function with no applications yields no entries.
    assert!(solver.function_application_entries(9).is_empty());
}

#[test]
fn test_function_application_entries_congruence_collapses_arg_reps() {
    // f(a), f(b); after a = b the two applications must share arg_reps and
    // result_rep so a model builder deduplicates them into one entry.
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let f = 42u32;
    let _fa = solver.intern_app(TermId::new(10), f, [a]);
    let _fb = solver.intern_app(TermId::new(11), f, [b]);

    // Before merge: two applications with DISTINCT argument reps.
    let before = solver.function_application_entries(f);
    assert_eq!(before.len(), 2);
    assert_ne!(
        before[0].arg_reps, before[1].arg_reps,
        "f(a) and f(b) have distinct arg reps before a=b"
    );

    // Merge a = b -> congruence unifies f(a) and f(b).
    solver.merge(a, b, TermId::new(20)).expect("merge a=b");

    let after = solver.function_application_entries(f);
    assert_eq!(after.len(), 2, "still two application nodes are reported");
    // ...but they now share the same canonical argument and result class,
    // which is exactly the dedup key a model builder relies on.
    assert_eq!(
        after[0].arg_reps, after[1].arg_reps,
        "after a=b the two applications must share canonical arg reps"
    );
    assert_eq!(
        after[0].result_rep, after[1].result_rep,
        "after a=b the two applications are in the same result class"
    );
    // The shared result class contains both application terms.
    assert!(after[0].result_class_terms.contains(&TermId::new(10)));
    assert!(after[0].result_class_terms.contains(&TermId::new(11)));
}

#[test]
fn test_function_application_entries_multi_arg() {
    // h(a, c) and h(b, c); after a = b they collapse on arg reps.
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));
    let h = 5u32;
    let _hac = solver.intern_app(TermId::new(10), h, [a, c]);
    let _hbc = solver.intern_app(TermId::new(11), h, [b, c]);

    solver.merge(a, b, TermId::new(20)).expect("merge a=b");

    let entries = solver.function_application_entries(h);
    assert_eq!(entries.len(), 2);
    // Both arg positions canonicalize identically (a~b, and shared c).
    assert_eq!(entries[0].arg_reps.len(), 2);
    assert_eq!(entries[0].arg_reps, entries[1].arg_reps);
}

#[test]
fn test_enode_size_regression() {
    // Guards against ENode growing larger than expected.
    // ENode fields: func (4B), fingerprint (8B), args (SmallVec=32B), term (4B)
    // With alignment padding the size should be ≤ 56 bytes.
    let size = std::mem::size_of::<ENode>();
    assert!(size <= 56, "ENode size should be ≤56 bytes, got {}", size);
}

#[test]
fn test_leaf_constructor_uses_sentinel() {
    let t = TermId::from(42u32);
    let node = ENode::leaf(t);
    assert!(!node.is_app(), "leaf node should not be an app");
    assert_eq!(
        node.func,
        ENode::NO_FUNC,
        "leaf node func should be NO_FUNC sentinel"
    );
    assert!(node.args.is_empty(), "leaf node should have no args");
}

// ──────────────────────────────────────────────────────────────────
// The explanation engine is complete or absent — never partial
// ──────────────────────────────────────────────────────────────────

/// A congruence between two applications of a *commutative* symbol is justified
/// by a matching of the arguments, not by their positions.
///
/// `f(a, b)` and `f(d, c)` are congruent once `a = c` and `b = d`, because the
/// canonical signature of a commutative symbol is sorted.  Zipping the argument
/// lists positionally pairs `a` with `d` and `b` with `c` — neither pair is
/// equal, so both sub-goals were dropped and the conflict core came back holding
/// only the disequality.  That core is not weaker, it is wrong: `f(a,b) ≠ f(d,c)`
/// alone has plenty of models.
#[test]
fn commutative_congruence_explanation_names_the_argument_equalities() {
    let mut solver = EufSolver::new();
    let f = 3u32;
    solver.register_function(
        f,
        FunctionProperties {
            associative: false,
            commutative: true,
            has_identity: false,
        },
    );

    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));
    let d = solver.intern(TermId::new(4));

    solver.merge(a, c, TermId::new(41)).expect("merge a=c");
    solver.merge(b, d, TermId::new(42)).expect("merge b=d");

    let fab = solver.intern_app(TermId::new(10), f, [a, b]);
    let fdc = solver.intern_app(TermId::new(11), f, [d, c]);
    assert!(
        solver.are_equal(fab, fdc),
        "sorted canonical signatures make f(a,b) and f(d,c) congruent"
    );

    solver.assert_diseq(fab, fdc, TermId::new(43));
    let core = solver
        .check_conflicts()
        .expect("f(a,b) = f(d,c) contradicts f(a,b) != f(d,c)");

    assert!(
        core.contains(&TermId::new(43)),
        "core must cite the disequality, got {core:?}"
    );
    assert!(
        core.contains(&TermId::new(41)) && core.contains(&TermId::new(42)),
        "core must cite BOTH argument equalities that make the two applications \
         congruent; without them it claims the disequality alone is \
         contradictory. got {core:?}"
    );
}

/// The conservative fallback core is sound: replaying only the reasons it names
/// reproduces the conflict.
///
/// `check_conflicts` falls back to `all_asserted_reasons` when congruence
/// closure cannot produce a complete explanation — an invariant violation that
/// nothing is expected to trigger.  Its *correctness* is testable regardless:
/// the set it returns is every reason EUF currently rests on, so replaying it
/// into a fresh solver must recreate the conflict, and it must be a superset of
/// the precise explanation it stands in for.
#[test]
fn conservative_core_covers_every_live_reason() {
    let mut solver = EufSolver::new();
    let f = 5u32;
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));
    let fa = solver.intern_app(TermId::new(10), f, [a]);
    let fc = solver.intern_app(TermId::new(11), f, [c]);

    // A retracted assertion must not appear in the conservative core.
    solver.push();
    solver
        .merge(b, c, TermId::new(90))
        .expect("scoped merge b=c");
    solver.pop();

    solver.merge(a, b, TermId::new(50)).expect("merge a=b");
    solver.merge(b, c, TermId::new(51)).expect("merge b=c");
    solver.assert_diseq(fa, fc, TermId::new(52));

    let conservative = solver.all_asserted_reasons();
    for live in [TermId::new(50), TermId::new(51), TermId::new(52)] {
        assert!(
            conservative.contains(&live),
            "the conservative core must name every live reason; {live:?} is \
             missing from {conservative:?}"
        );
    }
    assert!(
        !conservative.contains(&TermId::new(90)),
        "the conservative core must not name a retracted assertion: \
         {conservative:?}"
    );

    // It is a superset of the precise explanation it substitutes for.
    let precise = solver
        .try_explain_eq(fa, fc)
        .expect("the congruence has a complete explanation");
    for term in &precise {
        assert!(
            conservative.contains(term),
            "the conservative core must subsume the precise one; {term:?} is \
             missing"
        );
    }

    // And replaying only its reasons reproduces the conflict.
    let mut replay = EufSolver::new();
    let ra = replay.intern(TermId::new(1));
    let rb = replay.intern(TermId::new(2));
    let rc = replay.intern(TermId::new(3));
    let rfa = replay.intern_app(TermId::new(10), f, [ra]);
    let rfc = replay.intern_app(TermId::new(11), f, [rc]);
    if conservative.contains(&TermId::new(50)) {
        replay.merge(ra, rb, TermId::new(50)).expect("replay a=b");
    }
    if conservative.contains(&TermId::new(51)) {
        replay.merge(rb, rc, TermId::new(51)).expect("replay b=c");
    }
    if conservative.contains(&TermId::new(52)) {
        replay.assert_diseq(rfa, rfc, TermId::new(52));
    }
    assert!(
        replay.check_conflicts().is_some(),
        "the conservative core must entail the conflict on its own"
    );
}

/// `check_conflicts` always names the violated disequality, whichever route the
/// explanation took.
#[test]
fn conflict_core_always_names_the_violated_disequality() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    solver.assert_diseq(a, b, TermId::new(70));
    solver.merge(a, b, TermId::new(71)).expect("merge a=b");

    let core = solver.check_conflicts().expect("conflict");
    assert!(core.contains(&TermId::new(70)));
    assert!(core.contains(&TermId::new(71)));
}
