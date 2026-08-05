//! Unit tests for the non-Bool `ite` elimination and compound Bool
//! UF-argument abstraction pre-passes.
//!
//! Split out as a child module of `bool_euf_encoding`, mirroring
//! `encode/tests.rs`'s and `euf/solver/tests.rs`'s precedent.
use super::*;
use crate::solver::SolverResult;
use oxiz_core::sort::SortKind;

/// Intern a fresh uninterpreted sort named `name`, mirroring the pattern used
/// by `mbqi::integration::tests` (there is no `declare_uninterpreted`
/// shorthand on `Sorts`; SMT-LIB `declare-sort` itself goes through this same
/// `intern_str` + `SortKind::Uninterpreted` route in the parser).
fn uninterpreted_sort(manager: &mut TermManager, name: &str) -> oxiz_core::sort::SortId {
    let spur = manager.intern_str(name);
    manager.sorts.intern(SortKind::Uninterpreted(spur))
}

/// A non-Bool `ite` reachable from `term` must be replaced by a fresh
/// variable, and the two branch-selecting side-conditions must be conjoined.
#[test]
fn test_eliminate_nonbool_ite_replaces_uninterpreted_sort_ite() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let u = uninterpreted_sort(&mut manager, "U");
    let bool_sort = manager.sorts.bool_sort;

    let c = manager.mk_var("c", bool_sort);
    let t = manager.mk_var("t", u);
    let e = manager.mk_var("e", u);
    let a = manager.mk_var("a", u);
    let ite = manager.mk_ite(c, t, e);
    let term = manager.mk_eq(a, ite);

    let rewritten = solver.eliminate_nonbool_ite(term, &mut manager);
    assert_ne!(
        rewritten, term,
        "a term containing a non-Bool ite must change"
    );

    // The rewritten term must be a conjunction: the rewritten equality plus
    // (at least) the two branch-selection side-conditions.
    let rewritten_kind = manager.get(rewritten).expect("rewritten term exists");
    let TermKind::And(conjuncts) = &rewritten_kind.kind else {
        panic!("expected an And, got {:?}", rewritten_kind.kind);
    };
    assert!(
        conjuncts.len() >= 3,
        "expected the rewritten equality plus two side-conditions, got {conjuncts:?}"
    );
}

/// A term with no non-Bool `ite` at all must come back completely unchanged
/// (same `TermId`), not merely equivalent -- this is the fast-path guard
/// every `assert`/`assert_named` call pays for.
#[test]
fn test_eliminate_nonbool_ite_is_noop_without_ite() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let int_sort = manager.sorts.int_sort;
    let a = manager.mk_var("a", int_sort);
    let b = manager.mk_var("b", int_sort);
    let term = manager.mk_eq(a, b);

    let rewritten = solver.eliminate_nonbool_ite(term, &mut manager);
    assert_eq!(
        rewritten, term,
        "a term without ite must be returned unchanged"
    );
}

/// A non-Bool `ite` nested inside a quantifier's body must be left alone: the
/// fresh variable this pass introduces is unbound, so hoisting a subterm that
/// may depend on the bound variable out from under the quantifier would be
/// unsound (one global replacement cannot stand in for a value that differs
/// per instantiation).
#[test]
fn test_eliminate_nonbool_ite_does_not_descend_into_forall_body() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let u = uninterpreted_sort(&mut manager, "U");
    let bool_sort = manager.sorts.bool_sort;

    let x = manager.mk_var("x", u);
    let c = manager.mk_var("c", bool_sort);
    let t = manager.mk_var("t", u);
    // `(ite c t x)` inside the body -- mentions the bound variable `x`.
    let ite = manager.mk_ite(c, t, x);
    let body = manager.mk_eq(x, ite);
    let forall = manager.mk_forall([("x", u)], body);

    let rewritten = solver.eliminate_nonbool_ite(forall, &mut manager);
    assert_eq!(
        rewritten, forall,
        "an ite reachable only through a Forall body must not be touched"
    );
}

/// A compound Bool argument (`(and p q)`) passed to a UF must be abstracted
/// into a fresh Bool variable plus a defining equality.
#[test]
fn test_abstract_compound_bool_args_replaces_compound_arg() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let bool_sort = manager.sorts.bool_sort;
    let int_sort = manager.sorts.int_sort;

    let p = manager.mk_var("p", bool_sort);
    let q = manager.mk_var("q", bool_sort);
    let and_pq = manager.mk_and([p, q]);
    let h = manager.mk_apply("h", [and_pq], int_sort);
    let one = manager.mk_int(1);
    let term = manager.mk_eq(h, one);

    let rewritten = solver.abstract_compound_bool_args(term, &mut manager);
    assert_ne!(
        rewritten, term,
        "a compound Bool UF argument must trigger a rewrite"
    );
    let rewritten_kind = manager.get(rewritten).expect("rewritten term exists");
    let TermKind::And(conjuncts) = &rewritten_kind.kind else {
        panic!("expected an And, got {:?}", rewritten_kind.kind);
    };
    assert!(
        conjuncts.len() >= 2,
        "expected the rewritten equality plus the defining equality, got {conjuncts:?}"
    );
}

/// A plain `Var` used as a UF's Bool argument needs no rewriting -- but must
/// still be marked for Bool completion, or `f(b1)`/`f(b2)` for two
/// independent Bool variables the SAT assignment happens to make equal in
/// value would never be recognised as congruent.
#[test]
fn test_abstract_compound_bool_args_marks_plain_var_arg() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let bool_sort = manager.sorts.bool_sort;
    let int_sort = manager.sorts.int_sort;

    let b = manager.mk_var("b", bool_sort);
    let h = manager.mk_apply("h", [b], int_sort);
    let one = manager.mk_int(1);
    let term = manager.mk_eq(h, one);

    let rewritten = solver.abstract_compound_bool_args(term, &mut manager);
    assert_eq!(
        rewritten, term,
        "a plain Var argument needs no structural rewrite"
    );
    assert!(
        solver.bool_uf_arg_terms.contains(&b),
        "a plain Bool Var used as a UF argument must be marked for completion"
    );
}

/// A compound Bool argument reachable only through a quantifier's body must
/// not be abstracted -- same reasoning as the `ite` guard above.
#[test]
fn test_abstract_compound_bool_args_does_not_descend_into_forall_body() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let bool_sort = manager.sorts.bool_sort;
    let u = uninterpreted_sort(&mut manager, "U");
    let int_sort = manager.sorts.int_sort;

    let x = manager.mk_var("x", u);
    let p = manager.mk_var("p", bool_sort);
    let q = manager.mk_var("q", bool_sort);
    let and_pq = manager.mk_and([p, q]);
    let h = manager.mk_apply("h", [x, and_pq], int_sort);
    let one = manager.mk_int(1);
    let body = manager.mk_eq(h, one);
    let forall = manager.mk_forall([("x", u)], body);

    let rewritten = solver.abstract_compound_bool_args(forall, &mut manager);
    assert_eq!(
        rewritten, forall,
        "a compound Bool argument reachable only through a Forall body must not be touched"
    );
}

/// [`Solver::encode_nonbool_ite_equality`] must work correctly on its own,
/// standalone, without the whole-assertion `eliminate_nonbool_ite` pre-pass
/// ever running -- this is the shape MBQI instantiation and the axiom passes
/// hit, since they call [`Solver::encode`] directly rather than going through
/// [`Solver::assert`].
///
/// `(= (f u1) (ite c u2 u3))` with `(not c)` forces `(ite c u2 u3) = u3`, and
/// hence `(f u1) = u3` -- contradicting a separately asserted `(f u1) != u3`.
#[test]
fn test_encode_nonbool_ite_equality_backstop_without_assert_prepass() {
    let mut solver = Solver::new();
    let mut manager = TermManager::new();
    let u = uninterpreted_sort(&mut manager, "U");
    let bool_sort = manager.sorts.bool_sort;

    let c = manager.mk_var("c", bool_sort);
    let u1 = manager.mk_var("u1", u);
    let u2 = manager.mk_var("u2", u);
    let u3 = manager.mk_var("u3", u);
    let f_u1 = manager.mk_apply("f", [u1], u);
    let ite = manager.mk_ite(c, u2, u3);
    let eq = manager.mk_eq(f_u1, ite);

    // `check_core` short-circuits to `Sat` when `self.assertions` is empty
    // without ever running the SAT search -- assert a harmless `true` first
    // (via the ordinary `assert` path) purely so the search actually runs.
    // It carries no ite / compound-Bool content, so it is a no-op for both
    // pre-passes and does not interfere with the point of this test: the
    // *real* term below is encoded through `Solver::encode` directly, never
    // through `assert`'s pre-pass.
    let true_term = manager.mk_true();
    solver.assert(true_term, &mut manager);

    // Bypass `assert`'s pre-pass entirely: call `encode` directly, exactly
    // like MBQI instantiation and the axiom passes do.
    let eq_lit = solver.encode(eq, &mut manager);
    solver.sat.add_clause([eq_lit]);

    let not_c = manager.mk_not(c);
    let not_c_lit = solver.encode(not_c, &mut manager);
    solver.sat.add_clause([not_c_lit]);

    let f_u1_eq_u3 = manager.mk_eq(f_u1, u3);
    let f_u1_ne_u3 = manager.mk_not(f_u1_eq_u3);
    let ne_lit = solver.encode(f_u1_ne_u3, &mut manager);
    solver.sat.add_clause([ne_lit]);

    let result = solver.check(&mut manager);
    assert_eq!(
        result,
        SolverResult::Unsat,
        "the narrow backstop alone must catch this contradiction"
    );
}
