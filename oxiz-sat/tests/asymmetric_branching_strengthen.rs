//! Regression test for SAT-1: `AsymmetricBranching::strengthen_clause` used to
//! be a no-op stub that always returned `None` regardless of input. This
//! verifies it now performs real asymmetric-literal-elimination / self-
//! subsuming resolution: given a background clause database that certifies a
//! literal is redundant, the clause is genuinely shortened.

use oxiz_sat::{AsymmetricBranching, Clause, ClauseDatabase, Lit, Var};

/// Crafted instance: `db` contains
///   C1 = (a ∨ b ∨ c)   -- the very clause under test, also stored in `db`
///   C3 = (¬a)          -- forces a false
///
/// Assuming ¬b ∧ ¬c (the negation of every literal other than `a`) and
/// propagating over `db`: C1 becomes unit on `a`, forcing `a` true; C3 then
/// directly contradicts that. The conflict certifies `db ⊨ (b ∨ c)`, so `a`
/// is redundant in C1 and must be dropped, shortening the clause from 3
/// literals to 2.
#[test]
fn strengthen_clause_drops_a_literal_certified_redundant_by_background_clauses() {
    let a = Var::new(0);
    let b = Var::new(1);
    let c = Var::new(2);

    let mut db = ClauseDatabase::new();
    // C1 = (a ∨ b ∨ c), stored as an original clause so it participates in
    // the propagation `strengthen_clause` runs internally.
    let c1 = [Lit::pos(a), Lit::pos(b), Lit::pos(c)];
    db.add(Clause::original(c1));
    // C3 = (¬a)
    db.add(Clause::original([Lit::neg(a)]));

    let mut ab = AsymmetricBranching::new(3);
    let result = ab.strengthen_clause(&c1, &db);

    let strengthened = result.expect("clause must be strengthened (literal `a` is redundant)");
    assert_eq!(
        strengthened.len(),
        2,
        "expected the clause to shrink from 3 to 2 literals, got {strengthened:?}"
    );
    assert!(
        !strengthened.contains(&Lit::pos(a)),
        "redundant literal `a` must be dropped, got {strengthened:?}"
    );
    assert!(
        strengthened.contains(&Lit::pos(b)) && strengthened.contains(&Lit::pos(c)),
        "the remaining literals must be exactly b and c, got {strengthened:?}"
    );

    let stats = ab.stats();
    assert_eq!(stats.attempts, 1);
    assert_eq!(stats.successes, 1);
    assert_eq!(stats.strengthened, 1);
    assert_eq!(stats.literals_removed, 1);
}

/// Without any background clauses to certify redundancy, no literal of a
/// freestanding clause can be proven droppable, so the clause must be left
/// untouched (`None`), not spuriously shortened.
#[test]
fn strengthen_clause_leaves_unconstrained_clause_untouched() {
    let a = Var::new(0);
    let b = Var::new(1);
    let c = Var::new(2);

    let db = ClauseDatabase::new();
    let mut ab = AsymmetricBranching::new(3);

    let clause = [Lit::pos(a), Lit::pos(b), Lit::pos(c)];
    let result = ab.strengthen_clause(&clause, &db);

    assert!(
        result.is_none(),
        "an unconstrained clause must not be strengthened, got {result:?}"
    );
}

/// `strengthen_all` must apply the same certified strengthening across an
/// entire database and replace the original (longer) clause with the
/// strengthened one.
#[test]
fn strengthen_all_shortens_a_clause_backed_by_a_forcing_unit() {
    let a = Var::new(0);
    let b = Var::new(1);
    let c = Var::new(2);

    let mut db = ClauseDatabase::new();
    let c1_id = db.add(Clause::original([Lit::pos(a), Lit::pos(b), Lit::pos(c)]));
    db.add(Clause::original([Lit::neg(a)]));

    let mut ab = AsymmetricBranching::new(3);
    let count = ab.strengthen_all(&mut db);

    assert_eq!(count, 1, "exactly one clause should have been strengthened");

    // The original 3-literal clause was removed and replaced by a shorter
    // learned clause containing only b and c.
    assert!(
        db.get(c1_id).is_none_or(|c| c.deleted),
        "the original 3-literal clause must be retired"
    );
    let shortened = db
        .iter_ids()
        .filter_map(|id| db.get(id))
        .find(|c| c.lits.len() == 2)
        .expect("a shortened 2-literal clause must exist in the database");
    assert!(!shortened.lits.contains(&Lit::pos(a)));
}
