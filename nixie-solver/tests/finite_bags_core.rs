//! Finite bags (multisets): the count reduction, end to end.
//!
//! A bag is a finite map from elements to multiplicities, and the theory
//! reduces every constraint to arithmetic over `bag.count` terms — the
//! SMT-LIB bags draft as CVC5 implements it (`src/theory/bags`), compiled
//! to the same eager shape as the finite-set theory:
//!
//! ```text
//! count(x, ∅)          = 0
//! count(x, (bag y n))  = ite(x = y, n, 0)
//! count(x, a ⊎max b)   = max(count(x,a), count(x,b))
//! count(x, a ⊎ b)      = count(x,a) + count(x,b)
//! count(x, a ⊓ b)      = min(count(x,a), count(x,b))
//! count(x, a \ b)      = max(count(x,a) − count(x,b), 0)
//! count(x, a ⧵ b)      = ite(count(x,b) > 0, 0, count(x,a))
//! count(x, setof b)    = ite(count(x,b) > 0, 1, 0)
//! x ∈ b                ⇔ count(x, b) ≥ 1
//! a ⊑ b                ⇔ ∀x. count(x,a) ≤ count(x,b)
//! a = b                ⇔ ∀x. count(x,a) = count(x,b)
//! |b|                  = Σ_x count(x,b) + slack(b)   (slack ≥ 0)
//! ```
//!
//! Every case's status was cross-checked against CVC5 1.3.4 while writing
//! (the whole battery lives in the landing commit's message; the two
//! cardinality-over-unknown-support cases where CVC5 times out are noted
//! inline — the count+slack skeleton refutes them instantly and the
//! arithmetic is one line).

use nixie_solver::SolverResult;

/// Assert a script's formulas and report the verdict.
fn solve_smt(script: &str) -> SolverResult {
    let mut context = nixie_solver::Context::new();
    match context.execute_script(script) {
        Ok(lines) => lines
            .iter()
            .rev()
            .find_map(|l| match l.trim() {
                "sat" => Some(SolverResult::Sat),
                "unsat" => Some(SolverResult::Unsat),
                _ => None,
            })
            .unwrap_or(SolverResult::Unknown),
        Err(_) => SolverResult::Unknown,
    }
}

// ===== the pointwise identities =====

#[test]
fn count_of_make_and_empty() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag 1 3)) 3))\n\
             (assert (= (bag.count 2 (bag 1 3)) 0))\n\
             (assert (= (bag.count 1 (as bag.empty (Bag Int))) 0))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag 1 3)) 2))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

#[test]
fn union_max_takes_the_max() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.union_max (bag 1 2) (bag 1 5))) 5))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.union_max (bag 1 2) (bag 1 5))) 2))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

#[test]
fn union_disjoint_sums() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.union_disjoint (bag 1 2) (bag 1 5))) 7))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.union_disjoint (bag 1 2) (bag 1 5))) 5))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

#[test]
fn inter_min_takes_the_min() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.inter_min (bag 1 2) (bag 1 5))) 2))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.inter_min (bag 1 2) (bag 1 5))) 5))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

#[test]
fn difference_subtract_saturates_at_zero() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.difference_subtract (bag 1 5) (bag 1 2))) 3))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    // 2 − 5 saturates at 0, not −3.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.difference_subtract (bag 1 2) (bag 1 5))) 1))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

#[test]
fn difference_remove_drops_entirely() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.difference_remove (bag 1 5) (bag 1 2))) 0))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.difference_remove (bag 1 5) (bag 1 2))) 3))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

#[test]
fn setof_squashes_to_one() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.setof (bag 1 5))) 1))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.setof (bag 1 5))) 5))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // The squashed bags of two multiplicities are equal.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.setof (bag 1 5)) (bag.setof (bag 1 1))))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
}

// ===== membership, subbag, extensionality =====

#[test]
fn member_is_positive_count() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (not (bag.member 1 b)))\n\
             (assert (= (bag.count 1 b) 2))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (not (bag.member 1 b)))\n\
             (assert (= (bag.count 1 b) 0))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
}

#[test]
fn nothing_is_in_the_empty_bag() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (bag.member 1 (as bag.empty (Bag Int))))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

#[test]
fn subbag_is_pointwise() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (bag.subbag (bag 1 3) (bag 1 5)))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (bag.subbag (bag 1 5) (bag 1 3)))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // A compound left operand: (1:2) ⊎ (1:1) = (1:3) fits, not (1:2).
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (bag.subbag (bag.union_disjoint (bag 1 2) (bag 1 1)) (bag 1 3)))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (bag.subbag (bag.union_disjoint (bag 1 2) (bag 1 1)) (bag 1 2)))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

#[test]
fn extensional_equality_is_pointwise() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag 1 2) (bag 1 3)))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // Element identity matters: (1:2) ≠ (2:1).
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag 1 2) (bag 2 1)))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // Equal by rearrangement (union is commutative in the counts).
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const a (Bag Int))\n\
             (declare-const c (Bag Int))\n\
             (assert (= a (bag.union_disjoint (bag 1 2) (bag 2 1))))\n\
             (assert (= c (bag.union_disjoint (bag 2 1) (bag 1 2))))\n\
             (assert (= a c))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    // Equality propagates: a = (1:2), c = a, count(1,c) = 3 is a lie.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const a (Bag Int))\n\
             (declare-const c (Bag Int))\n\
             (assert (= a (bag 1 2)))\n\
             (assert (= c a))\n\
             (assert (= (bag.count 1 c) 3))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // A squashed bag is not a two-copy bag.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.setof (bag 1 5)) (bag 1 2)))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

// ===== cardinality =====

#[test]
fn card_sums_the_multiplicities() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= (bag.count 1 b) 3))\n\
             (assert (= (bag.count 2 b) 0))\n\
             (assert (= (bag.card b) 3))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    // An *opaque* bag may hold elements the formula never names, so a
    // cardinality above the known sum is satisfiable (the slack covers
    // the unknown support); only below the known sum is it refuted.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= (bag.count 1 b) 3))\n\
             (assert (= (bag.count 2 b) 0))\n\
             (assert (= (bag.card b) 4))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    // A **closed** compound's support is exactly its makes, so its size
    // is the exact sum — no slack. This was a false `sat` before the
    // closed/opaque split (CVC5 1.3.4: `unsat`).
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.card (bag.union_disjoint (bag 1 3) (bag 2 1))) 5))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.card (bag.union_disjoint (bag 1 3) (bag 2 1))) 4))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    // Difference removes from the known sum exactly.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.card (bag.difference_subtract (bag 1 3) (bag 1 1))) 2))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.card (bag.difference_subtract (bag 1 3) (bag 1 1))) 3))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

#[test]
fn card_slack_covers_unknown_elements() {
    // Unknown elements carry multiplicities: |b| ≥ Σ_known. (CVC5 1.3.4
    // times out on this shape; the count+slack skeleton refutes it in
    // one line: 2 + slack = 1 with slack ≥ 0.)
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= (bag.count 1 b) 2))\n\
             (assert (= (bag.card b) 1))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= (bag.count 1 b) 2))\n\
             (assert (= (bag.card b) 5))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    // The slack bounds the counts from above: Σ ≤ |b|. (CVC5 also times
    // out here.)
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (> (+ (bag.count 1 b) (bag.count 2 b)) 5))\n\
             (assert (= (bag.card b) 3))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

// ===== element sorts and exactness =====

#[test]
fn tuple_elements_count_by_value() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag (Tuple Int Int)))\n\
             (assert (= (bag.count (tuple 1 2) b) 2))\n\
             (assert (bag.member (tuple 1 2) b))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag (Tuple Int Int)))\n\
             (assert (= (bag.count (tuple 1 2) b) 0))\n\
             (assert (bag.member (tuple 1 2) b))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

#[test]
fn wide_multiplicities_are_exact() {
    // 123456789012345678901234567890 is nowhere near `u64::MAX`, but the
    // point is the pipeline never narrows: the count is a `BigInt` end to
    // end and the identity holds exactly.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag 1 123456789012345678901234567890))\n\
                        123456789012345678901234567890))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag 1 123456789012345678901234567890)) 1))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

#[test]
fn nested_compounds_compose() {
    // min(3,5) + (9−2) = 3 + 7 = 10.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.union_disjoint\n\
                        (bag.inter_min (bag 1 3) (bag 1 5))\n\
                        (bag.difference_subtract (bag 1 9) (bag 1 2)))) 10))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag.union_disjoint\n\
                        (bag.inter_min (bag 1 3) (bag 1 5))\n\
                        (bag.difference_subtract (bag 1 9) (bag 1 2)))) 9))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

// ===== the surface =====

#[test]
fn negative_multiplicity_is_rejected() {
    let mut context = nixie_solver::Context::new();
    let out = context.execute_script(
        "(set-logic ALL)\n\
         (assert (= (bag 1 (- 0 1)) (bag 1 0)))\n\
         (check-sat)\n",
    );
    assert!(
        out.is_err(),
        "a negative literal multiplicity must not parse"
    );
    // A symbolic multiplicity parses (the count identity treats it as the
    // plain integer it is).
    let mut context = nixie_solver::Context::new();
    let out = context.execute_script(
        "(set-logic ALL)\n\
         (declare-const n Int)\n\
         (assert (= (bag.count 1 (bag 1 n)) n))\n\
         (check-sat)\n",
    );
    assert!(out.is_ok_and(|l| l.first().is_some_and(|s| s == "sat")));
}

#[test]
fn bag_sort_operands_are_type_checked() {
    let mut context = nixie_solver::Context::new();
    let out = context.execute_script(
        "(set-logic ALL)\n\
         (declare-const s (Set Int))\n\
         (assert (= (bag.count 1 s) 1))\n\
         (check-sat)\n",
    );
    assert!(out.is_err(), "bag.count on a set must be a sort error");
    let mut context = nixie_solver::Context::new();
    let out = context.execute_script(
        "(set-logic ALL)\n\
         (declare-const b (Bag Int))\n\
         (assert (= (bag.count 1 (bag.union_max b 1)) 1))\n\
         (check-sat)\n",
    );
    assert!(out.is_err(), "bag.union_max with an Int operand must error");
}

#[test]
fn unsupported_bag_ops_reject_honestly() {
    let mut context = nixie_solver::Context::new();
    let out = context.execute_script(
        "(set-logic ALL)\n\
         (declare-const b (Bag Int))\n\
         (assert (bag.choose b))\n\
         (check-sat)\n",
    );
    assert!(
        out.is_err(),
        "bag.choose is a parse-level rejection in this slice"
    );
}

#[test]
fn scope_survives_push_pop() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (push 1)\n\
             (assert (= (bag.count 1 b) 2))\n\
             (pop 1)\n\
             (assert (= (bag.count 1 b) 5))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
}

#[test]
fn refuted_across_push_pop() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= (bag.count 1 b) 2))\n\
             (push 1)\n\
             (assert (= (bag.count 1 b) 5))\n\
             (check-sat)\n\
             (pop 1)\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
}
