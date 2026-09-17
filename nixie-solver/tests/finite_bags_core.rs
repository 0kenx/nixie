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
fn negative_multiplicities_clamp_to_zero() {
    // CVC5 accepts negative literal multiplicities and clamps them:
    // `count(x, (bag y n)) = ite(x = y ∧ n ≥ 1, n, 0)` (differential-
    // tested: the count of `(bag 1 -5)` is 0, `(bag 1 -5)` = `(bag 1 -1)`,
    // and a count of -1 is unsatisfiable).
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag 1 -5)) 0))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.count 1 (bag 1 -1)) -1))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag 1 -5) (bag 1 -1)))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    // A symbolic multiplicity clamps too: n = -1 forces the count 0, not
    // -1 (differential-tested against CVC5).
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const n Int)\n\
             (assert (= n -1))\n\
             (assert (= (bag.count 1 (bag 1 n)) 0))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const n Int)\n\
             (assert (= n -1))\n\
             (assert (= (bag.count 1 (bag 1 n)) -1))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

#[test]
fn opaque_counts_are_nonnegative() {
    // A multiplicity is nonnegative; without the axiom a free count
    // column could go negative and `count(1,b) = -3` answered `sat`
    // (CVC5: `unsat`; found by differential testing).
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= (bag.count 1 b) -3))\n\
             (assert (= (bag.card b) -3))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

// ===== the model: count-driven values and the readback =====

/// A bag variable's value assembles from the counts the arithmetic
/// solver valued, and prints as the canonical disjoint union — so the
/// printed model re-reads as itself. The `@bag_ext_*` witnesses merge by
/// *value* into the element cells (they are ordinary elements the
/// tableau values, usually equal to a real one; their consistency axioms
/// force exactly that).
#[test]
fn bag_variable_value_prints() {
    let mut context = nixie_solver::Context::new();
    let out = context
        .execute_script(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= b (bag.union_disjoint (bag 1 2) (bag 2 5))))\n\
             (assert (= (bag.count 1 b) 2))\n\
             (check-sat)\n\
             (get-model)\n",
        )
        .expect("script executes");
    let joined = out.join("\n");
    assert!(joined.contains("sat"), "{joined}");
    assert!(
        joined.contains("(define-fun b () (Bag Int) (bag.union_disjoint (bag 1 2) (bag 2 5)))"),
        "the bag value must assemble from the counts: {joined}"
    );
}

/// `bag.count`, `bag.card` and `bag.member` queries answer with numbers
/// and Booleans — including *query-only* cards, whose assertion stack
/// never constrained one (folded from the installed value, which is
/// evaluation of a verified object, not a guess).
#[test]
fn bag_queries_answer() {
    let mut context = nixie_solver::Context::new();
    let out = context
        .execute_script(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= b (bag.union_disjoint (bag 1 2) (bag 2 5))))\n\
             (assert (= (bag.count 1 b) 2))\n\
             (check-sat)\n\
             (get-value ((bag.count 1 b) (bag.count 2 b) (bag.card b)\n\
                         (bag.member 1 b) (bag.member 3 b) b))\n",
        )
        .expect("script executes");
    let joined = out.join("\n");
    assert!(joined.contains("sat"), "{joined}");
    assert!(joined.contains("((bag.count 1 b) 2)"), "{joined}");
    assert!(joined.contains("((bag.count 2 b) 5)"), "{joined}");
    assert!(joined.contains("((bag.card b) 7)"), "{joined}");
    assert!(joined.contains("((bag.member 1 b) true)"), "{joined}");
    assert!(joined.contains("((bag.member 3 b) false)"), "{joined}");
    assert!(
        joined.contains("(b (bag.union_disjoint (bag 1 2) (bag 2 5)))"),
        "{joined}"
    );
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
    // `bag.choose` returns an element: asserting one is ill-sorted, and
    // the pipeline answers `unknown` (the encoder's `BagChoose` arm keeps
    // the honesty gate up) rather than guessing a meaning for it.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (bag.choose b))\n\
             (check-sat)\n",
        ),
        SolverResult::Unknown
    );
    let mut context = nixie_solver::Context::new();
    let out = context.execute_script(
        "(set-logic ALL)\n\
         (declare-const b (Bag Int))\n\
         (declare-fun f (Int) Int)\n\
         (assert (= (bag.map f b) b))\n",
    );
    assert!(
        out.is_err(),
        "bag.map is a parse-level rejection until function handling lands"
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

// ===== the fuzz campaign's finds (each was a wrong verdict) =====

/// `b = ∅ ∧ |b| = 1` must refute: equal bags have equal sizes, and `|∅|`
/// folds to 0 — the aggregate the per-element equations cannot see
/// through the slack. Without the rule this answered `sat` (fuzz-found;
/// CVC5: `unsat`; the set theory has always had the analogue).
#[test]
fn equality_forces_equal_cardinality() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= b (as bag.empty (Bag Int))))\n\
             (assert (= (bag.card b) 1))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // Through a squashing compound, same story.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= b (as bag.empty (Bag Int))))\n\
             (assert (= (bag.card (bag.setof b)) 1))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

/// The counting sum de-duplicates: a bag pinned to `(2:3)` keeps
/// `|(2:3)| = 3` even though the extensionality witnesses usually equal
/// the real elements — summing every spelling counted one cell twice,
/// forced the slack to absorb the duplicate, and pinned the witnesses
/// away from the values the disequality directions needed. This exact
/// shape answered `unsat` before the guards (CVC5: `sat`).
#[test]
fn counting_dedups_equal_valued_elements() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= b (bag 2 3)))\n\
             (assert (not (= (bag.setof b) (bag.inter_min (bag 1 3) (bag 2 2)))))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
}

/// The lattice rewrites: a max-union with `a` on either side already
/// covers every copy `a` has, so the subtract-difference is empty and
/// the remove-difference is empty — the pointwise identities close
/// shapes the element-list reduction cannot (fuzz-found false-`sat`;
/// CVC5: `unsat`).
#[test]
fn lattice_rewrites_close_difference_shapes() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const x Int)\n\
             (declare-const c (Bag Int))\n\
             (assert (= (bag.card (bag.setof c)) 2))\n\
             (assert (= (bag.card (bag.difference_subtract c\n\
                        (bag.union_max c (bag x 1)))) 2))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // Absorption: `a ⊓ (a ⊎ z) = a`, both operand orders.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const a (Bag Int))\n\
             (declare-const z (Bag Int))\n\
             (assert (not (= (bag.inter_min a (bag.union_max a z)) a)))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const a (Bag Int))\n\
             (declare-const z (Bag Int))\n\
             (assert (not (= (bag.inter_min (bag.union_disjoint a z) a) a)))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

/// `bag.count` is a function of the element: `¬((1:3) ⊑ b)` beside
/// `count(1,b) ≥ 5` must refute — the witness element (valued 1) needs
/// `count(witness, b) < 3`, and the witness's count equals `count(1,b)`
/// by congruence. The purified arithmetic encoding gave each count term
/// its own column with no congruence tie (an `apply` would get it from
/// the theory combination layer); this answered `sat` (fuzz-found;
/// CVC5: `unsat`).
#[test]
fn count_is_congruent_in_its_element() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (not (bag.subbag (bag 1 3) b)))\n\
             (assert (> (bag.count 1 b) 4))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

/// `a ⊑ b → |a| ≤ |b|`: a subbag against a closed bag forces the whole
/// (unknown-support) size down, not just the known elements —
/// `b ⊑ ((1:-1) ⧵ (x:0))` is `b ⊑ ∅`, which empties `b`, contradicting
/// `|b| = 2`. Answered `sat` before the rule (fuzz-found; CVC5:
/// `unsat`).
#[test]
fn subbag_bounds_the_cardinality() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const x Int)\n\
             (declare-const b (Bag Int))\n\
             (assert (bag.subbag b (bag.difference_remove (bag 1 -1) (bag x 0))))\n\
             (assert (= (bag.card b) 2))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (declare-const c (Bag Int))\n\
             (assert (bag.subbag b c))\n\
             (assert (= (bag.card b) 3))\n\
             (assert (= (bag.card c) 2))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

// ===== the ite/congruence holes (differential probes, pre-choose) =====

/// A bag-shaped `ite` is *determined* by its branches — its counts are
/// `ite(c, count(e,a), count(e,b))`, never free integers. Before the arm
/// landed, `count_definition` fell through to the opaque treatment and
/// `x ≤ 0 ∧ count(1, ite(x > 0, (1:2), (2:2))) = 1` answered `sat`
/// (CVC5: `unsat`; differential probe on the pre-choose binary).
#[test]
fn ite_bags_counts_follow_the_branches() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const x Int)\n\
             (declare-const y Int)\n\
             (assert (<= x 0))\n\
             (assert (= y 1))\n\
             (assert (= (bag.count 1 (ite (> x 0) (bag 1 2) (bag 2 2))) y))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // The other branch is live: `x > 0` makes the same count 2.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const x Int)\n\
             (assert (> x 0))\n\
             (assert (= (bag.count 1 (ite (> x 0) (bag 1 2) (bag 2 2))) 2))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    // An ite of closed bags is closed: its support is exactly the
    // branches' makes, so the cardinality is the exact sum — no slack.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const x Int)\n\
             (assert (= x 1))\n\
             (assert (= (bag.card (ite (> x 0) (bag 1 1) (bag 2 2))) 3))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

/// `|ite(c, a, b)| = ite(c, |a|, |b|)` exactly — over *opaque* operands
/// too, where the count identities alone tie the sums but not the ite's
/// own slack: `|A| = 5 ∧ b = ite(¬c, A, ∅) ∧ |b| = 6` must refute through
/// the ite's cardinality, not through branch support.
#[test]
fn ite_cardinality_is_the_branch_cardinality() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const c Bool)\n\
             (declare-const A (Bag Int))\n\
             (assert (= (bag.card A) 5))\n\
             (assert (= (bag.card (ite c A (as bag.empty (Bag Int)))) 6))\n\
             (assert (not c))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // With the branch live the sizes agree.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const c Bool)\n\
             (declare-const A (Bag Int))\n\
             (assert (= (bag.card A) 5))\n\
             (assert (= (bag.card (ite c A (as bag.empty (Bag Int)))) 5))\n\
             (assert c)\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
}

/// `bag.count` is a function of the bag **value**, so a *derived* equality
/// — EUF congruence `f x = f 0` from `x = 0` — ties the counts with no
/// surveyed equality atom anywhere. Before the pair-congruence pass the
/// purified encoding gave each count term its own integer column and
/// `x = 0 ∧ count(1, f x) = 2 ∧ count(1, f 0) = 5` answered `sat`
/// (CVC5: `unsat`). `bag.card` rides the same pairs.
#[test]
fn counts_follow_derived_equality_congruence() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-fun f (Int) (Bag Int))\n\
             (declare-const x Int)\n\
             (assert (= x 0))\n\
             (assert (= (bag.count 1 (f x)) 2))\n\
             (assert (= (bag.count 1 (f 0)) 5))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // The cardinality has the same hole through the slack columns.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-fun f (Int) (Bag Int))\n\
             (declare-const x Int)\n\
             (assert (= x 0))\n\
             (assert (= (bag.card (f x)) 2))\n\
             (assert (= (bag.card (f 0)) 5))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // A `select`-over-`store` bag is determined by the array theory's
    // axiom: `select(A, 0) = (bag 1 2)`, so its count of 1 is 2, not 7.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const A (Array Int (Bag Int)))\n\
             (assert (= A (store ((as const (Array Int (Bag Int))) (bag 1 1)) 0 (bag 1 2))))\n\
             (assert (= (bag.count 1 (select A 0)) 7))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // Subbag respects derived congruence: `f x ⊑ B ∧ ¬(f 0 ⊑ B) ∧ x = 0`
    // is a contradiction.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-fun f (Int) (Bag Int))\n\
             (declare-const B (Bag Int))\n\
             (declare-const x Int)\n\
             (assert (= x 0))\n\
             (assert (bag.subbag (f x) B))\n\
             (assert (not (bag.subbag (f 0) B)))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

// ===== bag.choose =====

/// The CVC5 `BAG_CHOOSE` semantics end to end: `choose` of a nonempty bag
/// is a member, congruent in the bag, and the builder folds
/// `choose (bag y c) = y` for a literal `c > 0` (CVC5's
/// `CHOOSE_BAG_MAKE`).
#[test]
fn choose_picks_a_member() {
    // The fold: `(bag.choose (bag 1 3))` is `1`.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (= (bag.choose (bag 1 3)) 1))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    // The only element of a singleton make is forced; refusing it refutes.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (assert (not (= (bag.choose (bag 5 2)) 5)))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // `card >= 1` (the formula's own cardinality) makes `choose` a member.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (>= (bag.card b) 1))\n\
             (assert (= (bag.count (bag.choose b) b) 0))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
    // Without the cardinality, the emptiness disjunction carries it:
    // `b = ∅ ∨ count(choose(b), b) >= 1` beside a nonzero count.
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= (bag.count 3 b) 2))\n\
             (assert (= (bag.choose b) 3))\n\
             (check-sat)\n",
        ),
        SolverResult::Sat
    );
    // The same shape with the count on the choose pinned to zero refutes
    // through the element congruence (`choose(b) = 3` ties the counts).
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= (bag.count 3 b) 2))\n\
             (assert (= (bag.choose b) 3))\n\
             (assert (= (bag.count (bag.choose b) b) 0))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

/// `choose` is a function of the bag: `a = c -> choose(a) = choose(c)`,
/// stated over the choose pairs (the set theory's discipline).
#[test]
fn choose_is_congruent() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const a (Bag Int))\n\
             (declare-const c (Bag Int))\n\
             (assert (= a c))\n\
             (assert (= (bag.count 1 a) 2))\n\
             (assert (>= (bag.card a) 1))\n\
             (assert (not (= (bag.choose a) (bag.choose c))))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

/// `choose(ite c a b) = ite c (choose a) (choose b)`: with `c` committed
/// the ite *is* its branch, so the chooses must agree.
#[test]
fn choose_unfolds_over_ite() {
    assert_eq!(
        solve_smt(
            "(set-logic ALL)\n\
             (declare-const c Bool)\n\
             (declare-const b (Bag Int))\n\
             (assert (= b (ite c (bag 1 1) (bag 2 1))))\n\
             (assert c)\n\
             (assert (not (= (bag.choose b) 1)))\n\
             (check-sat)\n",
        ),
        SolverResult::Unsat
    );
}

/// The model side: an asserted choose prints its committed value (and its
/// count follows); a query-only choose completes from the installed bag
/// value; the empty bag's choose is unspecified (any value models it, the
/// count is 0). The `count(3,b) = 2 ∧ choose(b) = 3` case is the
/// card-mint regression: the choose axiom must not mint `bag.card` for a
/// bag the formula never cardinalized — its slack column rolled the bag
/// back to `∅`.
#[test]
fn choose_models_and_queries() {
    // Committed equality: the choose prints the element, the count its
    // multiplicity.
    let mut context = nixie_solver::Context::new();
    let out = context
        .execute_script(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= b (bag.union_disjoint (bag 5 2) (bag 7 1))))\n\
             (assert (= (bag.choose b) 5))\n\
             (check-sat)\n\
             (get-value ((bag.choose b) (bag.count (bag.choose b) b)))\n",
        )
        .expect("script executes");
    let joined = out.join("\n");
    assert!(joined.contains("((bag.choose b) 5)"), "{joined}");
    assert!(
        joined.contains("((bag.count (bag.choose b) b) 2)"),
        "{joined}"
    );

    // Query-only choose: completes from the installed value — a member
    // with its multiplicity, never a falsifying 0.
    let mut context = nixie_solver::Context::new();
    let out = context
        .execute_script(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= b (bag.union_disjoint (bag 5 2) (bag 7 1))))\n\
             (check-sat)\n\
             (get-value ((bag.choose b) (bag.count (bag.choose b) b)\n                         (bag.member (bag.choose b) b)))\n",
        )
        .expect("script executes");
    let joined = out.join("\n");
    assert!(joined.contains("((bag.choose b) 7)"), "{joined}");
    assert!(
        joined.contains("((bag.count (bag.choose b) b) 1)"),
        "{joined}"
    );
    assert!(
        joined.contains("((bag.member (bag.choose b) b) true)"),
        "{joined}"
    );

    // The card-mint regression: the bag's own value must survive.
    let mut context = nixie_solver::Context::new();
    let out = context
        .execute_script(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= (bag.count 3 b) 2))\n\
             (assert (= (bag.choose b) 3))\n\
             (check-sat)\n\
             (get-value (b (bag.choose b) (bag.count (bag.choose b) b)))\n",
        )
        .expect("script executes");
    let joined = out.join("\n");
    assert!(joined.contains("(b (bag 3 2))"), "{joined}");
    assert!(joined.contains("((bag.choose b) 3)"), "{joined}");
    assert!(
        joined.contains("((bag.count (bag.choose b) b) 2)"),
        "{joined}"
    );

    // The empty bag: choose is unspecified; `0` models it and the count
    // reads 0.
    let mut context = nixie_solver::Context::new();
    let out = context
        .execute_script(
            "(set-logic ALL)\n\
             (declare-const b (Bag Int))\n\
             (assert (= b (as bag.empty (Bag Int))))\n\
             (check-sat)\n\
             (get-value ((bag.choose b) (bag.count (bag.choose b) b)))\n",
        )
        .expect("script executes");
    let joined = out.join("\n");
    assert!(joined.contains("((bag.choose b) 0)"), "{joined}");
    assert!(
        joined.contains("((bag.count (bag.choose b) b) 0)"),
        "{joined}"
    );
}
