//! QF_BV eager-dispatch and bit-blaster folding regressions.
//!
//! These pin down two defect classes introduced (and fixed) while adding the
//! pure-QF_BV eager dispatch (`dispatch_pure_bv.rs`) and the constant-folding
//! gate layer (`Sig`/`gate_*` in `oxiz-theories::bv::solver`):
//!
//! 1. **Inverted equality-node encoding (false UNSAT).**  The first "flat"
//!    encoding of `encode_eq_node` wrote the reverse-direction clauses with
//!    the wrong polarity: any differing bit forced the equality node *true*,
//!    so `(or (not (= x y)) (not (= x #x00)))` with `x = y = 1` – whose second
//!    disjunct is true – answered `unsat`.  The same bug class also flipped
//!    `Sage2`/`bench_66`-style benchmarks between sat and unsat.
//! 2. **Model extraction through aliased bits.**  `extract`/`concat` now
//!    install *aliases* of the operand bits instead of fresh variables plus
//!    equivalence clauses (the structural sharing Z3's blaster inherits from
//!    hash-consing).  The model, `get-value` and the model-verification gate
//!    must all read correct values through the aliases.
//!
//! Plus end-to-end shapes of the eager dispatch itself: hash-chain
//! multiplication by a sparse constant (the Sage2 family), negated top-level
//! disequality, get-value over the dispatch-produced model, and slice wiring
//! (the `ext_con` family).

use oxiz_solver::{Context, SolverResult};

/// Run one SMT-LIB2 script, return the last verdict token.
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

fn check(script: &str, expected: SolverResult) {
    assert_eq!(
        run_script(script),
        expected,
        "script:\n{script}\nreturned the wrong verdict"
    );
}

// ======== inverted equality-node encoding (must stay SAT) ========

#[test]
fn eq_node_under_or_with_pinned_operands_stays_sat() {
    // `(not (= x y))` and `(not (= x #x00))` are Eq *nodes* (they sit under an
    // `or`, so their truth value is not known at assert time).  With x = y = 1
    // the second disjunct is true: satisfiable.  The inverted encoding forced
    // a difference at bit 0 (`1 != 0`) to make the first node TRUE and the
    // pinned `x = y` clauses then contradicted it – a false `unsat`.
    check(
        "(declare-fun x () (_ BitVec 8))
         (declare-fun y () (_ BitVec 8))
         (assert (= x y))
         (assert (= x #x01))
         (assert (or (not (= x y)) (not (= x #x00))))
         (check-sat)",
        SolverResult::Sat,
    );
}

#[test]
fn eq_node_constant_bits_neither_all_zero_nor_all_one() {
    // Exercises the const-vs-signal arm of the eq node in both directions:
    // bit 0 matches, bit 1 differs.  `(= x #b10)` is node-encoded under the
    // `or` while x is pinned to #b10 elsewhere: must be SAT, and the negated
    // variant must be UNSAT.
    check(
        "(declare-fun x () (_ BitVec 8))
         (assert (= x #b00000010))
         (assert (or (= x #b00000010) (= x #b00000001)))
         (check-sat)",
        SolverResult::Sat,
    );
    check(
        "(declare-fun x () (_ BitVec 8))
         (assert (= x #b00000010))
         (assert (not (or (= x #b00000010) (= x #b00000001))))
         (check-sat)",
        SolverResult::Unsat,
    );
}

#[test]
fn negated_eq_node_against_constant() {
    // The node-encoding of `(not (= x #x05))` with x pinned to 5: the node is
    // false; asserting it true must be UNSAT, asserting it false SAT.
    check(
        "(declare-fun x () (_ BitVec 8))
         (assert (= x #x05))
         (assert (not (= x #x05)))
         (check-sat)",
        SolverResult::Unsat,
    );
    // ...while the disjunction over an unreachable alternative is UNSAT.
    check(
        "(declare-fun x () (_ BitVec 8))
         (assert (= x #x05))
         (assert (or (not (= x #x05)) (= x #x06)))
         (check-sat)",
        SolverResult::Unsat,
    );
    // The same node shape is SAT when the second disjunct holds.
    check(
        "(declare-fun x () (_ BitVec 8))
         (assert (= x #x06))
         (assert (or (not (= x #x05)) (= x #x06)))
         (check-sat)",
        SolverResult::Sat,
    );
}

// ======== sage2 hash-chain shape (constant multiplication folding) ========

#[test]
fn sage2_hash_chain_disequality_unsat() {
    // h = ((c1 * 65599 + c2) * 65599 + c3) over 32-bit zero-extended bytes.
    // The target is a reachable hash value: the negated equality is UNSAT.
    // (Values verified with an independent Python computation of the chain.)
    // The chain over 0x61, 0x62, 0x63 hashes to 0x3025f862 (independently
    // computed); asserting that value with the bytes pinned is SAT.
    check(
        "(declare-fun c1 () (_ BitVec 8))
         (declare-fun c2 () (_ BitVec 8))
         (declare-fun c3 () (_ BitVec 8))
         (define-fun h () (_ BitVec 32)
           (bvadd (bvmul (bvadd (bvmul ((_ zero_extend 24) c1) (_ bv65599 32))
                                ((_ zero_extend 24) c2))
                         (_ bv65599 32))
                  ((_ zero_extend 24) c3)))
         (assert (= h #x3025f862))
         (assert (= c1 #x61))
         (assert (= c2 #x62))
         (assert (= c3 #x63))
         (check-sat)",
        SolverResult::Sat,
    );
    // A different target with the same pinned bytes: UNSAT.
    check(
        "(declare-fun c1 () (_ BitVec 8))
         (declare-fun c2 () (_ BitVec 8))
         (declare-fun c3 () (_ BitVec 8))
         (define-fun h () (_ BitVec 32)
           (bvadd (bvmul (bvadd (bvmul ((_ zero_extend 24) c1) (_ bv65599 32))
                                ((_ zero_extend 24) c2))
                         (_ bv65599 32))
                  ((_ zero_extend 24) c3)))
         (assert (= h #x3025f863))
         (assert (= c1 #x61))
         (assert (= c2 #x62))
         (assert (= c3 #x63))
         (check-sat)",
        SolverResult::Unsat,
    );
}

#[test]
fn sparse_constant_multiplication_folds() {
    // x * 65599 (0b1_0000_0000_0001_1111, seven set bits) with x's high bits
    // zero-extended from 8: the product's bits above 8+16 are constant, so
    // both directions are decided by the folding blaster.
    check(
        "(declare-fun x () (_ BitVec 8))
         (assert (= (bvmul ((_ zero_extend 24) x) (_ bv65599 32)) (_ bv0 32)))
         (check-sat)",
        SolverResult::Sat,
    );
    check(
        "(declare-fun x () (_ BitVec 8))
         (assert (bvult (bvmul ((_ zero_extend 24) x) (_ bv65599 32)) (_ bv0 32)))
         (check-sat)",
        SolverResult::Unsat,
    );
}

// ======== extract/concat aliasing ========

#[test]
fn extract_aliasing_model_value_is_correct() {
    // `get-value` through aliased extract bits: the read-back value must be
    // the pinned slice, not a free variable's default.
    let mut ctx = Context::new();
    let outputs = ctx
        .execute_script(
            "(declare-fun a () (_ BitVec 64))
             (declare-fun b () (_ BitVec 32))
             (assert (= ((_ extract 63 32) a) #xdeadbeef))
             (assert (= ((_ extract 31 0) a) b))
             (assert (= b #x01020304))
             (check-sat)
             (get-value (a))",
        )
        .unwrap_or_default();
    let joined = outputs.join(" ");
    assert!(joined.contains("sat"), "expected sat, got: {joined}");
    assert!(
        joined.contains("#xdeadbeef01020304") || joined.contains("deadbeef01020304"),
        "model value must be the pinned concatenation, got: {joined}"
    );
}

#[test]
fn concat_aliasing_equality_unsat() {
    // Equality between a concat and a constant whose halves disagree with the
    // operand pins: UNSAT through pure wire reasoning.
    check(
        "(declare-fun x () (_ BitVec 8))
         (declare-fun y () (_ BitVec 8))
         (assert (= x #x12))
         (assert (= y #x34))
         (assert (not (= (concat x y) #x1234)))
         (check-sat)",
        SolverResult::Unsat,
    );
}

#[test]
fn ext_con_slice_wiring_shape() {
    // The bruttomesso `ext_con` shape in miniature: overlapping slices of a
    // shared vector `a` tie `v`'s slices and `d` together, while `v` must
    // have two differing slice pairs (the `or`).  The tied slices are *not*
    // the constrained ones, so a model exists: SAT (verified with Z3).
    check(
        "(declare-fun a () (_ BitVec 256))
         (declare-fun d () (_ BitVec 32))
         (declare-fun v () (_ BitVec 128))
         (assert (or (not (= ((_ extract 63 32) v) ((_ extract 31 0) v)))
                     (not (= ((_ extract 127 96) v) ((_ extract 95 64) v)))))
         (assert (= ((_ extract 95 32) a) (concat ((_ extract 31 0) v) d)))
         (assert (= ((_ extract 63 0) a) (concat d ((_ extract 127 96) v))))
         (assert (= a #x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f))
         (check-sat)",
        SolverResult::Sat,
    );
    // Same wiring, but pinning *both* slice pairs equal falsifies the `or`.
    check(
        "(declare-fun a () (_ BitVec 256))
         (declare-fun d () (_ BitVec 32))
         (declare-fun v () (_ BitVec 128))
         (assert (or (not (= ((_ extract 63 32) v) ((_ extract 31 0) v)))
                     (not (= ((_ extract 127 96) v) ((_ extract 95 64) v)))))
         (assert (= ((_ extract 95 32) a) (concat ((_ extract 31 0) v) d)))
         (assert (= ((_ extract 63 0) a) (concat d ((_ extract 127 96) v))))
         (assert (= ((_ extract 63 32) v) ((_ extract 31 0) v)))
         (assert (= ((_ extract 127 96) v) ((_ extract 95 64) v)))
         (check-sat)",
        SolverResult::Unsat,
    );
}

// ======== eager dispatch integration ========

#[test]
fn dispatch_answers_and_models_bool_bv_mix() {
    // Bool leaf variables (millionaires shape) must receive model values from
    // the dispatch-produced model, and the verdict must verify.
    let mut ctx = Context::new();
    let outputs = ctx
        .execute_script(
            "(declare-fun sel () Bool)
             (declare-fun x () (_ BitVec 8))
             (assert (= x (ite sel #x2a #x10)))
             (assert (not (= x #x2a)))
             (check-sat)
             (get-value (sel x))",
        )
        .unwrap_or_default();
    let joined = outputs.join(" ");
    assert!(joined.contains("sat"), "expected sat, got: {joined}");
    // `sel` must be false in every model of the assertion set.
    assert!(
        joined.contains("(sel false)"),
        "sel must be false, got: {joined}"
    );
    assert!(joined.contains("(x #x10)"), "x must be #x10, got: {joined}");
}

#[test]
fn dispatch_falls_back_for_arith_mixed_goals() {
    // BV + Int in one goal is outside the fragment: the dispatch declines and
    // the general path must still answer (regression guard for the gate).
    check(
        "(declare-fun x () (_ BitVec 8))
         (declare-fun i () Int)
         (assert (>= i 5))
         (assert (< i 3))
         (assert (= x #x07))
         (check-sat)",
        SolverResult::Unsat,
    );
    check(
        "(declare-fun x () (_ BitVec 8))
         (declare-fun i () Int)
         (assert (>= i 5))
         (assert (= x #x07))
         (check-sat)",
        SolverResult::Sat,
    );
}

#[test]
fn negated_top_level_disequality_hash_chain_unsat() {
    // Direct Sage2/bench_3220 miniature: the assertion IS a negated equality
    // against the chain; only byte triples whose real hash differs satisfy it.
    // c1=0x61,c2=0x62,c3=0x63 hashes to 0x3025f862 (independently
    // computed), so the negated equality against that value is UNSAT.
    check(
        "(declare-fun c1 () (_ BitVec 8))
         (declare-fun c2 () (_ BitVec 8))
         (declare-fun c3 () (_ BitVec 8))
         (define-fun h () (_ BitVec 32)
           (bvadd (bvmul (bvadd (bvmul ((_ zero_extend 24) c1) (_ bv65599 32))
                                ((_ zero_extend 24) c2))
                         (_ bv65599 32))
                  ((_ zero_extend 24) c3)))
         (assert (not (= h #x3025f862)))
         (assert (= c1 #x61))
         (assert (= c2 #x62))
         (assert (= c3 #x63))
         (check-sat)",
        SolverResult::Unsat,
    );
}

#[test]
fn fully_aliased_equality_node_is_tautologically_true() {
    // After extract/concat aliasing, `(= (extract ..) (extract ..))` over the
    // same source range shares every bit: the eq node folds to true and the
    // assertion set must stay SAT (a free `out` variable here used to let the
    // search pick `false` and answer unsat).
    check(
        "(declare-fun a () (_ BitVec 64))
         (assert (not (= ((_ extract 63 32) a) ((_ extract 63 32) a))))
         (check-sat)",
        SolverResult::Unsat,
    );
    check(
        "(declare-fun a () (_ BitVec 64))
         (assert (= ((_ extract 63 32) a) ((_ extract 63 32) a)))
         (check-sat)",
        SolverResult::Sat,
    );
}

#[test]
fn bv_comparison_direct_asserts_both_polarities() {
    // The dispatch asserts comparisons through `assert_ult`/`assert_ule` with
    // their negations rewritten (not(a <u b) == b <=u a).  Both polarity
    // combinations of a contradictory pair must be UNSAT.
    check(
        "(declare-fun x () (_ BitVec 8))
         (declare-fun y () (_ BitVec 8))
         (assert (bvult x y))
         (assert (not (bvule x y)))
         (check-sat)",
        SolverResult::Unsat,
    );
    check(
        "(declare-fun x () (_ BitVec 8))
         (declare-fun y () (_ BitVec 8))
         (assert (not (bvult x y)))
         (assert (bvult x y))
         (check-sat)",
        SolverResult::Unsat,
    );
    check(
        "(declare-fun x () (_ BitVec 8))
         (declare-fun y () (_ BitVec 8))
         (assert (bvult x y))
         (assert (bvult y x))
         (check-sat)",
        SolverResult::Unsat,
    );
}
