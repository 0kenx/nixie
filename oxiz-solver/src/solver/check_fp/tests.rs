//! Regression tests for [`extended::collect_fp_constraints_extended`]'s
//! conversion from mutually-recursive native recursion to an explicit,
//! tagged worklist (see `extended.rs`'s module doc for the full rationale).
//!
//! Split out as a child module of `check_fp` (rather than appended inline) so
//! that `check_fp.rs` does not creep back up toward the workspace's
//! 2000-line ceiling; see `euf/solver/tests.rs` for the identical precedent.
use super::*;
use num_rational::Rational64;

/// Build a fresh, empty accumulator bundle -- the same type
/// `collect_fp_data_cached` (check_fp.rs) uses -- so every test spells out
/// only the fields it actually asserts on.
fn empty_data() -> FpConstraintData {
    FpConstraintData::new()
}

/// Calls `collect_fp_constraints_extended` with `data`'s fields as the
/// seventeen accumulator parameters, exactly mirroring
/// `collect_fp_data_cached`'s own call shape in check_fp.rs.
fn collect(
    solver: &Solver,
    term: TermId,
    manager: &TermManager,
    data: &mut FpConstraintData,
    positive: bool,
) {
    solver.collect_fp_constraints_extended(
        term,
        manager,
        &mut data.additions,
        &mut data.divisions,
        &mut data.multiplications,
        &mut data.comparisons,
        &mut data.equalities,
        &mut data.literals,
        &mut data.rounding_add_results,
        &mut data.is_zero,
        &mut data.is_positive,
        &mut data.is_negative,
        &mut data.not_nan,
        &mut data.gt_comparisons,
        &mut data.lt_comparisons,
        &mut data.conversions,
        &mut data.real_to_fp_conversions,
        &mut data.subtractions,
        positive,
    );
}

// ========  ========
// Shallow behavior preservation: small formulas with a known-exact answer.
// ========  ========

#[test]
fn is_zero_at_positive_polarity_is_collected() {
    let solver = Solver::new();
    let mut manager = TermManager::new();
    let fp_sort = manager.sorts.float_sort(11, 53);
    let x = manager.mk_var("x", fp_sort);
    let term = manager.mk_fp_is_zero(x);

    let mut data = empty_data();
    collect(&solver, term, &manager, &mut data, true);

    assert_eq!(data.is_zero, [x].into_iter().collect());
    assert!(data.is_positive.is_empty());
    assert!(data.equalities.is_empty());
}

#[test]
fn is_nan_under_not_records_not_nan_not_is_nan() {
    // `(not (fp.isNaN w))`, asserted positively at the top: the walk enters
    // `Not`, flips polarity to `false`, and reaches `FpIsNaN` at negative
    // polarity, which is precisely the condition that records `not_nan`.
    let solver = Solver::new();
    let mut manager = TermManager::new();
    let fp_sort = manager.sorts.float_sort(11, 53);
    let w = manager.mk_var("w", fp_sort);
    let is_nan = manager.mk_fp_is_nan(w);
    let term = manager.mk_not(is_nan);

    let mut data = empty_data();
    collect(&solver, term, &manager, &mut data, true);

    assert_eq!(data.not_nan, [w].into_iter().collect());
}

#[test]
fn de_morgan_not_and_asserts_neither_conjunct() {
    // `(not (and (fp.isZero a) (fp.isZero b)))` is `(or (not ..) (not ..))`,
    // so neither conjunct's isZero fact may be recorded -- the exact trap
    // `term_walk::asserted_children` exists to avoid, applied here through
    // the walk under test rather than through `asserted_children` directly.
    let solver = Solver::new();
    let mut manager = TermManager::new();
    let fp_sort = manager.sorts.float_sort(11, 53);
    let a = manager.mk_var("a", fp_sort);
    let b = manager.mk_var("b", fp_sort);
    let is_zero_a = manager.mk_fp_is_zero(a);
    let is_zero_b = manager.mk_fp_is_zero(b);
    let and_term = manager.mk_and(vec![is_zero_a, is_zero_b]);
    let term = manager.mk_not(and_term);

    let mut data = empty_data();
    collect(&solver, term, &manager, &mut data, true);

    assert!(
        data.is_zero.is_empty(),
        "neither conjunct of a negated `and` is unconditionally asserted"
    );
}

#[test]
fn and_at_positive_polarity_asserts_every_conjunct() {
    // Control for the De Morgan test above: a *positive* `and` does hand out
    // both conjuncts.
    let solver = Solver::new();
    let mut manager = TermManager::new();
    let fp_sort = manager.sorts.float_sort(11, 53);
    let a = manager.mk_var("a", fp_sort);
    let b = manager.mk_var("b", fp_sort);
    let is_zero_a = manager.mk_fp_is_zero(a);
    let is_zero_b = manager.mk_fp_is_zero(b);
    let term = manager.mk_and(vec![is_zero_a, is_zero_b]);

    let mut data = empty_data();
    collect(&solver, term, &manager, &mut data, true);

    assert_eq!(data.is_zero, [a, b].into_iter().collect());
}

#[test]
fn or_disjunct_predicate_is_not_asserted_but_conversion_is_still_discovered() {
    // `(or (fp.isZero p) (fp.to_fp ... real_to_fp(v)))`: `p` must NOT be
    // recorded as `is_zero` (a disjunct is conditional), but the FP/Real
    // conversion chain sitting in the *other* disjunct must still be found --
    // that discovery-only tracking is exactly what `Recurse` mode (the old
    // `collect_fp_constraints_extended_recurse`) is for, and `Or` is the one
    // arm in `Extended` mode that hands its children to `Recurse` instead of
    // continuing in `Extended` mode.
    let solver = Solver::new();
    let mut manager = TermManager::new();
    let fp_sort = manager.sorts.float_sort(11, 53);
    let p = manager.mk_var("p", fp_sort);
    let is_zero_p = manager.mk_fp_is_zero(p);

    let real_val = manager.mk_real(Rational64::from_integer(7));
    let real_to_fp = manager.mk_real_to_fp(RoundingMode::RNE, real_val, 11, 53);
    let conv = manager.mk_fp_to_fp(RoundingMode::RNE, real_to_fp, 11, 53);

    let term = manager.mk_or(vec![is_zero_p, conv]);

    let mut data = empty_data();
    collect(&solver, term, &manager, &mut data, true);

    assert!(
        data.is_zero.is_empty(),
        "a disjunct's predicate must not be recorded as unconditionally asserted"
    );
    assert!(
        data.conversions.contains(&(real_to_fp, 11, 53, conv)),
        "the conversion chain nested in the other disjunct must still be discovered"
    );
}

#[test]
fn equality_with_fp_add_records_equality_and_operation_result() {
    // `(= lhs (fp.add RNE x y))`, positive: records the equality itself, and
    // -- because `lhs` is now known equal to an `FpAdd` term -- the addition
    // operands/result and the `(x, y, rm) -> lhs` rounding-result mapping
    // Check 5 (`check_fp_constraints`) depends on.
    let solver = Solver::new();
    let mut manager = TermManager::new();
    let fp_sort = manager.sorts.float_sort(11, 53);

    // Built before `x`/`y`/`add_term` so it gets the smaller TermId, keeping
    // `mk_eq`'s canonicalization predictable: `Eq(lhs, add_term)` unchanged.
    let lhs = manager.mk_var("lhs", fp_sort);
    let x = manager.mk_var("x", fp_sort);
    let y = manager.mk_var("y", fp_sort);
    let add_term = manager.mk_fp_add(RoundingMode::RNE, x, y);
    let term = manager.mk_eq(lhs, add_term);

    let mut data = empty_data();
    collect(&solver, term, &manager, &mut data, true);

    assert_eq!(data.equalities, vec![(lhs, add_term)]);
    assert_eq!(
        data.additions,
        vec![(lhs, x, y, lhs, RoundingMode::RNE)],
        "the FpAdd result must be recorded against `lhs`, the other side of the equality"
    );
    assert_eq!(
        data.rounding_add_results.get(&(x, y, RoundingMode::RNE)),
        Some(&lhs)
    );
}

// ========  ========
// Deep structure: built iteratively, exercised on a 128 KiB stack.
//
// Each `(STACK_SIZE, DEPTH)` pair below was scaled down from (1 MiB, 100 000)
// by a factor of 8 on both sides.  What the tests pin is the ~10 bytes of
// stack available per nesting level – no native frame fits in that, so a
// recursive collector still dies – not the absolute depth, and the smaller
// pair costs a 64th of the construction work.  Never raise one alone.
// ========  ========

/// `fp.to_fp(fp.to_fp(...fp.to_fp(fp.real_to_fp(v))...))`, `depth` levels of
/// `FpToFp` deep, built with a plain iterative loop -- never a recursive
/// helper, which would overflow before the walk under test even ran.
///
/// `TermManager::mk_fp_to_fp` performs no simplification (unlike `mk_not` or
/// `mk_and`, which fold/flatten and so cannot be used to build genuine deep
/// *nesting*): each level's argument is the unique previous level's `TermId`,
/// so hash-consing cannot collapse the chain.
fn build_fp_to_fp_chain(manager: &mut TermManager, depth: usize) -> TermId {
    let real_val = manager.mk_real(Rational64::from_integer(1));
    let mut term = manager.mk_real_to_fp(RoundingMode::RNE, real_val, 11, 53);
    for _ in 0..depth {
        term = manager.mk_fp_to_fp(RoundingMode::RNE, term, 11, 53);
    }
    term
}

/// The point of the whole exercise: an embedder calling OxiZ from a worker
/// thread with a conventional ~1 MiB stack must get a normal return, not a
/// process abort.  The pinned stack here is an eighth of that, paired with an
/// eighth of the depth, which pins the same bytes-per-frame ratio.
///
/// A Rust stack overflow is not a panic -- it is a fatal runtime abort that
/// `catch_unwind` cannot intercept -- so the only way to assert on it is to
/// run on a thread whose stack size is pinned small and observe that the
/// thread returns at all. Asserting the exact conversion count additionally
/// rules out a silently truncated walk, which for this collector would mean
/// a missed conflict (a false `Sat`), not merely a missed optimization.
#[test]
fn fp_to_fp_conversion_chain_survives_a_small_stack() {
    const STACK_SIZE: usize = 1 << 17; // 128 KiB
    const DEPTH: usize = 12_500;

    let handle = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(|| {
            let solver = Solver::new();
            let mut manager = TermManager::new();
            let deepest = build_fp_to_fp_chain(&mut manager, DEPTH);

            let mut data = empty_data();
            collect(&solver, deepest, &manager, &mut data, true);

            assert_eq!(
                data.conversions.len(),
                DEPTH,
                "one `fp.to_fp` conversion entry per level of a {DEPTH}-deep chain"
            );
            assert_eq!(
                data.real_to_fp_conversions.len(),
                1,
                "exactly one `real_to_fp` entry at the bottom of the chain"
            );
            assert_eq!(
                data.literals.len(),
                1,
                "the literal at the bottom of the chain must still be extracted"
            );
        })
        .expect("spawning a 128 KiB-stack thread should succeed");

    handle
        .join()
        .expect("the FP-conversion walk must return on a 128 KiB stack instead of overflowing it");
}

// ========  ========
// The narrow (polarity-free) collector: `collect_fp_constraints`.  Same
// worklist conversion, same rationale – see its doc comment in `check_fp.rs`.
// ========  ========

/// Calls the narrow collector with `data`'s matching accumulator fields.
fn collect_narrow(
    solver: &Solver,
    term: TermId,
    manager: &TermManager,
    data: &mut FpConstraintData,
) {
    solver.collect_fp_constraints(
        term,
        manager,
        &mut data.additions,
        &mut data.divisions,
        &mut data.multiplications,
        &mut data.comparisons,
        &mut data.equalities,
        &mut data.literals,
        &mut data.rounding_add_results,
    );
}

/// Conjuncts of an `And` are collected in left-to-right order; `Or` (and
/// everything under it) stays untouched, because a disjunct is not
/// unconditionally asserted.
#[test]
fn narrow_collector_records_conjunct_facts_and_ignores_disjuncts() {
    let solver = Solver::new();
    let mut manager = TermManager::new();
    let fp_sort = manager.sorts.float_sort(11, 53);
    let lhs = manager.mk_var("lhs", fp_sort);
    let x = manager.mk_var("x", fp_sort);
    let y = manager.mk_var("y", fp_sort);
    let add_term = manager.mk_fp_add(RoundingMode::RNE, x, y);
    let eq = manager.mk_eq(lhs, add_term);
    let lt = manager.mk_fp_lt(x, y);
    let gt = manager.mk_fp_gt(y, x); // records as (x, y, true): `y > x` is `x < y`
    let or_lt = manager.mk_fp_lt(lhs, x);
    let or_term = manager.mk_or(vec![or_lt, eq]);
    let and = manager.mk_and(vec![eq, lt, gt, or_term]);

    let mut data = FpConstraintData::new();
    collect_narrow(&solver, and, &manager, &mut data);

    assert_eq!(data.equalities, vec![(lhs, add_term)]);
    assert_eq!(data.additions, vec![(lhs, x, y, lhs, RoundingMode::RNE)]);
    assert_eq!(
        data.rounding_add_results.get(&(x, y, RoundingMode::RNE)),
        Some(&lhs)
    );
    assert_eq!(
        data.comparisons,
        vec![(x, y, true), (x, y, true)],
        "lt then gt, in conjunct order; both normalise to (x, y, true)"
    );
    assert!(
        !data.comparisons.contains(&(lhs, x, true)),
        "a comparison living only inside an `Or` disjunct must not be collected"
    );
}

/// An `And` chain 12 500 levels deep – built through the raw interner, because
/// `mk_and` flattens nested conjunctions and cannot produce genuine nesting,
/// while an API user calling `intern_term` directly can – must be walked on a
/// 128 KiB stack.  One equality fact per level (plus the innermost leaf)
/// proves the walk was complete, not silently truncated.
#[test]
fn narrow_collector_survives_deep_raw_and_nesting_on_a_small_stack() {
    const STACK_SIZE: usize = 1 << 17; // 128 KiB
    const DEPTH: usize = 12_500;

    let handle = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(|| {
            let solver = Solver::new();
            let mut manager = TermManager::new();
            let fp_sort = manager.sorts.float_sort(11, 53);
            let bool_sort = manager.sorts.bool_sort;
            let x = manager.mk_var("x", fp_sort);
            let y = manager.mk_var("y", fp_sort);
            let eq = manager.mk_eq(x, y);
            let mut term = eq;
            for _ in 0..DEPTH {
                term =
                    manager.intern_term(TermKind::And([eq, term].into_iter().collect()), bool_sort);
            }

            let mut data = FpConstraintData::new();
            collect_narrow(&solver, term, &manager, &mut data);

            assert_eq!(
                data.equalities.len(),
                DEPTH + 1,
                "one equality per conjunction level plus the innermost leaf"
            );
        })
        .expect("spawning a 128 KiB-stack thread should succeed");

    handle
        .join()
        .expect("the narrow collector must return on a 128 KiB stack instead of overflowing it");
}
