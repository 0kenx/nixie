//! Regression tests for the independently-reimplemented arith<->EUF
//! combination fixes (upstream PR #30 against cool-japan/oxiz): numeric
//! uninterpreted-function-argument purification, non-convex LIA integer
//! case-splitting, and bidirectional Nelson-Oppen equality/disequality
//! exchange.
//!
//! Lower-level, mechanism-specific tests live next to the code they
//! exercise:
//! * `oxiz-solver/src/solver/int_case_split.rs` -- the interval-arithmetic
//!   helpers (`floor_div`/`ceil_div`/`bound_from_side`/...) in isolation.
//! * `oxiz-theories/src/arithmetic/solver.rs` -- doctests/unit coverage for
//!   `entailed_equal_reason` / `entailed_disequal_reason`, if any.
//!
//! This file covers the fixes whose defining property is only visible
//! end-to-end: does the *whole solver*, driven exactly as an SMT-LIB2 client
//! would drive it, answer `sat`/`unsat` correctly, and does a satisfiable
//! model still resolve through `get-value`.

use oxiz_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

// ========  ========
// 1. Numeric UF-argument purification: arithmetic entailing an equality to
//    a *constant* UF argument must reach EUF congruence.
// ========  ========

/// The PR's headline soundness repro: `f(y)` and `f(3)` are asserted
/// distinct, but arithmetic (via an unrelated chain `y = x + 1`, `x = 2`)
/// entails `y = 3`. Without purifying `f(3)`'s argument into a shared
/// variable, `3` is never an arithmetic interface term at all (it is folded
/// straight into the linear constraint), so the entailed equality has
/// nothing on the EUF side to attach to and the congruence `f(y) = f(3)` is
/// never discovered -- a false `sat`.
#[test]
fn test_pr30_purified_uf_arg_entailed_equality_false_sat() {
    let output = run(r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x 2))
        (assert (= y (+ x 1)))
        (assert (not (= (f y) (f 3))))
        (check-sat)
    "#);
    assert_eq!(
        output,
        vec!["unsat"],
        "arithmetic entails y = 3, so f(y) != f(3) must be refuted by congruence"
    );
}

/// Companion satisfiable control: flip the chain so `y` is entailed `4`, not
/// `3`. `f(y) != f(3)` is then perfectly consistent (an uninterpreted `f` can
/// map `4` and `3` to different results), so purification must not
/// over-constrain the formula into a spurious `unsat`.
#[test]
fn test_pr30_purified_uf_arg_stays_sat_when_not_entailed() {
    let output = run(r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x 2))
        (assert (= y (+ x 2)))
        (assert (not (= (f y) (f 3))))
        (check-sat)
    "#);
    assert_eq!(output, vec!["sat"]);
}

/// Order-independence: an unrelated quantifier over a *different* function
/// must not reintroduce the false-`sat` `test_pr30_purified_uf_arg_entailed_equality_false_sat`
/// closes just because it happens to be asserted first.
///
/// `purify_numeric_uf_args` used to gate itself on the solver-wide
/// `has_quantifiers` flag: true once *any* quantifier had been registered,
/// regardless of which function it applies to. That made the fix itself
/// order-dependent -- `g`'s quantifier here sets `has_quantifiers` before
/// `f`'s ground disequality is ever purified, even though `f` never occurs
/// under a binder, so the entailed `y = 3` had nothing on the EUF side to
/// attach to and the same spurious `sat` as the ungated bug returned. The
/// fix scopes the gate to `quantifier_uf_funcs` (the actual function
/// symbols used under a binder) instead, so a function that is never a
/// quantifier trigger gets purified in any assertion order.
#[test]
fn test_pr30_purification_is_sound_regardless_of_unrelated_quantifier_order() {
    let output = run(r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (forall ((z Int)) (> (g z) 0)))
        (assert (= x 2))
        (assert (= y (+ x 1)))
        (assert (not (= (f y) (f 3))))
        (check-sat)
    "#);
    assert_eq!(
        output,
        vec!["unsat"],
        "an unrelated quantifier over g must not suppress f's purification"
    );
}

/// SAT-preservation for the purified shape itself: once purification
/// rewrites `f(3)` to `f(v)` (plus `v = 3`) at encode time, `self.assertions`
/// and any `(get-value ((f 3)))` query still name the *original* `f(3)`.
/// `build_model`'s alias pass must resolve it to the same value its purified
/// twin was assigned, or a genuinely satisfiable model would print `(f 3)`
/// back unevaluated instead of a concrete value.
#[test]
fn test_pr30_purification_preserves_get_value_on_original_application() {
    let output = run(r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (assert (= (f 3) 5))
        (check-sat)
        (get-value ((f 3)))
    "#);
    assert_eq!(output[0], "sat");
    assert_eq!(
        output[1], "(((f 3) 5))",
        "get-value must resolve the purified application to its value, got: {}",
        output[1]
    );
}

// ========  ========
// 2. Non-convex LIA case-splitting: a UF argument pinned to a small finite
//    domain (not a single entailed value) needs an explicit case split.
// ========  ========

/// `x` is bounded to `{1, 2}` by direct level-0 facts (not a single entailed
/// value), and both `f(1)` and `f(2)` equal `a`. Equality sharing alone
/// cannot resolve this: neither `x = 1` nor `x = 2` is entailed on its own,
/// so there is no atom for the arith<->EUF combination to propagate and the
/// CDCL(T) core never sees a reason `f(x) != a` cannot hold. The explicit
/// case-split lemma `(or (= x 1) (= x 2))` is what gives the search
/// something to branch on and close the gap.
#[test]
fn test_pr30_noncovex_case_split_closes_false_sat() {
    let output = run(r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const a Int)
        (assert (<= 1 x))
        (assert (<= x 2))
        (assert (= (f 1) a))
        (assert (= (f 2) a))
        (assert (not (= (f x) a)))
        (check-sat)
    "#);
    assert_eq!(
        output,
        vec!["unsat"],
        "x in {{1,2}} and f(1)=f(2)=a together force f(x)=a for every possible x"
    );
}

/// Companion satisfiable control: drop `f(2) = a`, so `x = 2` no longer
/// forces `f(x) = a`. The case-split refinement must not manufacture a
/// spurious `unsat` out of a lemma that is merely a theorem, not a
/// strengthening.
#[test]
fn test_pr30_noncovex_case_split_stays_sat_when_consistent() {
    let output = run(r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const a Int)
        (assert (<= 1 x))
        (assert (<= x 2))
        (assert (= (f 1) a))
        (assert (not (= (f x) a)))
        (check-sat)
    "#);
    assert_eq!(output, vec!["sat"]);
}

// ========  ========
// 3. EUF -> arithmetic: a congruence-derived equality constraining
//    arithmetic. Already sound before this slice --
//    `TheoryManager::propagate_euf_equalities_to_arith` (pre-existing) --
//    kept here as an end-to-end regression pin.
// ========  ========

/// `p = q` is asserted directly, so EUF's congruence closure derives
/// `f(p) = f(q)` immediately. Arithmetic is never told this directly (no
/// atom compares `f(p)` to `f(q)`), so it takes the EUF -> arithmetic
/// direction of theory combination to propagate the congruence into the
/// tableau, where it contradicts `f(p) < 0 /\ f(q) > 0`.
#[test]
fn test_pr30_euf_congruence_forces_arith_conflict_already_sound() {
    let output = run(r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const p Int)
        (declare-const q Int)
        (assert (= p q))
        (assert (< (f p) 0))
        (assert (> (f q) 0))
        (check-sat)
    "#);
    assert_eq!(
        output,
        vec!["unsat"],
        "p = q forces f(p) = f(q) by congruence, contradicting f(p) < 0 /\\ f(q) > 0"
    );
}

// ========  ========
// 4. Disequality exchange: an arithmetic-entailed equality between two
//    (bare, unpurified) UF-argument variables contradicts a directly
//    asserted EUF disequality between their images.
// ========  ========

/// `p` and `q` are each pinned to exactly `3` by a pair of one-sided bound
/// atoms (`3 <= p /\ p <= 3`, and likewise for `q`) -- deliberately never by
/// a direct `(= p q)`, `(= p 3)` or `(= q 3)` assertion. A `Le`/`Ge` atom
/// does not go through EUF's eager merge path at all (only `Eq`/`Diseq`
/// constraints do; see `TheoryManager::process_constraint`), so nothing ever
/// tells EUF that `p` and `q` denote the same value -- only the tableau
/// knows, and only because both pairs of bounds coincide. There is also no
/// `(not (= p q))` atom for the pre-existing pure-arithmetic disequality
/// trichotomy to act on, since `p` and `q` are never compared to each other
/// syntactically at all. Only the model-value care-graph probe
/// (`TheoryManager::care_graph_candidates`'s UF-argument bucket) notices `p`
/// and `q` are both UF arguments the tableau currently assigns the same
/// value, entails their equality, and merges them in EUF -- which is what
/// makes the directly-asserted `f(p) != f(q)` a real, detected conflict via
/// congruence instead of a spurious `sat`.
#[test]
fn test_pr30_arith_entailed_equality_violates_euf_disequality() {
    let output = run(r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const p Int)
        (declare-const q Int)
        (assert (<= 3 p))
        (assert (<= p 3))
        (assert (<= 3 q))
        (assert (<= q 3))
        (assert (not (= (f p) (f q))))
        (check-sat)
    "#);
    assert_eq!(
        output,
        vec!["unsat"],
        "p and q are both entailed 3 by disjoint bound atoms, so f(p) != f(q) is refuted"
    );
}

/// Companion satisfiable control: widen `q`'s bounds so it is no longer
/// pinned to exactly `3` (merely bounded). `p` and `q` are then not entailed
/// equal, so `f(p) != f(q)` is a perfectly consistent assignment (e.g.
/// `q = 5`).
#[test]
fn test_pr30_arith_entailed_equality_disequality_stays_sat_when_not_entailed() {
    let output = run(r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const p Int)
        (declare-const q Int)
        (assert (<= 3 p))
        (assert (<= p 3))
        (assert (<= 0 q))
        (assert (<= q 10))
        (assert (not (= (f p) (f q))))
        (check-sat)
    "#);
    assert_eq!(output, vec!["sat"]);
}

// ========  ========
// 5. SAT-preservation on a broader mixed QF_UFLIA instance: the combination
//    machinery above must not turn a genuinely satisfiable, UF-heavy
//    instance into a spurious `unsat`, and `get-value` must still report a
//    consistent, verifiable model.
// ========  ========

#[test]
fn test_pr30_mixed_uflia_sat_preserved_with_consistent_model() {
    let output = run(r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= a (+ b 1)))
        (assert (= b 5))
        (assert (not (= c 6)))
        (assert (= (f a) (g b)))
        (assert (> (f c) 0))
        (check-sat)
        (get-value (a b c))
    "#);
    assert_eq!(output[0], "sat");
    // `a = b + 1 = 6` is entailed regardless of `c`, so the model must
    // report it exactly; `b = 5` is a direct fact; `c` need only differ
    // from `6`.
    let values = &output[1];
    assert!(
        values.contains("(a 6)") && values.contains("(b 5)"),
        "model must honour the entailed values of a and b: {values}"
    );
    assert!(
        !values.contains("(c 6)"),
        "model must respect (not (= c 6)): {values}"
    );
}

/// A satisfiable instance whose non-convex shape (a UF argument bounded to a
/// wider-than-case-split range) must not be perturbed by the case-split
/// refinement: the range exceeds what a single round can (or needs to)
/// enumerate, and the formula is satisfiable regardless of which value `x`
/// takes.
#[test]
fn test_pr30_wide_range_uf_argument_stays_sat() {
    let output = run(r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (assert (<= 0 x))
        (assert (<= x 1000))
        (assert (= (f x) 0))
        (check-sat)
    "#);
    assert_eq!(output, vec!["sat"]);
}

/// The other side of the per-function purification gate: when the ground
/// disequality is over the function that *is* a quantifier trigger, the
/// argument purification is deliberately skipped -- and that leaves a real
/// wrong-`sat`, not merely a re-ordered instantiation.
///
/// Here `f` occurs both under the binder and in the ground disequality. `f(3)`
/// is therefore left unpurified, `3` never becomes an arithmetic interface
/// term, the arithmetic-entailed `y = 3` has nothing on the EUF side to attach
/// to, and the congruence `f(y) = f(3)` is never derived. MBQI is only ever
/// asked about the `forall`, reports its fixpoint, and the solver used to
/// return `sat` for a formula whose *ground part alone* is unsatisfiable.
///
/// What closes it is the ROOT FIX (`encode::purify_numeric_uf_args`
/// per-function gate + `TheoryManager::nelson_oppen_combine` re-pin): the
/// constant numeric args of a quantified (un-purified) function are pinned
/// into arithmetic as interface terms fixed to their literal value – a
/// tautological row whose reason tag names no literal (empty
/// `DerivedReasons` explanation). The model-equal probe can then pair `3`
/// with the equal-valued shared `y`, `entailed_equal_reason` re-verifies
/// `y = 3` with two feasibility checks, EUF merges them, congruence fires on
/// `f(y) = f(3)`, and the asserted disequality refutes the candidate. The
/// verdict is now the full `unsat` (z3 agrees) – not the `unknown` the
/// removed exit-gate backstop used to produce: the gate masked this as an
/// honest downgrade while the search itself stayed broken.
#[test]
fn test_pr30_quantifier_trigger_function_ground_diseq_is_not_sat() {
    let output = run(r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (forall ((z Int)) (>= (f z) 0)))
        (assert (= x 2))
        (assert (= y (+ x 1)))
        (assert (not (= (f y) (f 3))))
        (check-sat)
    "#);
    assert_eq!(
        output,
        vec!["unsat"],
        "the ground part is unsatisfiable (y = 3 forces f(y) = f(3)), so the \
         answer is `unsat` — derived at the root by pinning `3` into arithmetic \
         so congruence can fire (z3: unsat)"
    );
}

/// Control for the gate above: a quantified formula whose ground part *is*
/// satisfiable must still answer `sat`. Same shape as the previous test with
/// the chain entailing `y = 4`, so `f(y) != f(3)` is consistent and the model
/// the solver reports really is a function.
#[test]
fn test_pr30_quantifier_trigger_function_stays_sat_when_consistent() {
    let output = run(r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (forall ((z Int)) (>= (f z) 0)))
        (assert (= x 2))
        (assert (= y (+ x 2)))
        (assert (not (= (f y) (f 3))))
        (check-sat)
    "#);
    assert_eq!(
        output,
        vec!["sat"],
        "the quantified model-verification gate must not downgrade a genuine sat"
    );
}

/// Root-fix regression: the pinned constant is NEGATIVE and reached through a
/// longer arithmetic chain (`y = 2x - 8 = -4`), so the pair (`y`, `-4`) must be
/// probed, entailed, merged, and refuted by congruence exactly as the positive
/// case.  `sat` here would mean the pin only works for non-negative constants.
#[test]
fn test_pr30_quantified_uf_negative_const_pin_closes_false_sat() {
    let output = run(r#"
        (set-logic UFLIA)
        (declare-fun g (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (assert (forall ((w Int)) (< (g w) 100)))
        (assert (= a 2))
        (assert (= b (- (* 2 a) 8)))
        (assert (not (= (g b) (g (- 4)))))
        (check-sat)
    "#);
    assert_eq!(
        output,
        vec!["unsat"],
        "b = -4 forces g(b) = g(-4) by congruence; z3: unsat"
    );
}

/// Root-fix control: same shape with the chain entailing a DIFFERENT value
/// (`y = 4`, so `f(y)` and `f(3)` are congruence-independent) — must stay
/// `sat`; a pin that over-merged (pairing unequal values or skipping the
/// entailment re-verification) would flip this to `unsat`/`unknown`.
#[test]
fn test_pr30_quantified_uf_pin_stays_sat_when_values_differ() {
    let output = run(r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (assert (forall ((z Int)) (>= (f z) 0)))
        (assert (= x 3))
        (assert (= y (+ x 1)))
        (assert (not (= (f y) (f 3))))
        (check-sat)
    "#);
    assert_eq!(
        output,
        vec!["sat"],
        "y = 4 ≠ 3: f(4) ≠ f(3) is consistent; z3: sat"
    );
}

/// Root-fix regression: the pinned constant is a COMPOUND arithmetic term
/// (`(- 8 2)`, not constant-folded by the parser), closed-form evaluated to 6
/// by the linear extractor.  Shape-by-shape pinning (literals only) left this
/// exact input a false `sat`; the pin now fires for any variable-free linear
/// form.
#[test]
fn test_pr30_quantified_uf_compound_const_pin_closes_false_sat() {
    let output = run(r#"
        (set-logic UFLIA)
        (declare-fun g (Int) Int)
        (declare-const b Int)
        (assert (forall ((w Int)) (< (g w) 100)))
        (assert (= b (- 10 4)))
        (assert (not (= (g b) (g (- 8 2)))))
        (check-sat)
    "#);
    assert_eq!(
        output,
        vec!["unsat"],
        "b = 6 = (- 8 2) forces g(b) = g(6) by congruence; z3: unsat"
    );
}
