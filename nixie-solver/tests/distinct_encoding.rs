//! Regression tests for the shape-aware `distinct` encoding
//! (`nixie-solver/src/solver/encode.rs`, `TermKind::Distinct` arm).
//!
//! The encoder picks one of three encodings per shape (Z3's
//! `euf_internalize.cpp` is the reference):
//!
//! 1. **pigeonhole short-circuit** – a finite argument sort with |S| < n makes
//!    the term logically false, one unit clause instead of C(n,2) atoms SAT
//!    would have to refute by rediscovering the pigeonhole;
//! 2. **pairwise** for n ≤ 32 (unchanged behaviour);
//! 3. **injective map** for larger n over an EUF-owned (uninterpreted) sort –
//!    O(n) theory atoms instead of O(n²), leaning on fresh `dist-f`/`dist-g`
//!    functions and e-graph distinguished values.
//!
//! Every unsatisfiable case below is paired with a satisfiable control that
//! differs by one constant, so a mistake in either direction (false `unsat`
//! from an over-strong encoding, false `sat` from an under-strong one) shows
//! up as a wrong verdict rather than silently passing.
//!
//! The injective-map family is additionally exercised in the polarity the
//! pairwise encoding never sees cheaply: the *negated* large `distinct`, whose
//! at-least-two counter plus `g∘f = id` units must force a genuine pair
//! collision – and whose congruence inversion through `g` must refute a
//! `¬distinct` asserted alongside pairwise disequalities.

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

fn check(script: &str, expected: &str) {
    let out = run(script);
    // Multi-check scripts produce several verdicts; the *last* one is the
    // verdict of the final `(check-sat)` the test name speaks about.
    let verdict = out
        .iter()
        .rfind(|l| {
            let l = l.as_str();
            l == "sat" || l == "unsat" || l == "unknown"
        })
        .unwrap_or_else(|| panic!("no verdict in {out:?}"));
    assert_eq!(verdict, expected, "script: {script}");
}

/// Header declaring `n` uninterpreted-sort constants `x1..xn`.
fn uf_header(n: usize) -> String {
    let mut s = String::from("(set-logic QF_UF)\n(declare-sort S 0)\n");
    for i in 1..=n {
        s.push_str(&format!("(declare-const x{i} S)\n"));
    }
    s
}

/// `(distinct x1 .. xn)`.
fn distinct_of(n: usize) -> String {
    let args = (1..=n)
        .map(|i| format!("x{i}"))
        .collect::<Vec<_>>()
        .join(" ");
    format!("(distinct {args})")
}

const N: usize = 40; // comfortably past the pairwise threshold (32)

// ---------------------------------------------------------------------
// Injective map: positive `distinct` over an uninterpreted sort
// ---------------------------------------------------------------------

#[test]
fn large_distinct_over_uninterpreted_sort_is_sat() {
    check(
        &format!("{}(assert {})\n(check-sat)\n", uf_header(N), distinct_of(N)),
        "sat",
    );
}

#[test]
fn large_distinct_with_one_forced_equality_is_unsat() {
    check(
        &format!(
            "{}(assert {})\n(assert (= x2 x17))\n(check-sat)\n",
            uf_header(N),
            distinct_of(N)
        ),
        "unsat",
    );
}

#[test]
fn large_distinct_with_duplicate_argument_is_unsat() {
    // `distinct(x1, x1, ...)` – the duplicate must collide the two
    // distinguished witnesses assigned to the same term.
    let mut args: Vec<String> = (1..=N).map(|i| format!("x{i}")).collect();
    args[1] = "x1".to_string();
    check(
        &format!(
            "{}(assert (distinct {}))\n(check-sat)\n",
            uf_header(N),
            args.join(" ")
        ),
        "unsat",
    );
}

#[test]
fn large_distinct_model_assigns_pairwise_distinct_witnesses() {
    // `get-model` must give the x_i pairwise-distinct elements: the value
    // true on the result literal has to be backed by a real model.
    let script = format!(
        "{}(assert {})\n(check-sat)\n(get-value ({}))\n",
        uf_header(N),
        distinct_of(N),
        distinct_of(N)
    );
    let out = run(&script);
    assert!(
        out.iter().any(|l| l.contains("true")),
        "distinct term evaluates true in the model: {out:?}"
    );
}

#[test]
fn large_distinct_nested_under_negation_of_equality_pair() {
    // Nested (non-root) occurrence: `(or (not D) (= x1 x2))` with x1 != x2
    // forces D true through the ordinary clause structure.
    check(
        &format!(
            "{}(assert (or (not {}) (= x1 x2)))\n(assert (not (= x1 x2)))\n(check-sat)\n",
            uf_header(N),
            distinct_of(N)
        ),
        "sat",
    );
    // ... and the same shape with D additionally falsified by a forced
    // collision is unsat.
    check(
        &format!(
            "{}(assert (or (not {}) (= x1 x2)))\n(assert (not (= x1 x2)))\n(assert (= x3 x4))\n(assert {})\n(check-sat)\n",
            uf_header(N),
            distinct_of(N),
            distinct_of(N)
        ),
        "unsat",
    );
}

// ---------------------------------------------------------------------
// Injective map: negated `distinct`
// ---------------------------------------------------------------------

#[test]
fn large_not_distinct_alone_is_sat() {
    check(
        &format!(
            "{}(assert (not {}))\n(check-sat)\n",
            uf_header(N),
            distinct_of(N)
        ),
        "sat",
    );
}

#[test]
fn large_not_distinct_with_forced_equality_is_sat() {
    check(
        &format!(
            "{}(assert (not {}))\n(assert (= x5 x17))\n(check-sat)\n",
            uf_header(N),
            distinct_of(N)
        ),
        "sat",
    );
}

#[test]
fn large_not_distinct_with_all_pairs_apart_is_unsat() {
    // The congruence inversion: at-least-two pins f(x_i) = f(x_j) = a, the
    // g-units give x_i = g(a) = x_j, and the pairwise disequalities refute.
    // This is the case a too-weak at-least-two encoding would answer `sat`.
    let mut script = uf_header(N);
    for i in 1..=N {
        for j in (i + 1)..=N {
            script.push_str(&format!("(assert (not (= x{i} x{j})))\n"));
        }
    }
    script.push_str(&format!("(assert (not {}))\n(check-sat)\n", distinct_of(N)));
    check(&script, "unsat");
}

#[test]
fn large_not_distinct_with_duplicate_argument_is_sat() {
    // ¬distinct(x1, x1, ...) is trivially true.
    let mut args: Vec<String> = (1..=N).map(|i| format!("x{i}")).collect();
    args[1] = "x1".to_string();
    check(
        &format!(
            "{}(assert (not (distinct {})))\n(check-sat)\n",
            uf_header(N),
            args.join(" ")
        ),
        "sat",
    );
}

// ---------------------------------------------------------------------
// Pigeonhole short-circuit on finite sorts
// ---------------------------------------------------------------------

#[test]
fn distinct_over_bool_pigeonhole_is_unsat() {
    check(
        "(declare-const b1 Bool)\n(declare-const b2 Bool)\n(declare-const b3 Bool)\n\
         (assert (distinct b1 b2 b3))\n(check-sat)\n",
        "unsat",
    );
}

#[test]
fn distinct_over_two_bools_is_sat() {
    // Control: exactly at the cardinality, no short-circuit may fire.
    check(
        "(declare-const b1 Bool)\n(declare-const b2 Bool)\n(assert (distinct b1 b2))\n(check-sat)\n",
        "sat",
    );
}

#[test]
fn not_distinct_over_bool_pigeonhole_is_sat() {
    // The negation of a pigeonhole-false term is true.
    check(
        "(declare-const b1 Bool)\n(declare-const b2 Bool)\n(declare-const b3 Bool)\n\
         (assert (not (distinct b1 b2 b3)))\n(check-sat)\n",
        "sat",
    );
}

#[test]
fn distinct_over_bv1_pigeonhole_is_unsat() {
    check(
        "(declare-const v1 (_ BitVec 1))\n(declare-const v2 (_ BitVec 1))\n\
         (declare-const v3 (_ BitVec 1))\n(assert (distinct v1 v2 v3))\n(check-sat)\n",
        "unsat",
    );
}

#[test]
fn distinct_over_bv1_pair_is_sat() {
    check(
        "(declare-const v1 (_ BitVec 1))\n(declare-const v2 (_ BitVec 1))\n\
         (assert (distinct v1 v2))\n(check-sat)\n",
        "sat",
    );
}

#[test]
fn distinct_over_enum_pigeonhole_is_unsat() {
    check(
        "(declare-datatypes ((E 0)) (((e1) (e2))))\n\
         (declare-const v1 E)\n(declare-const v2 E)\n(declare-const v3 E)\n\
         (assert (distinct v1 v2 v3))\n(check-sat)\n",
        "unsat",
    );
}

#[test]
fn distinct_over_enum_exact_fit_is_sat() {
    check(
        "(declare-datatypes ((E 0)) (((e1) (e2))))\n\
         (declare-const v1 E)\n(declare-const v2 E)\n(assert (distinct v1 v2))\n(check-sat)\n",
        "sat",
    );
}

#[test]
fn distinct_over_enum_with_selector_is_never_shortcircuited() {
    // A datatype *with* selectors has no computed cardinality: three vars
    // over an infinite list type must stay a normal (sat) distinct.
    check(
        "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n\
         (declare-const v1 L)\n(declare-const v2 L)\n(declare-const v3 L)\n\
         (assert (distinct v1 v2 v3))\n(check-sat)\n",
        "sat",
    );
}

#[test]
fn distinct_over_int_stays_pairwise_and_correct() {
    // Non-EUF-owned sort at large arity: still pairwise, still correct.  The
    // variables are pinned to distinct constants because the *unpinned*
    // satisfiable shape is a pre-existing arith-disequality performance gap
    // (a 33-variable `distinct` over Int takes minutes in debug builds on
    // both the old and new encoder – identical before and after this
    // change; see the commit notes).  Pinning keeps this test about the
    // encoding path, not that gap.
    let mut script = String::new();
    for i in 1..=N {
        script.push_str(&format!("(declare-const x{i} Int)\n"));
    }
    let args = (1..=N)
        .map(|i| format!("x{i}"))
        .collect::<Vec<_>>()
        .join(" ");
    script.push_str(&format!("(assert (distinct {args}))\n"));
    for i in 1..=N {
        script.push_str(&format!("(assert (= x{i} {i}))\n"));
    }
    script.push_str("(check-sat)\n");
    check(&script, "sat");
}

#[test]
fn large_distinct_int_with_forced_equality_is_unsat() {
    let decls = (1..=N)
        .map(|i| format!("(declare-const x{i} Int)"))
        .collect::<Vec<_>>()
        .join("\n");
    let args = (1..=N)
        .map(|i| format!("x{i}"))
        .collect::<Vec<_>>()
        .join(" ");
    check(
        &format!("{decls}\n(assert (distinct {args}))\n(assert (= x4 x9))\n(check-sat)\n"),
        "unsat",
    );
}

// ---------------------------------------------------------------------
// Scope consistency
// ---------------------------------------------------------------------

#[test]
fn large_distinct_push_pop_then_negate_is_sat() {
    // The clauses, witnesses and e-graph marks of a popped encoding must not
    // leak into the verdict of a later, opposite assertion.
    check(
        &format!(
            "{}(push 1)\n(assert {})\n(check-sat)\n(pop 1)\n(assert (not {}))\n(check-sat)\n",
            uf_header(N),
            distinct_of(N),
            distinct_of(N)
        ),
        "sat",
    );
}

#[test]
fn large_distinct_incremental_rechecks_stay_consistent() {
    // Several checks with intervening assertions exercise the theory rebase
    // path: the e-graph is rebuilt from the trail and the value marks must be
    // re-declared from the symbol registry on every rebuild.
    check(
        &format!(
            "{}(assert {})\n(check-sat)\n(assert (= x2 x3))\n(check-sat)\n",
            uf_header(N),
            distinct_of(N)
        ),
        "unsat",
    );
}

#[test]
fn popped_large_distinct_does_not_poison_outer_scope() {
    // Distinct asserted *inside* a push must vanish with the pop; the outer
    // negated-distinct verdict must be plain `sat`.
    let script = format!(
        "{}(assert (not {}))\n(push 1)\n(assert {})\n(check-sat)\n(pop 1)\n(check-sat)\n",
        uf_header(N),
        distinct_of(N),
        distinct_of(N)
    );
    let out = run(&script);
    assert_eq!(
        out.iter().filter(|l| l.as_str() == "unsat").count(),
        1,
        "{out:?}"
    );
    assert_eq!(
        out.iter().filter(|l| l.as_str() == "sat").count(),
        1,
        "{out:?}"
    );
}

// ---------------------------------------------------------------------
// Boundary: the pairwise threshold itself
// ---------------------------------------------------------------------

#[test]
fn distinct_at_threshold_32_and_just_above_agree() {
    // 32 (pairwise) and 33 (injective map) must both behave correctly in
    // both polarities, with and without a forced collision.
    for n in [32usize, 33] {
        check(
            &format!("{}(assert {})\n(check-sat)\n", uf_header(n), distinct_of(n)),
            "sat",
        );
        check(
            &format!(
                "{}(assert {})\n(assert (= x1 x2))\n(check-sat)\n",
                uf_header(n),
                distinct_of(n)
            ),
            "unsat",
        );
        check(
            &format!(
                "{}(assert (not {}))\n(check-sat)\n",
                uf_header(n),
                distinct_of(n)
            ),
            "sat",
        );
    }
}

// ---------------------------------------------------------------------
// Injective map over Int/Real (the separation machinery)
// ---------------------------------------------------------------------

/// `n` Int constants `x1..xn` + `(distinct x1 .. xn)`.
fn int_header(n: usize) -> String {
    let mut s = String::from("(set-logic QF_LIA)\n");
    for i in 1..=n {
        s.push_str(&format!("(declare-const x{i} Int)\n"));
    }
    s
}

fn int_distinct(n: usize) -> String {
    let args = (1..=n)
        .map(|i| format!("x{i}"))
        .collect::<Vec<_>>()
        .join(" ");
    format!("(distinct {args})")
}

#[test]
fn large_distinct_int_free_vars_is_sat_with_distinct_model() {
    // The shape that stalled before the separation machinery existed.
    let script = format!(
        "{}(assert {})\n(check-sat)\n(get-value ((= x1 x2) (= x1 x40) (= x39 x40)))\n",
        int_header(N),
        int_distinct(N)
    );
    let out = run(&script);
    assert!(
        out.iter()
            .any(|l| l.contains("false") || l.contains("(= x1 x2)")),
        "expected evaluated equalities, got {out:?}"
    );
    // Stronger: pull the model and check pairwise distinctness ourselves.
    let model_script = format!(
        "{}(assert {})\n(check-sat)\n(get-model)\n",
        int_header(N),
        int_distinct(N)
    );
    let out = run(&model_script);
    let body = out.join("\n");
    let vals: Vec<&str> = body
        .lines()
        .filter(|l| l.contains("define-fun x"))
        .map(|l| l.split_whitespace().last().unwrap_or("?"))
        .collect();
    assert_eq!(vals.len(), N, "model lists all {N} variables");
    let mut sorted = vals.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(
        sorted.len(),
        vals.len(),
        "all model values pairwise distinct"
    );
}

#[test]
fn large_distinct_int_forced_equality_is_unsat() {
    check(
        &format!(
            "{}(assert {})\n(assert (= x2 x17))\n(check-sat)\n",
            int_header(N),
            int_distinct(N)
        ),
        "unsat",
    );
}

#[test]
fn large_distinct_int_duplicate_argument_is_unsat() {
    let mut args: Vec<String> = (1..=N).map(|i| format!("x{i}")).collect();
    args[1] = "x1".to_string();
    check(
        &format!(
            "{}(assert (distinct {}))\n(check-sat)\n",
            int_header(N),
            args.join(" ")
        ),
        "unsat",
    );
}

#[test]
fn large_distinct_int_bounds_pinned_collision_is_unsat() {
    // x and y are both forced to 5 through *bounds*, never an equality atom –
    // the shape that needs the care graph's entailed-merge path.
    let mut script = String::from(
        "(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const y Int)\n\
         (assert (>= x 5))\n(assert (<= x 5))\n(assert (= y 5))\n",
    );
    for i in 1..=(N - 2) {
        script.push_str(&format!("(declare-const a{i} Int)\n"));
    }
    let args = format!(
        "x y {}",
        (1..=(N - 2))
            .map(|i| format!("a{i}"))
            .collect::<Vec<_>>()
            .join(" ")
    );
    script.push_str(&format!("(assert (distinct {args}))\n(check-sat)\n"));
    check(&script, "unsat");
}

// The *bare* `(not (distinct x1 .. xn))` over free Int variables used to be
// a slow shape for both encodings (the co-located proposal block ignored the
// result literal's polarity and manufactured phantom separation work –
// ~2500 final-check arith refutations at n = 33).  Since the polarity gate
// it is instant, and the bare shape is asserted directly below.

#[test]
fn large_distinct_int_negated_with_all_pinned_is_unsat() {
    let mut script = int_header(33);
    for i in 1..=33 {
        script.push_str(&format!("(assert (= x{i} {i}))\n"));
    }
    script.push_str(&format!(
        "(assert (not {}))\n(check-sat)\n",
        int_distinct(33)
    ));
    check(&script, "unsat");
}

#[test]
fn large_distinct_int_negated_alone_is_sat() {
    // 0.02 s since the polarity gate (was 10 s at n = 33, timeout at 100).
    check(
        &format!(
            "{}(assert (not {}))\n(check-sat)\n",
            int_header(N),
            int_distinct(N)
        ),
        "sat",
    );
    check(
        &format!(
            "{}(assert (not {}))\n(check-sat)\n",
            int_header(100),
            int_distinct(100)
        ),
        "sat",
    );
}

#[test]
fn large_distinct_int_negated_with_equality_is_sat() {
    check(
        &format!(
            "{}(assert (not {}))\n(assert (= x5 x17))\n(check-sat)\n",
            int_header(N),
            int_distinct(N)
        ),
        "sat",
    );
}

#[test]
fn large_distinct_int_boundary_32_33() {
    // Both sides of the encoding threshold.  n = 32 keeps pairwise (its
    // satisfiable shape is a pre-existing slow case in debug builds, so only
    // the refuted one is asserted there); n = 33 takes the injective map and
    // both polarities run fast.
    check(
        &format!(
            "{}(assert {})\n(assert (= x1 x2))\n(check-sat)\n",
            int_header(32),
            int_distinct(32)
        ),
        "unsat",
    );
    check(
        &format!(
            "{}(assert {})\n(check-sat)\n",
            int_header(33),
            int_distinct(33)
        ),
        "sat",
    );
    check(
        &format!(
            "{}(assert {})\n(assert (= x1 x2))\n(check-sat)\n",
            int_header(33),
            int_distinct(33)
        ),
        "unsat",
    );
    // The bare negated shape at the boundary, both encodings' sides.
    check(
        &format!(
            "{}(assert (not {}))\n(check-sat)\n",
            int_header(33),
            int_distinct(33)
        ),
        "sat",
    );
}

#[test]
fn large_distinct_int_pinned_to_constants_is_sat() {
    // Every argument pinned to its own constant: easy sat, but exercises the
    // separation under concrete values.
    let mut script = int_header(N);
    for i in 1..=N {
        script.push_str(&format!("(assert (= x{i} {i}))\n"));
    }
    script.push_str(&format!("(assert {})\n(check-sat)\n", int_distinct(N)));
    check(&script, "sat");
}

#[test]
fn large_distinct_int_scope_pop_then_negate_with_equality_is_sat() {
    // n = 33: just past the threshold, fast in debug builds.
    check(
        &format!(
            "{}(push 1)\n(assert {})\n(check-sat)\n(pop 1)\n(assert (not {}))\n(assert (= x1 x2))\n(check-sat)\n",
            int_header(33),
            int_distinct(33),
            int_distinct(33)
        ),
        "sat",
    );
}

#[test]
fn large_distinct_int_incremental_rechecks_stay_consistent() {
    check(
        &format!(
            "{}(assert {})\n(check-sat)\n(assert (= x2 x3))\n(check-sat)\n",
            int_header(N),
            int_distinct(N)
        ),
        "unsat",
    );
}

#[test]
fn large_distinct_int_scale_200_is_fast_sat_with_distinct_model() {
    // The chain-shaped separation: one round of n-1 oriented clauses
    // distinctifies the whole co-located group by transitivity.  Before the
    // chain, n = 200 free variables did not converge (star/clique-shaped
    // proposals, one pair separating per round).
    let script = format!(
        "{}(assert {})\n(check-sat)\n(get-model)\n",
        int_header(200),
        int_distinct(200)
    );
    let out = run(&script);
    let body = out.join("\n");
    let vals: Vec<&str> = body
        .lines()
        .filter(|l| l.contains("define-fun x"))
        .map(|l| l.split_whitespace().last().unwrap_or("?"))
        .collect();
    assert_eq!(vals.len(), 200, "model lists all 200 variables");
    let mut sorted = vals.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(
        sorted.len(),
        vals.len(),
        "all 200 model values pairwise distinct"
    );
}

#[test]
fn large_distinct_int_scale_200_forced_eq_is_unsat() {
    check(
        &format!(
            "{}(assert {})\n(assert (= x3 x77))\n(check-sat)\n",
            int_header(200),
            int_distinct(200)
        ),
        "unsat",
    );
}

#[test]
fn large_distinct_int_negated_scale_100_is_sat() {
    check(
        &format!(
            "{}(assert (not {}))\n(check-sat)\n",
            int_header(100),
            int_distinct(100)
        ),
        "sat",
    );
}

#[test]
fn large_distinct_real_free_vars_is_sat() {
    let mut script = String::from("(set-logic QF_LRA)\n");
    for i in 1..=N {
        script.push_str(&format!("(declare-const r{i} Real)\n"));
    }
    let args = (1..=N)
        .map(|i| format!("r{i}"))
        .collect::<Vec<_>>()
        .join(" ");
    script.push_str(&format!("(assert (distinct {args}))\n(check-sat)\n"));
    check(&script, "sat");
}

// ---------------------------------------------------------------------
// Composite finite datatypes and the pigeonhole short-circuit
// ---------------------------------------------------------------------

#[test]
fn distinct_over_composite_finite_datatype_pigeonhole_is_unsat() {
    // |Pair| = |E2| * |E3| = 6; seven arguments cannot be distinct.
    check(
        "(declare-datatypes ((E2 0)) (((e1) (e2))))\n\
         (declare-datatypes ((E3 0)) (((f1) (f2) (f3))))\n\
         (declare-datatypes ((Pair 0)) (((mk (a E2) (b E3)))))\n\
         (declare-const p1 Pair)(declare-const p2 Pair)(declare-const p3 Pair)\n\
         (declare-const p4 Pair)(declare-const p5 Pair)(declare-const p6 Pair)\n\
         (declare-const p7 Pair)\n\
         (assert (distinct p1 p2 p3 p4 p5 p6 p7))\n(check-sat)\n",
        "unsat",
    );
}

#[test]
fn distinct_over_composite_finite_datatype_exact_fit_is_sat() {
    // Exactly |Pair| = 6 arguments: no short-circuit may fire, and the
    // datatype theory itself must accept the enumeration.
    check(
        "(declare-datatypes ((E2 0)) (((e1) (e2))))\n\
         (declare-datatypes ((E3 0)) (((f1) (f2) (f3))))\n\
         (declare-datatypes ((Pair 0)) (((mk (a E2) (b E3)))))\n\
         (declare-const p1 Pair)(declare-const p2 Pair)(declare-const p3 Pair)\n\
         (declare-const p4 Pair)(declare-const p5 Pair)(declare-const p6 Pair)\n\
         (assert (distinct p1 p2 p3 p4 p5 p6))\n(check-sat)\n",
        "sat",
    );
}

#[test]
fn distinct_over_recursive_datatype_is_never_shortcircuited() {
    // A self-referential datatype is infinite: three variables over it stay
    // a normal (sat) distinct.
    check(
        "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n\
         (declare-const v1 L)(declare-const v2 L)(declare-const v3 L)\n\
         (assert (distinct v1 v2 v3))\n(check-sat)\n",
        "sat",
    );
}

#[test]
fn distinct_over_mutually_recursive_datatypes_is_never_shortcircuited() {
    // A ⇄ B mutual recursion: infinite carriers, no short-circuit.
    check(
        "(declare-datatypes ((A 0) (B 0)) (((a1) (mkA (b B))) ((b1) (mkB (a A)))))\n\
         (declare-const x1 A)(declare-const x2 A)(declare-const x3 A)\n\
         (assert (distinct x1 x2 x3))\n(check-sat)\n",
        "sat",
    );
}

#[test]
fn distinct_over_nested_composite_datatype_pigeonhole_is_unsat() {
    // |Wrap| = |Pair| = 6 through one level of nesting; 7 arguments refute.
    check(
        "(declare-datatypes ((E2 0)) (((e1) (e2))))\n\
         (declare-datatypes ((E3 0)) (((f1) (f2) (f3))))\n\
         (declare-datatypes ((Pair 0)) (((mk (a E2) (b E3)))))\n\
         (declare-datatypes ((Wrap 0)) (((wrap (inner Pair)))))\n\
         (declare-const w1 Wrap)(declare-const w2 Wrap)(declare-const w3 Wrap)\n\
         (declare-const w4 Wrap)(declare-const w5 Wrap)(declare-const w6 Wrap)\n\
         (declare-const w7 Wrap)\n\
         (assert (distinct w1 w2 w3 w4 w5 w6 w7))\n(check-sat)\n",
        "unsat",
    );
}
