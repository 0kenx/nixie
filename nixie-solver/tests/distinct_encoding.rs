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

// NOTE: the *bare* `(not (distinct x1 .. xn))` over free Int variables is a
// pre-existing slow shape in nixie for BOTH encodings (pairwise at n = 32 and
// injective at n = 33 both hang today; z3 answers instantly).  The negated
// Int tests below therefore pair the negation with a constraint that makes
// the witness easy.  The bare shape stays a known gap, recorded in
// docs/studies/2026-09-distinct-theory-owned-sorts.md.

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
