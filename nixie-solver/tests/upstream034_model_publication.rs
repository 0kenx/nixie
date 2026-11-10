//! Public model regressions from the upstream 0.3.4 publication migration.
use nixie_solver::Context;

#[test]
fn equality_model_partition_is_replaced_on_each_check() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(declare-sort U 0)
        (declare-const a U)(declare-const b U)(declare-const c U)(declare-const d U)
        (assert (or (= a c) (= a d)))(assert (or (= b c) (= b d)))
        (assert (distinct c d))(check-sat)
        (assert (= a c))(check-sat)(assert (= b d))(check-sat)
        (get-value ((= a c) (= b d) (= c d)))
        (push)(assert (= c d))(check-sat)(pop)(check-sat)
        (get-value ((= a c) (= b d) (= c d)))",
        )
        .expect("script");
    assert_eq!(&out[..3], ["sat", "sat", "sat"]);
    assert_eq!(
        out[3].replace('\n', ""),
        "(((= a c) true) ((= b d) true) ((= c d) false))"
    );
    assert_eq!(&out[4..6], ["unsat", "sat"]);
    assert_eq!(out[3], out[6]);
}

#[test]
fn witness_symbols_do_not_capture_declarations_or_rewrite_strings() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(declare-sort U 0)
        (declare-const @uc_U_0 U)(declare-const a U)
        (declare-const s String)(assert (distinct a @uc_U_0))
        (assert (= s \"@uc_U_0\"))(check-sat)(get-model)(get-model)
        (get-value (s (= a @uc_U_0)))",
        )
        .expect("script");
    assert_eq!(out[0], "sat", "{out:?}");
    assert_eq!(out[1], out[2]);
    assert!(!out[1].contains("() U @uc_U_0)"), "{out:?}");
    assert_eq!(
        out[3].replace('\n', ""),
        "((s \"@uc_U_0\") ((= a @uc_U_0) false))"
    );
}

#[test]
fn affine_certificate_is_the_published_function() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic UFLRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (= (f x) (+ (* 2.0 x) 1.0))))
        (check-sat)(get-model)(get-value ((f 3.0) (f (- 2.0))))",
        )
        .expect("script");
    assert_eq!(out[0], "sat", "{out:?}");
    assert!(out[1].contains("x!0"), "{out:?}");
    assert!(out[2].contains("7.0") && out[2].contains("-3.0"), "{out:?}");
    let definitions = out[1]
        .strip_prefix("(model")
        .and_then(|s| s.strip_suffix(')'))
        .expect("model");
    let replay = format!("{definitions}(assert (not (= (f 3.0) 7.0)))(check-sat)");
    assert_eq!(
        Context::new()
            .execute_script(&replay)
            .expect("model replay"),
        ["unsat"]
    );
}

#[test]
fn bitvector_condition_is_published_with_its_circuit_assignment() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(declare-const c Bool)(declare-const x (_ BitVec 8))
        (assert (or (= (ite c #x01 #x02) x) (= x #x09)))
        (check-sat)(get-model)",
        )
        .expect("script");
    assert_eq!(out[0], "sat", "{out:?}");
    let rows = ctx.get_model().expect("model");
    let definitions: String = rows
        .into_iter()
        .map(|(n, s, v)| format!("(define-fun {n} () {s} {v})"))
        .collect();
    let replay =
        format!("{definitions}(assert (not (or (= (ite c #x01 #x02) x) (= x #x09))))(check-sat)");
    assert_eq!(
        Context::new().execute_script(&replay).expect("replay"),
        ["unsat"]
    );
}

#[test]
fn positive_bag_images_require_real_preimages() {
    for assertion in [
        "(= (bag.count 5 (bag.map f b)) 1)",
        "(bag.member 5 (bag.map f b))",
    ] {
        let script = format!(
            "(set-logic ALL)(define-fun f ((x Int)) Int 0)
            (declare-const b (Bag Int))(assert {assertion})(check-sat)"
        );
        assert_eq!(
            Context::new().execute_script(&script).expect("script"),
            ["unsat"],
            "{script}"
        );
    }
}

#[test]
fn uninterpreted_constants_and_function_tables_share_witnesses() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_UF)
        (declare-sort U 0) (declare-fun f (U) U)
        (declare-const a U) (declare-const b U)
        (assert (distinct a b)) (assert (= (f a) b))
        (check-sat) (get-model) (get-value (a b (f a)))",
        )
        .expect("valid script");
    assert_eq!(out[0], "sat", "{out:?}");
    let rows = ctx.get_model().expect("published model");
    let a = &rows.iter().find(|(name, _, _)| name == "a").expect("a").2;
    let b = &rows.iter().find(|(name, _, _)| name == "b").expect("b").2;
    assert_ne!(a, b);
    assert!(out[2].contains(&format!("((f a) {b})")), "{out:?}");
    assert!(out[2].contains(&format!("(a {a})")), "{out:?}");
    assert!(out[1].contains("(define-fun f "), "{out:?}");
}

#[test]
fn distinct_arrays_publish_the_extensional_witness() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 1) (_ BitVec 1)))
        (declare-const b (Array (_ BitVec 1) (_ BitVec 1)))
        (assert (distinct a b)) (check-sat) (get-model)",
        )
        .expect("valid script");
    assert_eq!(out[0], "sat", "{out:?}");
    let rows = ctx.get_model().expect("published arrays");
    assert_ne!(rows[0].2, rows[1].2, "{out:?}");
    let mut replay = Context::new();
    let pinned = format!(
        "(set-logic QF_ABV)
        (define-fun a () (Array (_ BitVec 1) (_ BitVec 1)) {})
        (define-fun b () (Array (_ BitVec 1) (_ BitVec 1)) {})
        (assert (distinct a b)) (check-sat)",
        rows[0].2, rows[1].2
    );
    assert_eq!(replay.execute_script(&pinned).expect("replay"), ["sat"]);
}

#[test]
fn published_models_follow_assumptions_and_scope_changes() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(declare-const p Bool)
        (declare-const a (Array Bool Bool))
        (assert (= (select a false) p))
        (check-sat-assuming (p)) (get-value ((select a false)))
        (check-sat-assuming ((not p))) (get-value ((select a false)))
        (push) (get-model) (assert p) (check-sat) (get-value (p))
        (pop) (get-model)",
        )
        .expect("valid script");
    assert_eq!(out[0], "sat", "{out:?}");
    assert!(out[1].contains("true"), "{out:?}");
    assert_eq!(out[2], "sat", "{out:?}");
    assert!(out[3].contains("false"), "{out:?}");
    assert!(out[4].starts_with("(error"), "{out:?}");
    assert_eq!(out[5], "sat", "{out:?}");
    assert!(out[6].contains("true"), "{out:?}");
    assert!(out[7].starts_with("(error"), "{out:?}");
}

#[test]
fn a_new_declaration_refreshes_the_published_witness_names() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(declare-sort U 0)(declare-const a U)(check-sat)
        (declare-const @uc_U_0 U)(get-model)(check-sat)(get-model)",
        )
        .expect("script");
    assert_eq!(out[0], "sat");
    assert!(out[1].starts_with("(model"), "{out:?}");
    assert!(!out[1].contains("() U @uc_U_0)"), "{out:?}");
    assert_eq!(out[2], "sat");
    assert!(!out[3].contains("() U @uc_U_0)"), "{out:?}");
}

#[test]
fn unverified_zero_division_model_is_withheld() {
    let mut ctx = Context::new();
    let out = ctx
        .execute_script(
            "(set-logic UFLIA)(declare-fun f (Int) Int)(declare-const y Int)
        (assert (forall ((z Int)) (>= (f z) 0)))
        (assert (= y 1))(assert (distinct (f y) (f (div 1 0))))
        (check-sat)(get-model)(get-value ((div 1 0) (div 7 0) (distinct (f y) (f (div 1 0)))))",
        )
        .expect("script");
    assert_eq!(out[0], "unknown", "{out:?}");
    assert!(
        out[1].contains("error") && out[2].contains("error"),
        "{out:?}"
    );
}

#[test]
fn integer_values_are_printed_at_the_declared_sort() {
    let out = Context::new()
        .execute_script(
            "(declare-const x Int)
        (assert (= (to_real x) 3.0))(check-sat)(get-model)(get-value (x))",
        )
        .expect("script");
    assert_eq!(out[0], "sat");
    assert!(out[1].contains("(define-fun x () Int 3)"), "{out:?}");
    assert_eq!(out[2], "((x 3))");
}

#[test]
fn nested_array_function_arguments_cannot_publish_inconsistent_tables() {
    let out = Context::new()
        .execute_script(
            "(declare-datatype E ((ea)(eb)(ec)))
        (declare-const x Int)(declare-const y Int)
        (declare-fun h ((Array Int E)) Int)(declare-const a (Array Int (Array Int E)))
        (assert (<= 0 x 4))(assert (<= 0 y 4))
        (assert (distinct (h (select a x)) (h (select a y))))
        (assert (= (select (select a x) 0) ea))(check-sat)(get-model)
        (get-value ((distinct (h (select a x)) (h (select a y))) (= (select (select a x) 0) ea)))",
        )
        .expect("script");
    // The independent parser and reader must catch the former model, whose
    // two h arguments both denoted the everywhere-ea array but had -1/0 results.
    assert!(matches!(out[0].as_str(), "sat" | "unknown"), "{out:?}");
    if out[0] == "unknown" {
        assert!(out[1].starts_with("(error"));
    } else {
        assert!(
            out[2].contains("(distinct (h (select a x)) (h (select a y))) true"),
            "{out:?}"
        );
        assert!(
            out[2].contains("(= (select (select a x) 0) ea) true"),
            "{out:?}"
        );
    }
}
