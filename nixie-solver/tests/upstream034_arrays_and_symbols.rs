//! OxiZ 0.3.4 array congruence and SMT-LIB naming regressions.
use nixie_solver::Context;

#[test]
fn upstream_e77bed0344bffb4a() {
    let output = Context::new()
        .execute_script(
            r##"
(set-logic QF_AUFLIA)
(declare-const arr (Array Int Int))
(declare-const i Int)
(declare-const v Int)
(declare-const w Int)
(assert (= v w))
(assert (distinct (store arr i v) (store arr i w)))
(check-sat)
"##,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
}

#[test]
fn upstream_9269018a5a5dfd37() {
    let output = Context::new()
        .execute_script(
            r##"
(set-logic QF_AUFBV)
(declare-fun |(as const)| ((_ BitVec 8)) (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= (select (|(as const)| #x00) #x00) #x05))
(check-sat)
"##,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["sat"]);
}

#[test]
fn upstream_e3db58089d90293f() {
    let output = Context::new()
        .execute_script(
            r##"
(set-logic QF_AUF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const arr (Array U U))
(declare-const i U)
(declare-const v U)
(assert (distinct (f (select (store arr i v) i)) (f v)))
(check-sat)
"##,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
}

#[test]
fn upstream_8e513ca57fd8f614() {
    let output = Context::new()
        .execute_script(
            r##"
(set-logic QF_AUF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const arr (Array U U))
(declare-const i U)
(declare-const j U)
(declare-const v U)
(assert (distinct i j))
(assert (distinct (f (select (store arr i v) j)) (f (select arr j))))
(check-sat)
"##,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
}

#[test]
fn upstream_6f7226844b3a571f() {
    let output = Context::new()
        .execute_script(
            r##"
(set-logic QF_AUF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const arr (Array U U))
(declare-const i U)
(declare-const j U)
(declare-const v U)
(assert (distinct i j))
(assert (distinct (f (select (store arr i v) j)) (f v)))
(check-sat)
"##,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["sat"]);
}

#[test]
fn upstream_90bb84b06ae53573() {
    let output = Context::new()
        .execute_script(
            r##"
(set-logic QF_AUF)
(declare-sort U 0)
(declare-const arr (Array U U))
(declare-const i U)
(declare-const v U)
(assert (distinct (select (store arr i v) i) v))
(check-sat)
"##,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
}

#[test]
fn upstream_db729f7712870791() {
    let output = Context::new()
        .execute_script(
            r##"
(set-logic QF_AUF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const arr (Array U U))
(declare-const i U)
(declare-const v U)
(assert (distinct (f (select (store arr i v) i)) (f v)))
(assert (= (select (store arr i v) i) v))
(check-sat)
"##,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
}

#[test]
fn get_value_preserves_definition_and_quoted_query_spelling() {
    let output = Context::new()
        .execute_script(
            r#"
        (declare-const |a b| Int)
        (assert (= |a b| 4))
        (define-fun twice ((x Int)) Int (+ x x))
        (check-sat)
        (get-value (|a b| (twice |a b|) (+ 1 2)))
        (get-model)
    "#,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output[0], "sat");
    assert_eq!(output[1], "((|a b| 4)\n ((twice |a b|) 8)\n ((+ 1 2) 3))");
    assert!(
        output[2].contains("(define-fun |a b| () Int 4)"),
        "{}",
        output[2]
    );
}

#[test]
fn internal_symbol_capture_and_ill_sorted_constant_arrays_are_errors() {
    for input in [
        r"(declare-const |\nixie.ext!0!1| Int)",
        r"(declare-fun |\nixie.const-array| (Int) (Array Int Int))",
        "(assert (= ((as const Int) 0) 0))",
        "(assert (= ((as const (Array Int Bool)) 0) ((as const (Array Int Bool)) true)))",
        "(assert (= ((as const (Array Int Int)) 0 1) ((as const (Array Int Int)) 0)))",
    ] {
        let result = Context::new().execute_script(input);
        assert!(
            result.is_err()
                || result
                    .as_ref()
                    .is_ok_and(|lines| lines.iter().any(|line| line.starts_with("(error"))),
            "{input}: {result:?}"
        );
    }
}

#[test]
fn upstream_3b00fbac3636ab3c() {
    let output = Context::new()
        .execute_script(
            r####"
(set-logic QF_AUFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(assert (distinct (f (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x03) #x01)) (f #x03)))
(check-sat)
"####,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
}

#[test]
fn array_discovery_survives_scope_rollback() {
    let output = Context::new()
        .execute_script(
            r#"
        (set-logic QF_AUF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a (Array U U))
        (declare-const i U)
        (declare-const v U)
        (push 1)
        (assert (distinct (f (select (store a i v) i)) (f v)))
        (check-sat)
        (pop 1)
        (check-sat)
        (push 1)
        (assert (distinct (f (select (store a i v) i)) (f v)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat", "sat", "unsat", "sat"]);
}

#[test]
fn quoted_sorts_and_constructors_round_trip_in_models() {
    let output = Context::new()
        .execute_script(
            r#"
        (declare-datatype |D ()| ((|nil x|) (|cons x| (|head x| Int))))
        (declare-const |value x| |D ()|)
        (assert (= |value x| |nil x|))
        (check-sat)
        (get-model)
        (get-value (|value x|))
    "#,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output[0], "sat");
    assert!(
        output[1].contains("(define-fun |value x| () |D ()| |nil x|)"),
        "{}",
        output[1]
    );
    assert_eq!(output[2], "((|value x| |nil x|))");
}

#[test]
fn quoted_sort_names_survive_nested_array_sort_resolution() {
    let output = Context::new()
        .execute_script(
            r#"
        (declare-sort |U ()| 0)
        (declare-const a (Array |U ()| (Array Int |U ()|)))
        (declare-const x |U ()|)
        (check-sat)
        (get-model)
    "#,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output[0], "sat");
    assert!(
        output[1].contains("(define-fun a () (Array |U ()| (Array Int |U ()|))"),
        "{}",
        output[1]
    );
    assert!(
        output[1].contains("(define-fun x () |U ()| |@uc_U ()_0|)"),
        "{}",
        output[1]
    );
}
