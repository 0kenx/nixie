//! A scalar constant with no model entry is not handed to the array renderer.
//!
//! `Context::model_rows` renders an array-sorted constant in its own arm (the
//! sort is matched before anything else).  A later arm used to call the same
//! renderer again for every constant that reached it – which, arrays having
//! been answered already, were exactly the *non-array* constants with no model
//! entry.  For a scalar sort the renderer can only answer `None`: the class
//! holds no array, so there is no constant default, no `store` member, no
//! read and no store to inherit.  But it established that by walking the
//! constant's congruence class, the model's assignments and the whole term
//! arena – once per constant.  4,096 unconstrained `Int` constants spent 70 ms
//! there for rows that cost 0.4 ms (`docs/studies`).
//!
//! The arm is gone; the rows are what these tests pin.  The equivalence
//! itself – "the renderer answers `None` for every constant that reaches the
//! later arms" – is asserted under `debug_assertions` in `model_rows` itself,
//! so every dev-profile model rendering checks it.

/// One script mixing every shape the later arms of `model_rows` answer:
/// sort defaults of `Int`, `Bool`, `BitVec` and `Real`, the two witnesses of
/// uninterpreted-sort constants proven apart, a constant the model assigns,
/// and an array constant (its own arm).
const MIXED: &str = "
(set-logic ALL)
(declare-sort U 0)
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun b1 () Bool)
(declare-fun bv () (_ BitVec 4))
(declare-fun r () Real)
(declare-fun u () U)
(declare-fun w () U)
(declare-fun a () (Array Int Int))
(assert (= i2 7))
(assert (= (select a 1) 5))
(assert (= b1 (= u w)))
(check-sat)
(get-model)
(get-value (i1 i2 b1 bv r u a (select a 1) (select a 2) (+ i1 1)))
";

fn outputs(script: &str) -> Vec<String> {
    let mut ctx = nixie_solver::Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

#[test]
fn mixed_model_rows_and_the_batch_that_reads_them() {
    let out = outputs(MIXED);
    assert_eq!(out.len(), 3, "sat, the model, the values: {out:?}");
    assert_eq!(out[0].trim(), "sat");
    let model = &out[1];
    for row in [
        "(define-fun i1 () Int 0)",
        "(define-fun i2 () Int 7)",
        "(define-fun b1 () Bool false)",
        "(define-fun bv () (_ BitVec 4) #b0000)",
        "(define-fun r () Real 0.0)",
        "(define-fun u () U @uc_U_0)",
        "(define-fun w () U @uc_U_1)",
        "(define-fun a () (Array Int Int) (store ((as const (Array Int Int)) 0) 1 5))",
    ] {
        assert!(model.contains(row), "no row {row} in:\n{model}");
    }
    assert_eq!(
        model.matches("(define-fun ").count(),
        8,
        "one row per declared constant, no function interpretations:\n{model}"
    );
    // The batch answers from the same rows.
    let values = &out[2];
    for answer in [
        "(i1 0)",
        "(i2 7)",
        "(b1 false)",
        "(bv #b0000)",
        "(r 0.0)",
        "(u @uc_U_0)",
        "(a (store ((as const (Array Int Int)) 0) 1 5))",
        "((select a 1) 5)",
        "((select a 2) 0)",
        "((+ i1 1) 1)",
    ] {
        assert!(values.contains(answer), "no answer {answer} in:\n{values}");
    }
}

/// Many unassigned scalar constants of several sorts: every row is the
/// sort's default, in declaration order, and `(get-value)` over the same
/// batch answers row for row the same.
#[test]
fn many_unassigned_scalar_constants_render_their_defaults() {
    const PER_SORT: usize = 128;
    let mut script = String::from("(set-logic ALL)\n");
    for i in 0..PER_SORT {
        script.push_str(&format!(
            "(declare-fun i{i} () Int)\n(declare-fun b{i} () Bool)\n(declare-fun h{i} () (_ \
             BitVec 8))\n(declare-fun s{i} () String)\n"
        ));
    }
    script.push_str("(check-sat)\n(get-model)\n(get-value (");
    for i in 0..PER_SORT {
        script.push_str(&format!("i{i} b{i} h{i} s{i} "));
    }
    script.push_str("))\n");

    let out = outputs(&script);
    assert_eq!(out.len(), 3);
    assert_eq!(out[0].trim(), "sat");
    let model = &out[1];
    let mut rows = 0;
    for line in model.lines().map(str::trim) {
        let Some(rest) = line.strip_prefix("(define-fun ") else {
            continue;
        };
        rows += 1;
        let (name, _) = rest
            .split_once(" () ")
            .expect("a constant's row has an empty parameter list");
        let expected = if name.starts_with('i') {
            "Int 0)"
        } else if name.starts_with('b') {
            "Bool false)"
        } else if name.starts_with('h') {
            "(_ BitVec 8) #b00000000)"
        } else if name.starts_with('s') {
            "String \"\")"
        } else {
            panic!("unexpected row {line}");
        };
        assert!(
            rest.ends_with(expected),
            "row {line} does not end with the sort default {expected}"
        );
    }
    assert_eq!(rows, 4 * PER_SORT, "one row per constant:\n{model}");
    // Declaration order.
    let first_i = model.find("(define-fun i0 ").expect("i0");
    let first_b = model.find("(define-fun b0 ").expect("b0");
    let first_h = model.find("(define-fun h0 ").expect("h0");
    let first_s = model.find("(define-fun s0 ").expect("s0");
    assert!(first_i < first_b && first_b < first_h && first_h < first_s);
    let last_i = model.rfind("(define-fun i").expect("last i");
    assert!(first_s < last_i, "the rows follow the declaration list");

    let values = &out[2];
    for i in 0..PER_SORT {
        for answer in [
            format!("(i{i} 0)"),
            format!("(b{i} false)"),
            format!("(h{i} #b00000000)"),
            format!("(s{i} \"\")"),
        ] {
            assert!(values.contains(&answer), "no answer {answer}");
        }
    }
}

/// The completion `(get-value)` builds for an unconstrained constant is the
/// row's value, so a compound query over one folds: `(+ x 1)` is `1`, not
/// `(+ 0 1)` and not an echo of the term.
#[test]
fn compounds_over_unassigned_scalars_fold_with_the_default() {
    let out = outputs(
        "(set-logic ALL)\
         (declare-fun x () Int)\
         (declare-fun v () (_ BitVec 4))\
         (declare-fun p () Bool)\
         (check-sat)\
         (get-value ((+ x 1) (bvnot v) (not p) (ite p 1 2) (select ((as const (Array Int Int)) 3) x)))",
    );
    assert_eq!(out.len(), 2);
    assert_eq!(out[0].trim(), "sat");
    let values = &out[1];
    for answer in [
        "((+ x 1) 1)",
        "((bvnot v) #xf)",
        "((not p) true)",
        "((ite p 1 2) 2)",
        "x) 3)",
    ] {
        assert!(values.contains(answer), "no answer {answer} in:\n{values}");
    }
}
