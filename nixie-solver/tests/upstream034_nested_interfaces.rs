use nixie_solver::Context;
#[test]
fn upstream_0dc1430b51db7091() {
    let output = Context::new()
        .execute_script(
            r####"
(set-logic QF_ABV)
(declare-const i (_ BitVec 8))
(assert (= (bvadd (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x02) i) #x01) #x06))
(check-sat)
"####,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
}
#[test]
fn upstream_b5dfcc97b6ffaa95() {
    let output = Context::new()
        .execute_script(
            r####"(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((T 0) (E 0)) (((leaf) (node (val Int) (lft T) (rgt T))) ((ea) (eb) (ec))))
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(assert (<= 0 x 4))
(assert (<= 0 y 4))
(assert (<= 0 z 4))
(assert (<= 0 w 4))
(declare-const u1 U)
(declare-const u2 U)
(declare-const u3 U)
(declare-const a (Array (_ BitVec 1) (Array (_ BitVec 1) E)))
(declare-const i (_ BitVec 1))
(declare-const j (_ BitVec 1))
(declare-const k (_ BitVec 1))
(assert (distinct (select (select a i) i) (select (select a j) j) (select (select a k) k)))
(assert (distinct (select (select a i) #b0) eb))
(check-sat)

"####,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
}
#[test]
fn upstream_da4a7dbb324e905d() {
    let output = Context::new()
        .execute_script(
            r####"(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((T 0) (E 0)) (((leaf) (node (val Int) (lft T) (rgt T))) ((ea) (eb) (ec))))
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(assert (<= 0 x 4))
(assert (<= 0 y 4))
(assert (<= 0 z 4))
(assert (<= 0 w 4))
(declare-const u1 U)
(declare-const u2 U)
(declare-const u3 U)
(declare-const a (Array Bool (Array Int U)))
(declare-const p Bool)
(declare-const q Bool)
(assert (distinct u1 u2 u3))
(assert (= (select (select a p) 0) u1))
(assert (= (select (select a q) 0) u2))
(assert (= (select (select a (and p q)) 0) u3))
(check-sat)
"####,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
}
#[test]
fn upstream_703c86c2d469b0d5() {
    let output = Context::new()
        .execute_script(
            r####"(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((T 0) (E 0)) (((leaf) (node (val Int) (lft T) (rgt T))) ((ea) (eb) (ec))))
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(assert (<= 0 x 4))
(assert (<= 0 y 4))
(assert (<= 0 z 4))
(assert (<= 0 w 4))
(declare-const u1 U)
(declare-const u2 U)
(declare-const u3 U)
(declare-const a (Array Int (Array Int E)))
(assert (= a ((as const (Array Int (Array Int E))) ((as const (Array Int E)) ea))))
(assert (= (select (select a x) y) eb))
(check-sat)
"####,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
}

#[test]
fn upstream_ebbda25801e853ef() {
    let output = Context::new()
        .execute_script(
            r####"(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((T 0) (E 0)) (((leaf) (node (val Int) (lft T) (rgt T))) ((ea) (eb) (ec))))
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(assert (<= 0 x 4))
(assert (<= 0 y 4))
(assert (<= 0 z 4))
(assert (<= 0 w 4))
(declare-const u1 U)
(declare-const u2 U)
(declare-const u3 U)
(declare-const a (Array Int (Array Int E)))
(assert (forall ((k Int)) (=> (and (<= 0 k) (<= k 4)) (= (select (select a k) 0) ea))))
(assert (= (select (select a x) 0) eb))
(check-sat)
"####,
        )
        .expect("valid SMT-LIB");
    assert_eq!(output, ["unsat"]);
}

#[test]
fn finite_bv_arguments_are_checked_without_bv_result_circuits() {
    for mode in ["eager", "lazy"] {
        let script = format!("(set-logic ALL)(set-option :theory-mode {mode})
            (declare-sort U 0)(declare-fun f ((_ BitVec 1)) U)
            (declare-const x (_ BitVec 1))(declare-const y (_ BitVec 1))(declare-const z (_ BitVec 1))
            (assert (distinct (f x) (f y)))(check-sat)
            (push 1)(assert (distinct (f x) (f y) (f z)))(check-sat)(pop 1)(check-sat)");
        assert_eq!(
            Context::new().execute_script(&script).unwrap(),
            ["sat", "unsat", "sat"],
            "{mode}"
        );
    }
}

#[test]
fn boolean_array_indices_follow_sat_polarities_and_scopes() {
    for mode in ["eager", "lazy"] {
        for (definitions, first, second) in [
            (
                "(declare-const p Bool)(declare-const q Bool)",
                "(and p q)",
                "(not (or (not p) (not q)))",
            ),
            (
                "(declare-const x Int)(declare-const y Int)",
                "(< x y)",
                "(not (>= x y))",
            ),
            ("(declare-const p Bool)", "(not p)", "(= p false)"),
            ("", "true", "(not false)"),
        ] {
            let script = format!(
                "(set-logic ALL)(set-option :theory-mode {mode})
                {definitions}(declare-const a (Array Bool Int))
                (assert (= (select a {first}) 1))(check-sat)
                (push 1)(assert (= (select a {second}) 2))(check-sat)(pop 1)(check-sat)"
            );
            assert_eq!(
                Context::new().execute_script(&script).unwrap(),
                ["sat", "unsat", "sat"],
                "{script}"
            );
        }
    }
}

#[test]
fn boolean_uf_arguments_can_be_compound_array_reads() {
    for mode in ["eager", "lazy"] {
        let script = format!(
            "(set-logic ALL)(set-option :theory-mode {mode})
            (declare-const a (Array Bool Bool))(declare-const p Bool)
            (declare-fun f (Bool) Int)
            (assert (= (select a p) (not p)))
            (assert (< (f (select a p)) (f (not p))))(check-sat)"
        );
        assert_eq!(
            Context::new().execute_script(&script).unwrap(),
            ["unsat"],
            "{mode}"
        );
    }
}

#[test]
fn nested_constant_arrays_are_conditional_and_scope_consistent() {
    for mode in ["eager", "lazy"] {
        let script = format!("(set-logic ALL)(set-option :theory-mode {mode})
            (declare-datatype E ((ea)(eb)))(declare-const p Bool)
            (declare-const a (Array Int (Array Int E)))
            (assert (=> p (= a ((as const (Array Int (Array Int E))) ((as const (Array Int E)) ea)))))
            (assert (= (select (select a 0) 1) eb))(check-sat)
            (push 1)(assert p)(check-sat)(pop 1)(check-sat)
            (push 1)(assert (not p))(check-sat)(pop 1)");
        assert_eq!(
            Context::new().execute_script(&script).unwrap(),
            ["sat", "unsat", "sat", "sat"],
            "{mode}"
        );
    }
}

#[test]
fn numeric_array_arrangements_work_beyond_small_range_enumeration() {
    for quantified in [false, true] {
        let mut script = "(set-logic ALL)(declare-datatype E ((ea)(eb)))
            (declare-const x Int)(declare-const a (Array Int (Array Int E)))
            (assert (<= 0 x 12))(assert (= (select (select a x) 0) eb))"
            .to_string();
        if quantified {
            script.push_str("(assert (forall ((k Int)) (=> (and (<= 0 k) (<= k 12)) (= (select (select a k) 0) ea))))");
        } else {
            for k in 0..=12 {
                script.push_str(&format!("(assert (= (select (select a {k}) 0) ea))"));
            }
        }
        script.push_str("(check-sat)");
        assert_eq!(
            Context::new().execute_script(&script).unwrap(),
            ["unsat"],
            "{quantified}"
        );
    }
}

#[test]
fn boolean_index_campaign_matches_exhaustive_two_element_models() {
    let forms = [
        "p",
        "q",
        "(not p)",
        "(and p q)",
        "(or p q)",
        "(xor p q)",
        "(= p q)",
        "false",
    ];
    let eval = |form: usize, p: bool, q: bool| match form {
        0 => p,
        1 => q,
        2 => !p,
        3 => p && q,
        4 => p || q,
        5 => p != q,
        6 => p == q,
        7 => false,
        _ => unreachable!(),
    };
    for mode in ["eager", "lazy"] {
        for a in 0..forms.len() {
            for b in 0..forms.len() {
                for distinct in [false, true] {
                    let possible = [false, true].into_iter().any(|p| {
                        [false, true]
                            .into_iter()
                            .any(|q| !distinct || eval(a, p, q) != eval(b, p, q))
                    });
                    let value = u8::from(distinct);
                    let script = format!("(set-logic ALL)(set-option :theory-mode {mode})
                        (declare-const p Bool)(declare-const q Bool)(declare-const arr (Array Bool Int))
                        (assert (= (select arr {}) 0))(assert (= (select arr {}) {value}))(check-sat)", forms[a], forms[b]);
                    let expected = if possible { "sat" } else { "unsat" };
                    assert_eq!(
                        Context::new().execute_script(&script).unwrap(),
                        [expected],
                        "{script}"
                    );
                }
            }
        }
    }
}

#[test]
fn popped_quantifiers_do_not_disable_finite_ground_argument_checks() {
    for reset in [false, true] {
        let undo = if reset {
            "(reset-assertions)"
        } else {
            "(pop 1)"
        };
        let script = format!("(set-logic ALL)(declare-sort U 0)(declare-fun f ((_ BitVec 1)) U)
            (declare-const u U)(declare-const x (_ BitVec 1))(declare-const y (_ BitVec 1))(declare-const z (_ BitVec 1))
            (push 1)(assert (forall ((t (_ BitVec 1))) (= (f t) u)))
            {undo}(assert (distinct (f x) (f y) (f z)))(check-sat)");
        assert_eq!(
            Context::new().execute_script(&script).unwrap(),
            ["unsat"],
            "reset={reset}"
        );
    }
}

#[test]
fn a_fresh_bv_argument_only_goal_uses_the_theory_bridge() {
    let script = "(set-logic ALL)(declare-sort U 0)(declare-fun f ((_ BitVec 1)) U)
        (declare-const x (_ BitVec 1))(declare-const y (_ BitVec 1))(declare-const z (_ BitVec 1))
        (assert (distinct (f x) (f y) (f z)))(check-sat)";
    assert_eq!(Context::new().execute_script(script).unwrap(), ["unsat"]);
}
