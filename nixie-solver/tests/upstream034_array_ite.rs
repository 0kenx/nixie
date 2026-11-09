//! Array-valued conditionals retain their branch identities in every position.
use nixie_solver::Context;

#[test]
fn array_ite_cannot_be_distinct_from_both_branches() {
    for mode in ["eager", "lazy"] {
        for sort in [
            "(Array Int Int)",
            "(Array (_ BitVec 1) (_ BitVec 1))",
            "(Array U (Array Bool U))",
        ] {
            for body in [
                "(distinct a b (ite p a b))",
                "(and (distinct a (ite p a b)) (distinct b (ite p a b)))",
                "(distinct a b (ite (and p q) a (ite q b a)))",
                "(and (distinct (h a) (h (ite p a b))) (distinct (h b) (h (ite p a b))))",
            ] {
                let script = format!(
                    "(set-logic ALL)(set-option :theory-mode {mode})
                    (declare-sort U 0)(declare-const a {sort})(declare-const b {sort})
                    (declare-const p Bool)(declare-const q Bool)(declare-fun h ({sort}) U)
                    (assert {body})(check-sat)"
                );
                assert_eq!(
                    Context::new().execute_script(&script).unwrap(),
                    ["unsat"],
                    "{script}"
                );
            }
        }
    }
}

#[test]
fn array_ite_definitions_follow_push_pop_and_reset() {
    for mode in ["eager", "lazy"] {
        let mut context = Context::new();
        let prelude = format!(
            "(set-logic ALL)(set-option :theory-mode {mode})
            (declare-const a (Array Int Int))(declare-const b (Array Int Int))
            (declare-const p Bool)"
        );
        for _ in 0..2 {
            let script = format!(
                "{prelude}(assert (distinct a b))(check-sat)
                (push 1)(assert (distinct a b (ite p a b)))(check-sat)(pop 1)
                (check-sat)(push 1)(assert p)(assert (distinct a (ite p a b)))
                (check-sat)(pop 1)(push 1)(assert (not p))
                (assert (distinct a (ite p a b)))(check-sat)(pop 1)
                (push 1)(assert (not p))(assert (distinct b (ite p a b)))
                (check-sat)(pop 1)(check-sat)"
            );
            assert_eq!(
                context.execute_script(&script).unwrap(),
                ["sat", "unsat", "sat", "unsat", "sat", "unsat", "sat"]
            );
            context.execute_script("(reset)").unwrap();
        }
    }
}

#[test]
fn array_ite_from_quantified_instances_has_branch_semantics() {
    for binder in ["exists", "forall"] {
        let script = format!(
            "(set-logic ALL)(declare-const a (Array Int Int))
            (declare-const b (Array Int Int))
            (assert ({binder} ((p Bool)) (distinct a b (ite p a b))))(check-sat)"
        );
        assert_eq!(Context::new().execute_script(&script).unwrap(), ["unsat"]);
    }
}

#[test]
fn ground_reads_through_an_array_ite_are_refuted_in_every_spelling() {
    let prelude = "(set-logic ALL)\n\
         (declare-const a0 (Array (_ BitVec 1) (_ BitVec 1)))\n\
         (declare-const a1 (Array (_ BitVec 1) (_ BitVec 1)))\n\
         (declare-const p Bool)\n\
         (assert (= (select a0 #b0) #b0))\n\
         (assert (= (select a1 #b0) #b0))\n";
    let bodies: [(&str, &str); 11] = [
        (
            "let",
            "(assert (let ((t (ite p a0 a1))) (= (select t #b0) #b1)))",
        ),
        (
            "define-fun",
            "(define-fun t () (Array (_ BitVec 1) (_ BitVec 1)) (ite p a0 a1))\n\
             (assert (= (select t #b0) #b1))",
        ),
        (
            "named",
            "(assert (! (= (select (ite p a0 a1) #b0) #b1) :named lbl))",
        ),
        (
            "nested-ite",
            "(declare-const q Bool)\n\
             (assert (= (select (ite p a0 (ite q a1 a0)) #b0) #b1))",
        ),
        (
            "store-over-ite",
            "(assert (= (select (store (ite p a0 a1) #b1 #b0) #b0) #b1))",
        ),
        (
            "ite-of-stores",
            "(assert (= (select (ite p (store a0 #b1 #b0) (store a1 #b1 #b1)) #b0) #b1))",
        ),
        ("distinct", "(assert (distinct a0 a1 (ite p a0 a1)))"),
        (
            "const-default",
            "(declare-const d (_ BitVec 1))\n\
             (assert (= (ite p a0 a1) ((as const (Array (_ BitVec 1) (_ BitVec 1))) d)))\n\
             (assert (distinct (select a0 #b0) d))\n\
             (assert (distinct (select a1 #b0) d))",
        ),
        (
            "uf-of-array",
            "(declare-fun h ((Array (_ BitVec 1) (_ BitVec 1))) (_ BitVec 1))\n\
             (assert (distinct (h (ite p a0 a1)) (h a0)))\n\
             (assert (distinct (h (ite p a0 a1)) (h a1)))",
        ),
        (
            "store-equality",
            "(assert (= (ite p a0 a1) (store a0 #b0 #b1)))",
        ),
        (
            "push-pop",
            "(push 1)\n(assert (= (select (ite p a0 a1) #b0) #b1))\n(check-sat)\n(pop 1)\n\
             (assert (= (select (ite p a0 a1) #b0) #b1))",
        ),
    ];
    for (tag, body) in bodies {
        let script = format!("{prelude}{body}\n(check-sat)\n");
        let lines = Context::new().execute_script(&script).unwrap();
        assert_eq!(
            lines.last().map(String::as_str).unwrap(),
            "unsat",
            "[{tag}] a ground read through an array-sorted `ite` must be \
             refuted (decision (14)).  Response:\n{}",
            lines.join("\n")
        );
    }

    // The three spellings that need their own prelude.
    let standalone: [(&str, &str); 3] = [
        (
            "uninterpreted-index",
            "(set-logic ALL)\n\
             (declare-sort U 0)\n\
             (declare-const b0 (Array U (_ BitVec 1)))\n\
             (declare-const b1 (Array U (_ BitVec 1)))\n\
             (declare-const u U)\n\
             (declare-const p Bool)\n\
             (assert (= (select b0 u) #b0))\n\
             (assert (= (select b1 u) #b0))\n\
             (assert (= (select (ite p b0 b1) u) #b1))\n",
        ),
        (
            "array-of-array",
            "(set-logic ALL)\n\
             (declare-const a0 (Array (_ BitVec 1) (Array (_ BitVec 1) (_ BitVec 1))))\n\
             (declare-const a1 (Array (_ BitVec 1) (Array (_ BitVec 1) (_ BitVec 1))))\n\
             (declare-const p Bool)\n\
             (assert (= (select (select a0 #b0) #b0) #b0))\n\
             (assert (= (select (select a1 #b0) #b0) #b0))\n\
             (assert (= (select (select (ite p a0 a1) #b0) #b0) #b1))\n",
        ),
        (
            "int-index",
            "(set-logic ALL)\n\
             (declare-const c0 (Array Int Int))\n\
             (declare-const c1 (Array Int Int))\n\
             (declare-const p Bool)\n\
             (assert (= (select c0 0) 0))\n\
             (assert (= (select c1 0) 0))\n\
             (assert (= (select (ite p c0 c1) 0) 1))\n",
        ),
    ];
    for (tag, head) in standalone {
        let script = format!("{head}(check-sat)\n");
        let lines = Context::new().execute_script(&script).unwrap();
        assert_eq!(
            lines.last().map(String::as_str).unwrap(),
            "unsat",
            "[{tag}] a ground read through an array-sorted `ite` must be \
             refuted (decision (14)).  Response:\n{}",
            lines.join("\n")
        );
    }
}
