//! Quantifier truth must survive every Boolean position and scope boundary.
use nixie_solver::Context;

#[test]
fn quantified_truth_tables_match_their_boolean_expansions() {
    for sort in ["Int", "(_ BitVec 7)", "U"] {
        for (binder, body, value) in [
            ("forall", "(= x x)", true),
            ("forall", "(distinct x x)", false),
            ("exists", "(= x x)", true),
            ("exists", "(distinct x x)", false),
        ] {
            for p in [false, true] {
                for q in [false, true] {
                    for (position, expected) in [
                        ("(=> p Q)", !p || value),
                        ("(=> Q p)", !value || p),
                        ("(or p Q)", p || value),
                        ("(or (not Q) p)", !value || p),
                        ("(ite p Q q)", if p { value } else { q }),
                        ("(ite Q p q)", if value { p } else { q }),
                        ("(= p Q)", p == value),
                        ("(xor p Q)", p ^ value),
                        ("(not Q)", !value),
                        ("(and p (or q Q))", p && (q || value)),
                    ] {
                        let quantifier = format!("({binder} ((x {sort})) {body})");
                        let assertion = position.replace('Q', &quantifier);
                        let script = format!(
                            "(set-logic ALL)(declare-sort U 0)
                            (declare-const p Bool)(declare-const q Bool)
                            (assert (= p {p}))(assert (= q {q}))
                            (assert {assertion})(check-sat)"
                        );
                        let result = Context::new().execute_script(&script).unwrap();
                        assert_eq!(result, [if expected { "sat" } else { "unsat" }], "{script}");
                    }
                }
            }
        }
    }
}

#[test]
fn named_conditional_quantifiers_keep_source_identity_and_scopes() {
    let output = Context::new()
        .execute_script(
            "(set-logic ALL)(set-option :produce-unsat-cores true)
        (declare-const p Bool)
        (assert (! (= p (forall ((x Int)) (= x x))) :named universal))
        (check-sat)(push 1)(assert (! (not p) :named negative))(check-sat)
        (get-unsat-core)(pop 1)(check-sat)
        (push 1)(assert (not p))(check-sat)(pop 1)(check-sat)",
        )
        .unwrap();
    assert_eq!(&output[..2], ["sat", "unsat"]);
    assert!(
        output[2].contains("universal") && output[2].contains("negative"),
        "{output:?}"
    );
    assert_eq!(&output[3..], ["sat", "unsat", "sat"]);
}
