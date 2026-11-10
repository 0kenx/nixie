//! Public namespace isolation and diagnostic counters migrated from 0.3.4.
use nixie_solver::Context;

#[test]
fn source_names_cannot_capture_existential_witnesses() {
    for (sort, zero, body) in [
        ("Int", "(= sk!0 0)", "(> x 0)"),
        ("Bool", "(not sk!0)", "x"),
    ] {
        let mut context = Context::new();
        let script = format!(
            "(set-logic ALL)(declare-const sk!0 {sort})(assert {zero})
            (push 1)(assert (exists ((x {sort})) {body}))(check-sat)(pop 1)(check-sat)
            (push 1)(assert (exists ((x {sort})) {body}))(check-sat)(pop 1)"
        );
        assert_eq!(
            context.execute_script(&script).unwrap(),
            ["sat", "sat", "sat"]
        );
    }
}
