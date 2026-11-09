//! OxiZ 0.3.4 guard-region and unnamed-array-region soundness regressions.
use nixie_solver::Context;

fn verdicts(script: &str) -> Vec<String> {
    Context::new()
        .execute_script(script)
        .expect("well-sorted script")
        .into_iter()
        .filter(|s| matches!(s.as_str(), "sat" | "unsat" | "unknown"))
        .collect()
}

#[test]
fn strict_and_negated_guards_cover_nonboundary_points() {
    for (sort, guard) in [
        ("Int", "(> q 7)"),
        ("Int", "(< q 7)"),
        ("Int", "(not (= q 7))"),
        ("Real", "(and (> q 1.0) (< q 2.0))"),
        ("Real", "(and (> q 1.0) (< q 1.5))"),
        ("Real", "(not (= q 7.0))"),
    ] {
        for wrapped in [guard.to_string(), format!("(ite {guard} true false)")] {
            let input = format!("(assert (forall ((q {sort})) (=> {wrapped} false)))(check-sat)");
            assert_eq!(verdicts(&input), ["unsat"], "{input}");
        }
    }
}

#[test]
fn pinned_array_default_is_checked_outside_named_indices() {
    for (sort, zero, one) in [
        ("(_ BitVec 7)", "#b0000000", "#b0000001"),
        ("Int", "0", "1"),
        ("Real", "0.0", "1.0"),
    ] {
        let head = format!(
            "(declare-const a (Array {sort} (_ BitVec 1)))
            (assert (= a (store ((as const (Array {sort} (_ BitVec 1))) #b0) {zero} #b1)))"
        );
        let universal = format!("(forall ((i {sort})) (= (select a i) #b1))");
        let input = format!(
            "{head}(push 1)(assert {universal})(check-sat)(pop 1)
            (assert (= (select a {one}) #b0))(check-sat)
            (push 1)(assert {universal})(check-sat)(pop 1)(check-sat)"
        );
        assert_eq!(
            verdicts(&input),
            ["unsat", "sat", "unsat", "sat"],
            "{input}"
        );
    }
}

#[test]
fn satisfiable_guards_keep_their_verdicts() {
    for input in [
        "(assert (forall ((q Int)) (=> (> q 7) (> q 6))))(check-sat)",
        "(assert (forall ((q Real)) (=> (and (> q 1.0) (< q 2.0)) (< q 3.0))))(check-sat)",
        "(declare-fun f (Int) Int)(assert (forall ((q Int)) (=> (> q 7) (= (f q) 1))))(check-sat)",
    ] {
        assert_eq!(verdicts(input), ["sat"], "{input}");
    }
}

#[test]
fn conditional_false_instance_does_not_refute_the_other_disjunct() {
    for body in ["(> q 7)", "(=> (> q 7) false)", "(and (>= q 0) (<= q 2))"] {
        let script =
            format!("(declare-const p Bool)(assert (or p (forall ((q Int)) {body})))(check-sat)");
        assert_ne!(verdicts(&script), ["unsat"], "{script}");
    }
}
