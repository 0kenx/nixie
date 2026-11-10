//! Upstream 0.3.4 exact finite-array cardinalities and extensionality domains.
use nixie_solver::Context;

fn declarations(count: usize, sort: &str) -> String {
    (0..count)
        .map(|i| format!("(declare-const a{i} {sort})\n"))
        .collect()
}

fn distinct(count: usize) -> String {
    format!(
        "(distinct {})",
        (0..count)
            .map(|i| format!("a{i}"))
            .collect::<Vec<_>>()
            .join(" ")
    )
}

fn verdicts(script: &str) -> Vec<String> {
    Context::new()
        .execute_script(script)
        .expect("valid SMT-LIB")
        .into_iter()
        .filter(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .collect()
}

#[test]
fn nine_small_arrays_have_a_model_but_seventeen_do_not() {
    for (count, expected) in [(9, "sat"), (17, "unsat")] {
        let script = format!(
            "(set-logic QF_ABV)\n{}(assert {})\n(check-sat)",
            declarations(count, "(Array (_ BitVec 2) (_ BitVec 1))"),
            distinct(count)
        );
        let mut context = Context::new();
        assert_eq!(
            context.execute_script(&script).expect("valid input"),
            [expected],
            "{count} arrays"
        );
        if expected == "sat" {
            let rows = context.get_model().expect("published finite arrays");
            assert_eq!(rows.len(), count);
            let definitions: String = rows
                .iter()
                .map(|(name, sort, value)| format!("(define-fun {name} () {sort} {value})\n"))
                .collect();
            // Every array is now a closed value. Refuting the negation checks
            // the actual published functions, not just their chosen names.
            let replay = format!(
                "(set-logic QF_ABV)\n{definitions}(assert (not {}))(check-sat)",
                distinct(count)
            );
            assert_eq!(verdicts(&replay), ["unsat"]);
        }
    }
}

#[test]
fn finite_pigeonholes_are_guarded_and_scope_consistent() {
    let script = format!(
        "(set-logic ALL)\n{}(declare-const gate Bool)\n\
        (assert (or gate {}))\n(check-sat)\n\
        (push 1)\n(assert (not gate))\n(check-sat)\n(pop 1)\n(check-sat)",
        declarations(5, "(Array Bool Bool)"),
        distinct(5)
    );
    assert_eq!(verdicts(&script), ["sat", "unsat", "sat"]);
}

#[test]
fn nested_array_cardinality_is_exponentiation() {
    let script = format!(
        "(set-logic ALL)\n{}(assert {})\n(check-sat)",
        declarations(17, "(Array Bool (Array Bool Bool))"),
        distinct(17)
    );
    assert_eq!(verdicts(&script), ["unsat"]);
}

#[test]
fn complete_reads_determine_array_equality() {
    for (domain, values) in [
        ("Bool", vec!["false", "true"]),
        ("(_ BitVec 2)", vec!["#b00", "#b01", "#b10", "#b11"]),
    ] {
        let script = format!(
            "(set-logic QF_AUFBV)\n\
            (declare-const a (Array {domain} (_ BitVec 1)))\n\
            (declare-const b (Array {domain} (_ BitVec 1)))\n{}\n\
            (push 1)\n(assert (distinct a b))\n(check-sat)\n\
            (pop 1)\n(check-sat)",
            values
                .iter()
                .map(|value| format!("(assert (= (select a {value}) (select b {value})))"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        assert_eq!(verdicts(&script), ["unsat", "sat"]);
    }
}
