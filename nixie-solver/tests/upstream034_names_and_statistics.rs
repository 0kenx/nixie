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

fn counter(stats: &str, name: &str) -> u64 {
    let words: Vec<_> = stats.trim_matches(['(', ')']).split_whitespace().collect();
    let index = words
        .iter()
        .position(|word| *word == name)
        .expect("published counter");
    words[index + 1].parse().expect("integer counter")
}

#[test]
fn array_work_and_embedded_conflicts_are_published_per_query() {
    let mut context = Context::new();
    let output = context
        .execute_script(
            "(set-logic QF_ALIA)
        (declare-const a (Array Int Int))(declare-const i Int)
        (assert (= (select (store a i 7) i) 7))(check-sat)
        (get-info :all-statistics)",
        )
        .unwrap();
    assert_eq!(output[0], "sat");
    let stats = &output[1];
    assert!(counter(stats, ":array-refinement-rounds") > 0);
    assert!(counter(stats, ":array-lemma-instances") > 0);
    assert_eq!(counter(stats, ":bv-embedded-conflicts"), 0);
    context
        .execute_script("(reset-assertions)(check-sat)")
        .unwrap();
    let stats = context.get_statistics();
    assert_eq!(counter(&stats, ":array-refinement-rounds"), 0);
    assert_eq!(counter(&stats, ":array-lemma-instances"), 0);
    assert_eq!(counter(&stats, ":bv-embedded-conflicts"), 0);
}
