//! Native Seq T semantics and conservative fragment boundaries.
use nixie_solver::Context;

fn run(s: &str) -> Vec<String> {
    Context::new()
        .execute_script(s)
        .expect("well-sorted sequence script")
}
fn verdict(s: &str) -> String {
    run(&format!("(set-logic ALL)\n{s}\n(check-sat)"))
        .into_iter()
        .find(|s| matches!(s.as_str(), "sat" | "unsat" | "unknown"))
        .expect("verdict")
}

#[test]
fn empty_singletons_and_symbolic_element_congruence() {
    for (s, expected) in [
        ("(assert (= (seq.len (as seq.empty (Seq Int))) 0))", "sat"),
        (
            "(assert (distinct (as seq.empty (Seq Bool)) (as seq.empty (Seq Bool))))",
            "unsat",
        ),
        (
            "(declare-const x Int)(declare-const y Int)(assert (= x y))(assert (distinct (seq.unit x) (seq.unit y)))",
            "unsat",
        ),
        (
            "(declare-const x Int)(declare-const y Int)(assert (distinct x y))(assert (= (seq.unit x) (seq.unit y)))",
            "unsat",
        ),
        (
            "(declare-const x Int)(assert (= (seq.len (seq.unit x)) 1))",
            "sat",
        ),
    ] {
        assert_eq!(verdict(s), expected, "{s}");
    }
}

#[test]
fn concat_extensionality_and_nested_sequences() {
    for (s, expected) in [
        (
            "(assert (= (seq.++ (as seq.empty (Seq Int)) (seq.unit 1)) (seq.unit 1)))",
            "sat",
        ),
        (
            "(assert (= (seq.++ (seq.unit 1) (seq.unit 2)) (seq.++ (seq.unit 2) (seq.unit 1))))",
            "unsat",
        ),
        (
            "(assert (distinct (seq.++ (seq.unit 1) (seq.unit 2)) (seq.++ (seq.unit 2) (seq.unit 1))))",
            "sat",
        ),
        (
            "(assert (= (seq.nth (seq.unit (seq.unit true)) 0) (seq.unit true)))",
            "sat",
        ),
        (
            "(assert (distinct (seq.unit (seq.unit true)) (seq.unit (seq.unit false))))",
            "sat",
        ),
        (
            "(assert (= (seq.len (seq.nth (seq.unit (seq.unit true)) 0)) 1))",
            "sat",
        ),
        (
            "(assert (= (seq.nth (seq.unit (_ bv18446744073709551617 128)) 0) (_ bv18446744073709551617 128)))",
            "sat",
        ),
    ] {
        assert_eq!(verdict(s), expected, "{s}");
    }
}

#[test]
fn extraction_and_updates_at_boundaries() {
    let s = "(seq.++ (seq.unit 10) (seq.unit 20) (seq.unit 30))";
    for (index, count, expected) in [
        (-1, 2, "(as seq.empty (Seq Int))"),
        (0, 0, "(as seq.empty (Seq Int))"),
        (1, -1, "(as seq.empty (Seq Int))"),
        (1, 20, "(seq.++ (seq.unit 20) (seq.unit 30))"),
        (3, 1, "(as seq.empty (Seq Int))"),
    ] {
        assert_eq!(
            verdict(&format!(
                "(assert (= (seq.extract {s} {index} {count}) {expected}))"
            )),
            "sat"
        );
    }
    for (index, expected) in [
        (-1, s.to_string()),
        (3, s.to_string()),
        (
            2,
            "(seq.++ (seq.unit 10) (seq.unit 20) (seq.unit 4))".into(),
        ),
    ] {
        assert_eq!(
            verdict(&format!(
                "(assert (= (seq.update {s} {index} (seq.++ (seq.unit 4) (seq.unit 5))) {expected}))"
            )),
            "sat"
        );
    }
    assert_eq!(
        verdict(
            "(assert (= (seq.len (seq.extract (seq.unit 3) 0 9999999999999999999999999999999999)) 1))"
        ),
        "sat"
    );
    assert_eq!(
        verdict(
            "(assert (= (seq.update (seq.unit 3) 9999999999999999999999999999999999 (seq.unit 4)) (seq.unit 3)))"
        ),
        "sat"
    );
}

#[test]
fn exact_length_variables_and_history_queue_obligations() {
    assert_eq!(
        verdict(
            "(declare-const q (Seq Int))(assert (= (seq.len q) 2))(assert (= (seq.nth q 0) 7))(assert (= (seq.nth q 1) 8))"
        ),
        "sat"
    );
    assert_eq!(
        verdict(
            "(declare-const h (Seq Int))(declare-const next (Seq Int))(declare-const x Int)(assert (= h (seq.++ (seq.unit 1) (seq.unit 2))))(assert (= next (seq.++ h (seq.unit x))))(assert (distinct (seq.len next) (+ (seq.len h) 1)))"
        ),
        "unsat"
    );
    assert_eq!(
        verdict(
            "(declare-const q (Seq Int))(assert (= (seq.len q) 2))(assert (distinct (seq.nth (seq.extract q 1 1) 0) (seq.nth q 1)))"
        ),
        "unsat"
    );
    assert_eq!(
        verdict(
            "(declare-const n Int)(assert (= n (seq.len (seq.++ (seq.unit 1) (seq.unit 2)))))(assert (= n 2))"
        ),
        "sat"
    );
}

#[test]
fn scope_and_model_queries() {
    let out = run(
        "(set-logic ALL)(set-option :produce-models true)(declare-const q (Seq Int))(assert (= q (seq.unit 7)))(check-sat)(get-value (q (seq.len q) (seq.nth q 0)))(push 1)(assert (= q (seq.unit 8)))(check-sat)(pop 1)(check-sat)(get-value ((seq.nth q 0)))",
    );
    assert_eq!(
        out.iter()
            .filter(|s| matches!(s.as_str(), "sat" | "unsat" | "unknown"))
            .cloned()
            .collect::<Vec<_>>(),
        ["sat", "unsat", "sat"]
    );
    assert!(out.join("\n").contains("7"), "{out:?}");
}

#[test]
fn unsupported_cases_are_honest() {
    for s in [
        "(declare-const s (Seq Int))(assert (> (seq.len s) 2))",
        "(declare-const i Int)(assert (= (seq.nth (seq.unit 3) i) 3))",
        "(assert (= (seq.nth (as seq.empty (Seq Int)) 0) 3))",
        "(assert (= (seq.nth (seq.unit 3) (- 1)) 3))",
        "(declare-const s (Seq Int))(assert (= (seq.len s) 4097))",
        "(declare-const a (Array Int (Seq Int)))(assert (= (select a 0) (seq.unit 1)))",
        "(declare-fun f ((Seq Int)) Int)(assert (= (f (seq.unit 1)) 1))",
        "(assert (forall ((s (Seq Int))) (>= (seq.len s) 0)))",
    ] {
        assert_eq!(verdict(s), "unknown", "{s}");
    }
}

#[test]
fn bad_sorts_and_arities_are_errors() {
    for s in [
        "(assert (= (seq.len 1) 0))",
        "(assert (= (seq.nth (seq.unit 1) true) 0))",
        "(assert (= (seq.++ (seq.unit true) (seq.unit 1)) (seq.unit true)))",
        "(assert (= (as seq.empty Int) 0))",
        "(assert (= (seq.update (seq.unit 1) 0 2) (seq.unit 1)))",
    ] {
        assert!(Context::new().execute_script(s).is_err(), "{s}");
    }
}

#[test]
#[ignore = "requires the installed Z3 reference executable"]
fn reference_differential_z3_416() {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };
    let version = Command::new("z3")
        .arg("--version")
        .output()
        .expect("installed Z3 required");
    eprintln!("reference: {}", String::from_utf8_lossy(&version.stdout));
    let mut cases: Vec<String> = [
        "(assert (= (seq.extract (seq.++ (seq.unit 1) (seq.unit 2)) 1 9) (seq.unit 2)))",
        "(declare-const x Int)(assert (distinct (seq.unit x) (seq.++ (as seq.empty (Seq Int)) (seq.unit x))))",
        "(declare-const s (Seq Int))(assert (= (seq.len s) 2))(assert (distinct (seq.nth s 0) (seq.nth s 1)))",
        "(assert (= (seq.len (seq.unit (seq.unit true))) 1))",
    ].into_iter().map(str::to_string).collect();

    let base = "(seq.++ (seq.unit 10) (seq.unit 20) (seq.unit 30))";
    for index in -2..5 {
        for count in -1..6 {
            for expected in 0..=3 {
                cases.push(format!(
                    "(assert (= (seq.len (seq.extract {base} {index} {count})) {expected}))"
                ));
            }
        }
        for expected in [10, 99] {
            cases.push(format!("(assert (= (seq.nth (seq.update {base} {index} (seq.++ (seq.unit 99) (seq.unit 98))) 0) {expected}))"));
        }
    }
    // Z3 4.16 has no seq.update. This is the CVC5 update definition,
    // expressed using Z3's native extract/concat/length primitives.
    let update_definition = "(define-fun ref.update ((s (Seq Int)) (i Int) (r (Seq Int))) (Seq Int) (ite (or (< i 0) (>= i (seq.len s))) s (seq.++ (seq.extract s 0 i) (seq.extract r 0 (- (seq.len s) i)) (seq.extract s (+ i (seq.len r)) (seq.len s)))))";
    for s in cases {
        let script = format!(
            "(set-logic ALL){update_definition}{}(check-sat)",
            s.replace("seq.update", "ref.update")
        );
        let mut child = Command::new("z3")
            .args(["-in", "-smt2", "-T:5"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("z3");
        child
            .stdin
            .take()
            .expect("stdin")
            .write_all(script.as_bytes())
            .expect("write");
        let output = child.wait_with_output().expect("Z3 verdict");
        assert!(output.status.success());
        let reference = String::from_utf8(output.stdout).expect("UTF-8");
        assert!(matches!(reference.trim(), "sat" | "unsat"), "{reference}");
        assert_eq!(verdict(&s), reference.trim(), "{s}");
    }
}

#[test]
fn proof_requests_and_sat_only_are_honest() {
    use nixie_core::{TermManager, ast::sequence::SeqOp};
    use nixie_solver::{Solver, SolverConfig, SolverResult};
    let mut tm = TermManager::new();
    let one = tm.mk_int(1);
    let two = tm.mk_int(2);
    let unit = tm.mk_sequence(SeqOp::Unit, &[one]).expect("unit");
    let len = tm.mk_sequence(SeqOp::Len, &[unit]).expect("len");
    let contradiction = tm.mk_eq(len, two);
    let mut solver = Solver::new();
    solver.assert(contradiction, &mut tm);
    assert_eq!(solver.check_sat_only(&mut tm), SolverResult::Unsat);
    for config in [
        SolverConfig {
            proof: true,
            ..SolverConfig::default()
        },
        SolverConfig::default().certified(),
    ] {
        let mut solver = Solver::with_config(config);
        solver.assert(contradiction, &mut tm);
        assert_eq!(solver.check(&mut tm), SolverResult::Unknown);
        assert!(solver.model().is_none());
    }
}

#[test]
fn scope_invalidates_values_even_when_next_shape_is_unsupported() {
    use nixie_core::{TermManager, ast::sequence::SeqOp};
    use nixie_solver::{Solver, SolverResult};
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let sort = tm.sorts.seq(int);
    let q = tm.mk_var("q", sort);
    let one = tm.mk_int(1);
    let unit = tm.mk_sequence(SeqOp::Unit, &[one]).expect("unit");
    let eq = tm.mk_eq(q, unit);
    let mut solver = Solver::new();
    solver.push();
    solver.assert(eq, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    assert!(solver.model().is_some());
    solver.pop();
    assert!(solver.model().is_none());
    let len = tm.mk_sequence(SeqOp::Len, &[q]).expect("len");
    let lower = tm.mk_gt(len, one);
    solver.assert(lower, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unknown);
    assert!(solver.model().is_none());
}

#[test]
fn element_sorts_and_sort_aliases_round_trip() {
    for s in [
        "(declare-const a (Seq Bool))(assert (= a (seq.unit true)))(assert (= (seq.nth a 0) true))",
        "(define-sort SI () (Seq Int))(declare-const a SI)(assert (= a (seq.unit 4)))",
        "(declare-const a (Seq (Seq Int)))(assert (= a (seq.unit (seq.unit 4))))(assert (= (seq.nth (seq.nth a 0) 0) 4))",
        "(assert (= (seq.nth (seq.unit \"hello\") 0) \"hello\"))",
        "(assert (= (seq.nth (seq.unit (/ 1.0 2.0)) 0) (/ 1.0 2.0)))",
        "(declare-datatype D ((item (key Int))))(assert (= (seq.nth (seq.unit (item 4)) 0) (item 4)))",
    ] {
        assert_eq!(verdict(s), "sat", "{s}");
    }
}

#[test]
fn unasserted_sequence_model_completion_is_consistent() {
    let out = run(
        "(set-logic ALL)(set-option :produce-models true)(declare-const q (Seq Int))(check-sat)(get-model)(get-value (q (seq.len q)))",
    );
    let text = out.join("\n");
    assert!(text.contains("(as seq.empty (Seq Int))"), "{text}");
    assert!(text.contains("((seq.len q) 0)"), "{text}");
}
