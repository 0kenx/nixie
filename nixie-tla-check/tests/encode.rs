//! Encoding kernel terms, and what the solver does with them.

use nixie_core::TermManager;
use nixie_solver::{Solver, SolverResult};
use nixie_tla::{Evaluator, Lowerer};
use nixie_tla_check::{EncodeError, Encoder};
use nixie_tla_syntax::parse_file;

/// Lower `A == <body>`, encode it, and ask whether the claim is valid.
fn validity_of(body: &str) -> SolverResult {
    let src = format!("---- MODULE M ----\nEXTENDS Integers\nA == {body}\n====\n");
    let parsed = parse_file(&src).expect("parses");
    let m = parsed.module;
    let mut low = Lowerer::new();
    low.add_module(&m);
    let k = low.lower_named(&m, "A").expect("lowers");
    let value = Evaluator::new().eval(&k).expect("evaluates");

    let mut tm = TermManager::new();
    let mut enc = Encoder::new();
    let t = enc.encode(&k, &mut tm).expect("encodes");
    let claim = match value {
        nixie_tla::Value::Bool(true) => t,
        nixie_tla::Value::Bool(false) => tm.mk_not(t),
        nixie_tla::Value::Int(n) => {
            let lit = tm.mk_int(num_bigint::BigInt::from(n));
            tm.mk_eq(t, lit)
        }
        other => panic!("not encodable: {other}"),
    };
    // Valid iff the negation is unsatisfiable.
    let negated = tm.mk_not(claim);
    let mut solver = Solver::new();
    solver.assert(negated, &mut tm);
    solver.check(&mut tm)
}

fn encode_err(body: &str) -> EncodeError {
    let src = format!("---- MODULE M ----\nEXTENDS Integers\nA == {body}\n====\n");
    let parsed = parse_file(&src).expect("parses");
    let m = parsed.module;
    let mut low = Lowerer::new();
    low.add_module(&m);
    let k = low.lower_named(&m, "A").expect("lowers");
    let mut tm = TermManager::new();
    match Encoder::new().encode(&k, &mut tm) {
        Ok(_) => panic!("expected {body} to be declined"),
        Err(e) => e,
    }
}

#[test]
fn the_solver_agrees_with_the_evaluator_on_arithmetic() {
    for body in [
        "2 + 3 * 4",
        "(-7) + 1",
        "100 - 1",
        "2 < 3",
        "5 >= 5",
        "1 = 1",
        "TRUE /\\ FALSE",
        "IF 1 < 2 THEN 10 ELSE 20",
        "~(1 = 2)",
    ] {
        assert_eq!(
            validity_of(body),
            SolverResult::Unsat,
            "the claim about `{body}` must be valid, so its negation unsatisfiable"
        );
    }
}

#[test]
fn wide_literals_reach_the_solver_intact() {
    // Routed through `BigInt`, never `i64`: truncating here has produced both
    // false `sat` and false `unsat` elsewhere in this codebase. 2^62 is below
    // the boundary documented in the study referenced below.
    assert_eq!(validity_of("4611686018427387903 + 1"), SolverResult::Unsat);
}

/// Integer arithmetic near and above `i64::MAX` does not work.
///
/// `(i64::MAX + 1) = i64::MAX + 1` **panics** inside `num-rational`
/// (`attempt to add with overflow`), so the arithmetic path is carrying a
/// fixed-width rational where a `BigRational` is needed; above that the solver
/// returns `Unknown`. Reproduced without any TLA+ by
/// `examples/widerepro.rs`, and written up in
/// `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md`.
///
/// Ignored because it aborts the process rather than failing. Run it with
/// `cargo test -p nixie-tla-check -- --ignored` once the gap is closed.
#[test]
#[ignore = "panics in num-rational; see docs/studies/2026-09-13-lia-wide-literal-arithmetic.md"]
fn wide_literals_above_i64_max() {
    assert_eq!(validity_of("9223372036854775807 + 1"), SolverResult::Unsat);
}

/// Nixie returns `Unknown` for integer `\div` and `%` applied to literals.
///
/// `26 \div 2 = 13` is trivially decidable, and the solver does not decide it;
/// multiplication of the same literals is fine. `Unknown` is *sound* — it is
/// never a wrong answer — but it makes any TLA+ specification using `\div` or
/// `%` undecidable through this path, which is most specifications that do
/// arithmetic at all.
///
/// Written up in `docs/studies/2026-09-13-lia-div-mod-literal-incompleteness.md`.
/// This test asserts only the sound property, so it keeps passing when the gap
/// is closed; the study is what records the gap.
#[test]
fn division_on_literals_is_currently_undecided_but_never_wrong() {
    for body in ["26 \\div 2", "26 % 4"] {
        let r = validity_of(body);
        assert_ne!(
            r,
            SolverResult::Sat,
            "a valid claim about `{body}` must never come back satisfiable"
        );
    }
}

#[test]
fn unencodable_constructs_are_declined_by_name() {
    for (body, want) in [
        ("{1, 2}", "set"),
        ("<<1, 2>>", "tuple"),
        ("[a |-> 1]", "record"),
        ("\\A x \\in {1} : x = 1", "quantifier"),
        ("2 ^ 3", "^"),
    ] {
        let e = encode_err(body);
        let EncodeError::Unsupported(what) = &e else {
            panic!("expected Unsupported for `{body}`, got {e:?}");
        };
        assert!(
            what.contains(want),
            "for `{body}`: expected a message naming {want}, got {what}"
        );
    }
}

#[test]
fn a_free_name_needs_a_declared_sort() {
    let src = "---- MODULE M ----\nVARIABLE v\nA == v = v\n====\n";
    let parsed = parse_file(src).expect("parses");
    let m = parsed.module;
    let mut low = Lowerer::new();
    low.add_module(&m);
    let k = low.lower_named(&m, "A").expect("lowers");

    let mut tm = TermManager::new();
    let mut enc = Encoder::new();
    assert!(matches!(
        enc.encode(&k, &mut tm),
        Err(EncodeError::UnknownSort(_))
    ));

    // Declared, it encodes and `v = v` is valid.
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let mut enc = Encoder::new();
    enc.declare("v", int);
    let t = enc.encode(&k, &mut tm).expect("encodes once declared");
    let negated = tm.mk_not(t);
    let mut solver = Solver::new();
    solver.assert(negated, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
}
