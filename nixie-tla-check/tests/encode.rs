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

/// Integer arithmetic at and above `i64::MAX` is decided exactly.
///
/// The original defect: `(i64::MAX + 1) = i64::MAX + 1` **panicked** inside
/// `num-rational` (`attempt to add with overflow`) because the linear-parse
/// accumulator summed two individually-fitting literals into a `Ratio<i64>`;
/// above that the solver returned `Unknown`. Fixed at the root by exact
/// `BigInt` constant folding in `TermManager::mk_add` (and checked
/// accumulation behind it); reproduced without any TLA+ by
/// `examples/widerepro.rs`, written up in
/// `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md`.
#[test]
fn wide_literals_above_i64_max() {
    for body in [
        "4611686018427387903 + 1",           // 2^62: always fine
        "9223372036854775806 + 1",           // i64::MAX - 1: the old boundary case
        "9223372036854775807 + 1",           // i64::MAX: used to panic
        "18446744073709551615 + 1",          // 2^64 - 1: used to be Unknown
        "79228162514264337593543950335 + 1", // 2^96 - 1
    ] {
        assert_eq!(validity_of(body), SolverResult::Unsat, "body: {body}");
    }
}

/// Integer `\div` and `%` on literals are decided.
///
/// The original defect: the default arithmetic solver ran real mode, which
/// refuses the Euclidean `div`/`mod` defining axioms, so every division atom
/// was gated to `Unknown` (`26 \div 2 = 13` among them) — sound, but it made
/// any TLA+ specification doing integer division undecidable. The default
/// became mixed-integer and the builder constant-folds two-literal
/// `div`/`mod` exactly, so these are decided.
#[test]
fn division_on_literals_is_decided() {
    for body in [
        "26 \\div 2",
        "26 % 4",
        "-7 \\div 2", // Euclidean: (- 7) \div 2 = - 4
        "-7 % 2",     // Euclidean: (- 7) % 2 = 1
    ] {
        assert_eq!(validity_of(body), SolverResult::Unsat, "body: {body}");
    }
}

/// Tuples and records **do** encode now — as single-constructor datatypes —
/// so the two that used to head this list have moved to their own test below.
/// A function is still declined as a single term: it is a domain *and* a
/// graph, and handing back the graph alone would drop the half that makes
/// equality right.
#[test]
fn unencodable_constructs_are_declined_by_name() {
    for (body, want) in [("2 ^ 3", "^"), ("[x \\in {1} |-> x]", "function")] {
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

/// A tuple and a record reify into a datatype term rather than being refused.
/// Each field keeps its own sort, which is what an SMT array could not do and
/// is why they were structural-only before.
#[test]
fn tuples_and_records_reify_into_datatype_terms() {
    for body in ["<<1, 2>>", "<<1, \"a\">>", "[a |-> 1, b |-> \"x\"]"] {
        let src = format!("---- MODULE M ----\nEXTENDS Integers\nA == {body}\n====\n");
        let parsed = parse_file(&src).expect("parses");
        let m = parsed.module;
        let mut low = Lowerer::new();
        low.add_module(&m);
        let k = low.lower_named(&m, "A").expect("lowers");
        let mut tm = TermManager::new();
        let t = Encoder::new()
            .encode(&k, &mut tm)
            .unwrap_or_else(|e| panic!("`{body}` should encode, got {e}"));
        let sort = tm.get(t).map(|d| d.sort).expect("the term has a sort");
        assert!(
            tm.sorts.is_datatype(sort),
            "`{body}` should be datatype-sorted"
        );
    }
}

/// A set whose candidate members cannot be listed is refused *by that name*,
/// not by "unsupported": the difference matters, because it says the
/// construct is understood and the *bound* is what is missing.
#[test]
fn a_set_with_no_finite_candidate_list_is_refused() {
    let e = encode_err("\\A x \\in 1..n : x > 0");
    assert!(
        matches!(
            e,
            EncodeError::NotEnumerable(_) | EncodeError::UnknownSort(_)
        ),
        "a symbolic range has no candidate list; got {e:?}"
    );
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
