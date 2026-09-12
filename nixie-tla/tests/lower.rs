//! Lowering the surface tree to the KerA kernel.

use nixie_tla::kera::{ArithOp, Kera, SetOp};
use nixie_tla::{LowerErrorKind, Lowerer};
use nixie_tla_syntax::parse_file;

/// Lower the named definition of a one-module spec.
fn lower(src: &str, name: &str) -> std::rc::Rc<Kera> {
    let parsed = match parse_file(src) {
        Ok(p) => p,
        Err(e) => panic!("parse failed: {e}"),
    };
    let module = parsed.module;
    let mut low = Lowerer::new();
    low.add_module(&module);
    match low.lower_named(&module, name) {
        Ok(k) => k,
        Err(e) => panic!("lowering {name} failed: {e}"),
    }
}

fn lower_err(src: &str, name: &str) -> LowerErrorKind {
    let parsed = parse_file(src).expect("parses");
    let module = parsed.module;
    let mut low = Lowerer::new();
    low.add_module(&module);
    match low.lower_named(&module, name) {
        Ok(k) => panic!("expected {name} to be rejected, got {k:?}"),
        Err(e) => e.kind,
    }
}

fn module(body: &str) -> String {
    format!("---- MODULE M ----\nEXTENDS Integers\nVARIABLES x, y\nCONSTANT N\n{body}\n====\n")
}

/// Render a kernel term compactly, for shape assertions.
fn show(k: &Kera) -> String {
    match k {
        Kera::Var(n) => n.to_string(),
        Kera::Prime(a) => format!("{}'", show(a)),
        Kera::Int(v) => v.clone(),
        Kera::Str(s) => format!("{s:?}"),
        Kera::Bool(b) => b.to_string(),
        Kera::Not(a) => format!("~{}", show(a)),
        Kera::And(xs) => format!("({})", join(xs, " /\\ ")),
        Kera::Or(xs) => format!("({})", join(xs, " \\/ ")),
        Kera::Ite(c, t, e) => format!("IF {} THEN {} ELSE {}", show(c), show(t), show(e)),
        Kera::Forall { var, set, body } => format!("\\A {var} \\in {}: {}", show(set), show(body)),
        Kera::Exists { var, set, body } => format!("\\E {var} \\in {}: {}", show(set), show(body)),
        Kera::Choose { var, set, body } => {
            format!("CHOOSE {var} \\in {}: {}", show(set), show(body))
        }
        Kera::ChooseUnbounded { var, body } => format!("CHOOSE {var}: {}", show(body)),
        Kera::Eq(a, b) => format!("{} = {}", show(a), show(b)),
        Kera::In(a, b) => format!("{} \\in {}", show(a), show(b)),
        Kera::SetEnum(xs) => format!("{{{}}}", join(xs, ", ")),
        Kera::Filter { var, set, pred } => {
            format!("{{{var} \\in {}: {}}}", show(set), show(pred))
        }
        Kera::Map { var, set, expr } => format!("{{{} : {var} \\in {}}}", show(expr), show(set)),
        Kera::SetBin(op, a, b) => format!("{} {} {}", show(a), op.as_str(), show(b)),
        Kera::Powerset(a) => format!("SUBSET {}", show(a)),
        Kera::BigUnion(a) => format!("UNION {}", show(a)),
        Kera::Range(a, b) => format!("{}..{}", show(a), show(b)),
        Kera::Times(xs) => join(xs, " \\X "),
        Kera::FunDef { var, set, body } => {
            format!("[{var} \\in {} |-> {}]", show(set), show(body))
        }
        Kera::FunApp(f, a) => format!("{}[{}]", show(f), show(a)),
        Kera::Domain(a) => format!("DOMAIN {}", show(a)),
        Kera::Except { fun, index, value } => format!(
            "[{} EXCEPT ![{}] = {}]",
            show(fun),
            show(index),
            show(value)
        ),
        Kera::FunSet { set, cod } => format!("[{} -> {}]", show(set), show(cod)),
        Kera::Tuple(xs) => format!("<<{}>>", join(xs, ", ")),
        Kera::Record(fs) => format!(
            "[{}]",
            fs.iter()
                .map(|(k, v)| format!("{k} |-> {}", show(v)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Kera::RecordSet(fs) => format!(
            "[{}]",
            fs.iter()
                .map(|(k, v)| format!("{k} : {}", show(v)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Kera::Arith(op, a, b) => format!("{} {} {}", show(a), op.as_str(), show(b)),
        Kera::Neg(a) => format!("-{}", show(a)),
        Kera::Cmp(op, a, b) => format!("{} {} {}", show(a), op.as_str(), show(b)),
        Kera::Opaque(n, args) if args.is_empty() => format!("{n}"),
        Kera::Opaque(n, args) => format!("{n}({})", join(args, ", ")),
    }
}

fn join(xs: &[std::rc::Rc<Kera>], sep: &str) -> String {
    xs.iter().map(|x| show(x)).collect::<Vec<_>>().join(sep)
}

// ---- basics ---------------------------------------------------------------

#[test]
fn literals_and_names() {
    assert_eq!(show(&lower(&module("A == x"), "A")), "x");
    assert_eq!(show(&lower(&module("A == x'"), "A")), "x'");
    assert_eq!(show(&lower(&module("A == 42"), "A")), "42");
    assert_eq!(show(&lower(&module("A == \"hi\""), "A")), "\"hi\"");
}

#[test]
fn based_numerals_are_exact() {
    // A 96-bit literal: truncating through `u64` would lose it, and
    // `AGENTS.md` is explicit that wide values stay exact.
    let src = module("A == \\hFFFFFFFFFFFFFFFFFFFFFFFF");
    assert_eq!(
        show(&lower(&src, "A")),
        "79228162514264337593543950335",
        "2^96 - 1 must survive lowering exactly"
    );
    assert_eq!(show(&lower(&module("A == \\b1011"), "A")), "11");
    assert_eq!(show(&lower(&module("A == \\o777"), "A")), "511");
}

#[test]
fn propositional_and_arithmetic() {
    assert_eq!(show(&lower(&module("A == x /\\ y"), "A")), "(x /\\ y)");
    assert_eq!(show(&lower(&module("A == x => y"), "A")), "(~x \\/ y)");
    assert_eq!(show(&lower(&module("A == x /= y"), "A")), "~x = y");
    assert_eq!(show(&lower(&module("A == x \\notin y"), "A")), "~x \\in y");
    assert!(matches!(
        lower(&module("A == x + 1"), "A").as_ref(),
        Kera::Arith(ArithOp::Add, _, _)
    ));
}

#[test]
fn set_operations_survive_lowering() {
    // Deliberately NOT expanded into comprehensions: Nixie has a set theory,
    // and expanding here would destroy the structure it needs (design doc O3).
    assert!(matches!(
        lower(&module("A == x \\cup y"), "A").as_ref(),
        Kera::SetBin(SetOp::Union, _, _)
    ));
    assert!(matches!(
        lower(&module("A == x \\cap y"), "A").as_ref(),
        Kera::SetBin(SetOp::Intersect, _, _)
    ));
    assert!(matches!(
        lower(&module("A == SUBSET x"), "A").as_ref(),
        Kera::Powerset(_)
    ));
    // `\subseteq` is the exception: it is a quantifier in every encoding.
    assert!(matches!(
        lower(&module("A == x \\subseteq y"), "A").as_ref(),
        Kera::Forall { .. }
    ));
}

// ---- desugaring -----------------------------------------------------------

#[test]
fn case_becomes_nested_ite() {
    let k = lower(
        &module("A == CASE x = 1 -> 10 [] x = 2 -> 20 [] OTHER -> 30"),
        "A",
    );
    assert_eq!(show(&k), "IF x = 1 THEN 10 ELSE IF x = 2 THEN 20 ELSE 30");
}

#[test]
fn case_without_other_is_marked_not_defaulted() {
    // TLA+ leaves a `CASE` with no matching arm undefined. Inventing a value
    // here would be exactly the fabrication AGENTS.md forbids.
    let k = lower(&module("A == CASE x = 1 -> 10"), "A");
    assert!(show(&k).contains("$CaseNoMatch"), "got {}", show(&k));
}

#[test]
fn unchanged_expands_componentwise() {
    assert_eq!(show(&lower(&module("A == UNCHANGED x"), "A")), "x' = x");
    assert_eq!(
        show(&lower(&module("A == UNCHANGED <<x, y>>"), "A")),
        "(x' = x /\\ y' = y)"
    );
}

#[test]
fn record_fields_become_function_application() {
    assert_eq!(show(&lower(&module("A == x.fld"), "A")), "x[\"fld\"]");
    // Record fields are sorted so that two orders compare equal.
    let a = lower(&module("A == [p |-> 1, q |-> 2]"), "A");
    let b = lower(&module("A == [q |-> 2, p |-> 1]"), "A");
    assert_eq!(a, b);
}

#[test]
fn except_paths_nest_and_bind_at() {
    let k = lower(&module("A == [x EXCEPT ![1] = @ + 1]"), "A");
    assert_eq!(show(&k), "[x EXCEPT ![1] = x[1] + 1]");

    // A two-step path becomes nested updates, with `@` the full path.
    let k = lower(&module("A == [x EXCEPT ![1][2] = @]"), "A");
    assert_eq!(show(&k), "[x EXCEPT ![1] = [x[1] EXCEPT ![2] = x[1][2]]]");

    // Field steps and multiple updates.
    let k = lower(&module("A == [x EXCEPT !.a = 1, ![2] = 3]"), "A");
    assert_eq!(
        show(&k),
        "[[x EXCEPT [\"a\"] = 1] EXCEPT ![2] = 3]".replace("[\"a\"]", "![\"a\"]")
    );
}

#[test]
fn multi_bound_quantifiers_nest() {
    let k = lower(&module("A == \\A i, j \\in 1..N : i = j"), "A");
    let s = show(&k);
    assert_eq!(s.matches("\\A").count(), 2, "two binders: {s}");
    assert!(s.contains("1..N"));
}

#[test]
fn tuple_patterns_are_projected() {
    let k = lower(&module("A == \\E <<p, q>> \\in x : p = q"), "A");
    let s = show(&k);
    assert!(s.contains("[1]") && s.contains("[2]"), "got {s}");
}

#[test]
fn multi_variable_function_constructor_uses_a_product() {
    let k = lower(&module("A == [i \\in 1..2, j \\in 1..3 |-> i + j]"), "A");
    let s = show(&k);
    assert!(s.contains("\\X"), "domain is a product: {s}");
    assert!(s.contains("[1]") && s.contains("[2]"), "projected: {s}");
}

// ---- inlining -------------------------------------------------------------

#[test]
fn definitions_are_inlined() {
    let k = lower(&module("Limit == 10\nA == x < Limit"), "A");
    assert_eq!(show(&k), "x < 10");
}

#[test]
fn parameterised_definitions_are_inlined() {
    let k = lower(&module("Add(a, b) == a + b\nA == Add(x, 1)"), "A");
    assert_eq!(show(&k), "x + 1");
}

#[test]
fn let_definitions_are_inlined_and_scoped() {
    let k = lower(&module("A == LET z == x + 1 IN z * z"), "A");
    assert_eq!(show(&k), "x + 1 * x + 1");
    // The LET name does not leak past its body: the inner `z` inlines to 1,
    // while the outer one is an ordinary free name (an undeclared name is a
    // constant as far as the kernel is concerned).
    let k = lower(&module("A == (LET z == 1 IN z) + z"), "A");
    assert_eq!(show(&k), "1 + z");
}

#[test]
fn user_defined_operator_symbols_are_inlined() {
    // `a \oplus b == …` registers under its spelling; consulting the built-in
    // table first meant every spec defining an infix operator failed.
    let k = lower(&module("a \\oplus b == a + b\nA == x \\oplus 1"), "A");
    assert_eq!(show(&k), "x + 1");
}

#[test]
fn higher_order_arguments_are_bound_as_operators() {
    let src =
        module("Apply2(F(_,_), a, b) == F(a, b)\nPlus(p, q) == p + q\nA == Apply2(Plus, x, 1)");
    assert_eq!(show(&lower(&src, "A")), "x + 1");

    let src = module("Apply2(F(_,_), a, b) == F(a, b)\nA == Apply2(LAMBDA p, q : p * q, x, 2)");
    assert_eq!(show(&lower(&src, "A")), "x * 2");
}

#[test]
fn inlining_cannot_capture_an_argument() {
    // Every binder is renamed on the way down, so the argument's `i` cannot be
    // captured by the `i` the body binds.
    let src = module("F(v) == \\A i \\in 1..N : v = i\nA == F(i)");
    let s = show(&lower(&src, "A"));
    assert!(
        s.contains("\\A i#"),
        "the body's binder must be renamed: {s}"
    );
    assert!(
        s.contains("i = i#") || s.contains("i ="),
        "the argument's free `i` must survive unrenamed: {s}"
    );
}

#[test]
fn function_definitions_expand_at_use_sites() {
    let k = lower(&module("f[i \\in 1..N] == i + 1\nA == f[2]"), "A");
    assert_eq!(
        show(&k),
        "[i# \\in 1..N |-> i# + 1][2]".replace("i#", "i#1")
    );
}

// ---- rejections -----------------------------------------------------------

#[test]
fn spec_structure_is_rejected_by_name() {
    for (body, want) in [
        // The action inside is reached first, so either name is a correct
        // report; both are spec structure rather than kernel expressions.
        ("A == [][x' = x]_x", "action"),
        ("A == <>(x = 1)", "temporal"),
        ("A == WF_x(x' = x)", "fairness"),
        ("A == ENABLED (x' = x)", "enabled"),
        ("A == \\A i : i = i", "unbounded"),
    ] {
        let e = lower_err(&module(body), "A");
        let LowerErrorKind::Unsupported { construct, .. } = &e else {
            panic!("expected Unsupported for {body}, got {e:?}");
        };
        assert!(
            construct.to_lowercase().contains(want),
            "for {body}: expected a message naming {want}, got {construct}"
        );
    }
}

#[test]
fn arity_mismatch_is_reported() {
    let e = lower_err(&module("Add(a, b) == a + b\nA == Add(1)"), "A");
    assert!(matches!(e, LowerErrorKind::Arity { .. }), "got {e:?}");
}

#[test]
fn recursive_inlining_is_bounded() {
    // A recursive operator has no finite unfolding; the limit must be a
    // diagnostic, not a hang or a stack overflow.
    let src = module("RECURSIVE F(_)\nF(n) == F(n)\nA == F(1)");
    let parsed = parse_file(&src).expect("parses");
    let m = parsed.module;
    let mut low = Lowerer::new().with_max_inline_depth(16);
    low.add_module(&m);
    let e = low.lower_named(&m, "A").map(|_| ()).unwrap_err();
    assert!(
        matches!(e.kind, LowerErrorKind::InlineLimit { .. }),
        "got {:?}",
        e.kind
    );
}

#[test]
fn standard_module_operators_are_carried_not_dropped() {
    // `\o` is sequence concatenation from `Sequences`; there is no kernel node
    // for it, so it is recorded by name for the encoder rather than rejected
    // or silently discarded.
    let k = lower(&module("A == x \\o y"), "A");
    assert_eq!(show(&k), "\\o(x, y)");
}

#[test]
fn deep_input_does_not_overflow_the_stack() {
    let depth = 2000;
    let body = format!("A == {}x{}", "(".repeat(depth), ")".repeat(depth));
    let src = module(&body);
    let parsed = parse_file(&src);
    // The parser's own depth limit may fire first; either way there is a
    // diagnostic rather than a crash.
    if let Ok(p) = parsed {
        let m = p.module;
        let mut low = Lowerer::new();
        low.add_module(&m);
        let _ = low.lower_named(&m, "A");
    }
}
