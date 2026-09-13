//! Type inference: the cases a corpus tally cannot pin down precisely.
//!
//! The corpus measures *coverage*; these pin *which* type is inferred, which
//! is what the encoder will depend on.

use nixie_tla::types::{Inference, Type};
use nixie_tla::{Lowerer, TypeError};
use std::collections::BTreeMap;

/// Lower one definition of a one-module spec.
fn lower(src: &str, name: &str) -> nixie_tla::KeraRef {
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let mut low = Lowerer::new();
    low.add_module(&parsed.module);
    low.lower_named(&parsed.module, name).expect("lowers")
}

fn ty_of(src: &str, name: &str) -> Type {
    let k = lower(src, name);
    let mut inf = Inference::new();
    let t = inf.infer(&k).expect("types");
    inf.to_type(t).expect("materialises")
}

fn free_ty(src: &str, name: &str, free: &str) -> Type {
    let k = lower(src, name);
    let mut inf = Inference::new();
    inf.infer(&k).expect("types");
    let id = inf.free_name(free).expect("free name appeared");
    inf.to_type(id).expect("materialises")
}

fn err_of(src: &str, name: &str) -> TypeError {
    let k = lower(src, name);
    let mut inf = Inference::new();
    inf.infer(&k).expect_err("should not type")
}

fn module(body: &str) -> String {
    format!("---- MODULE T ----\nEXTENDS Naturals, Sequences, FiniteSets\n{body}\n====\n")
}

#[test]
fn arithmetic_forces_int() {
    let src = module("VARIABLE x\nA == x + 1 > 0");
    assert_eq!(ty_of(&src, "A"), Type::Bool);
    assert_eq!(free_ty(&src, "A", "x"), Type::Int);
}

#[test]
fn priming_preserves_type() {
    let src = module("VARIABLE x\nA == x' = x + 1");
    assert_eq!(free_ty(&src, "A", "x"), Type::Int);
}

#[test]
fn set_membership_relates_element_and_set() {
    let src = module("CONSTANT S\nVARIABLE x\nA == x \\in S /\\ x > 0");
    assert_eq!(free_ty(&src, "A", "S"), Type::Set(Box::new(Type::Int)));
}

#[test]
fn set_map_changes_the_element_type() {
    let src = module("A == {<<i, i>> : i \\in 1..3}");
    assert_eq!(
        ty_of(&src, "A"),
        Type::Set(Box::new(Type::Tuple(vec![Type::Int, Type::Int])))
    );
}

#[test]
fn function_definition_gets_domain_and_codomain() {
    let src = module("A == [i \\in 1..3 |-> i > 0]");
    assert_eq!(
        ty_of(&src, "A"),
        Type::Fun(Box::new(Type::Int), Box::new(Type::Bool))
    );
}

#[test]
fn powerset_and_big_union_are_inverse_in_shape() {
    let src = module("A == UNION SUBSET {1, 2}");
    assert_eq!(ty_of(&src, "A"), Type::Set(Box::new(Type::Int)));
}

#[test]
fn record_literal_is_closed() {
    let src = module("A == [a |-> 1, b |-> TRUE]");
    let Type::Rec { fields, open } = ty_of(&src, "A") else {
        panic!("expected a record");
    };
    assert!(!open, "a record literal states all its fields");
    assert_eq!(fields.get("a"), Some(&Type::Int));
    assert_eq!(fields.get("b"), Some(&Type::Bool));
}

/// The row-type payoff: `r.a` says `r` has an `a` field and says nothing at
/// all about the rest. A closed record type here would have to invent the
/// remaining fields or reject the expression.
#[test]
fn field_access_yields_an_open_row() {
    let src = module("CONSTANT r\nA == r.a > 0");
    let Type::Rec { fields, open } = free_ty(&src, "A", "r") else {
        panic!("expected a record");
    };
    assert!(open, "field access learns one field, not the whole record");
    assert_eq!(fields.get("a"), Some(&Type::Int));
    assert_eq!(fields.len(), 1);
}

/// Two accesses to different fields must *merge* into one row, not conflict.
#[test]
fn two_field_accesses_merge_into_one_row() {
    let src = module("CONSTANT r\nA == r.a > 0 /\\ r.b = \"x\"");
    let Type::Rec { fields, open } = free_ty(&src, "A", "r") else {
        panic!("expected a record");
    };
    assert!(open);
    assert_eq!(fields.get("a"), Some(&Type::Int));
    assert_eq!(fields.get("b"), Some(&Type::Str));
}

/// An open row meeting a closed literal closes it, and the literal must have
/// the field.
#[test]
fn open_row_meets_closed_literal() {
    let src = module("A == LET r == [a |-> 1, b |-> TRUE] IN r.a");
    assert_eq!(ty_of(&src, "A"), Type::Int);
}

#[test]
fn closed_record_rejects_an_absent_field() {
    let src = module("A == LET r == [a |-> 1] IN r.zzz");
    assert!(
        matches!(err_of(&src, "A"), TypeError::NoField { .. }),
        "a closed record must reject a field it does not have"
    );
}

/// A tuple is a function on `1..n`, so a literal index picks the component and
/// heterogeneous tuples stay legal.
#[test]
fn literal_index_selects_a_tuple_component() {
    let src = module("A == <<1, \"a\", TRUE>>[2]");
    assert_eq!(ty_of(&src, "A"), Type::Str);
}

#[test]
fn tuple_index_out_of_range_is_rejected() {
    let src = module("A == <<1, 2>>[5]");
    assert!(matches!(
        err_of(&src, "A"),
        TypeError::TupleIndex { index: 5, arity: 2 }
    ));
}

/// `Len` demands a sequence, and a tuple is one — so a homogeneous tuple
/// passes and the components are equated.
#[test]
fn tuple_unifies_with_seq_when_homogeneous() {
    let src = module("A == Len(<<1, 2, 3>>)");
    assert_eq!(ty_of(&src, "A"), Type::Int);
}

#[test]
fn tuple_meeting_seq_must_be_homogeneous() {
    let src = module("A == Len(<<1, \"a\">>) = 2");
    assert!(
        matches!(err_of(&src, "A"), TypeError::Mismatch { .. }),
        "a sequence is homogeneous; a heterogeneous tuple is not one"
    );
}

#[test]
fn append_propagates_the_element_type() {
    let src = module("CONSTANT s\nA == Append(s, 1) = s");
    assert_eq!(free_ty(&src, "A", "s"), Type::Seq(Box::new(Type::Int)));
}

/// The refusal that matters: nothing says whether `f` is a tuple, a sequence
/// or a function, and the three do not encode the same way.
#[test]
fn an_unconstrained_index_is_reported_not_guessed() {
    let src = module("CONSTANT f\nA == f[1] = f[1]");
    assert!(
        matches!(err_of(&src, "A"), TypeError::Ambiguous { .. }),
        "an index into an unknown shape must be reported, never defaulted"
    );
}

/// A single extra fact resolves it, and then the shape is exact.
#[test]
fn one_constraint_resolves_the_ambiguity() {
    let src = module("CONSTANT f\nA == f \\in [{1} -> BOOLEAN] /\\ f[1]");
    assert_eq!(
        free_ty(&src, "A", "f"),
        Type::Fun(Box::new(Type::Int), Box::new(Type::Bool))
    );
}

#[test]
fn mismatched_branches_are_rejected() {
    let src = module("A == IF TRUE THEN 1 ELSE \"x\"");
    assert!(matches!(err_of(&src, "A"), TypeError::Mismatch { .. }));
}

/// `S \X T` is a set of pairs, and the components keep their own types.
#[test]
fn cartesian_product_builds_a_tuple() {
    let src = module("A == {1} \\X {\"a\"}");
    assert_eq!(
        ty_of(&src, "A"),
        Type::Set(Box::new(Type::Tuple(vec![Type::Int, Type::Str])))
    );
}

#[test]
fn record_set_is_a_set_of_records() {
    let src = module("A == [a : {1}, b : BOOLEAN]");
    let Type::Set(inner) = ty_of(&src, "A") else {
        panic!("expected a set");
    };
    let expected: BTreeMap<String, Type> =
        [("a".to_string(), Type::Int), ("b".to_string(), Type::Bool)]
            .into_iter()
            .collect();
    assert_eq!(
        *inner,
        Type::Rec {
            fields: expected,
            open: false
        }
    );
}

#[test]
fn except_keeps_the_function_type_and_checks_the_value() {
    let src = module("A == [[i \\in 1..3 |-> i] EXCEPT ![1] = \"x\"]");
    assert!(
        matches!(err_of(&src, "A"), TypeError::Mismatch { .. }),
        "EXCEPT must type the replacement against the element type"
    );
}

/// An occurs failure is a real TLA+ program: `x = {x}` has no well-founded
/// value, and the type system is what notices.
#[test]
fn self_containing_set_is_rejected() {
    let src = module("VARIABLE x\nA == x = {x}");
    assert!(matches!(err_of(&src, "A"), TypeError::Occurs { .. }));
}

/// `CASE` with no matching arm is TLA+-undefined — the bottom of the lattice.
/// It must fit wherever it lands rather than forcing a type.
#[test]
fn case_with_no_match_constrains_nothing() {
    let src = module("VARIABLE x\nA == (CASE x = 1 -> 5) + 1");
    assert_eq!(ty_of(&src, "A"), Type::Int);
}

/// An operator declared but never defined is monomorphic: nothing in the
/// specification licenses using it at two different types.
#[test]
fn declared_operator_is_monomorphic() {
    let src = module("CONSTANT Op(_)\nA == Op(1) /\\ Op(\"x\")");
    assert!(
        matches!(err_of(&src, "A"), TypeError::Mismatch { .. }),
        "a declared CONSTANT operator has one type, not a scheme"
    );
}

/// ...whereas a standard-module operator genuinely is polymorphic, and must be
/// instantiated freshly at each use.
#[test]
fn standard_operators_are_polymorphic() {
    let src = module("A == Cardinality({1, 2}) + Cardinality({\"a\"})");
    assert_eq!(ty_of(&src, "A"), Type::Int);
}

/// Deep input must not overflow the stack: `AGENTS.md` requires an explicit
/// heap stack for every walk over user-controlled structure, and a type walk
/// is one.
#[test]
fn deep_nesting_does_not_overflow() {
    let depth = 20_000;
    let mut body = String::from("0");
    for _ in 0..depth {
        body = format!("({body} + 1)");
    }
    let src = module(&format!("A == {body} > 0"));
    let parsed = match nixie_tla_syntax::parse_file(&src) {
        Ok(p) => p,
        // The parser has its own limit; if it declines, the point is moot.
        Err(_) => return,
    };
    let mut low = Lowerer::new();
    low.add_module(&parsed.module);
    let Ok(k) = low.lower_named(&parsed.module, "A") else {
        return;
    };
    let mut inf = Inference::new();
    // Must return, either way — what must not happen is a stack overflow.
    let _ = inf.infer(&k);
}

/// `<<>>` is the empty **sequence**, not a zero-component tuple.
///
/// Regression for a corpus finding: as a 0-tuple it unified with `Seq(e)`
/// vacuously (no components to equate) and the arity-0 shape survived, so
/// every later index into that sequence failed with "index outside a 0-tuple".
#[test]
fn empty_tuple_is_the_empty_sequence() {
    let src = module("A == <<>>");
    assert!(
        matches!(ty_of(&src, "A"), Type::Seq(_)),
        "`<<>>` must type as a sequence, not a 0-tuple"
    );
}

#[test]
fn empty_sequence_takes_the_element_type_of_its_use() {
    let src = module("VARIABLE s\nA == s = <<>> /\\ Append(s, 1) = s");
    assert_eq!(free_ty(&src, "A", "s"), Type::Seq(Box::new(Type::Int)));
}

/// The shape the bug actually produced: an empty sequence that is later
/// indexed. Before the fix this was `index 1 is outside a 0-tuple`.
#[test]
fn empty_sequence_can_still_be_indexed() {
    let src = module("VARIABLE s\nA == s = <<>> /\\ s[1] = 3");
    assert_eq!(free_ty(&src, "A", "s"), Type::Seq(Box::new(Type::Int)));
}

/// Two tuple literals of different arity are **sequences**, not a conflict.
///
/// Regression for a corpus finding: TLA+ has no separate sequence syntax, so a
/// set of counterexample traces is written `{<<3, 5, 7, 8>>, <<2, 4, 6, 7, 8>>}`.
/// Rejecting that as a 4-tuple/5-tuple mismatch accounted for 75 definitions.
#[test]
fn tuples_of_different_arity_are_sequences() {
    let src = module("A == {<<3, 5, 7, 8>>, <<2, 4, 6, 7, 8>>}");
    assert_eq!(
        ty_of(&src, "A"),
        Type::Set(Box::new(Type::Seq(Box::new(Type::Int))))
    );
}

/// ...but only when the components agree. Different arities *and* incompatible
/// components is still a real conflict, and the diagnostic must name the
/// component conflict rather than the arities.
#[test]
fn differing_arity_with_clashing_components_is_still_an_error() {
    let src = module("A == {<<1, 2>>, <<\"a\", \"b\", \"c\">>}");
    assert!(matches!(err_of(&src, "A"), TypeError::Mismatch { .. }));
}

/// Same arity keeps per-position types, so heterogeneous tuples still work.
#[test]
fn same_arity_tuples_stay_heterogeneous() {
    let src = module("A == {<<1, \"a\">>, <<2, \"b\">>}");
    assert_eq!(
        ty_of(&src, "A"),
        Type::Set(Box::new(Type::Tuple(vec![Type::Int, Type::Str])))
    );
}

/// `DOMAIN` must wait for the subject's shape, not force it to be a function.
///
/// Regression for a corpus finding: `"GRAPH" \in DOMAIN IOEnv /\ IOEnv.GRAPH`
/// learns that `IOEnv` is a **record** only from the second conjunct. Deciding
/// at the `DOMAIN` node that it must be a function ruled the record reading out
/// before it could be established, and mis-typed 12 definitions.
#[test]
fn domain_of_a_record_is_a_set_of_strings() {
    let src = module("CONSTANT r\nA == \"g\" \\in DOMAIN r /\\ r.g = 1");
    let Type::Rec { fields, open } = free_ty(&src, "A", "r") else {
        panic!("expected a record, not a function");
    };
    assert!(open);
    assert_eq!(fields.get("g"), Some(&Type::Int));
}

#[test]
fn domain_of_a_function_is_its_domain() {
    let src = module("A == DOMAIN [i \\in {\"a\"} |-> 1]");
    assert_eq!(ty_of(&src, "A"), Type::Set(Box::new(Type::Str)));
}

#[test]
fn domain_of_a_sequence_is_a_set_of_ints() {
    let src = module("CONSTANT s\nA == DOMAIN s = {1} /\\ Head(s) = 3");
    assert_eq!(free_ty(&src, "A", "s"), Type::Seq(Box::new(Type::Int)));
}

/// `DOMAIN` on an otherwise unconstrained value needs no guess and no
/// ambiguity report: `Fun(d, r)` is the *top* of the shape lattice, since a
/// tuple, a sequence and a record are each a function, and each can still
/// refine `d` afterwards. That is what separates it from a literal index,
/// where committing to `Fun` would force a tuple to be homogeneous.
#[test]
fn domain_of_an_unknown_shape_stays_general() {
    let src = module("CONSTANT f\nA == DOMAIN f = DOMAIN f");
    assert_eq!(ty_of(&src, "A"), Type::Bool);
}

/// The refinement actually happening, in both directions from one `DOMAIN`.
#[test]
fn domain_refines_once_the_shape_arrives() {
    let rec = module("CONSTANT f\nA == DOMAIN f = {\"a\"} /\\ f.a = 1");
    assert!(
        matches!(free_ty(&rec, "A", "f"), Type::Rec { .. }),
        "a field access after DOMAIN must still make it a record"
    );
    let seq = module("CONSTANT f\nA == DOMAIN f = {1} /\\ Head(f) = 3");
    assert_eq!(free_ty(&seq, "A", "f"), Type::Seq(Box::new(Type::Int)));
}

/// A record used *both* by field name and as a string-indexed function is
/// exactly `IOUtils!IOEnv`, and must not be rejected.
#[test]
fn a_function_from_strings_accepts_field_syntax() {
    let src = module("CONSTANT IOEnv\nA == IOEnv \\in [STRING -> STRING] /\\ IOEnv.GRAPH = \"x\"");
    // Either representation is defensible; what matters is that it types.
    let t = free_ty(&src, "A", "IOEnv");
    assert!(matches!(t, Type::Rec { .. } | Type::Fun(_, _)), "got {t}");
}
