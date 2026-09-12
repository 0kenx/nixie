//! Parser acceptance tests.
//!
//! These are the seed of the parser differential suite described in
//! `docs/TLA_FRONTEND_DESIGN.md` §5: every construct here is one the Apalache
//! fragment requires, and every rejection is one that must stay a rejection.

use nixie_tla_syntax::ast::*;
use nixie_tla_syntax::error::ErrorKind;
use nixie_tla_syntax::{NumBase, parse_expr_str, parse_file};

fn expr(src: &str) -> Expr {
    match parse_expr_str(src) {
        Ok(e) => e,
        Err(e) => panic!("failed to parse {src:?}: {e}"),
    }
}

fn expr_err(src: &str) -> ErrorKind {
    match parse_expr_str(src) {
        Ok(e) => panic!("expected {src:?} to be rejected, got {:?}", e.kind),
        Err(e) => e.kind,
    }
}

// ---- lexing ----------------------------------------------------------------

#[test]
fn based_numerals_are_not_confused_with_operators() {
    // `\o` is circle-composition; `\o777` is octal. `\h`'s digits are letters.
    assert_eq!(
        expr("\\o777").kind,
        ExprKind::Int {
            base: NumBase::Octal,
            digits: "777".to_string()
        }
    );
    assert_eq!(
        expr("\\hFF").kind,
        ExprKind::Int {
            base: NumBase::Hex,
            digits: "FF".to_string()
        }
    );
    assert_eq!(
        expr("\\b1011").kind,
        ExprKind::Int {
            base: NumBase::Binary,
            digits: "1011".to_string()
        }
    );
    // Bare `\o` is still the operator, and `\bullet` is not binary 0b-ullet.
    assert!(matches!(
        expr("f \\o g").kind,
        ExprKind::Infix { ref op, .. } if op == "\\o"
    ));
    assert!(matches!(
        expr("f \\bullet g").kind,
        ExprKind::Infix { ref op, .. } if op == "\\bullet"
    ));
}

#[test]
fn range_operator_is_not_a_real_literal() {
    // `1..5` must be `1 .. 5`, not `1.` followed by `.5`.
    assert!(matches!(
        expr("1..5").kind,
        ExprKind::Infix { ref op, .. } if op == ".."
    ));
    assert_eq!(expr("3.14").kind, ExprKind::Real("3.14".to_string()));
}

#[test]
fn unicode_spellings_canonicalise() {
    let ascii = expr("a /\\ b \\in S");
    let unicode = expr("a ∧ b ∈ S");
    // Spans differ (different byte lengths), so compare the shapes.
    fn shape(e: &Expr) -> String {
        match &e.kind {
            ExprKind::Infix { op, lhs, rhs, .. } => {
                format!("({} {} {})", shape(lhs), op, shape(rhs))
            }
            ExprKind::Name(n) => n.path.iter().map(|i| i.name.clone()).collect(),
            other => format!("{other:?}"),
        }
    }
    assert_eq!(shape(&ascii), shape(&unicode));
}

#[test]
fn unicode_columns_count_scalars_not_bytes() {
    // A junction list whose items mix ASCII and Unicode still aligns.
    let src = "---- MODULE M ----\nA == /\\ x ∈ S\n     /\\ y = 1\n====\n";
    let parsed = parse_file(src).expect("mixed-encoding junction list parses");
    let Some(UnitKind::OpDef { body, .. }) = parsed.module.units.first().map(|u| &u.kind) else {
        panic!("expected an operator definition");
    };
    let ExprKind::Junction { items, .. } = &body.kind else {
        panic!("expected a junction list, got {:?}", body.kind);
    };
    assert_eq!(items.len(), 2);
}

#[test]
fn comments_are_retained_for_type_annotations() {
    let src = "---- MODULE M ----\n\\* @type: Int -> Bool;\nOp(x) == TRUE\n(* a (* nested *) block *)\n====\n";
    let parsed = parse_file(src).expect("comments parse");
    assert_eq!(parsed.comments.len(), 2);
    assert!(parsed.comments[0].text.contains("@type:"));
    assert!(parsed.comments[1].block);
    assert!(parsed.comments[1].text.contains("nested"));
}

#[test]
fn unterminated_block_comment_is_an_error() {
    let src = "---- MODULE M ----\n(* never closed\n====\n";
    assert!(matches!(
        parse_file(src).map(|_| ()).unwrap_err().kind,
        ErrorKind::UnterminatedComment
    ));
}

// ---- precedence ------------------------------------------------------------

#[test]
fn precedence_ranges_bind_as_expected() {
    // `*` (13) binds tighter than `+` (10).
    let e = expr("a + b * c");
    let ExprKind::Infix { op, rhs, .. } = &e.kind else {
        panic!("expected infix");
    };
    assert_eq!(op, "+");
    assert!(matches!(rhs.kind, ExprKind::Infix { ref op, .. } if op == "*"));

    // `=>` (1) is the loosest.
    let e = expr("a /\\ b => c");
    assert!(matches!(e.kind, ExprKind::Infix { ref op, .. } if op == "=>"));
}

#[test]
fn overlapping_precedence_is_a_named_conflict() {
    // `=` and `<` both sit at 5-5, so `a = b < c` is an error in TLA+ — and
    // the diagnostic must name both operators, which is the whole reason this
    // crate uses Pratt rather than a generated table.
    let err = expr_err("a = b < c");
    let ErrorKind::PrecedenceConflict { left, right, .. } = err else {
        panic!("expected a precedence conflict, got {err:?}");
    };
    assert_eq!(left, "=");
    assert_eq!(right, "<");

    // Parenthesising resolves it.
    expr("(a = b) < c");
    // Chaining an associative operator is fine.
    expr("a + b + c");
    expr("a \\cup b \\cup c");
    // Non-associative same-operator chaining is not.
    assert!(matches!(
        expr_err("a = b = c"),
        ErrorKind::PrecedenceConflict { .. }
    ));
}

#[test]
fn prime_is_postfix_and_binds_tightest() {
    let e = expr("x' = x + 1");
    let ExprKind::Infix { op, lhs, .. } = &e.kind else {
        panic!("expected infix");
    };
    assert_eq!(op, "=");
    assert!(matches!(lhs.kind, ExprKind::Postfix { ref op, .. } if op == "'"));
}

#[test]
fn unary_minus_is_distinct_from_subtraction() {
    assert!(matches!(
        expr("-x").kind,
        ExprKind::Prefix { ref op, .. } if op == "-."
    ));
    assert!(matches!(
        expr("a - b").kind,
        ExprKind::Infix { ref op, .. } if op == "-"
    ));
}

// ---- layout ----------------------------------------------------------------

#[test]
fn junction_list_versus_infix_junction() {
    // Same token, two meanings, decided by expression position.
    let infix = expr("a /\\ b");
    assert!(matches!(infix.kind, ExprKind::Infix { .. }));

    let list = expr("/\\ a\n/\\ b");
    let ExprKind::Junction { kind, items } = &list.kind else {
        panic!("expected a junction list, got {:?}", list.kind);
    };
    assert_eq!(*kind, Junct::And);
    assert_eq!(items.len(), 2);
}

#[test]
fn nested_junction_lists_close_by_column() {
    let src = "---- MODULE M ----\nNext ==\n  /\\ \\/ x\n     \\/ y\n  /\\ z\n====\n";
    let parsed = parse_file(src).expect("nested junction lists parse");
    let Some(UnitKind::OpDef { body, .. }) = parsed.module.units.first().map(|u| &u.kind) else {
        panic!("expected an operator definition");
    };
    let ExprKind::Junction { kind, items } = &body.kind else {
        panic!("expected outer conjunction, got {:?}", body.kind);
    };
    assert_eq!(*kind, Junct::And);
    assert_eq!(items.len(), 2, "outer list has two items");
    let ExprKind::Junction {
        kind: ik,
        items: ii,
    } = &items[0].kind
    else {
        panic!("expected inner disjunction, got {:?}", items[0].kind);
    };
    assert_eq!(*ik, Junct::Or);
    assert_eq!(ii.len(), 2, "inner list has two items");
}

#[test]
fn junction_list_does_not_swallow_the_next_unit() {
    // The `-` starting the next line is at column 1, inside a list aligned at
    // column 8; layout must stop the Pratt loop rather than parsing `a - 5`.
    let src = "---- MODULE M ----\nA == /\\ a\nB == 5\n====\n";
    let parsed = parse_file(src).expect("list terminates at column 1");
    assert_eq!(parsed.module.units.len(), 2);
}

#[test]
fn junction_list_terminates_at_a_closing_bracket() {
    let e = expr("f(/\\ a\n  /\\ b)");
    let ExprKind::Apply { args, .. } = &e.kind else {
        panic!("expected application, got {:?}", e.kind);
    };
    assert!(matches!(args[0].kind, ExprKind::Junction { .. }));
}

// ---- the six-way `[` ------------------------------------------------------

#[test]
fn bracket_forms_are_distinguished() {
    assert!(matches!(expr("[S -> T]").kind, ExprKind::FnSet { .. }));
    assert!(matches!(
        expr("[x \\in S |-> x + 1]").kind,
        ExprKind::FnConstruct { .. }
    ));
    assert!(matches!(
        expr("[a |-> 1, b |-> 2]").kind,
        ExprKind::RecordLit(_)
    ));
    assert!(matches!(
        expr("[a : S, b : T]").kind,
        ExprKind::RecordSet(_)
    ));
    assert!(matches!(
        expr("[f EXCEPT ![i] = 1]").kind,
        ExprKind::Except { .. }
    ));
    assert!(matches!(
        expr("[Next]_vars").kind,
        ExprKind::Action {
            kind: ActionKind::Stuttering,
            ..
        }
    ));
}

#[test]
fn bracket_disambiguation_sees_past_nesting() {
    // The inner `\in` is at depth 1 and must not make this a function
    // constructor; the top-level `EXCEPT` decides.
    let e = expr("[[x \\in S |-> 0] EXCEPT ![1] = 2]");
    assert!(matches!(e.kind, ExprKind::Except { .. }));

    // A `:` inside a set-filter must not make this a record set.
    let e = expr("[x \\in {y \\in S : P(y)} |-> x]");
    assert!(matches!(e.kind, ExprKind::FnConstruct { .. }));
}

#[test]
fn subscript_underscore_is_not_an_identifier() {
    // `_vars` is a legal TLA+ identifier, so `]_vars` would otherwise lex as
    // `]` followed by the identifier `_vars`.
    let e = expr("[Next]_vars");
    let ExprKind::Action { subscript, .. } = &e.kind else {
        panic!("expected an action");
    };
    let ExprKind::Name(n) = &subscript.kind else {
        panic!("expected a name subscript");
    };
    assert_eq!(n.path[0].name, "vars");
}

#[test]
fn temporal_always_of_an_action() {
    let e = expr("[][Next]_vars");
    let ExprKind::Prefix { op, operand, .. } = &e.kind else {
        panic!("expected `[]`, got {:?}", e.kind);
    };
    assert_eq!(op, "[]");
    assert!(matches!(operand.kind, ExprKind::Action { .. }));
}

#[test]
fn angle_action_versus_tuple() {
    assert!(matches!(expr("<<a, b>>").kind, ExprKind::Tuple(_)));
    assert!(matches!(
        expr("<<Next>>_vars").kind,
        ExprKind::Action {
            kind: ActionKind::NonStuttering,
            ..
        }
    ));
}

#[test]
fn except_paths_and_at() {
    let e = expr("[f EXCEPT ![i][j] = @ + 1, !.fld = 2]");
    let ExprKind::Except { updates, .. } = &e.kind else {
        panic!("expected EXCEPT");
    };
    assert_eq!(updates.len(), 2);
    assert_eq!(updates[0].path.len(), 2);
    assert!(matches!(updates[1].path[0], ExceptSel::Field(_)));
    // `@` survives as its own node so the desugarer can bind it.
    let ExprKind::Infix { lhs, .. } = &updates[0].value.kind else {
        panic!("expected `@ + 1`");
    };
    assert_eq!(lhs.kind, ExprKind::At);
}

// ---- braces ----------------------------------------------------------------

#[test]
fn brace_forms_are_distinguished() {
    assert!(matches!(expr("{}").kind, ExprKind::SetEnum(_)));
    assert!(matches!(expr("{1, 2, 3}").kind, ExprKind::SetEnum(_)));
    assert!(matches!(
        expr("{x \\in S : P(x)}").kind,
        ExprKind::SetFilter { .. }
    ));
    assert!(matches!(
        expr("{f[x] : x \\in S}").kind,
        ExprKind::SetMap { .. }
    ));
    // `{a \in b}` is a singleton holding a membership test, not a filter.
    assert!(matches!(expr("{a \\in b}").kind, ExprKind::SetEnum(_)));
    assert!(matches!(
        expr("{<<x, y>> \\in S : P}").kind,
        ExprKind::SetFilter {
            pattern: Pattern::Tuple(_),
            ..
        }
    ));
}

// ---- binders ---------------------------------------------------------------

#[test]
fn quantifiers_bounded_and_unbounded() {
    let e = expr("\\A x \\in S : P(x)");
    let ExprKind::Quant { kind, bounds, .. } = &e.kind else {
        panic!("expected a bounded quantifier");
    };
    assert_eq!(*kind, QuantKind::Forall);
    assert_eq!(bounds.len(), 1);

    // Unbounded stays a distinct node: Apalache rejects it, and the rejection
    // has to be able to name the construct.
    assert!(matches!(
        expr("\\E x : P(x)").kind,
        ExprKind::UnboundedQuant { .. }
    ));

    // Several patterns sharing one domain, and several domains.
    let e = expr("\\A x, y \\in S, z \\in T : P");
    let ExprKind::Quant { bounds, .. } = &e.kind else {
        panic!("expected a bounded quantifier");
    };
    assert_eq!(bounds.len(), 2);
    assert_eq!(bounds[0].patterns.len(), 2);
    assert_eq!(bounds[1].patterns.len(), 1);
}

#[test]
fn choose_lambda_and_fairness() {
    assert!(matches!(
        expr("CHOOSE x \\in S : P(x)").kind,
        ExprKind::Choose {
            domain: Some(_),
            ..
        }
    ));
    assert!(matches!(
        expr("CHOOSE x : P(x)").kind,
        ExprKind::Choose { domain: None, .. }
    ));
    assert!(matches!(
        expr("LAMBDA x, y : x + y").kind,
        ExprKind::Lambda { .. }
    ));
    assert!(matches!(
        expr("WF_vars(Next)").kind,
        ExprKind::Fairness {
            kind: FairnessKind::Weak,
            ..
        }
    ));
    assert!(matches!(
        expr("SF_vars(Next)").kind,
        ExprKind::Fairness {
            kind: FairnessKind::Strong,
            ..
        }
    ));
}

#[test]
fn if_case_and_let() {
    assert!(matches!(
        expr("IF p THEN 1 ELSE 2").kind,
        ExprKind::If { .. }
    ));

    let e = expr("CASE p -> 1 [] q -> 2 [] OTHER -> 3");
    let ExprKind::Case { arms, other } = &e.kind else {
        panic!("expected CASE, got {:?}", e.kind);
    };
    assert_eq!(arms.len(), 2);
    assert!(other.is_some());

    let e = expr("LET a == 1 b == 2 IN a + b");
    let ExprKind::Let { defs, .. } = &e.kind else {
        panic!("expected LET");
    };
    assert_eq!(defs.len(), 2);
}

#[test]
fn qualified_names_and_application() {
    let e = expr("I!J!Op(x, y)");
    let ExprKind::Apply { head, args } = &e.kind else {
        panic!("expected an application");
    };
    assert_eq!(head.path.len(), 3);
    assert!(head.is_qualified());
    assert_eq!(args.len(), 2);

    assert!(matches!(expr("f[x]").kind, ExprKind::FnApply { .. }));
    assert!(matches!(expr("r.field").kind, ExprKind::Field { .. }));
    assert!(matches!(expr("r.a.b").kind, ExprKind::Field { .. }));
}

// ---- modules and units -----------------------------------------------------

#[test]
fn a_realistic_module() {
    let src = r"
---- MODULE Counter ----
EXTENDS Naturals, Sequences
CONSTANTS N, Op(_, _)
VARIABLES x, q

vars == <<x, q>>

TypeOK == /\ x \in 0..N
          /\ q \in Seq(Nat)

Init == /\ x = 0
        /\ q = <<>>

Inc == /\ x < N
       /\ x' = x + 1
       /\ UNCHANGED q

Next == \/ Inc
        \/ /\ q # <<>>
           /\ q' = Tail(q)
           /\ UNCHANGED x

Spec == Init /\ [][Next]_vars /\ WF_vars(Inc)

THEOREM Spec => []TypeOK
====
";
    let parsed = parse_file(src).expect("a realistic module parses");
    let m = &parsed.module;
    assert_eq!(m.name.name, "Counter");
    assert_eq!(m.extends().len(), 2);
    assert_eq!(m.variables().len(), 2);
    let consts = m.constants();
    assert_eq!(consts.len(), 2);
    assert_eq!(consts[1].arity, 2, "Op(_, _) has arity 2");
    assert!(
        m.units
            .iter()
            .any(|u| matches!(u.kind, UnitKind::Theorem { .. }))
    );
}

#[test]
fn definition_shapes() {
    let src = r"
---- MODULE Defs ----
Simple == 1
Parms(a, b) == a + b
HigherOrder(F(_), x) == F(x)
Fn[i \in S] == i + 1
a \oplus b == a + b
x ^+ == x + 1
LOCAL Hidden == 2
I == INSTANCE M WITH a <- 1, b <- 2
J(p) == INSTANCE M WITH a <- p
INSTANCE Naturals
ASSUME N > 0
ASSUME Named == N > 1
====
";
    let parsed = parse_file(src).expect("definition shapes parse");
    let kinds: Vec<&UnitKind> = parsed.module.units.iter().map(|u| &u.kind).collect();

    assert!(matches!(kinds[0], UnitKind::OpDef { params, .. } if params.is_empty()));
    assert!(matches!(kinds[1], UnitKind::OpDef { params, .. } if params.len() == 2));
    assert!(
        matches!(kinds[2], UnitKind::OpDef { params, .. } if params[0].arity == 1),
        "higher-order parameter keeps its arity"
    );
    assert!(matches!(kinds[3], UnitKind::FnDef { .. }));
    assert!(matches!(kinds[4], UnitKind::OpDef { name, .. } if name.name == "\\oplus"));
    assert!(matches!(kinds[5], UnitKind::OpDef { name, .. } if name.name == "^+"));
    assert!(matches!(kinds[6], UnitKind::OpDef { local: true, .. }));
    assert!(matches!(kinds[7], UnitKind::ModuleDef { .. }));
    assert!(matches!(kinds[8], UnitKind::ModuleDef { params, .. } if params.len() == 1));
    assert!(matches!(kinds[9], UnitKind::Instance { .. }));
    assert!(matches!(kinds[10], UnitKind::Assume { name: None, .. }));
    assert!(matches!(kinds[11], UnitKind::Assume { name: Some(_), .. }));
}

#[test]
fn separators_and_submodules() {
    let src = r"
---- MODULE Outer ----
A == 1
--------------------------
---- MODULE Inner ----
B == 2
====
C == 3
====
";
    let parsed = parse_file(src).expect("separators and submodules parse");
    assert!(
        parsed
            .module
            .units
            .iter()
            .any(|u| matches!(u.kind, UnitKind::Submodule(_)))
    );
    assert!(
        parsed
            .module
            .units
            .iter()
            .any(|u| matches!(u.kind, UnitKind::Separator))
    );
}

#[test]
fn simple_proofs_are_consumed_without_swallowing_the_next_unit() {
    let src = r"
---- MODULE P ----
THEOREM T1 == 1 = 1
  OBVIOUS
THEOREM T2 == 2 = 2
  BY DEF T1
A == 3
====
";
    let parsed = parse_file(src).expect("simple proofs parse");
    let theorems = parsed
        .module
        .units
        .iter()
        .filter(|u| matches!(u.kind, UnitKind::Theorem { proof: Some(_), .. }))
        .count();
    assert_eq!(theorems, 2);
    assert!(
        parsed
            .module
            .units
            .iter()
            .any(|u| matches!(&u.kind, UnitKind::OpDef { name, .. } if name.name == "A")),
        "the unit after a BY proof is still found"
    );
}

// ---- rejections ------------------------------------------------------------

#[test]
fn recursive_is_rejected_by_name() {
    let src = "---- MODULE M ----\nRECURSIVE F(_)\n====\n";
    let err = parse_file(src).map(|_| ()).unwrap_err();
    let ErrorKind::Unsupported { construct, .. } = &err.kind else {
        panic!("expected an Unsupported diagnostic, got {:?}", err.kind);
    };
    assert!(construct.contains("RECURSIVE"));
}

#[test]
fn structured_proofs_are_rejected_rather_than_guessed_at() {
    let src = "---- MODULE M ----\nTHEOREM T == 1 = 1\n<1>1. TRUE\n<1> QED\n====\n";
    let err = parse_file(src).map(|_| ()).unwrap_err();
    assert!(
        matches!(err.kind, ErrorKind::Unsupported { .. }),
        "got {:?}",
        err.kind
    );
}

#[test]
fn unknown_backslash_word_is_rejected() {
    assert!(matches!(
        expr_err("a \\notanop b"),
        ErrorKind::UnknownOperator(_)
    ));
}

#[test]
fn deep_nesting_yields_a_diagnostic_not_a_stack_overflow() {
    // AGENTS.md: deep user-controlled input must not overflow the stack.
    let depth = 5_000;
    let src = format!("{}x{}", "(".repeat(depth), ")".repeat(depth));
    let err = parse_expr_str(&src).map(|_| ()).unwrap_err();
    assert!(
        matches!(err.kind, ErrorKind::RecursionLimit { .. }),
        "got {:?}",
        err.kind
    );
}

#[test]
fn spans_point_at_the_offending_token() {
    let err = parse_expr_str("a = b < c").map(|_| ()).unwrap_err();
    assert_eq!(err.span.start.line, 1);
    assert_eq!(err.span.start.col, 7, "the `<` is at column 7");
}
