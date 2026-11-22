//! The Apalache standard-library operators (issue #16, landed subset).
//!
//! `Apalache.tla`'s operators that lower exactly, per `StandardLibrary`
//! and the `__rewire_*` modules; a user's own definition of the same name
//! still wins. `Guess` and `Gen` are deliberately absent — their module
//! bodies are `CHOOSE`- and `{} `-based, and lowering either would change
//! the semantics silently (see the issue's soundness notes).

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome};

fn claim(defs: &str, body: &str) -> Outcome {
    let src = format!(
        r#"
---- MODULE Claim ----
EXTENDS Integers, FiniteSets, Apalache
{defs}
VARIABLE x
Init == x = 0
Next == UNCHANGED <<x>>
Inv  == {body}
====
"#
    );
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let mut bmc =
        Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
    bmc.check(0, &mut tm).expect("checks")
}

fn holds(defs: &str, body: &str) {
    assert_eq!(
        claim(defs, body),
        Outcome::NoViolationWithin(0),
        "`{body}` with `{defs}`"
    );
}

fn fails(defs: &str, body: &str) {
    assert_eq!(
        claim(defs, body),
        Outcome::Violation { step: 0 },
        "`{body}` with `{defs}`"
    );
}

// ---- the function constructors ----

#[test]
fn the_singleton_function_constructors() {
    holds("", r#"("a" :> 1)["a"] = 1"#);
    // `:=` is Apalache's alias for the same shape.
    holds("", r#"("a" := 1)["a"] = 1"#);
    // Two keys, two entries.
    holds(
        "",
        r#"LET f == ("a" :> 1) @@ ("b" :> 2) IN f["b"] = 2 /\ f["a"] = 1"#,
    );
    // `@@`'s LEFT side wins where the domains overlap — Apalache's rewire
    // tests the left domain first (`__rewire_tlc_in_apalache.tla:38`), and
    // TLC's module agrees.
    holds("", r#"LET f == ("a" :> 1) @@ ("a" :> 7) IN f["a"] = 1"#);
    fails("", r#"LET f == ("a" :> 1) @@ ("a" :> 7) IN f["a"] = 7"#);
}

// ---- the hint operators ----

/// `Skolem`, `Expand`, `ConstCardinality` are identity on their argument:
/// Apalache's encoder hints, which this encoder's exact sets make moot.
#[test]
fn the_hint_operators_are_identity() {
    holds("", r"Skolem({1, 2}) = {1, 2}");
    holds("", r"Expand({1, 2}) = {1, 2}");
    holds("", r"ConstCardinality({1, 2}) = {1, 2}");
    fails("", r"Skolem({1, 2}) = {1, 3}");
}

// ---- SetAsFun ----

/// `SetAsFun(S)`: the function mapping each pair's first to its second —
/// Apalache's own rewire, exact through the kernel `CHOOSE` over the set
/// of pairs. The encode gap this used to pin (the domain's tuple members
/// had no scalar form) closed by reifying structural members in
/// `native_set_of`, so both of the issue's claims are assertions again.
#[test]
fn set_as_fun_builds_the_function() {
    // The issue's Inv, verbatim.
    holds("", r#"SetAsFun({<<"a", 1>>, <<"b", 2>>})["a"] = 1"#);
    // And its DOMAIN claim.
    holds(
        "",
        r#"DOMAIN SetAsFun({<<"a", 1>>, <<"b", 2>>}) = {"a", "b"}"#,
    );
    // The function is exact, not approximate: a wrong value is a
    // violation. (An out-of-domain read such as `SetAsFun({<<"a", 1>>})["b"]`
    // is deliberately *not* asserted: TLA+ leaves it undefined, and the
    // encoding's underspecified answer there is a documented choice, not a
    // claim either way.)
    fails("", r#"SetAsFun({<<"a", 1>>, <<"b", 2>>})["a"] = 2"#);
}

// ---- Repeat ----

/// `Repeat(F, N, x)`: N-fold application, literal N only — Apalache's
/// `RepeatRule`, as ONE ordered sequence fold (F need not be commutative).
#[test]
fn repeat_applies_the_operator_n_times() {
    // The issue's own Inv1: F(a,i) = a+1, five times from 0.
    holds(
        "Op(a, i) == a + 1",
        "LET Op2(a, i) == a + 1 IN Repeat(Op2, 5, 0) = 5",
    );
    // And Inv2: F(a,i) = a+i — the step index participates.
    holds("", "LET Op(a, i) == a + i IN Repeat(Op, 5, 0) = 15");
    // A wrong count is a violation, not a decline.
    fails("", "LET Op(a, i) == a + i IN Repeat(Op, 5, 0) = 14");
    // Zero repeats: the value unchanged.
    holds("", "LET Op(a, i) == a + 1 IN Repeat(Op, 0, 41) = 41");
    // A `LAMBDA` works as the operator.
    holds("", r"Repeat(LAMBDA a, i: a * 2, 4, 1) = 16");
}

/// A non-literal count declines by name — Apalache errors on it too, and a
/// symbolic count has no finite unfolding.
#[test]
fn repeat_with_a_symbolic_count_declines() {
    let src = r#"
---- MODULE RepBad ----
EXTENDS Integers, Apalache
VARIABLE n
Init == n \in 1..3
Next == UNCHANGED n
Inv == Repeat(LAMBDA a, i: a + 1, n, 0) = n
====
"#;
    let parsed = nixie_tla_syntax::parse_file(src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("has a root module");
    let mut tm = TermManager::new();
    let err = match Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm) {
        Ok(_) => panic!("a symbolic count must not prepare"),
        Err(e) => e,
    };
    assert!(
        err.to_string().contains("literal"),
        "the decline names the literal-count requirement: {err}"
    );
}

// ---- MkSeq ----

/// `MkSeq(N, F) == [i \in 1..N |-> F(i)]`, literal N.
#[test]
fn mk_seq_builds_the_sequence() {
    holds("", r#"LET Id(i) == i IN MkSeq(3, Id) = <<1, 2, 3>>"#);
    holds("", r#"LET Sq(i) == i * i IN MkSeq(3, Sq)[2] = 4"#);
    fails("", r#"LET Id(i) == i IN MkSeq(3, Id) = <<1, 2>>"#);
}

// ---- the never-lowered operators ----

/// `Guess` and `Gen` must NOT lower from their module bodies: `Guess`'s body
/// is a `CHOOSE` (deterministic — *fewer* behaviours than Apalache's
/// nondeterministic pick, which hides violations), and `Gen`'s is `{}`. A
/// spec using them declines by name instead.
#[test]
fn guess_and_gen_decline_rather_than_lower() {
    for body in ["Gen(3)", "Guess()"] {
        let src = format!(
            r#"
---- MODULE G ----
EXTENDS Integers, Apalache
VARIABLE x
Init == x = 0
Next == UNCHANGED <<x>>
Inv  == {body} # x
====
"#
        );
        let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
        let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
        let module = spec.root_module().expect("has a root module");
        let mut tm = TermManager::new();
        let mut bmc =
            Bmc::prepare(&spec, module, "Init", "Next", "Inv", &[], &mut tm).expect("prepares");
        assert!(
            bmc.check(0, &mut tm).is_err(),
            "`{body}` must decline, not lower from its body"
        );
    }
}

// ---- FunAsSeq ----

/// `FunAsSeq(f, len, capacity)`: the function's `1..len` prefix as a
/// sequence — Apalache's own rewire shape, `SubSeq([i \in 1..cap |-> f[i]],
/// 1, len)`, with `SubSeq`'s window arithmetic carrying a symbolic `len`
/// exactly. The two-argument form reads `capacity = len`.
#[test]
fn fun_as_seq_casts_a_function_prefix() {
    // The whole function, as a sequence: reads and length.
    holds(
        "",
        r#"LET s == FunAsSeq([i \in 1..3 |-> 2 * i], 3, 3) IN s[2] = 4"#,
    );
    holds("", r#"Len(FunAsSeq([i \in 1..3 |-> 2 * i], 3, 3)) = 3"#);
    // A prefix: only `1..len` is the sequence, the capacity just bounds it.
    holds(
        "",
        r#"LET s == FunAsSeq([i \in 1..3 |-> 2 * i], 2, 3) IN /\ s[2] = 4 /\ Len(s) = 2"#,
    );
    // The elements are the function's, not placeholders.
    fails("", r#"FunAsSeq([i \in 1..3 |-> 2 * i], 3, 3)[2] = 5"#);
    // The two-argument form: capacity = len.
    holds("", r#"FunAsSeq([i \in 1..3 |-> 7], 3)[3] = 7"#);
}

// ---- the community folds, rewired ----

/// The community modules' folds, exactly as Apalache's `__rewire_*` modules
/// define them: the operator's **right** parameter is the accumulator
/// (`op(x, acc)`), and the function folds read the function's *values*.
/// The `ApaFoldSet` order-independence audit still applies: a non-AC
/// operator over a set is refused, never silently reordered.
#[test]
fn the_community_folds_rewire_with_their_argument_order() {
    // FoldSet: op(x, acc) — right-associative accumulation over a set.
    holds("", r#"FoldSet(LAMBDA x, acc: x + acc, 0, {1, 2, 3}) = 6"#);
    // A sequence fold keeps its order (left fold), so a non-commutative
    // operator is still exact: `((0 - 1) - 2) - 3`, never any other order.
    holds(
        "",
        r#"FoldSeq(LAMBDA x, acc: acc - x, 0, <<1, 2, 3>>) = -6"#,
    );
    // FoldFunction: over the function's values, `op(f[i], acc)`.
    holds(
        "",
        r#"FoldFunction(LAMBDA x, acc: x + acc, 0, [i \in {1, 2} |-> 10 * i]) = 30"#,
    );
    // FoldFunctionOnSet: over the values at the given indices only.
    holds(
        "",
        r#"FoldFunctionOnSet(LAMBDA x, acc: x + acc, 0, [i \in {1, 2, 3} |-> i], {1, 3}) = 4"#,
    );
    // A wrong total is a violation, not a decline.
    fails("", r#"FoldSet(LAMBDA x, acc: x + acc, 0, {1, 2, 3}) = 5"#);
}
