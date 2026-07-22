//! Semantic validation of `InterpolantExtractor` (PF-01 regression).
//!
//! Each test builds a concrete propositional resolution refutation of `A ∧ B`,
//! extracts a Craig interpolant `I` through the crate's *public* API, and then
//! independently verifies the three defining interpolant properties with a
//! self-contained, dependency-free truth-table checker:
//!
//! - (a) `vocab(I) ⊆ vocab(A) ∩ vocab(B)` (shared vocabulary only),
//! - (b) `A ⟹ I`,
//! - (c) `I ∧ B` is unsatisfiable.
//!
//! Coverage includes a purely propositional refutation, an A-only refutation
//! (`A` alone unsat), a B-only refutation (`B` alone unsat), the classic
//! `(A: p ∧ q) (B: ¬p)` shape, and cases whose interpolant is a compound
//! conjunction / disjunction (exercising both the shared/`B`-local `∧` branch
//! and the `A`-local `∨` branch of McMillan's pivot rule).

use oxiz_proof::premise::PremiseTracker;
use oxiz_proof::proof::Proof;
use oxiz_proof::{InterpolantExtractor, Partition};
use std::collections::{BTreeSet, HashMap};

// ---------------------------------------------------------------------------
// Tiny propositional formula parser + truth-table evaluator (test-only)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum F {
    True,
    False,
    Atom(String),
    Not(Box<F>),
    And(Vec<F>),
    Or(Vec<F>),
}

fn tokenize(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for ch in s.chars() {
        match ch {
            '(' | ')' => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                out.push(ch.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

fn parse(s: &str) -> F {
    let tokens = tokenize(s);
    let mut pos = 0usize;
    let f = parse_expr(&tokens, &mut pos);
    assert_eq!(pos, tokens.len(), "trailing tokens parsing {s:?}");
    f
}

fn parse_expr(tokens: &[String], pos: &mut usize) -> F {
    let tok = tokens.get(*pos).expect("unexpected end of formula").clone();
    *pos += 1;
    if tok == "(" {
        let head = tokens.get(*pos).expect("missing operator after (").clone();
        *pos += 1;
        let mut args = Vec::new();
        while tokens.get(*pos).map(String::as_str) != Some(")") {
            args.push(parse_expr(tokens, pos));
        }
        *pos += 1; // consume ")"
        match head.as_str() {
            "and" => F::And(args),
            "or" => F::Or(args),
            "not" => {
                assert_eq!(args.len(), 1, "`not` takes one argument");
                F::Not(Box::new(args.into_iter().next().expect("checked len == 1")))
            }
            other => panic!("unknown operator {other:?}"),
        }
    } else {
        match tok.as_str() {
            "true" => F::True,
            "false" => F::False,
            atom => F::Atom(atom.to_string()),
        }
    }
}

fn collect_vars(f: &F, out: &mut BTreeSet<String>) {
    match f {
        F::True | F::False => {}
        F::Atom(a) => {
            out.insert(a.clone());
        }
        F::Not(inner) => collect_vars(inner, out),
        F::And(xs) | F::Or(xs) => {
            for x in xs {
                collect_vars(x, out);
            }
        }
    }
}

/// Evaluate a parsed propositional formula AST under a boolean assignment.
/// This is a pure structural interpreter over the `F` enum -- it executes no
/// external or arbitrary code (it is unrelated to any language `eval`).
fn eval(f: &F, env: &HashMap<String, bool>) -> bool {
    match f {
        F::True => true,
        F::False => false,
        F::Atom(a) => *env.get(a).unwrap_or(&false),
        F::Not(inner) => !eval(inner, env),
        F::And(xs) => xs.iter().all(|x| eval(x, env)),
        F::Or(xs) => xs.iter().any(|x| eval(x, env)),
    }
}

fn formula_vars(formulas: &[F]) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    for f in formulas {
        collect_vars(f, &mut set);
    }
    set
}

/// Verify (a) shared vocabulary, (b) `A ⟹ I`, (c) `I ∧ B` unsat, by exhaustive
/// truth-table enumeration over the union of all variables involved.
fn validate_interpolant(interpolant: &str, a_formulas: &[&str], b_formulas: &[&str]) {
    let i = parse(interpolant);
    let a: Vec<F> = a_formulas.iter().map(|s| parse(s)).collect();
    let b: Vec<F> = b_formulas.iter().map(|s| parse(s)).collect();

    let a_vars = formula_vars(&a);
    let b_vars = formula_vars(&b);
    let shared: BTreeSet<String> = a_vars.intersection(&b_vars).cloned().collect();

    let mut i_vars = BTreeSet::new();
    collect_vars(&i, &mut i_vars);

    // (a) The interpolant may only mention shared symbols.
    assert!(
        i_vars.is_subset(&shared),
        "interpolant {interpolant:?} uses non-shared symbols: I={i_vars:?}, shared={shared:?}"
    );

    // Enumerate over the union of every variable that appears anywhere.
    let mut all: BTreeSet<String> = BTreeSet::new();
    all.extend(a_vars.iter().cloned());
    all.extend(b_vars.iter().cloned());
    all.extend(i_vars.iter().cloned());
    let all: Vec<String> = all.into_iter().collect();
    assert!(all.len() <= 20, "too many variables for truth-table check");

    for mask in 0u32..(1u32 << all.len()) {
        let mut env = HashMap::new();
        for (bit, name) in all.iter().enumerate() {
            env.insert(name.clone(), (mask >> bit) & 1 == 1);
        }

        let a_val = a.iter().all(|f| eval(f, &env)); // conjunction of A (true if empty)
        let b_val = b.iter().all(|f| eval(f, &env)); // conjunction of B (true if empty)
        let i_val = eval(&i, &env);

        // (b) A ⟹ I.
        assert!(
            !a_val || i_val,
            "A ⟹ I violated at {env:?}: A={a_val}, I={i_val} (interpolant {interpolant:?})"
        );
        // (c) I ∧ B unsatisfiable.
        assert!(
            !(i_val && b_val),
            "I ∧ B satisfiable at {env:?} (interpolant {interpolant:?})"
        );
    }
}

// ---------------------------------------------------------------------------
// Scenarios
// ---------------------------------------------------------------------------

/// The classic shape: A = p ∧ q, B = ¬p. Shared vocabulary is {p}.
#[test]
fn classic_p_and_q_versus_not_p() {
    let mut tracker = PremiseTracker::new();
    let a_p = tracker.add_assertion("p");
    let a_q = tracker.add_assertion("q");
    let b_np = tracker.add_assertion("(not p)");
    let partition = Partition::new(vec![a_p, a_q], vec![b_np]);

    let mut proof = Proof::new();
    let n_p = proof.add_axiom("p");
    let _n_q = proof.add_axiom("q");
    let n_np = proof.add_axiom("(not p)");
    proof.add_inference("resolution", vec![n_p, n_np], "false");

    let mut extractor = InterpolantExtractor::new(partition, tracker);
    let interp = extractor.extract(&proof).expect("should interpolate");

    validate_interpolant(&interp.formula, &["p", "q"], &["(not p)"]);
}

/// A purely propositional refutation whose interpolant is a single shared atom
/// reached through an A-local pivot then a shared pivot.
/// A = p ∧ (¬p ∨ q), B = ¬q. Shared vocabulary is {q}.
fn build_alocal_shared() -> (InterpolantExtractor, Proof) {
    let mut tracker = PremiseTracker::new();
    let a_p = tracker.add_assertion("p");
    let a_pq = tracker.add_assertion("(or (not p) q)");
    let b_nq = tracker.add_assertion("(not q)");
    let partition = Partition::new(vec![a_p, a_pq], vec![b_nq]);

    let mut proof = Proof::new();
    let n_p = proof.add_axiom("p");
    let n_pq = proof.add_axiom("(or (not p) q)");
    let n_nq = proof.add_axiom("(not q)");
    let n_q = proof.add_inference("resolution", vec![n_p, n_pq], "q");
    proof.add_inference("resolution", vec![n_q, n_nq], "false");

    (InterpolantExtractor::new(partition, tracker), proof)
}

#[test]
fn propositional_alocal_then_shared_pivot() {
    let (mut extractor, proof) = build_alocal_shared();
    let interp = extractor.extract(&proof).expect("should interpolate");
    validate_interpolant(&interp.formula, &["p", "(or (not p) q)"], &["(not q)"]);
}

/// Interpolant is a compound conjunction over shared vocabulary.
/// A = a ∧ b, B = ¬a ∨ ¬b. Shared vocabulary is {a, b}.
#[test]
fn compound_conjunction_interpolant() {
    let mut tracker = PremiseTracker::new();
    let a_a = tracker.add_assertion("a");
    let a_b = tracker.add_assertion("b");
    let b_clause = tracker.add_assertion("(or (not a) (not b))");
    let partition = Partition::new(vec![a_a, a_b], vec![b_clause]);

    let mut proof = Proof::new();
    let n_a = proof.add_axiom("a");
    let n_b = proof.add_axiom("b");
    let n_c = proof.add_axiom("(or (not a) (not b))");
    let n_nb = proof.add_inference("resolution", vec![n_a, n_c], "(not b)");
    proof.add_inference("resolution", vec![n_b, n_nb], "false");

    let mut extractor = InterpolantExtractor::new(partition, tracker);
    let interp = extractor.extract(&proof).expect("should interpolate");
    validate_interpolant(&interp.formula, &["a", "b"], &["(or (not a) (not b))"]);
}

/// Interpolant is a compound disjunction over shared vocabulary, produced via
/// an A-local pivot. A = (a ∨ x) ∧ (b ∨ ¬x), B = ¬a ∧ ¬b. x is A-local;
/// shared vocabulary is {a, b}.
#[test]
fn compound_disjunction_interpolant_alocal_pivot() {
    let mut tracker = PremiseTracker::new();
    let a_1 = tracker.add_assertion("(or a x)");
    let a_2 = tracker.add_assertion("(or b (not x))");
    let b_1 = tracker.add_assertion("(not a)");
    let b_2 = tracker.add_assertion("(not b)");
    let partition = Partition::new(vec![a_1, a_2], vec![b_1, b_2]);

    let mut proof = Proof::new();
    let n1 = proof.add_axiom("(or a x)");
    let n2 = proof.add_axiom("(or b (not x))");
    let n3 = proof.add_axiom("(not a)");
    let n4 = proof.add_axiom("(not b)");
    let r1 = proof.add_inference("resolution", vec![n1, n2], "(or a b)"); // pivot x
    let r2 = proof.add_inference("resolution", vec![r1, n3], "b"); // pivot a
    proof.add_inference("resolution", vec![r2, n4], "false"); // pivot b

    let mut extractor = InterpolantExtractor::new(partition, tracker);
    let interp = extractor.extract(&proof).expect("should interpolate");
    validate_interpolant(
        &interp.formula,
        &["(or a x)", "(or b (not x))"],
        &["(not a)", "(not b)"],
    );
}

/// A-only refutation: every input clause is on the A side (A alone is unsat),
/// so the interpolant is `false`. B is empty (shared vocabulary is empty).
#[test]
fn a_only_refutation_interpolant_false() {
    let mut tracker = PremiseTracker::new();
    let a_p = tracker.add_assertion("p");
    let a_np = tracker.add_assertion("(not p)");
    let partition = Partition::new(vec![a_p, a_np], Vec::new());

    let mut proof = Proof::new();
    let n_p = proof.add_axiom("p");
    let n_np = proof.add_axiom("(not p)");
    proof.add_inference("resolution", vec![n_p, n_np], "false");

    let mut extractor = InterpolantExtractor::new(partition, tracker);
    let interp = extractor.extract(&proof).expect("should interpolate");

    assert_eq!(interp.formula, "false");
    // B is empty; A = p ∧ ¬p.
    validate_interpolant(&interp.formula, &["p", "(not p)"], &[]);
}

/// B-only refutation: every input clause is on the B side (B alone is unsat),
/// so the interpolant is `true`. A is empty (shared vocabulary is empty).
#[test]
fn b_only_refutation_interpolant_true() {
    let mut tracker = PremiseTracker::new();
    let b_p = tracker.add_assertion("p");
    let b_np = tracker.add_assertion("(not p)");
    let partition = Partition::new(Vec::new(), vec![b_p, b_np]);

    let mut proof = Proof::new();
    let n_p = proof.add_axiom("p");
    let n_np = proof.add_axiom("(not p)");
    proof.add_inference("resolution", vec![n_p, n_np], "false");

    let mut extractor = InterpolantExtractor::new(partition, tracker);
    let interp = extractor.extract(&proof).expect("should interpolate");

    assert_eq!(interp.formula, "true");
    // A is empty; B = p ∧ ¬p.
    validate_interpolant(&interp.formula, &[], &["p", "(not p)"]);
}

/// Re-extraction from the same extractor instance must be idempotent (the
/// per-call state is reset), producing a semantically valid interpolant again.
#[test]
fn repeated_extraction_is_stable() {
    let (mut extractor, proof) = build_alocal_shared();
    let first = extractor.extract(&proof).expect("first extraction").formula;
    let second = extractor
        .extract(&proof)
        .expect("second extraction")
        .formula;
    assert_eq!(first, second);
    validate_interpolant(&second, &["p", "(or (not p) q)"], &["(not q)"]);
}

/// A proof that does not derive the empty clause is not a refutation and must
/// be rejected rather than yield a fabricated interpolant.
#[test]
fn non_refutation_is_rejected() {
    let mut tracker = PremiseTracker::new();
    let a_p = tracker.add_assertion("p");
    let b_np = tracker.add_assertion("(not p)");
    let partition = Partition::new(vec![a_p], vec![b_np]);

    let mut proof = Proof::new();
    let n_p = proof.add_axiom("p");
    let n_np = proof.add_axiom("(not p)");
    // Root conclusion is a non-empty clause, not the empty clause.
    proof.add_inference("resolution", vec![n_p, n_np], "(or p (not p))");

    let mut extractor = InterpolantExtractor::new(partition, tracker);
    assert!(extractor.extract(&proof).is_err());
}
