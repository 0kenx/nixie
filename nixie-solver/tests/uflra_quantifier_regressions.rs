//! Regression tests for the UFLRA quantifier parity gap (2026-09, the
//! FFT/set family of `smt-lib/non-incremental/UFLRA`).
//!
//! Two stacked defects kept z3-decidable goals `unknown` here; each is
//! pinned by a test:
//!
//! 1. **Compound linear UF arguments never reached the arithmetic
//!    interface** (`Solver::intern_compound_uf_args_into_arith`): the
//!    assert-time purifier (`purify_numeric_uf_args`) deliberately skips
//!    functions that appear under quantifiers, and the quantifier engines
//!    mint fresh application arguments anyway (every e-matching lemma
//!    `(= (f3 f4 (+ f6 (- f5 f6))) ...)` introduces one).  Without an
//!    arithmetic variable for such an argument, the Nelson-Oppen
//!    model-equal / entailed-equality probe can never pair it with the
//!    equal-valued argument it collapses onto, congruence
//!    `f(.. x ..) = f(.. y ..)` never fires, and a refutable ground
//!    combination is accepted round after round.  The repair internalizes
//!    each such argument with its definitional (tautological) row.
//!
//! 2. **The MBQI universe restriction leaked to sampled sorts** (the
//!    `restrict_to_universe` port in `mbqi::model_checker`): the completed
//!    model's "universe" for an *interpreted* sort is merely a sample of
//!    the model's values, so restricting an Int/Real Skolem to it
//!    fabricated an unsat verdict out of values the Skolem was never
//!    allowed to take — a false `Satisfied` on `2v+1 = y` whose falsifier
//!    sat outside the sample.  Only uninterpreted sorts (genuinely finite
//!    domains, the finite-model semantics) may be restricted; the
//!    ite-chain completion covers the infinite ones.

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

fn last_status(output: &[String]) -> &str {
    output
        .iter()
        .rev()
        .find(|line| {
            let t = line.trim();
            matches!(t, "sat" | "unsat" | "unknown")
        })
        .map(String::as_str)
        .unwrap_or("<no verdict>")
}

/// The FFT shape (`smtlib.620487`): the ground disequality
/// `f3(f4, f5-f6) != -f3(f4, f5)` together with the periodicity axiom
/// `forall v. f3(f4, f6+v) = -f3(f4, v)` is refuted by the single instance
/// `v := f5-f6` — e-matching finds it, and the ground layer needs the
/// arithmetic congruence `f6 + (f5-f6) = f5` to close (defect 1).
#[test]
fn fft_periodicity_is_unsat() {
    let output = run(r#"
        (set-logic UFLRA)
        (declare-sort S2 0)
        (declare-fun f3 (S2 Real) Real)
        (declare-fun f4 () S2)
        (declare-fun f5 () Real)
        (declare-fun f6 () Real)
        (assert (not (= (f3 f4 (- f5 f6)) (- (f3 f4 f5)))))
        (assert (forall ((?v0 Real)) (= (f3 f4 (+ f6 ?v0)) (- (f3 f4 ?v0)))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The same refutation with the instance already spelled out as a ground
/// assertion: the quantifier-under-function purification skip must not
/// leave `(+ f6 (- f5 f6))` outside the arithmetic interface (defect 1's
/// assert-path exposure — was `unknown`, z3 `unsat`).
#[test]
fn spelled_out_instance_is_unsat() {
    let output = run(r#"
        (set-logic UFLRA)
        (declare-sort S2 0)
        (declare-fun f3 (S2 Real) Real)
        (declare-fun f4 () S2)
        (declare-fun f5 () Real)
        (declare-fun f6 () Real)
        (assert (forall ((?v0 Real)) (= (f3 f4 (+ f6 ?v0)) (- (f3 f4 ?v0)))))
        (assert (not (= (f3 f4 (- f5 f6)) (- (f3 f4 f5)))))
        (assert (= (f3 f4 (+ f6 (- f5 f6))) (- (f3 f4 (- f5 f6)))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The ground combination itself: the positive instance refutes, the
/// negated one does not.  Pins that the interface repair adds congruence
/// without flipping the satisfiable twin (defect 1's soundness guard).
#[test]
fn ground_instance_congruence_pair() {
    let unsat_output = run(r#"
        (set-logic QF_UFLRA)
        (declare-sort S2 0)
        (declare-fun f3 (S2 Real) Real)
        (declare-fun f4 () S2)
        (declare-fun f5 () Real)
        (declare-fun f6 () Real)
        (assert (not (= (f3 f4 (- f5 f6)) (- (f3 f4 f5)))))
        (assert (= (f3 f4 (+ f6 (- f5 f6))) (- (f3 f4 (- f5 f6)))))
        (check-sat)
    "#);
    assert_eq!(last_status(&unsat_output), "unsat");

    let sat_output = run(r#"
        (set-logic QF_UFLRA)
        (declare-sort S2 0)
        (declare-fun f3 (S2 Real) Real)
        (declare-fun f4 () S2)
        (declare-fun f5 () Real)
        (declare-fun f6 () Real)
        (assert (not (= (f3 f4 (- f5 f6)) (- (f3 f4 f5)))))
        (assert (not (= (f3 f4 (+ f6 (- f5 f6))) (- (f3 f4 (- f5 f6))))))
        (check-sat)
    "#);
    assert_eq!(last_status(&sat_output), "sat");
}

/// Defect 2's shape: the derived universal of a negated arithmetic
/// existential (`not (exists v. 2v+1 = y)` becomes `forall v. 2v+1 != y`)
/// must not be "certified" by restricting the Int Skolem to the sampled
/// model values.  `y` is pinned odd by the asserted existential, so the
/// falsifier `v := (y-1)/2` exists at a point no finite sample contains;
/// the pre-fix nested check reported `Satisfied` → false `sat`.
#[test]
fn derived_universal_over_int_is_not_falsely_satisfied() {
    let output = run(r#"
        (set-logic LIA)
        (declare-const y Int)
        (assert (exists ((a Int) (b Int) (c Int) (d Int))
          (= (+ (* 2 a) (* 2 b) (* 2 c) (* 2 d) 1) y)))
        (assert (not (exists ((v Int)) (= (+ (* 2 v) 1) y))))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The Rodin shape (AUFLIA, `:status unsat`, minimized from
/// `20170829-Rodin/smt4688353851435564037`): rounds of heavy instantiation
/// leave the goal quantifiers with exhausted budgets or stale tuple
/// evaluations, and the *legacy* finite-exhaustion `Satisfied` then
/// certified a model the completed interpretation demonstrably refutes —
/// a false `sat` that many pre-compile binaries also answer.  The nested
/// checker's second opinion (`check_veto`) now gates that verdict: an
/// aux-`sat` under the finite-universe restriction — a falsifier at a
/// domain point the tuple check missed or mis-evaluated — vetoes it.
/// Pinned: the goal may be decided `unsat` (it is), or honestly `unknown`;
/// never `sat`.
#[test]
fn rodin_goal_quantifiers_are_never_falsely_satisfied() {
    let output = run(r#"
        (set-logic AUFLIA)
        (declare-sort B 0)
        (declare-sort R 0)
        (declare-fun LBT (B) Bool)
        (declare-fun OCC (B) Bool)
        (declare-fun TRK (B B) Bool)
        (declare-fun rdy (R) Bool)
        (declare-fun rtbl (B R) Bool)
        (declare-fun b () B)
        (declare-fun r () R)
        ;; hyp1: a ready route's table rows are unoccupied
        (assert (forall ((r0 R))
          (=> (rdy r0)
              (forall ((x B))
                (not (and (exists ((x0 R)) (and (rtbl x x0) (= x0 r0)))
                          (OCC x)))))))
        (assert (LBT b))
        ;; hyp3: no track from b
        (assert (not (exists ((x1 B)) (TRK b x1))))
        (assert (rdy r))
        ;; goal (negated): some occupied block x2 routes to r, and it is b
        (assert (not (forall ((x2 B))
          (=> (and (exists ((x3 R)) (and (rtbl x2 x3) (= x3 r)))
                   (OCC x2))
              (= x2 b)))))
        (check-sat)
    "#);
    let status = last_status(&output);
    assert!(
        status == "unsat" || status == "unknown",
        "a Rodin goal with :status unsat must never be answered sat; got {status}"
    );
}

/// The A2+A3 alternation shape (the `set16` family's engine, minimized):
/// a witness axiom (`~subset(s1,s2) => exists x. member(x,s1) /\ ~member(x,s2)`)
/// together with the subset-extensionality axiom.  Satisfiable (subset true
/// except the one ground-false pair, with a member witness for it), and the
/// convergence machinery now reaches the target subset table — but the
/// final `Satisfied` is blocked by the assert path's nested-`exists` gap
/// (see the study): an asserted `forall` whose body carries the `exists` in
/// a non-head position is registered unskolemized, so its instances carry
/// an opaque `exists` Boolean and the witness is never forced into the
/// model.  Pinned as never-wrong: `sat` once that gap closes, `unknown`
/// meanwhile — never `unsat` (the spurious-`unsat` shape a first cut of
/// the nested-binder registration produced, by emitting a guarded
/// binder's instances as e-matching units).
#[test]
fn witness_extensionality_alternation_is_never_wrong() {
    let output = run(r#"
        (set-logic UFLRA)
        (declare-sort Set 0)
        (declare-fun member (Real Set) Bool)
        (declare-fun subset (Set Set) Bool)
        (assert (forall ((?s1 Set) (?s2 Set))
          (=> (not (subset ?s1 ?s2))
              (exists ((?x Real)) (and (member ?x ?s1) (not (member ?x ?s2)))))))
        (assert (forall ((?s1 Set) (?s2 Set))
          (=> (forall ((?x Real)) (=> (member ?x ?s1) (member ?x ?s2)))
              (subset ?s1 ?s2))))
        (declare-fun a () Set)
        (declare-fun b () Set)
        (assert (not (subset b a)))
        (check-sat)
    "#);
    let status = last_status(&output);
    assert!(
        status == "sat" || status == "unknown",
        "a satisfiable witness/extensionality pair must never be refuted; got {status}"
    );
}

/// The set-theory sat shape (the `set16` family, minimized): axioms over
/// `Bool`-valued functions on an uninterpreted sort with a `Real` member
/// index.  The completed model with `else = false` satisfies every axiom
/// vacuously off the finitely many entries, and the nested model check can
/// certify that over the whole `Real` domain — but the outer loop's
/// convergence (else-choice search in the finite-model finder) is not yet
/// there, so the goal may honestly answer `unknown`.  What it must never
/// do is answer `unsat`: the two-element model (member always false,
/// subset/seteq only where forced, `seteq a b` false) is exhibited by the
/// solver's own ground layer.  Pinned as never-wrong (the
/// `parity_infeasibility_four_free_vars_is_never_wrong` pattern).
#[test]
fn set_theory_axioms_over_vacuous_membership_are_never_wrong() {
    let output = run(r#"
        (set-logic UFLRA)
        (declare-sort Set 0)
        (declare-fun member (Real Set) Bool)
        (declare-fun seteq (Set Set) Bool)
        (declare-fun subset (Set Set) Bool)
        (assert (forall ((?x Real) (?s1 Set) (?s2 Set))
          (=> (and (member ?x ?s1) (subset ?s1 ?s2)) (member ?x ?s2))))
        (assert (forall ((?s1 Set) (?s2 Set))
          (= (seteq ?s1 ?s2) (and (subset ?s1 ?s2) (subset ?s2 ?s1)))))
        (declare-fun a () Set)
        (declare-fun b () Set)
        (assert (not (seteq a b)))
        (check-sat)
    "#);
    let status = last_status(&output);
    assert!(
        status == "sat" || status == "unknown",
        "a satisfiable set-theory axiom set must never be refuted; got {status}"
    );
}
