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

/// Run with a bounded wall-clock budget: the set-family goals honestly
/// answer `unknown` only after their full round budget, which is minutes
/// of productive-spin rounds — fine for the solver, too slow for a
/// regression pin (the never-wrong property is verdict-level and does not
/// need the full budget).
fn run_bounded(script: &str, timeout_ms: u64) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(timeout_ms);
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

/// The `set16` corpus shape (reconstructed verbatim; the on-disk corpus
/// is `.gitignore`d external data): ten set-theory axioms over an
/// uninterpreted `Set` sort with a `Real` member index, `a = a ∩ b` and
/// `¬(b ⊆ a)`.  z3 answers `sat`; the honest nixie answer may be `sat`
/// or `unknown` (the else-table search that closes the family is the
/// `smt_model_finder` project).  It must **never** answer `unsat`: the
/// ground layer's own two/three-element models satisfy every axiom the
/// instantiation engines actually emitted.
#[test]
fn set16_family_is_never_wrong() {
    let output = run_bounded(
        r#"
        (set-logic UFLRA)
        (declare-sort Set 0)
        (declare-fun member (Real Set) Bool)
        (declare-fun subset (Set Set) Bool)
        (assert (forall ((?x Real) (?s1 Set) (?s2 Set)) (=> (and (member ?x ?s1) (subset ?s1 ?s2)) (member ?x ?s2))))
        (assert (forall ((?s1 Set) (?s2 Set)) (=> (not (subset ?s1 ?s2)) (exists ((?x Real)) (and (member ?x ?s1) (not (member ?x ?s2)))))))
        (assert (forall ((?s1 Set) (?s2 Set)) (=> (forall ((?x Real)) (=> (member ?x ?s1) (member ?x ?s2))) (subset ?s1 ?s2))))
        (declare-fun seteq (Set Set) Bool)
        (assert (forall ((?s1 Set) (?s2 Set)) (= (seteq ?s1 ?s2) (= ?s1 ?s2))))
        (assert (forall ((?s1 Set) (?s2 Set)) (= (seteq ?s1 ?s2) (and (subset ?s1 ?s2) (subset ?s2 ?s1)))))
        (declare-fun union (Set Set) Set)
        (assert (forall ((?x Real) (?s1 Set) (?s2 Set)) (= (member ?x (union ?s1 ?s2)) (or (member ?x ?s1) (member ?x ?s2)))))
        (declare-fun intersection (Set Set) Set)
        (assert (forall ((?x Real) (?s1 Set) (?s2 Set)) (= (member ?x (intersection ?s1 ?s2)) (and (member ?x ?s1) (member ?x ?s2)))))
        (declare-fun difference (Set Set) Set)
        (assert (forall ((?x Real) (?s1 Set) (?s2 Set)) (= (member ?x (difference ?s1 ?s2)) (and (member ?x ?s1) (not (member ?x ?s2))))))
        (declare-fun a () Set)
        (declare-fun b () Set)
        (assert (= a (intersection a b)))
        (assert (not (subset b a)))
        (check-sat)
    "#,
        8_000,
    );
    let status = last_status(&output);
    assert!(
        status == "sat" || status == "unknown",
        "the set16 family is satisfiable (z3: sat); got {status}"
    );
}

/// The universe-distinctness fold's groundness guard: the completed
/// model's universes contain bound-variable artifact terms (entry args
/// harvested by `collect_universes_from_model`), and folding
/// `(= ?s1 ?s2)` to `false` for symbolic operands fabricates a
/// pointwise-constant body the completion does not justify — on
/// `(or (not (= s1 s2)) (not (seteq s1 s2)))`-shaped bodies it would
/// certify satisfaction of an axiom that fails at every diagonal
/// (`seteq(z,z) = (z=z) = true`, so the disjunct is false there).  z3
/// refutes this goal; the fold must never turn it into `sat`.
#[test]
fn set16_diagonal_diseq_disjunct_is_never_falsely_satisfied() {
    let output = run_bounded(
        r#"
        (set-logic UFLRA)
        (declare-sort Set 0)
        (declare-fun member (Real Set) Bool)
        (declare-fun subset (Set Set) Bool)
        (assert (forall ((?x Real) (?s1 Set) (?s2 Set)) (=> (and (member ?x ?s1) (subset ?s1 ?s2)) (member ?x ?s2))))
        (assert (forall ((?s1 Set) (?s2 Set)) (=> (not (subset ?s1 ?s2)) (exists ((?x Real)) (and (member ?x ?s1) (not (member ?x ?s2)))))))
        (assert (forall ((?s1 Set) (?s2 Set)) (=> (forall ((?x Real)) (=> (member ?x ?s1) (member ?x ?s2))) (subset ?s1 ?s2))))
        (declare-fun seteq (Set Set) Bool)
        (assert (forall ((?s1 Set) (?s2 Set)) (= (seteq ?s1 ?s2) (= ?s1 ?s2))))
        (assert (forall ((?s1 Set) (?s2 Set)) (= (seteq ?s1 ?s2) (and (subset ?s1 ?s2) (subset ?s2 ?s1)))))
        (declare-fun union (Set Set) Set)
        (assert (forall ((?x Real) (?s1 Set) (?s2 Set)) (= (member ?x (union ?s1 ?s2)) (or (member ?x ?s1) (member ?x ?s2)))))
        (declare-fun intersection (Set Set) Set)
        (assert (forall ((?x Real) (?s1 Set) (?s2 Set)) (= (member ?x (intersection ?s1 ?s2)) (and (member ?x ?s1) (member ?x ?s2)))))
        (declare-fun difference (Set Set) Set)
        (assert (forall ((?x Real) (?s1 Set) (?s2 Set)) (= (member ?x (difference ?s1 ?s2)) (and (member ?x ?s1) (not (member ?x ?s2))))))
        (declare-fun a () Set)
        (declare-fun b () Set)
        (assert (= a (intersection a b)))
        (assert (not (subset b a)))
        (assert (forall ((?s1 Set) (?s2 Set)) (or (not (= ?s1 ?s2)) (not (seteq ?s1 ?s2)))))
        (check-sat)
    "#,
        8_000,
    );
    let status = last_status(&output);
    assert!(
        status == "unsat" || status == "unknown",
        "the diagonal disjunct is refuted by the seteq definition (z3: unsat); a fabricated \
         pointwise-true fold must never certify it; got {status}"
    );
}

/// The emission-side binder collapse: an instance of
/// `(forall z. (forall x. P(x) => P(x)) => g(z))` must reach the ground
/// solver with its tautological antecedent folded away — the forcing unit
/// `g(z)` — instead of a wrapper the SAT core can dodge by committing the
/// binder's free Boolean FALSE.  With `(not (g 0))` asserted the goal is
/// refuted exactly by the instance at `z := 0`.
#[test]
fn tautological_antecedent_instance_becomes_a_forcing_unit() {
    let output = run(r#"
        (set-logic UFLRA)
        (declare-fun f (Real) Bool)
        (declare-fun g (Real) Bool)
        (assert (forall ((z Real))
          (=> (forall ((x Real)) (=> (f x) (f x))) (g z))))
        (assert (not (g 0.0)))
        (check-sat)
    "#);
    let status = last_status(&output);
    assert_eq!(
        status, "unsat",
        "the instance at z := 0 must force (g 0) against (not (g 0))"
    );
}

/// The `quant_fuzz` false-`unsat` (2026-09-14, found within 120 generated
/// cases): a tautological-antecedent axiom over two disequal constants,
/// where the falsifier miner's *substituted completed body* bakes in the
/// entry-chain conditions — one of which is the asserted
/// `(not (= c1 c0))`.  The (now removed) blocking-clause emission
/// recorded that disequality as a "commitment" and blocked it, asserting
/// `c1 = c0` against the assertion — instant refutation of a goal whose
/// only models keep the constants distinct (z3: `sat`).  The verdict must
/// never be `unsat`.
#[test]
fn tautological_axiom_over_disequal_constants_is_never_unsat() {
    let output = run(r#"
        (set-logic UFLRA)
        (declare-sort S 0)
        (declare-fun c0 () S)
        (declare-fun c1 () S)
        (declare-fun P (S S) Bool)
        (declare-fun M (Real S) Bool)
        (assert (P c1 c0))
        (assert (forall ((x S) (y S))
          (=> (forall ((z S)) (=> (not (P y y)) (not (P y y)))) (P x y))))
        (assert (not (= c1 c0)))
        (check-sat)
    "#);
    let status = last_status(&output);
    assert!(
        status == "sat" || status == "unknown",
        "the axiom's antecedent is valid, so P is forced everywhere — satisfiable \
         with c0 != c1 (z3: sat); got {status}"
    );
}

/// The strengthened `quant_fuzz` false-`sat` (2026-09-14, seed 42): two
/// definitional axioms that contradict (`P = not (phi => phi)` makes `P`
/// pointwise false; the tautological-antecedent axiom forces `P`
/// everywhere) — z3 refutes; the solver certified `sat` once the
/// ground-universe filter admitted free constants (`2700e3d7`, since
/// reverted).  Root-cause trail (see the study's sixth pass): an
/// artifact variable outside the check's bound set leaked into the
/// completion's entry chains, survived the falsifier substitution, and
/// the mining eval's *empty* bound set made the groundness fold vacuous
/// — the fabrication class the filter admission exposed.  The verdict
/// must never be `sat`.
#[test]
fn contradictory_definitional_twins_are_never_sat() {
    let output = run(r#"
        (set-logic UFLRA)
        (declare-sort S 0)
        (declare-fun c0 () S)
        (declare-fun c1 () S)
        (declare-fun c2 () S)
        (declare-fun P (S S) Bool)
        (declare-fun F (S S) S)
        (declare-fun M (Real S) Bool)
        (assert (forall ((x S) (y S)) (= (P x y) (not (=> (= x y) (= x y))))))
        (assert (forall ((x S) (y S)) (= (P x y) (not (=> (M 1.0 y) false)))))
        (assert (forall ((x S) (y S)) (=> (forall ((z S)) (=> false false)) (P x y))))
        (assert (not (= c2 c0)))
        (check-sat)
    "#);
    let status = last_status(&output);
    assert!(
        status == "unsat" || status == "unknown",
        "the twins contradict (z3: unsat); got {status}"
    );
}

/// The saturation false-`sat` (2026-09-15, quant_fuzz seed 46 with the
/// hint completion enabled): the axiom `(=> (forall ((z S)) true) (P x))`
/// has a *collapsed* nested-quantifier premise that mentions no bound
/// variable, so the fragment certifier's EU walk admitted the body, the
/// round-0 instances were asserted with the raw `forall z. true` wrapper
/// (a free Boolean the SAT core committed FALSE — the dodge), and
/// `sat_certify` saturation later observed "every relevant instance
/// emitted + a ground model" over a set the model only satisfied in its
/// Tseitin encoding.  z3 refutes; the verdict must never be `sat`.
/// Root fix: a body containing any quantifier is not in the certifiable
/// fragment (`sat_certify::universal_instances`).
#[test]
fn nested_quantifier_premise_never_saturates_a_false_sat() {
    let output = run(r#"
        (declare-sort S 0)
        (declare-fun c1 () S)
        (declare-fun P (S) Bool)
        (declare-fun M (Real S) Bool)
        (assert (forall ((x S)) (=> (forall ((z S)) (=> (or true (P x)) (or true (P x)))) (P x))))
        (assert (forall ((x S)) (= (P x) (not (=> (P x) (P x))))))
        (assert (forall ((x S)) (=> (forall ((z S)) (=> false false)) (P x))))
        (check-sat)
    "#);
    let status = last_status(&output);
    assert!(
        status == "unsat" || status == "unknown",
        "P is forced both true (tautological antecedents) and false (its \
         own definition contradicts); z3: unsat; got {status}"
    );
}
