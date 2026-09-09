//! Eager single-shot solve for pure QF_BV goals.
//!
//! This is the nixie port of Z3's `qfbv` tactic pipeline (`simplify` →
//! `solve-eqs` → `bit-blast` → `sat`): when *every* assertion lives in the
//! quantifier-free Bool+BV fragment, the whole formula is normalized
//! (see [`crate::solver::bv_preprocess`]), bit-blasted into the BV solver's
//! embedded SAT instance up front, each assertion is pinned true, and **one**
//! CDCL run decides the goal.
//!
//! # Why a dedicated dispatch exists
//!
//! The general CDCL(T) architecture treats each BV atom as a free Boolean and
//! lets the theory manager replay atom assignments into the BV solver
//! lazily, re-running the embedded solver once per probe. On pure QF_BV
//! inputs that interaction loop is all cost and no benefit:
//!
//! * the top-level constraint only reaches the bit-blasted circuits after
//!   the outer search has committed a full atom assignment, so the embedded
//!   solver spends its first probes on a *strictly weaker* formula (the
//!   circuits alone), finds spurious models, and the manager then feeds back
//!   thousands of model-value equality clauses per round (`Sage2/bench_3220`:
//!   +26 k clauses and 12 s in the *first* round, with the actual disequality
//!   still unasserted);
//! * every round re-solves a ~100 k-clause instance that the previous round
//!   already proved almost everything about.
//!
//! Z3 solves the same file in 35 ms because the bit-blasted clauses and the
//! assertions live in **one** SAT instance from the start.
//!
//! # Soundness envelope
//!
//! * [`BvSolver::encode_bool_node`] / `encode_bv_term_recursive` either blast
//!   a sub-term completely or refuse it; any refusal makes this dispatch
//!   return `None` and the caller falls back to the general CDCL(T) loop, so
//!   a partially-blasted formula is never decided here.
//! * `Unsat` is a complete SAT refutation of a faithful encoding of the whole
//!   assertion set (the preprocessing pass is equivalence-preserving by
//!   construction).
//! * `Sat` is only reported after a concrete model built from the embedded
//!   solver's satisfying assignment passes [`Solver::model_certifies_assertions`]
//!   (every assertion evaluates to true under it); otherwise the dispatch
//!   defers to the general path.
//! * Certified mode and proof production keep using the general pipeline (the
//!   dispatch has no LRAT chain for the main solver's clause numbering).

use crate::SolverResult;
use crate::solver::types::Model;
use nixie_theories::Theory;
use nixie_theories::TheoryCheckResult;

use nixie_core::ast::{TermId, TermKind, TermManager};

impl crate::solver::Solver {
    /// Solve a pure QF_BV goal with one eager bit-blast + one SAT run.
    ///
    /// Returns `None` when the goal is outside the fragment (or the dispatch
    /// cannot honestly decide it), signalling the caller to continue with
    /// the general CDCL(T) path.
    pub(super) fn dispatch_pure_bv_solve(
        &mut self,
        manager: &mut TermManager,
    ) -> Option<SolverResult> {
        let result = self.dispatch_pure_bv_impl(manager, true);
        if result.is_none() {
            // The dispatch declined a goal some of whose assertions were
            // *deferred* at assert time (the elim-uncnstr deferral bet that
            // the rewrite would remove their circuits).  Pay the bet back:
            // eagerly link/blast the deferred assertions now so the general
            // path keeps exactly the circuits it would have had without the
            // deferral (measured regressions otherwise: deferral false
            // positives flipped solved `sat` goals to `unknown`).
            self.bv_restore_deferred_circuits(manager);
        }
        result
    }

    /// The dispatch body; `allow_elim` gates the elim-uncnstr trial (kept
    /// separate so a rerun keeps every other behavior identical).
    fn dispatch_pure_bv_impl(
        &mut self,
        manager: &mut TermManager,
        allow_elim: bool,
    ) -> Option<SolverResult> {
        if std::env::var("NIXIE_ELIM_UNCNSTR_TRACE").is_ok() {
            eprintln!(
                "[elim-uncnstr] dispatch entered: quant={} wide_mul={} bv_terms={} arith={}",
                self.has_quantifiers,
                self.has_bv_wide_mul,
                self.bv_terms.len(),
                self.arith_terms.len()
            );
        }
        if !self.goal_is_pure_bv(manager) {
            if std::env::var("NIXIE_ELIM_UNCNSTR_TRACE").is_ok() {
                eprintln!("[elim-uncnstr] dispatch declined at fragment gate");
            }
            return None;
        }

        // Stage-4 routing (`bv_dispatch_unified`): pure goals without wide
        // multipliers are owned by the unified general path — unless the
        // unconstrained-variable elimination fires, in which case the
        // eager dispatch takes the goal over (Z3's `qfbv` pipeline runs
        // `elim-uncnstr` after `solve-eqs` and before bit-blasting; goals
        // like `brummayerbiere4/unconstrained*` collapse to free atoms
        // that the general path would otherwise blast at full width).
        // The trial below touches only the term manager, not solver
        // state, so declining leaves the unified path exactly as before.
        //
        // `NIXIE_BV_ELIM_UNCNSTR=0` disables the pass (A/B null arm): the
        // dispatch then keeps its pre-existing behavior for both routes.
        let elim_enabled =
            allow_elim && std::env::var("NIXIE_BV_ELIM_UNCNSTR").as_deref() != Ok("0");
        let mut elim_uncnstr: Option<super::bv_elim_uncnstr::ElimUncnstrOutcome> = None;
        let mut preprocess_run: Option<super::bv_preprocess::PreprocessOutcome> = None;
        if Self::bv_dispatch_unified() && !self.has_bv_wide_mul {
            let pre = self.bv_preprocess_assertions(manager);
            if elim_enabled {
                let outcome =
                    super::bv_elim_uncnstr::elim_uncnstr_assertions(&pre.rewritten, manager);
                if std::env::var("NIXIE_ELIM_UNCNSTR_TRACE").is_ok() {
                    eprintln!(
                        "[elim-uncnstr] fresh_vars={} defs={} assertions={}",
                        outcome.fresh_vars,
                        outcome.defs.len(),
                        outcome.assertions.len()
                    );
                }
                let shrunk = super::bv_elim_uncnstr::dag_nodes(&outcome.assertions, manager)
                    * super::bv_elim_uncnstr::TAKEOVER_SHRINK_DEN
                    <= super::bv_elim_uncnstr::dag_nodes(&pre.rewritten, manager)
                        * super::bv_elim_uncnstr::TAKEOVER_SHRINK_NUM;
                if outcome.fresh_vars == 0 || !shrunk {
                    // Nothing eliminated, or the rewrite does not meaningfully
                    // shrink the goal — diverting a goal its existing route
                    // already solves is a measured regression
                    // (`tacas07/BBB-32` & friends): the unified general path
                    // owns this goal (its stage-4 preprocessing-parity pass
                    // re-runs the preprocessor itself).
                    return None;
                }
                elim_uncnstr = Some(outcome);
            } else {
                // A/B null arm: no elimination, unified routing keeps the
                // goal.
                return None;
            }
            preprocess_run = Some(pre);
        }

        // The dispatch drives the BV solver's *embedded* instance; a unified
        // generation's tables name main-core vars and must not be consumed by
        // it.  End the generation (already-added main-core circuits are
        // definitional and stay sound); the dispatch re-blasts everything it
        // needs into the embedded instance below.
        self.end_bv_unified_generation();

        // Fresh theory state: `rebase_theory_state` drops any residue an
        // earlier check or the assert-time pre-passes left in the embedded
        // solver (branch facts, per-probe learned clauses).
        self.rebase_theory_state();

        // Rewrite every assertion through the BV normalizer (Z3's `qfbv`
        // preamble: solve-eqs + simplify-with-som before bit-blast) —
        // already computed for the routing trial above, so reuse it.
        // Ring identities become syntactic here – `distrib16`-style goals
        // collapse to `true`/`false` with no SAT search, and `X±c`
        // comparisons fold to bounds.  The pass is equivalence-preserving,
        // so the *original* assertions stay the recorded constraint terms
        // (unsat cores keep naming the user's input) and remain the
        // fallback if any rewritten assertion leaves the blastable
        // fragment.
        let super::bv_preprocess::PreprocessOutcome {
            rewritten: preprocessed,
            eliminations,
            origins: preprocessed_origins,
            ..
        } = match preprocess_run {
            Some(pre) => pre,
            None => self.bv_preprocess_assertions(manager),
        };

        // For goals the dispatch already owns (wide-`bvmul` routing or
        // `NIXIE_BV_DISPATCH_UNIFIED=0`), run the elimination as well —
        // Z3's qfbv preamble does so unconditionally, and the wide-mul
        // unconstrained family (`brummayerbiere4/unconstrained04/05`:
        // 1024-bit `bvmul`s around unconstrained operands) is unreachable
        // otherwise.
        if elim_enabled && elim_uncnstr.is_none() {
            let pre_nodes = super::bv_elim_uncnstr::dag_nodes(&preprocessed, manager);
            let outcome = super::bv_elim_uncnstr::elim_uncnstr_assertions(&preprocessed, manager);
            if std::env::var("NIXIE_ELIM_UNCNSTR_TRACE").is_ok() {
                eprintln!(
                    "[elim-uncnstr] fresh_vars={} defs={} assertions={}",
                    outcome.fresh_vars,
                    outcome.defs.len(),
                    outcome.assertions.len()
                );
            }
            let shrunk = super::bv_elim_uncnstr::dag_nodes(&outcome.assertions, manager)
                * super::bv_elim_uncnstr::TAKEOVER_SHRINK_DEN
                <= pre_nodes * super::bv_elim_uncnstr::TAKEOVER_SHRINK_NUM;
            if outcome.fresh_vars > 0 && shrunk {
                elim_uncnstr = Some(outcome);
            }
        }

        // Unconstrained-variable rewrite (Z3 `elim-uncnstr` port — see
        // `bv_elim_uncnstr`): *satisfiability*-preserving, not
        // implication-preserving.  Sound here because this dispatch
        // decides the rewritten set alone: `Unsat` is a refutation of an
        // equisatisfiable rewrite, and `Sat` reconstructs eliminated
        // variables from the recorded definitions and must still certify
        // against the *original* assertions below.  Origins stay the
        // preprocessed ones (the pass never splits or reorders
        // assertions), so unsat cores keep naming the user's input.
        /// The dispatch's working set after preprocessing (+ elimination).
        struct WorkSet {
            assertions: Vec<TermId>,
            origins: Vec<TermId>,
            eliminations: Vec<(TermId, TermId)>,
            complete_free_vars: bool,
        }
        let work_set: WorkSet = if let Some(outcome) = elim_uncnstr
            && outcome
                .assertions
                .iter()
                .all(|&a| term_in_blastable_fragment(a, manager))
        {
            // Definition replay order: the uncnstr defs (dependency
            // order, newest round first) then the solve-eqs definitions —
            // the reconstruction fixpoint absorbs any residual order.
            let mut all_elims = outcome.defs;
            all_elims.extend(eliminations);
            WorkSet {
                assertions: outcome.assertions,
                origins: preprocessed_origins,
                eliminations: all_elims,
                complete_free_vars: true,
            }
        } else {
            let blastable = preprocessed
                .iter()
                .all(|&a| term_in_blastable_fragment(a, manager));
            if blastable {
                WorkSet {
                    assertions: preprocessed,
                    origins: preprocessed_origins,
                    eliminations,
                    complete_free_vars: false,
                }
            } else {
                WorkSet {
                    assertions: self.assertions.clone(),
                    origins: self.assertions.clone(),
                    eliminations: Vec::new(),
                    complete_free_vars: false,
                }
            }
        };

        // Bit-blast every BV sub-term of every assertion at the embedded
        // solver's base scope, so the circuits survive the whole search
        // (see `blast_bv_circuits_at_base_scope` for the scope-invariant
        // rationale). After the rebase the memo is empty, so this is the
        // one full blast.
        //
        // CEGAR (Niemetz/Preiner/Zohar, Scalable Bit-Blasting with
        // Abstractions): while the abstraction width is set, a `bvmul` with
        // non-constant operands at or above it is replaced by fresh result
        // wires + sound identity lemmas instead of its exact circuit (the
        // multiplier is the dominant gate count of a wide blast).  The
        // abstract instance is a RELAXATION (every abstraction clause is a
        // consequence of the exact definition), so its `Unsat` transfers
        // soundly at every stage; its `Sat` is checked against the exact
        // BigUint product and refined (value lemma, then the exact circuit
        // as the guaranteed terminal) below.  Default width 32; disable
        // with NIXIE_BV_CEGAR=0.
        let cegar_min_width = match std::env::var("NIXIE_BV_CEGAR").as_deref() {
            Ok("0") => 0,
            _ => 32,
        };
        // Division threshold: OFF by default — a measured negative.  Both
        // 32 and 64 thresholds A/B'd neutral-to-negative on the only
        // wide-division corpus available (`spear`: geomean 1.079×/1.057×
        // vs exact, solved identical, 0 verdict changes — see the study):
        // the quotient-multiplication circuit is expensive, but the value
        // lemmas rarely converge there and the round tax is real.  The
        // capability ships sound + regression-tested; enable with
        // `NIXIE_BV_CEGAR_DIV=<width>` (64 = abstract width-64 divisions).
        let cegar_div_width = match std::env::var("NIXIE_BV_CEGAR_DIV").ok() {
            Some(v) => v.parse().unwrap_or(0),
            None => 0,
        };
        self.bv.set_mul_abstraction_width(cegar_min_width);
        self.bv.set_div_abstraction_width(cegar_div_width);
        for &assertion in &work_set.assertions {
            self.blast_bv_circuits_at_base_scope(assertion, manager);
        }
        let abstracted = self.bv.take_mul_abstractions();
        self.bv.set_mul_abstraction_width(0);
        self.bv.set_div_abstraction_width(0);
        if std::env::var("NIXIE_BV_CEGAR_TRACE").is_ok() && !abstracted.is_empty() {
            eprintln!("[cegar] abstracted {} wide muls", abstracted.len());
        }

        // Assert each assertion true, using the direct literal encodings
        // (an equality becomes `assert_eq`'s two clauses per bit, a
        // comparison its cached circuit) instead of building an equivalence
        // circuit and pinning it. A `false` return means the assertion
        // reaches a construct outside the blastable fragment: back out
        // entirely (the constraints already added are level-0 facts about
        // faithfully-encoded assertions and are wiped by the next rebase, so
        // falling through is sound).  Guard terms stay the *original*
        // assertions so an unsat core names the user's input even when the
        // blasted form is the normalized one.
        for (&assertion, &original) in work_set.assertions.iter().zip(work_set.origins.iter()) {
            self.bv.record_constraint_term(original);
            if !self.bv.assert_formula_true(assertion, manager) {
                return None;
            }
        }

        // The refinement loop.  `terminal` holds the abstracted muls that
        // have been replaced by their exact circuit; every abstraction is
        // refined at most a few times by cheap value lemmas before the
        // exact circuit lands (guaranteed progress: each terminal blast
        // permanently removes one abstraction, so the loop terminates with
        // a fully exact instance even on adversarial value patterns).
        const CEGAR_MAX_ROUNDS: usize = 50;
        const CEGAR_VALUE_ROUNDS: u32 = 2;
        let mut terminal: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
        let mut value_rounds: rustc_hash::FxHashMap<TermId, u32> = rustc_hash::FxHashMap::default();
        let mut round = 0usize;
        loop {
            match self.bv.check() {
                // Relaxation unsat: every abstraction clause is a logical
                // consequence of the exact `bvmul` definition, so a refuted
                // abstract instance refutes the exact formula.  The
                // conflict terms are the recorded constraint-level
                // assertions – a sound superset of any minimal core.
                Ok(TheoryCheckResult::Unsat(_conflict_terms)) => {
                    self.build_unsat_core();
                    return Some(SolverResult::Unsat);
                }
                Ok(TheoryCheckResult::Sat) => {
                    if abstracted.is_empty() {
                        break;
                    }
                    // Exact product check under the candidate model, per
                    // abstraction (BigUint, no truncation).
                    // (abstraction, operand values) pairs; the default
                    // value pair marks "value unreadable — terminal-refine".
                    let mut spurious: Vec<(
                        nixie_theories::bv::BvAbstraction,
                        Option<(num_bigint::BigUint, num_bigint::BigUint)>,
                    )> = Vec::new();
                    for abs in &abstracted {
                        if terminal.contains(&abs.result) {
                            continue;
                        }
                        let (Some(va), Some(vb), Some(vm)) = (
                            self.bv.get_value_big(abs.a),
                            self.bv.get_value_big(abs.b),
                            self.bv.get_value_big(abs.result),
                        ) else {
                            // Value unreadable: cannot certify, must refine.
                            spurious.push((*abs, None));
                            continue;
                        };
                        if abs.exact_value(&va, &vb) != vm {
                            spurious.push((*abs, Some((va, vb))));
                        }
                    }
                    if spurious.is_empty() {
                        // Every abstracted mul carries its exact product
                        // value in this model: the assignment satisfies the
                        // exact formula's semantics at those subterms.  The
                        // independent whole-assertion validation below is
                        // still the gate that reports `Sat`.
                        break;
                    }
                    round += 1;
                    if std::env::var("NIXIE_BV_CEGAR_TRACE").is_ok() {
                        eprintln!(
                            "[cegar] round {round}: {} spurious ({} terminal so far)",
                            spurious.len(),
                            terminal.len()
                        );
                    }
                    if round > CEGAR_MAX_ROUNDS {
                        // Budget exhausted: terminal-blast every remaining
                        // abstraction; the next check is fully exact, so
                        // either arm of the loop is a final verdict.
                        for abs in &abstracted {
                            if !terminal.contains(&abs.result) {
                                match abs.kind {
                                    nixie_theories::bv::AbstractionKind::Mul => {
                                        self.bv.bv_mul(abs.result, abs.a, abs.b);
                                    }
                                    nixie_theories::bv::AbstractionKind::Udiv => {
                                        self.bv.bv_udiv(abs.result, abs.a, abs.b);
                                    }
                                    nixie_theories::bv::AbstractionKind::Urem => {
                                        self.bv.bv_urem(abs.result, abs.a, abs.b);
                                    }
                                }
                                terminal.insert(abs.result);
                            }
                        }
                        continue;
                    }
                    for (abs, values) in &spurious {
                        let n = value_rounds.entry(abs.result).or_insert(0);
                        *n += 1;
                        match (values, *n > CEGAR_VALUE_ROUNDS) {
                            // Tier 2: value lemma for this spurious assignment.
                            (Some((va, vb)), false) => {
                                self.bv.refine_abstraction_value(abs, va, vb);
                            }
                            // Tier 3: the exact circuit, wired into the
                            // already-abstracted result bits — the
                            // guaranteed terminal refinement (also the path
                            // for unreadable model values).
                            (_, true) | (None, false) => {
                                match abs.kind {
                                    nixie_theories::bv::AbstractionKind::Mul => {
                                        self.bv.bv_mul(abs.result, abs.a, abs.b);
                                    }
                                    nixie_theories::bv::AbstractionKind::Udiv => {
                                        self.bv.bv_udiv(abs.result, abs.a, abs.b);
                                    }
                                    nixie_theories::bv::AbstractionKind::Urem => {
                                        self.bv.bv_urem(abs.result, abs.a, abs.b);
                                    }
                                }
                                terminal.insert(abs.result);
                            }
                        }
                    }
                    continue;
                }
                // Resource exhaustion (conflict limit): defer to the general
                // path, which enforces the limits itself.
                _ => return None,
            }
        }

        {
            let mut model = self.build_pure_bv_model(manager);
            // The unconstrained-elimination rewrite ran: complete every
            // still-unassigned free variable — of the original assertions
            // and of the recorded definitions — with a chosen default
            // (an unconstrained variable's model value is chosen, not
            // searched; the certificate gate below decides whether the
            // completion works).  Variables that carry an elimination
            // *definition* are excluded — defaulting them first would
            // shadow the definition's own value (the reconstruction pass
            // below skips vars the model already assigns, so a wrong
            // default would win and the completed model could contradict
            // the very def chain it is supposed to extend).  Order:
            // default the definition-free leaves, then reconstruct the
            // def chain on top of them.
            if work_set.complete_free_vars {
                Self::bv_complete_free_vars(
                    &mut model,
                    &self.assertions,
                    &work_set.eliminations,
                    manager,
                );
            }
            // Solve-eqs eliminated variables carry no bits, so the
            // satisfying assignment gives them no value; reconstruct
            // each by evaluating its definition under the model (in
            // dependency order) before validating against the original
            // assertions.  Without this, every `sat` instance that had
            // definitions eliminated paid the eager attempt *and* the
            // general path's full re-solve.
            Self::bv_reconstruct_eliminations(&mut model, &work_set.eliminations, manager);
            self.model = Some(model);
            // Certificate gate (see `model_certifies_assertions`): the
            // dispatch is the *sole* decider of this `Sat`, so an assertion
            // it cannot evaluate concretely must decline the verdict – the
            // refutation gate's fail-open on `Undetermined` is what let the
            // ring-elimination bug reach users as a false `sat`.
            if !self.model_certifies_assertions(manager) {
                if std::env::var("NIXIE_ELIM_UNCNSTR_TRACE").is_ok() {
                    let Some(model) = self.model.as_ref() else {
                        eprintln!("[elim-uncnstr] no model at certification");
                        return None;
                    };
                    for &assertion in &self.assertions {
                        let outcome = self.eval_in_model_outcome(assertion, model, manager, 0);
                        eprintln!("[elim-uncnstr] assertion {assertion:?} eval={outcome:?}");
                        if !matches!(outcome, crate::solver::model_eval::EvalOutcome::Value(_)) {
                            // Descend to the deepest declining sub-term.
                            let mut cursor = assertion;
                            for _ in 0..64 {
                                let undet = |t: nixie_core::ast::TermId| {
                                    !matches!(
                                        self.eval_in_model_outcome(t, model, manager, 0),
                                        crate::solver::model_eval::EvalOutcome::Value(_)
                                    )
                                };
                                let Some(td) = manager.get(cursor) else { break };
                                let next = nixie_core::ast::traversal::get_children(&td.kind)
                                    .into_iter()
                                    .find(|&c| undet(c));
                                match next {
                                    Some(child) => cursor = child,
                                    None => break,
                                }
                            }
                            let root_kind = manager
                                .get(assertion)
                                .map(|td| format!("{:?}", td.kind))
                                .unwrap_or_else(|| "?".into());
                            let kind = manager
                                .get(cursor)
                                .map(|td| format!("{:?}", td.kind))
                                .unwrap_or_else(|| "?".into());
                            eprintln!(
                                "[elim-uncnstr]     assertion kind: {root_kind}; deepest declining term {cursor:?}: {kind}"
                            );
                            if let Some(nixie_core::ast::TermKind::Eq(l, r)) =
                                manager.get(assertion).map(|td| td.kind.clone())
                            {
                                let lv = crate::solver::model_eval::eval_bv_value_for_debug(
                                    self, l, model, manager,
                                );
                                let rv = crate::solver::model_eval::eval_bv_value_for_debug(
                                    self, r, model, manager,
                                );
                                let k = |t| {
                                    manager
                                        .get(t)
                                        .map(|td| {
                                            let base = format!("{:?}", td.kind);
                                            if base.len() > 90 {
                                                format!("{}...", &base[..90])
                                            } else {
                                                base
                                            }
                                        })
                                        .unwrap_or_else(|| "?".into())
                                };
                                eprintln!(
                                    "[elim-uncnstr]     eq sides: {l:?}={}={lv:?} {r:?}={}={rv:?}",
                                    k(l),
                                    k(r)
                                );
                            }
                            if matches!(
                                manager.get(cursor).map(|td| &td.kind),
                                Some(nixie_core::ast::TermKind::Var(_))
                            ) {
                                let entry = model.get(cursor).map(|v| {
                                    manager
                                        .get(v)
                                        .map(|td| format!("{:?}", td.kind))
                                        .unwrap_or_else(|| "missing-term".into())
                                });
                                let bits = self.bv.debug_bv_terms().any(|(t, _, _)| t == cursor);
                                eprintln!(
                                    "[elim-uncnstr]     var detail: model={entry:?} has_bits={bits}"
                                );
                            }
                        }
                    }
                    for (&var, &val) in model.assignments().iter() {
                        let ks = |t: TermId| {
                            manager
                                .get(t)
                                .map(|td| format!("{:?}", td.kind))
                                .unwrap_or_else(|| "?".into())
                        };
                        eprintln!(
                            "[elim-uncnstr]   model {var:?} ({}) := {val:?} ({})",
                            ks(var),
                            ks(val)
                        );
                    }
                    eprintln!("[elim-uncnstr] model failed certification; declining");
                }
                // The satisfying assignment does not evaluate to `true`
                // under every assertion: do not trust it. Hand the goal
                // to the general path rather than answer `Unknown`
                // outright, because the fallback may still decide it.
                self.model = None;
                return None;
            }
            Some(SolverResult::Sat)
        }
    }

    /// Whether every assertion is a quantifier-free Bool/BV formula and the
    /// goal is worth an eager blast (it has BV content and no other theory
    /// can own any atom).
    fn goal_is_pure_bv(&self, manager: &TermManager) -> bool {
        if self.has_quantifiers {
            return false;
        }
        // Stage-4 routing (`bv_dispatch_unified`): pure goals without wide
        // multipliers decline the dispatch and solve through the unified
        // main core (the general path's link pass owns their circuits) —
        // with the elim-uncnstr takeover exception decided inside
        // [`Self::dispatch_pure_bv_solve`] after the trial run.
        // Wide-`bvmul` goals keep the dispatch for its CEGAR machinery, and
        // ring-dominated goals keep their existing general-path routing (the
        // checks below).
        // (The unified/wide-mul routing branch lives in the dispatch entry,
        // which needs a mutable manager for the elimination trial.)
        // No BV content: nothing to blast eagerly; the plain Boolean path in
        // `check_core` handles it.
        if self.bv_terms.is_empty() {
            return false;
        }
        // Word-level arith routing (Z3-`qfbv`-vs-CDCL(T) port): the general
        // path additionally *relaxes* unsigned BV comparisons into the
        // linear arithmetic solver (`track_theory_vars` interns the compared
        // operands as bounded integers), which is a genuinely different
        // decision procedure – and for arith-dominated formulas the better
        // one: `Sage2/bench_7140` (489 `bvadd`, 72 comparisons) solves in
        // 16 ms through the relaxation but needs >0.5 s of bit-blasting.
        // Bitwise-dominated formulas with comparisons (`stp_samples`:
        // ~1100 bitwise ops, 70 `bvult`) are the opposite – the eager blast
        // is 5× faster there – so the route follows the *shape*:
        // comparison-relaxed AND ring-dominated (adds/subs/muls at least half
        // of the BV operation nodes) goes to the general path; everything
        // else stays eager.  (Int/Real-sorted terms are rejected by the
        // fragment walk below regardless.)
        if !self.arith_terms.is_empty() && assertions_ring_dominated(&self.assertions, manager) {
            return false;
        }
        if self.has_array_ops
            || !self.array_select_terms.is_empty()
            || !self.array_store_terms.is_empty()
        {
            return false;
        }
        // Certified mode / proof production use the general pipeline (see the
        // module docs).
        if self.config.certification_mode == crate::solver::CertificationMode::Certified {
            return false;
        }
        if self.proof.is_some() {
            return false;
        }
        self.assertions
            .iter()
            .all(|&assertion| term_in_blastable_fragment(assertion, manager))
    }

    /// Build a concrete [`Model`] from the embedded solver's satisfying
    /// assignment: one value per bit-blasted term (fully determined ones
    /// only) plus one value per encoded Bool term.
    fn build_pure_bv_model(&self, manager: &mut TermManager) -> Model {
        let mut model = Model::new();
        for (term, value) in self.bv.model_bv_values() {
            let width = Self::term_width(term, manager).unwrap_or(u64::BITS);
            let raw = num_bigint::BigInt::from(value);
            let value_term =
                manager.mk_bitvec(nixie_core::ast::bv_wrap_unsigned(&raw, width), width);
            model.set(term, value_term);
        }
        for (term, value) in self.bv.model_bool_values() {
            model.set(term, manager.mk_bool(value));
        }
        model
    }

    /// Declared bit-width of `term`, or `None` when it is not bit-vector
    /// sorted.
    fn term_width(term: TermId, manager: &TermManager) -> Option<u32> {
        let td = manager.get(term)?;
        manager.sorts.get(td.sort)?.bitvec_width()
    }

    /// Complete a `sat` model with default values for every **definition-free**
    /// free variable (of the original assertions and of the recorded
    /// elimination definitions) that the satisfying assignment left
    /// unassigned.
    ///
    /// The unconstrained-elimination rewrite can drop whole sub-DAGs from
    /// the blasted set (their circuits are never built), so variables the
    /// *original* assertions mention may have no bits to read.  Their
    /// values are **chosen** (`0` / `false`), not searched — sound because
    /// the dispatch's `Sat` is only ever reported after the completed
    /// model certifies every original assertion
    /// (`model_certifies_assertions`); a completion that does not satisfy
    /// the originals declines the verdict instead of fabricating one.
    ///
    /// Variables with an elimination definition are deliberately *not*
    /// defaulted here: `bv_reconstruct_eliminations` skips vars the model
    /// already assigns, so a default would shadow the definition and could
    /// contradict it (measured as a failed certification on
    /// `brummayerbiere4/unconstrained03`, where a defaulted `u6 := 0`
    /// overrode `u6 := ~u9`).
    fn bv_complete_free_vars(
        model: &mut crate::solver::types::Model,
        assertions: &[TermId],
        eliminations: &[(TermId, TermId)],
        manager: &mut TermManager,
    ) {
        use nixie_core::ast::TermKind;
        let defined: rustc_hash::FxHashSet<TermId> =
            eliminations.iter().map(|&(var, _)| var).collect();
        // Iterative walk (stack-safety rule) collecting every free
        // variable of the roots.
        let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
        let mut stack: Vec<TermId> = assertions.to_vec();
        stack.extend(eliminations.iter().map(|&(_, def)| def));
        let mut vars: Vec<TermId> = Vec::new();
        while let Some(tid) = stack.pop() {
            if !seen.insert(tid) {
                continue;
            }
            let Some(data) = manager.get(tid) else {
                continue;
            };
            if let TermKind::Var(_) = data.kind {
                vars.push(tid);
                continue;
            }
            stack.extend(nixie_core::ast::traversal::get_children(&data.kind));
        }
        for v in vars {
            if model.get(v).is_some() || defined.contains(&v) {
                continue;
            }
            let Some(data) = manager.get(v) else {
                continue;
            };
            let sort_data = manager.sorts.get(data.sort);
            if sort_data.is_some_and(|s| s.is_bool()) {
                model.set(v, manager.mk_false());
            } else if let Some(width) = sort_data.and_then(|s| s.bitvec_width()) {
                model.set(v, manager.mk_bitvec(0u32, width));
            }
            // Other sorts have no default here: the variable stays
            // unassigned and certification declines rather than guess.
        }
    }
}

/// Whether `bvadd`/`bvsub`/`bvmul` nodes make up at least half of the
/// bit-vector operation nodes across the assertions (shared subterms visited
/// once; iterative walk).
///
/// The eager/general routing above uses this as its shape signal: a
/// ring-dominated formula leans on adder/multiplier circuits the word-level
/// arithmetic relaxation reasons about natively, while a bitwise-dominated
/// one is exactly what bit-blasting digests best.
fn assertions_ring_dominated(assertions: &[TermId], manager: &TermManager) -> bool {
    let mut visited = rustc_hash::FxHashSet::default();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut ring = 0usize;
    let mut total = 0usize;
    while let Some(tid) = stack.pop() {
        if !visited.insert(tid) {
            continue;
        }
        let Some(term) = manager.get(tid) else {
            continue;
        };
        let is_ring = matches!(
            term.kind,
            TermKind::BvAdd(_, _) | TermKind::BvSub(_, _) | TermKind::BvMul(_, _)
        );
        let is_bv_op = is_ring
            || matches!(
                term.kind,
                TermKind::BvAnd(_, _)
                    | TermKind::BvOr(_, _)
                    | TermKind::BvXor(_, _)
                    | TermKind::BvNot(_)
                    | TermKind::BvUdiv(_, _)
                    | TermKind::BvSdiv(_, _)
                    | TermKind::BvUrem(_, _)
                    | TermKind::BvSrem(_, _)
                    | TermKind::BvShl(_, _)
                    | TermKind::BvLshr(_, _)
                    | TermKind::BvAshr(_, _)
                    | TermKind::BvConcat(_, _)
                    | TermKind::BvExtract { .. }
            );
        if is_bv_op {
            total += 1;
            if is_ring {
                ring += 1;
            }
            stack.extend(nixie_core::ast::traversal::get_children(&term.kind));
        } else {
            // Non-BV nodes can still carry BV subterms (Bool connectives over
            // BV atoms); keep walking.
            stack.extend(nixie_core::ast::traversal::get_children(&term.kind));
        }
    }
    total > 0 && ring * 2 >= total
}

/// Whether `term` stays inside the fragment `BvSolver::encode_bool_node` /
/// `encode_bv_term_recursive` can blast completely.
///
/// This is a conservative syntactic pre-check so the dispatch can decline
/// without polluting the embedded solver; the authoritative refusal still
/// comes from the encoders themselves (`encode_bool_node` returning `None`).
/// Iterative: the check walks children on an explicit stack (shared
/// sub-terms are visited once), so a deeply nested input cannot overflow
/// the native call stack.
/// Whether `term` lies in the blastable Bool+BV fragment (the dispatch's
/// per-assertion eligibility).  Exposed for the unified-blasting router
/// (`bv_unified::link_or_blast_bv_circuits`): while *every* assertion is in
/// the fragment, the eager dispatch owns the goal and unified linking stays
/// off.
pub(super) fn assertion_in_bv_fragment(term: TermId, manager: &TermManager) -> bool {
    term_in_blastable_fragment(term, manager)
}

fn term_in_blastable_fragment(term: TermId, manager: &TermManager) -> bool {
    // Bound the total work: the walk visits each distinct sub-term once, so
    // this is a defence against pathologically large inputs rather than a
    // depth limit. Hash-consed inputs are far below it in practice.
    const MAX_VISITED: usize = 2_000_000;

    let mut stack = vec![term];
    let mut visited = rustc_hash::FxHashSet::default();
    while let Some(tid) = stack.pop() {
        if !visited.insert(tid) {
            continue;
        }
        if visited.len() > MAX_VISITED {
            return false;
        }
        let Some(term_data) = manager.get(tid) else {
            return false;
        };
        let sort_data = manager.sorts.get(term_data.sort);
        let is_bool = sort_data.is_some_and(|s| s.is_bool());
        let is_bv = sort_data.is_some_and(|s| s.is_bitvec());
        let ok = match &term_data.kind {
            // Bool leaves.
            TermKind::True | TermKind::False => true,
            TermKind::Var(_) => is_bool || is_bv,
            // Boolean connectives.
            TermKind::Not(_) | TermKind::And(_) | TermKind::Or(_) => is_bool,
            // Boolean XOR / implication / distinct and Bool-sorted `ite`/
            // `=`: `encode_bool_node` lowers each through the same gate
            // primitives (these are common in `bmc-bv-svcomp14` and
            // `2018-Mann` inputs; without them whole families fell out of
            // the eager dispatch and into the slow lazy CDCL(T) loop).
            TermKind::Xor(_, _) | TermKind::Implies(_, _) => is_bool,
            TermKind::Distinct(_) => is_bool,
            // BV (dis)equalities and comparisons.
            TermKind::Eq(_, _)
            | TermKind::BvUlt(_, _)
            | TermKind::BvUle(_, _)
            | TermKind::BvSlt(_, _)
            | TermKind::BvSle(_, _) => is_bool,
            // BV-sorted operations and constants: exactly the set
            // `encode_bv_term_recursive` encodes.
            TermKind::BvAdd(_, _)
            | TermKind::BvMul(_, _)
            | TermKind::BvSub(_, _)
            | TermKind::BvAnd(_, _)
            | TermKind::BvOr(_, _)
            | TermKind::BvXor(_, _)
            | TermKind::BvUdiv(_, _)
            | TermKind::BvSdiv(_, _)
            | TermKind::BvUrem(_, _)
            | TermKind::BvSrem(_, _)
            | TermKind::BvShl(_, _)
            | TermKind::BvLshr(_, _)
            | TermKind::BvAshr(_, _)
            | TermKind::BvConcat(_, _)
            | TermKind::BvExtract { .. }
            | TermKind::BvNot(_)
            | TermKind::BitVecConst { .. } => is_bv,
            // `ite` over BV or Bool branches with a blastable condition.
            TermKind::Ite(_, _, _) => is_bv || is_bool,
            // Everything else (arrays, strings, arithmetic, datatypes,
            // uninterpreted functions, quantifiers, ...) is outside the
            // fragment.
            _ => false,
        };
        if !ok {
            return false;
        }
        stack.extend(nixie_core::ast::traversal::get_children(&term_data.kind));
    }
    true
}
