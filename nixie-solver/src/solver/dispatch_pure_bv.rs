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
//!   solver's satisfying assignment passes [`Solver::model_refutes_assertions`]
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
        if !self.goal_is_pure_bv(manager) {
            return None;
        }

        // Fresh theory state: `rebase_theory_state` drops any residue an
        // earlier check or the assert-time pre-passes left in the embedded
        // solver (branch facts, per-probe learned clauses).
        self.rebase_theory_state();

        // Rewrite every assertion through the BV normalizer (Z3's `qfbv`
        // preamble: solve-eqs + simplify-with-som before bit-blast).  Ring
        // identities become syntactic here – `distrib16`-style goals collapse
        // to `true`/`false` with no SAT search, and `X±c` comparisons fold to
        // bounds.  The pass is equivalence-preserving, so the *original*
        // assertions stay the recorded constraint terms (unsat cores keep
        // naming the user's input) and remain the fallback if any rewritten
        // assertion leaves the blastable fragment.
        let (preprocessed, eliminations, preprocessed_origins) =
            self.bv_preprocess_assertions(manager);
        let blastable = preprocessed
            .iter()
            .all(|&a| term_in_blastable_fragment(a, manager));
        let (assertions, origins, eliminations): (Vec<TermId>, Vec<TermId>, Vec<(TermId, TermId)>) =
            if blastable {
                (preprocessed, preprocessed_origins, eliminations)
            } else {
                (self.assertions.clone(), self.assertions.clone(), Vec::new())
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
        for &assertion in &assertions {
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
        for (&assertion, &original) in assertions.iter().zip(origins.iter()) {
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
            // Solve-eqs eliminated variables carry no bits, so the
            // satisfying assignment gives them no value; reconstruct
            // each by evaluating its definition under the model (in
            // dependency order) before validating against the original
            // assertions.  Without this, every `sat` instance that had
            // definitions eliminated paid the eager attempt *and* the
            // general path's full re-solve.
            Self::bv_reconstruct_eliminations(&mut model, &eliminations, manager);
            self.model = Some(model);
            if self.model_refutes_assertions(manager) {
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
