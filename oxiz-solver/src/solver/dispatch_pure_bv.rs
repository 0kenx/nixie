//! Eager single-shot solve for pure QF_BV goals.
//!
//! This is the oxiz port of Z3's `qfbv` tactic pipeline (`simplify` →
//! `bit-blast` → `sat`): when *every* assertion lives in the quantifier-free
//! Bool+BV fragment, the whole formula is bit-blasted into the BV solver's
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
//!   assertion set.
//! * `Sat` is only reported after a concrete model built from the embedded
//!   solver's satisfying assignment passes [`Solver::model_refutes_assertions`]
//!   (every assertion evaluates to true under it); otherwise the dispatch
//!   defers to the general path.
//! * Certified mode and proof production keep using the general pipeline (the
//!   dispatch has no LRAT chain for the main solver's clause numbering).

use crate::SolverResult;
use crate::solver::types::Model;
use oxiz_theories::Theory;
use oxiz_theories::TheoryCheckResult;

use oxiz_core::ast::{TermId, TermKind, TermManager};

impl crate::solver::Solver {
    /// Solve a pure QF_BV goal with one eager bit-blast + one SAT run.
    ///
    /// Returns `None` when the goal is outside the fragment (or the dispatch
    /// cannot honestly decide it), signalling the caller to continue with the
    /// general CDCL(T) path.
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

        // Bit-blast every BV sub-term of every assertion at the embedded
        // solver's base scope, so the circuits survive the whole search
        // (see `blast_bv_circuits_at_base_scope` for the scope-invariant
        // rationale). After the rebase the memo is empty, so this is the
        // one full blast.
        let assertions = self.assertions.clone();
        for &assertion in &assertions {
            self.blast_bv_circuits_at_base_scope(assertion, manager);
        }

        // Assert each assertion true, using the direct literal encodings
        // (an equality becomes `assert_eq`'s two clauses per bit, a
        // comparison its cached circuit) instead of building an equivalence
        // circuit and pinning it. A `false` return means the assertion
        // reaches a construct outside the blastable fragment: back out
        // entirely (the constraints already added are level-0 facts about
        // faithfully-encoded assertions and are wiped by the next rebase, so
        // falling through is sound).
        for &assertion in &assertions {
            self.bv.record_constraint_term(assertion);
            if !self.bv.assert_formula_true(assertion, manager) {
                return None;
            }
        }

        match self.bv.check() {
            Ok(TheoryCheckResult::Unsat(_conflict_terms)) => {
                // The conflict terms are the recorded constraint-level
                // assertions – a sound superset of any minimal core.
                self.build_unsat_core();
                Some(SolverResult::Unsat)
            }
            Ok(TheoryCheckResult::Sat) => {
                let model = self.build_pure_bv_model(manager);
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
            // Resource exhaustion (conflict limit): defer to the general
            // path, which enforces the limits itself.
            _ => None,
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
        // Integer/Real-sorted terms present: arithmetic owns those atoms and
        // the CDCL(T) combination is required.
        // (`var_to_parsed_arith` is *not* a pure-BV signal: unsigned BV
        // comparisons are additionally relaxed into the arithmetic solver.)
        if !self.arith_terms.is_empty() {
            return false;
        }
        // Arrays, strings, floating point, datatypes or uninterpreted
        // functions: the blastable-fragment check below would also reject
        // them, but walking is not free, so cheap flags come first.
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
                manager.mk_bitvec(oxiz_core::ast::bv_wrap_unsigned(&raw, width), width);
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

/// Whether `term` stays inside the fragment `BvSolver::encode_bool_node` /
/// `encode_bv_term_recursive` can blast completely.
///
/// This is a conservative syntactic pre-check so the dispatch can decline
/// without polluting the embedded solver; the authoritative refusal still
/// comes from the encoders themselves (`encode_bool_node` returning `None`).
/// Iterative: the check walks children on an explicit stack (shared
/// sub-terms are visited once), so a deeply nested input cannot overflow the
/// native call stack.
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
            | TermKind::BitVecConst { .. } => is_bv,
            // `ite` over BV or Bool branches with a blastable condition.
            TermKind::Ite(_, _, _) => is_bv || is_bool,
            // Everything else (arrays, strings, arithmetic, datatypes,
            // uninterpreted functions, quantifiers, `distinct`, `xor`, ...)
            // is outside the fragment.
            _ => false,
        };
        if !ok {
            return false;
        }
        stack.extend(oxiz_core::ast::traversal::get_children(&term_data.kind));
    }
    true
}
