//! Interpolation utilities for Spacer.
//!
//! Craig interpolation is used to compute over-approximations of reachable states
//! and to learn inductive invariants.
//!
//! Given formulas A and B such that A ∧ B is unsatisfiable, an interpolant I satisfies:
//! - A implies I
//! - I ∧ B is unsatisfiable
//! - I only contains symbols common to both A and B
//!
//! Reference: Z3's `muz/spacer/spacer_iuc.h` and `spacer_interpolant.h`

use crate::chc::PredId;
use crate::generalize::Generalizer;
use nixie_core::{TermId, TermManager};
use smallvec::SmallVec;
use std::collections::HashSet;
use thiserror::Error;

/// Errors that can occur during interpolation
#[derive(Error, Debug)]
pub enum InterpolationError {
    /// The formula is not unsatisfiable
    #[error("formula is satisfiable, cannot interpolate")]
    Satisfiable,
    /// No common symbols between A and B
    #[error("no common symbols between formulas")]
    NoCommonSymbols,
    /// Interpolation not supported for this formula type
    #[error("interpolation not supported: {0}")]
    Unsupported(String),
    /// Internal error
    #[error("internal error: {0}")]
    Internal(String),
}

/// Result of interpolation
pub type InterpolationResult = Result<Interpolant, InterpolationError>;

/// An interpolant computed from an UNSAT proof
#[derive(Debug, Clone)]
pub struct Interpolant {
    /// The interpolant formula
    pub formula: TermId,
    /// Variables in the interpolant
    pub vars: SmallVec<[TermId; 4]>,
    /// Strength metric (smaller is weaker, larger is stronger)
    pub strength: u32,
}

impl Interpolant {
    /// Create a new interpolant
    pub fn new(formula: TermId) -> Self {
        Self {
            formula,
            vars: SmallVec::new(),
            strength: 0,
        }
    }

    /// Create an interpolant with variables
    pub fn with_vars(formula: TermId, vars: impl IntoIterator<Item = TermId>) -> Self {
        Self {
            formula,
            vars: vars.into_iter().collect(),
            strength: 0,
        }
    }

    /// Set the strength metric
    pub fn with_strength(mut self, strength: u32) -> Self {
        self.strength = strength;
        self
    }
}

/// Interpolation context for a predicate
#[derive(Debug)]
pub struct InterpolationContext {
    /// The predicate this context is for
    pred: PredId,
    /// Cached interpolants
    cache: Vec<Interpolant>,
}

impl InterpolationContext {
    /// Create a new interpolation context
    pub fn new(pred: PredId) -> Self {
        Self {
            pred,
            cache: Vec::new(),
        }
    }

    /// Get the predicate
    #[must_use]
    pub fn pred(&self) -> PredId {
        self.pred
    }

    /// Add an interpolant to the cache
    pub fn cache_interpolant(&mut self, interp: Interpolant) {
        self.cache.push(interp);
    }

    /// Get all cached interpolants
    pub fn cached_interpolants(&self) -> &[Interpolant] {
        &self.cache
    }

    /// Clear the cache
    pub fn clear_cache(&mut self) {
        self.cache.clear();
    }
}

/// Interpolation manager
#[derive(Debug)]
pub struct Interpolator {
    /// Interpolation contexts per predicate
    contexts: rustc_hash::FxHashMap<PredId, InterpolationContext>,
}

impl Default for Interpolator {
    fn default() -> Self {
        Self::new()
    }
}

impl Interpolator {
    /// Create a new interpolator
    pub fn new() -> Self {
        Self {
            contexts: rustc_hash::FxHashMap::default(),
        }
    }

    /// Get or create an interpolation context for a predicate
    pub fn context(&mut self, pred: PredId) -> &mut InterpolationContext {
        self.contexts
            .entry(pred)
            .or_insert_with(|| InterpolationContext::new(pred))
    }

    /// Compute a **validated** Craig interpolant for `A ∧ B` (which the caller
    /// must have established is UNSAT).
    ///
    /// A Craig interpolant `I` must satisfy all three of:
    /// 1. `A ⇒ I`,
    /// 2. `I ∧ B` is UNSAT, and
    /// 3. `I` mentions only symbols common to `A` and `B`.
    ///
    /// This restricts to the sound *shared-literal fragment*: the candidate is
    /// the sub-conjunction of `A`'s literals whose variables are all shared with
    /// `B`. That construction makes (1) and (3) hold by construction, but *not*
    /// (2) – a projection can share symbols yet fail to contradict `B`. So we
    /// **verify** property (2) (and defensively re-verify (1)) with the solver
    /// before returning, and **fail closed** to an honest
    /// [`InterpolationError`] otherwise. We never return an unvalidated
    /// projection as if it were a Craig interpolant.
    ///
    /// Reference: Z3's `muz/spacer/spacer_iuc.h` (interpolant validity).
    pub fn interpolate(
        &mut self,
        terms: &mut TermManager,
        a: TermId,
        b: TermId,
    ) -> InterpolationResult {
        use nixie_core::TermKind;

        // Symbols shared between A and B.
        let vars_a = Self::collect_vars(terms, a);
        let vars_b = Self::collect_vars(terms, b);
        let common: HashSet<TermId> = vars_a
            .iter()
            .filter(|v| vars_b.contains(v))
            .copied()
            .collect();

        // Candidate: the sub-conjunction of A whose literals mention only shared
        // symbols. This guarantees A ⇒ I (I is a weakening of A) and
        // vars(I) ⊆ vars(A) ∩ vars(B).
        let a_cube = Generalizer::extract_cube(terms, a);
        let shared_lits: Vec<TermId> = a_cube
            .into_iter()
            .filter(|&lit| {
                let lit_vars = Self::collect_vars(terms, lit);
                !lit_vars.is_empty() && lit_vars.iter().all(|v| common.contains(v))
            })
            .collect();

        let candidate = match shared_lits.len() {
            0 => terms.mk_true(),
            1 => shared_lits[0],
            _ => terms.mk_and(shared_lits.iter().copied()),
        };

        // Property (2): I ∧ B must be UNSAT. This is the property the projection
        // does NOT guarantee, so it is validated against the solver. Fail closed
        // if the solver cannot prove it (UNSAT-or-nothing).
        if !Self::is_unsat(terms, &[candidate, b]) {
            return Err(InterpolationError::Unsupported(
                "no Craig interpolant derivable in the shared-literal fragment".to_string(),
            ));
        }

        // Property (1): A ⇒ I, i.e. A ∧ ¬I UNSAT. Holds by construction, but
        // re-verify so a surprising simplification can never yield an
        // interpolant that A does not actually imply.
        let not_candidate = terms.mk_not(candidate);
        if !Self::is_unsat(terms, &[a, not_candidate]) {
            return Err(InterpolationError::Unsupported(
                "candidate interpolant is not implied by A".to_string(),
            ));
        }

        let common_vars: Vec<TermId> = common.into_iter().collect();
        let strength = match terms.get(candidate) {
            Some(term) => match &term.kind {
                TermKind::And(args) => args.len() as u32,
                _ => 1,
            },
            None => 0,
        };

        Ok(Interpolant::with_vars(candidate, common_vars).with_strength(strength))
    }

    /// Return `true` iff the conjunction of `formulas` is UNSAT according to the
    /// solver. Anything other than a definite UNSAT (SAT, or the solver
    /// returning unknown) yields `false`, so interpolant validation fails
    /// closed rather than trusting an unproven claim.
    fn is_unsat(terms: &mut TermManager, formulas: &[TermId]) -> bool {
        use nixie_solver::{Solver, SolverResult};

        // Assert each top-level `And` conjunct separately (mirrors
        // `SmtSolver::assert`): a single `And` carrying disequalities can be
        // mis-answered SAT by the backend, which would unsoundly weaken the
        // validation guard.
        // `And`-nesting comes from parsed input and is unbounded, so the
        // flattening is an explicit-stack walk (`crate::walk`), not
        // recursion.
        let mut solver = Solver::new();
        for &formula in formulas {
            for conjunct in crate::walk::flatten_conjuncts(terms, formula) {
                solver.assert(conjunct, terms);
            }
        }
        matches!(solver.check(terms), SolverResult::Unsat)
    }

    /// Collect all variables in a formula.
    ///
    /// Iterative walk with a visited set (see [`crate::walk`]). The old
    /// recursive helper threaded a `HashSet` that was the *output* set, not
    /// a visited set, so it never pruned traversal: a shared DAG was
    /// re-expanded once per path. It also had no depth bound, and its
    /// `_ => {}` arm silently skipped variables under any operator outside a
    /// short enumeration, which understated the "common variables" set an
    /// interpolant is required to be built from.
    fn collect_vars(terms: &TermManager, formula: TermId) -> Vec<TermId> {
        crate::walk::collect_vars(terms, formula)
    }

    /// Compute a sequence interpolant for a trace
    ///
    /// Given a trace A₀ ∧ A₁ ∧ ... ∧ Aₙ that is UNSAT,
    /// compute interpolants I₁, I₂, ..., Iₙ such that:
    /// - A₀ implies I₁
    /// - Aᵢ ∧ Iᵢ implies Iᵢ₊₁ for all i
    /// - Iₙ ∧ Aₙ is UNSAT
    pub fn sequence_interpolate(
        &mut self,
        terms: &mut TermManager,
        trace: &[TermId],
    ) -> Result<Vec<Interpolant>, InterpolationError> {
        if trace.is_empty() {
            return Err(InterpolationError::Internal("empty trace".to_string()));
        }

        let mut interpolants = Vec::new();

        // For each position in the trace, compute an interpolant
        for i in 1..trace.len() {
            // A is the prefix: A₀ ∧ ... ∧ Aᵢ₋₁
            let a = if i == 1 {
                trace[0]
            } else {
                terms.mk_and(trace[0..i].iter().copied())
            };

            // B is the suffix: Aᵢ ∧ ... ∧ Aₙ
            let b = if i == trace.len() - 1 {
                trace[i]
            } else {
                terms.mk_and(trace[i..].iter().copied())
            };

            // Compute interpolant
            let interp = self.interpolate(terms, a, b)?;
            interpolants.push(interp);
        }

        Ok(interpolants)
    }

    /// Strengthen an interpolant using counterexample
    pub fn strengthen_interpolant(
        &mut self,
        terms: &mut TermManager,
        interp: Interpolant,
        counterexample: TermId,
    ) -> Interpolant {
        // Strengthen the interpolant by adding constraints from the counterexample
        // This is similar to CTG (Counterexample-Guided strengthening)

        use nixie_core::TermKind;

        // Extract literals from the counterexample that involve variables in the interpolant
        let cex_cube = crate::generalize::Generalizer::extract_cube(terms, counterexample);

        // Filter to only constraints involving interpolant variables
        let relevant_lits: Vec<TermId> = cex_cube
            .into_iter()
            .filter(|&lit| {
                let lit_vars = Self::collect_vars(terms, lit);
                lit_vars.iter().any(|v| interp.vars.contains(v))
            })
            .collect();

        if relevant_lits.is_empty() {
            // No relevant constraints to add
            return interp;
        }

        // Conjoin relevant constraints with the interpolant
        let mut all_constraints = vec![interp.formula];
        all_constraints.extend(relevant_lits);

        let strengthened = if all_constraints.len() == 1 {
            all_constraints[0]
        } else {
            terms.mk_and(all_constraints)
        };

        // Update strength metric
        let new_strength = match terms.get(strengthened) {
            Some(term) => match &term.kind {
                TermKind::And(args) => args.len() as u32,
                _ => 1,
            },
            None => 0,
        };

        Interpolant::with_vars(strengthened, interp.vars).with_strength(new_strength)
    }

    /// Weaken an interpolant to make it more general
    pub fn weaken_interpolant(
        &mut self,
        terms: &mut TermManager,
        interp: Interpolant,
    ) -> Interpolant {
        // Weaken the interpolant by removing literals
        // This is similar to MIC (Minimal Inductive Core)

        use nixie_core::TermKind;

        // Extract cube from interpolant
        let cube = crate::generalize::Generalizer::extract_cube(terms, interp.formula);

        if cube.len() <= 1 {
            // Already minimal
            return interp;
        }

        // Try to remove some literals (simple heuristic: remove half)
        // A full implementation would use SMT queries to check if weakening is valid
        let keep_count = cube.len().div_ceil(2);
        let weakened_cube: Vec<TermId> = cube.into_iter().take(keep_count).collect();

        let weakened = if weakened_cube.is_empty() {
            terms.mk_true()
        } else if weakened_cube.len() == 1 {
            weakened_cube[0]
        } else {
            terms.mk_and(weakened_cube)
        };

        let new_strength = match terms.get(weakened) {
            Some(term) => match &term.kind {
                TermKind::And(args) => args.len() as u32,
                _ => 1,
            },
            None => 0,
        };

        Interpolant::with_vars(weakened, interp.vars).with_strength(new_strength)
    }

    /// Clear all cached interpolants
    pub fn clear(&mut self) {
        self.contexts.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chc::PredId;
    use nixie_core::TermManager;

    #[test]
    fn test_interpolant_creation() {
        let mut terms = TermManager::new();
        let formula = terms.mk_var("p", terms.sorts.bool_sort);

        let interp = Interpolant::new(formula);
        assert_eq!(interp.formula, formula);
        assert_eq!(interp.vars.len(), 0);
        assert_eq!(interp.strength, 0);
    }

    #[test]
    fn test_interpolant_with_vars() {
        let mut terms = TermManager::new();
        let x = terms.mk_var("x", terms.sorts.int_sort);
        let formula = terms.mk_var("p", terms.sorts.bool_sort);

        let interp = Interpolant::with_vars(formula, [x]);
        assert_eq!(interp.formula, formula);
        assert_eq!(interp.vars.len(), 1);
        assert_eq!(interp.vars[0], x);
    }

    #[test]
    fn test_interpolation_context() {
        let pred = PredId::new(0);
        let mut ctx = InterpolationContext::new(pred);

        assert_eq!(ctx.pred(), pred);
        assert_eq!(ctx.cached_interpolants().len(), 0);

        let mut terms = TermManager::new();
        let formula = terms.mk_var("p", terms.sorts.bool_sort);
        let interp = Interpolant::new(formula);

        ctx.cache_interpolant(interp);
        assert_eq!(ctx.cached_interpolants().len(), 1);

        ctx.clear_cache();
        assert_eq!(ctx.cached_interpolants().len(), 0);
    }

    #[test]
    fn test_interpolator() {
        let mut interpolator = Interpolator::new();
        let pred = PredId::new(0);

        let ctx = interpolator.context(pred);
        assert_eq!(ctx.pred(), pred);
    }

    #[test]
    fn test_basic_interpolation() {
        // A = (x >= 5), B = (x <= 3): A ∧ B is UNSAT over the shared symbol x.
        // The validated Craig interpolant is A's shared literal (x >= 5), which
        // is verified to contradict B before being returned.
        let mut terms = TermManager::new();
        let mut interpolator = Interpolator::new();

        let x = terms.mk_var("x", terms.sorts.int_sort);
        let five = terms.mk_int(5);
        let three = terms.mk_int(3);
        let a = terms.mk_ge(x, five);
        let b = terms.mk_le(x, three);

        let result = interpolator.interpolate(&mut terms, a, b);
        let interp = result.expect("a valid interpolant exists for x>=5 / x<=3");
        assert_eq!(
            interp.formula, a,
            "the shared literal x>=5 is the interpolant"
        );
    }

    #[test]
    fn test_interpolation_fails_closed_without_contradiction() {
        // Two independent boolean variables: A ∧ B is satisfiable, so there is
        // no Craig interpolant. The validated interpolator must fail closed
        // instead of returning an unvalidated projection.
        let mut terms = TermManager::new();
        let mut interpolator = Interpolator::new();

        let a = terms.mk_var("a", terms.sorts.bool_sort);
        let b = terms.mk_var("b", terms.sorts.bool_sort);

        let result = interpolator.interpolate(&mut terms, a, b);
        assert!(
            result.is_err(),
            "no interpolant exists when A ∧ B is satisfiable; must not fabricate one"
        );
    }

    #[test]
    fn test_sequence_interpolation() {
        // An UNSAT trace over the shared symbol x: x>=5, x<=3, x>=0. Every
        // prefix/suffix split is UNSAT, so each position yields a validated
        // interpolant.
        let mut terms = TermManager::new();
        let mut interpolator = Interpolator::new();

        let x = terms.mk_var("x", terms.sorts.int_sort);
        let five = terms.mk_int(5);
        let three = terms.mk_int(3);
        let zero = terms.mk_int(0);
        let a0 = terms.mk_ge(x, five);
        let a1 = terms.mk_le(x, three);
        let a2 = terms.mk_ge(x, zero);

        let trace = vec![a0, a1, a2];
        let result = interpolator.sequence_interpolate(&mut terms, &trace);
        let interpolants = result.expect("each split of the UNSAT trace interpolates");
        assert_eq!(interpolants.len(), 2);
    }

    #[test]
    fn test_empty_trace() {
        let mut terms = TermManager::new();
        let mut interpolator = Interpolator::new();

        let trace = vec![];
        let result = interpolator.sequence_interpolate(&mut terms, &trace);
        assert!(result.is_err());
    }
}
