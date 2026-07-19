//! Arithmetic Bounds Analysis Tactic.
//!
//! Extracts and propagates bounds on arithmetic variables from asserted
//! comparison literals, using them to detect inconsistencies early and to
//! drop constraints that are provably implied by other constraints.
//!
//! ## Strategy
//!
//! - Extract bounds from literal constraints (`x >= a`, `x <= b`, `x = a`),
//!   recursing through top-level conjunctions.
//! - Detect inconsistent bounds (`lower > upper`) as an early UNSAT.
//! - Drop a top-level comparison assertion when it is provably implied by
//!   the bounds derived from the *surviving* assertions (every other
//!   assertion not already dropped). Excluding already-dropped assertions
//!   prevents two equivalent constraints from mutually justifying each
//!   other's removal, which would drop both and unsoundly widen the goal.
//!
//! Full equation-based propagation (`x = y + c` ⟹ propagate bounds between
//! `x` and `y`) is out of scope for this pass; see [`ArithBoundsTactic::analyze`]
//! for the precise, honestly-documented capability.
//!
//! ## Benefits
//!
//! - Simpler constraints for theory solver
//! - Earlier conflict detection
//!
//! ## References
//!
//! - Z3's `tactic/arith/propagate_ineqs_tactic.cpp`

use crate::ast::{TermId, TermKind, TermManager};
use crate::error::Result;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::tactic::core::{Goal, SolveResult, Tactic, TacticResult};
use core::fmt;
use num_bigint::BigInt;
use num_rational::BigRational;

/// Variable identifier — the underlying variable term's raw [`TermId`]
/// value, used directly as a stable per-goal key.
pub type VarId = usize;

/// Bound on a variable.
#[derive(Debug, Clone)]
pub struct Bound {
    /// Lower bound (if any).
    pub lower: Option<BigRational>,
    /// Upper bound (if any).
    pub upper: Option<BigRational>,
}

impl Bound {
    /// Create unbounded.
    pub fn unbounded() -> Self {
        Self {
            lower: None,
            upper: None,
        }
    }

    /// Check if bounds are consistent.
    pub fn is_consistent(&self) -> bool {
        match (&self.lower, &self.upper) {
            (Some(l), Some(u)) => l <= u,
            _ => true,
        }
    }

    /// Intersect with another bound.
    pub fn intersect(&mut self, other: &Bound) {
        // Take maximum of lower bounds
        if let Some(other_lower) = &other.lower {
            self.lower = match &self.lower {
                Some(current) => Some(current.clone().max(other_lower.clone())),
                None => Some(other_lower.clone()),
            };
        }

        // Take minimum of upper bounds
        if let Some(other_upper) = &other.upper {
            self.upper = match &self.upper {
                Some(current) => Some(current.clone().min(other_upper.clone())),
                None => Some(other_upper.clone()),
            };
        }
    }
}

/// Configuration for bounds analysis.
#[derive(Debug, Clone)]
pub struct ArithBoundsConfig {
    /// Enable bound propagation.
    pub enable_propagation: bool,
    /// Enable bound tightening.
    pub enable_tightening: bool,
    /// Maximum propagation iterations.
    pub max_iterations: usize,
}

impl Default for ArithBoundsConfig {
    fn default() -> Self {
        Self {
            enable_propagation: true,
            enable_tightening: true,
            max_iterations: 100,
        }
    }
}

/// Statistics for bounds analysis.
#[derive(Debug, Clone, Default)]
pub struct ArithBoundsStats {
    /// Goals processed.
    pub goals_processed: u64,
    /// Bounds discovered.
    pub bounds_discovered: u64,
    /// Inconsistencies detected.
    pub inconsistencies: u64,
    /// Constraints tightened.
    pub constraints_tightened: u64,
}

/// Arithmetic bounds analysis tactic.
pub struct ArithBoundsTactic {
    /// Configuration.
    config: ArithBoundsConfig,
    /// Known bounds on variables.
    bounds: FxHashMap<VarId, Bound>,
    /// Statistics.
    stats: ArithBoundsStats,
}

impl ArithBoundsTactic {
    /// Create a new bounds tactic.
    pub fn new(config: ArithBoundsConfig) -> Self {
        Self {
            config,
            bounds: FxHashMap::default(),
            stats: ArithBoundsStats::default(),
        }
    }

    /// Create with default configuration.
    pub fn default_config() -> Self {
        Self::new(ArithBoundsConfig::default())
    }

    /// Add bound for variable.
    pub fn add_bound(&mut self, var: VarId, bound: Bound) {
        let entry = self.bounds.entry(var).or_insert_with(Bound::unbounded);

        entry.intersect(&bound);
        self.stats.bounds_discovered += 1;

        // Check consistency
        if !entry.is_consistent() {
            self.stats.inconsistencies += 1;
        }
    }

    /// Get bound for variable.
    pub fn get_bound(&self, var: VarId) -> Option<&Bound> {
        self.bounds.get(&var)
    }

    /// Get statistics.
    pub fn stats(&self) -> &ArithBoundsStats {
        &self.stats
    }

    /// Reset tactic state.
    pub fn reset(&mut self) {
        self.bounds.clear();
        self.stats = ArithBoundsStats::default();
    }

    // -- real extraction/analysis (requires `&TermManager`) -----------------

    /// Extract a variable id for `term_id` if it denotes a bare variable.
    fn as_var(term_id: TermId, manager: &TermManager) -> Option<VarId> {
        match manager.get(term_id).map(|t| &t.kind) {
            Some(TermKind::Var(_)) => Some(term_id.0 as usize),
            _ => None,
        }
    }

    /// Extract a rational constant value for `term_id`, if any.
    fn as_const(term_id: TermId, manager: &TermManager) -> Option<BigRational> {
        match manager.get(term_id).map(|t| &t.kind) {
            Some(TermKind::IntConst(n)) => Some(BigRational::from_integer(n.clone())),
            Some(TermKind::RealConst(r)) => Some(BigRational::new(
                BigInt::from(*r.numer()),
                BigInt::from(*r.denom()),
            )),
            _ => None,
        }
    }

    fn apply_cmp_bound(&mut self, var: VarId, value: BigRational, kind: CmpKind) {
        if !self.config.enable_propagation {
            return;
        }
        let mut bound = Bound::unbounded();
        match kind {
            CmpKind::Ge | CmpKind::Gt => bound.lower = Some(value),
            CmpKind::Le | CmpKind::Lt => bound.upper = Some(value),
        }
        self.add_bound(var, bound);
    }

    fn extract_comparison(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        kind: CmpKind,
        manager: &TermManager,
    ) {
        if let (Some(v), Some(c)) = (Self::as_var(lhs, manager), Self::as_const(rhs, manager)) {
            self.apply_cmp_bound(v, c, kind);
        } else if let (Some(c), Some(v)) =
            (Self::as_const(lhs, manager), Self::as_var(rhs, manager))
        {
            self.apply_cmp_bound(v, c, kind.flip());
        }
    }

    fn extract_equality(&mut self, lhs: TermId, rhs: TermId, manager: &TermManager) {
        if !self.config.enable_propagation {
            return;
        }
        let point = if let (Some(v), Some(c)) =
            (Self::as_var(lhs, manager), Self::as_const(rhs, manager))
        {
            Some((v, c))
        } else if let (Some(c), Some(v)) =
            (Self::as_const(lhs, manager), Self::as_var(rhs, manager))
        {
            Some((v, c))
        } else {
            None
        };
        if let Some((v, c)) = point {
            self.add_bound(
                v,
                Bound {
                    lower: Some(c.clone()),
                    upper: Some(c),
                },
            );
        }
    }

    /// Recursively extract bounds on variables from the literal comparisons
    /// in `term_id`, recursing through top-level conjunctions.
    fn extract_from_term(&mut self, term_id: TermId, manager: &TermManager) {
        let Some(term) = manager.get(term_id) else {
            return;
        };
        match &term.kind {
            TermKind::And(args) => {
                for &a in args.iter() {
                    self.extract_from_term(a, manager);
                }
            }
            TermKind::Ge(lhs, rhs) => self.extract_comparison(*lhs, *rhs, CmpKind::Ge, manager),
            TermKind::Gt(lhs, rhs) => self.extract_comparison(*lhs, *rhs, CmpKind::Gt, manager),
            TermKind::Le(lhs, rhs) => self.extract_comparison(*lhs, *rhs, CmpKind::Le, manager),
            TermKind::Lt(lhs, rhs) => self.extract_comparison(*lhs, *rhs, CmpKind::Lt, manager),
            TermKind::Eq(lhs, rhs) => self.extract_equality(*lhs, *rhs, manager),
            _ => {}
        }
    }

    /// Classify a top-level `Ge`/`Gt`/`Le`/`Lt` comparison of a variable
    /// against a constant as provably always-true (`Some(true)`), provably
    /// always-false (`Some(false)`), or unknown (`None`) given `self`'s
    /// currently-known bounds.
    fn classify_top_level(&self, assertion: TermId, manager: &TermManager) -> Option<bool> {
        let term = manager.get(assertion)?;
        let (lhs, rhs, kind) = match &term.kind {
            TermKind::Ge(l, r) => (*l, *r, CmpKind::Ge),
            TermKind::Gt(l, r) => (*l, *r, CmpKind::Gt),
            TermKind::Le(l, r) => (*l, *r, CmpKind::Le),
            TermKind::Lt(l, r) => (*l, *r, CmpKind::Lt),
            _ => return None,
        };

        if let (Some(v), Some(c)) = (Self::as_var(lhs, manager), Self::as_const(rhs, manager)) {
            return self.classify(v, kind, &c);
        }
        if let (Some(c), Some(v)) = (Self::as_const(lhs, manager), Self::as_var(rhs, manager)) {
            return self.classify(v, kind.flip(), &c);
        }
        None
    }

    fn classify(&self, var: VarId, kind: CmpKind, value: &BigRational) -> Option<bool> {
        let bound = self.bounds.get(&var)?;
        match kind {
            CmpKind::Ge => {
                if let Some(l) = &bound.lower
                    && l >= value
                {
                    return Some(true);
                }
                if let Some(u) = &bound.upper
                    && u < value
                {
                    return Some(false);
                }
                None
            }
            CmpKind::Gt => {
                if let Some(l) = &bound.lower
                    && l > value
                {
                    return Some(true);
                }
                if let Some(u) = &bound.upper
                    && u <= value
                {
                    return Some(false);
                }
                None
            }
            CmpKind::Le => {
                if let Some(u) = &bound.upper
                    && u <= value
                {
                    return Some(true);
                }
                if let Some(l) = &bound.lower
                    && l > value
                {
                    return Some(false);
                }
                None
            }
            CmpKind::Lt => {
                if let Some(u) = &bound.upper
                    && u < value
                {
                    return Some(true);
                }
                if let Some(l) = &bound.lower
                    && l >= value
                {
                    return Some(false);
                }
                None
            }
        }
    }

    /// Extract bounds from `goal`'s assertions and use them to (a) detect
    /// an early UNSAT from inconsistent bounds, and (b) drop top-level
    /// comparison assertions that are provably implied by the *other*
    /// assertions.
    ///
    /// This is a real, term-aware analysis; it requires `&TermManager`
    /// access that the registry-dispatched [`Tactic::apply`] — whose
    /// signature is `fn apply(&self, goal: &Goal) -> Result<TacticResult>`,
    /// with no manager parameter — structurally cannot provide. That is why
    /// `Tactic::apply` on this type honestly reports
    /// [`TacticResult::NotApplicable`] instead of guessing; callers with
    /// `TermManager` access should call `analyze` directly.
    ///
    /// Note: only *literal* bounds (`x >= a`, `x <= b`, `x = a` against a
    /// constant, recursed through top-level `And`) are extracted; general
    /// equation-based propagation (`x = y + c`) is intentionally out of
    /// scope for this pass.
    pub fn analyze(&mut self, goal: &Goal, manager: &TermManager) -> Result<TacticResult> {
        self.stats.goals_processed += 1;

        self.bounds.clear();
        for &assertion in &goal.assertions {
            self.extract_from_term(assertion, manager);
        }

        for bound in self.bounds.values() {
            if !bound.is_consistent() {
                self.stats.inconsistencies += 1;
                return Ok(TacticResult::Solved(SolveResult::Unsat));
            }
        }

        if !self.config.enable_tightening || goal.assertions.len() > self.config.max_iterations {
            return Ok(TacticResult::NotApplicable);
        }

        // Greedily drop redundant assertions. An assertion is dropped only
        // when it is provably implied by the bounds derived from the
        // *surviving* assertions — i.e. every other assertion not already
        // dropped (the kept-so-far set together with the not-yet-processed
        // remainder). Excluding already-dropped assertions is what makes the
        // transformation sound: it prevents two syntactically-distinct but
        // logically-equivalent constraints (e.g. `x >= 5` and `5 <= x`, or two
        // copies of `x >= 5`) from mutually justifying each other's removal.
        // Were both dropped, the goal would lose the bound entirely and admit
        // models the original forbids — a model-widening under `Precise`.
        //
        // Soundness: let `K` be the final surviving set. Processing the dropped
        // assertions in reverse order, each was implied by a set contained in
        // `K` ∪ {assertions dropped later}; by reverse induction `K` implies
        // every dropped assertion, so `K` is equivalent to the original
        // conjunction (each side implies the other).
        let n = goal.assertions.len();
        let mut dropped = vec![false; n];

        for i in 0..n {
            let mut others = ArithBoundsTactic::new(self.config.clone());
            for (j, &other) in goal.assertions.iter().enumerate() {
                if i != j && !dropped[j] {
                    others.extract_from_term(other, manager);
                }
            }

            match others.classify_top_level(goal.assertions[i], manager) {
                Some(true) => {
                    dropped[i] = true;
                    self.stats.constraints_tightened += 1;
                }
                Some(false) => {
                    self.stats.constraints_tightened += 1;
                    return Ok(TacticResult::Solved(SolveResult::Unsat));
                }
                None => {}
            }
        }

        if !dropped.iter().any(|&d| d) {
            return Ok(TacticResult::NotApplicable);
        }

        let new_assertions: Vec<TermId> = goal
            .assertions
            .iter()
            .enumerate()
            .filter(|&(i, _)| !dropped[i])
            .map(|(_, &a)| a)
            .collect();

        Ok(TacticResult::SubGoals(vec![Goal {
            assertions: new_assertions,
            precision: goal.precision,
        }]))
    }
}

/// Kind of a literal comparison, used while extracting/classifying bounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CmpKind {
    /// `lhs >= rhs`
    Ge,
    /// `lhs > rhs`
    Gt,
    /// `lhs <= rhs`
    Le,
    /// `lhs < rhs`
    Lt,
}

impl CmpKind {
    /// The comparison obtained by swapping the two sides, e.g. `c <= x`
    /// (parsed as `Le` with `lhs = c`) is equivalent to `x >= c`.
    fn flip(self) -> Self {
        match self {
            CmpKind::Ge => CmpKind::Le,
            CmpKind::Le => CmpKind::Ge,
            CmpKind::Gt => CmpKind::Lt,
            CmpKind::Lt => CmpKind::Gt,
        }
    }
}

impl Tactic for ArithBoundsTactic {
    fn apply(&self, _goal: &Goal) -> Result<TacticResult> {
        // See the doc comment on `ArithBoundsTactic::analyze`: this
        // dispatch path has no `TermManager` access and therefore honestly
        // reports NotApplicable rather than fabricating a result.
        Ok(TacticResult::NotApplicable)
    }

    fn name(&self) -> &str {
        "arith-bounds"
    }

    fn description(&self) -> &str {
        "Analyze and propagate arithmetic bounds (see ArithBoundsTactic::analyze for the real, TermManager-aware entry point)"
    }
}

impl fmt::Debug for ArithBoundsTactic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ArithBoundsTactic")
            .field("config", &self.config)
            .field("stats", &self.stats)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    #[test]
    fn test_tactic_creation() {
        let tactic = ArithBoundsTactic::default_config();
        assert_eq!(tactic.stats().goals_processed, 0);
    }

    #[test]
    fn test_bound_consistency() {
        let mut bound = Bound::unbounded();
        bound.lower = Some(BigRational::from_integer(BigInt::from(5)));
        bound.upper = Some(BigRational::from_integer(BigInt::from(10)));

        assert!(bound.is_consistent());
    }

    #[test]
    fn test_bound_inconsistency() {
        let mut bound = Bound::unbounded();
        bound.lower = Some(BigRational::from_integer(BigInt::from(10)));
        bound.upper = Some(BigRational::from_integer(BigInt::from(5)));

        assert!(!bound.is_consistent());
    }

    #[test]
    fn test_bound_intersect() {
        let mut bound1 = Bound::unbounded();
        bound1.lower = Some(BigRational::from_integer(BigInt::from(0)));
        bound1.upper = Some(BigRational::from_integer(BigInt::from(10)));

        let mut bound2 = Bound::unbounded();
        bound2.lower = Some(BigRational::from_integer(BigInt::from(5)));
        bound2.upper = Some(BigRational::from_integer(BigInt::from(15)));

        bound1.intersect(&bound2);

        assert_eq!(
            bound1.lower,
            Some(BigRational::from_integer(BigInt::from(5)))
        );
        assert_eq!(
            bound1.upper,
            Some(BigRational::from_integer(BigInt::from(10)))
        );
    }

    #[test]
    fn test_add_bound() {
        let mut tactic = ArithBoundsTactic::default_config();

        let mut bound = Bound::unbounded();
        bound.lower = Some(BigRational::from_integer(BigInt::from(0)));

        tactic.add_bound(0, bound);

        assert!(tactic.get_bound(0).is_some());
        assert_eq!(tactic.stats().bounds_discovered, 1);
    }

    // Regression tests for the previously-permanent-NotApplicable stub:
    // `analyze` must do real term-aware bounds analysis.

    #[test]
    fn test_analyze_detects_inconsistency() {
        let mut manager = TermManager::default();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let ten = manager.mk_int(10);
        let five = manager.mk_int(5);
        let ge = manager.mk_ge(x, ten); // x >= 10
        let le = manager.mk_le(x, five); // x <= 5

        let goal = Goal::new(vec![ge, le]);
        let mut tactic = ArithBoundsTactic::default_config();
        let result = tactic
            .analyze(&goal, &manager)
            .expect("test operation should succeed");

        assert!(matches!(result, TacticResult::Solved(SolveResult::Unsat)));
    }

    #[test]
    fn test_analyze_not_applicable_without_literal_bounds() {
        let mut manager = TermManager::default();
        let bool_sort = manager.sorts.bool_sort;
        let p = manager.mk_var("p", bool_sort);

        let goal = Goal::new(vec![p]);
        let mut tactic = ArithBoundsTactic::default_config();
        let result = tactic
            .analyze(&goal, &manager)
            .expect("test operation should succeed");

        assert!(matches!(result, TacticResult::NotApplicable));
    }

    #[test]
    fn test_analyze_drops_assertion_implied_by_others() {
        let mut manager = TermManager::default();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let three = manager.mk_int(3);
        let five = manager.mk_int(5);
        let ge5 = manager.mk_ge(x, five); // x >= 5
        let ge3 = manager.mk_ge(x, three); // x >= 3 (implied by x >= 5)

        let goal = Goal::new(vec![ge5, ge3]);
        let mut tactic = ArithBoundsTactic::default_config();
        let result = tactic
            .analyze(&goal, &manager)
            .expect("test operation should succeed");

        match result {
            TacticResult::SubGoals(goals) => {
                assert_eq!(goals.len(), 1);
                assert_eq!(goals[0].assertions, vec![ge5]);
            }
            other => panic!("expected SubGoals dropping the redundant assertion, got {other:?}"),
        }
    }

    #[test]
    fn test_analyze_never_uses_an_assertion_to_justify_itself() {
        // A single literal bound must never be treated as "provably true"
        // (and therefore droppable) using only its own contribution --
        // that would silently discard the constraint and unsoundly widen
        // the goal.
        let mut manager = TermManager::default();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let five = manager.mk_int(5);
        let ge5 = manager.mk_ge(x, five); // x >= 5, alone

        let goal = Goal::new(vec![ge5]);
        let mut tactic = ArithBoundsTactic::default_config();
        let result = tactic
            .analyze(&goal, &manager)
            .expect("test operation should succeed");

        assert!(matches!(result, TacticResult::NotApplicable));
    }

    #[test]
    fn test_analyze_keeps_one_of_two_identical_bounds() {
        // Regression: two syntactically-identical bounds `x >= 5, x >= 5`
        // must NOT both be dropped. Dropping both would yield an empty goal
        // that still carries `Precision::Precise` and admits `x = 0`, which
        // the original forbids — a model-widening (unsound) transformation.
        let mut manager = TermManager::default();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let five = manager.mk_int(5);
        let ge5a = manager.mk_ge(x, five); // x >= 5
        let ge5b = manager.mk_ge(x, five); // x >= 5 (same term)

        let goal = Goal::new(vec![ge5a, ge5b]);
        let mut tactic = ArithBoundsTactic::default_config();
        let result = tactic
            .analyze(&goal, &manager)
            .expect("test operation should succeed");

        match result {
            // Either untouched, or exactly one copy dropped — but never both.
            TacticResult::NotApplicable => {}
            TacticResult::SubGoals(goals) => {
                assert_eq!(goals.len(), 1);
                assert_eq!(
                    goals[0].assertions.len(),
                    1,
                    "must retain the bound, not drop both copies"
                );
                assert_eq!(goals[0].assertions[0], ge5a);
            }
            other => panic!("unexpected result {other:?}"),
        }
    }

    #[test]
    fn test_analyze_keeps_one_of_two_equivalent_bounds() {
        // Regression: `x >= 5` and `5 <= x` are syntactically distinct but
        // logically equivalent. They must not mutually justify each other's
        // removal (which would drop both and lose the bound entirely).
        let mut manager = TermManager::default();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let five = manager.mk_int(5);
        let ge = manager.mk_ge(x, five); // x >= 5
        let le = manager.mk_le(five, x); // 5 <= x  (equivalent)

        let goal = Goal::new(vec![ge, le]);
        let mut tactic = ArithBoundsTactic::default_config();
        let result = tactic
            .analyze(&goal, &manager)
            .expect("test operation should succeed");

        match result {
            TacticResult::NotApplicable => {}
            TacticResult::SubGoals(goals) => {
                assert_eq!(goals.len(), 1);
                assert_eq!(
                    goals[0].assertions.len(),
                    1,
                    "must retain one bound, not drop both equivalent copies"
                );
            }
            other => panic!("unexpected result {other:?}"),
        }
    }
}
