//! Destructive Equality Resolution (DER) tactic.
//!
//! Split out of the former single-file `tactic/quantifier.rs`; see
//! [`super`] for the module layout. Pure code motion.

use crate::ast::traversal::{TermVisitor, VisitorAction, traverse};
use crate::ast::{TermId, TermKind, TermManager};
use crate::error::Result;
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortId;
use smallvec::SmallVec;

use super::subst::substitute_single_var;
use crate::tactic::{Goal, TacticResult};

// ============================================================================
// Destructive Equality Resolution (DER)
// ============================================================================

/// Configuration for Destructive Equality Resolution
#[derive(Debug, Clone)]
pub struct DerConfig {
    /// Maximum *quantifier-alternation* depth to search for eliminable
    /// equalities.
    ///
    /// This bounds only how many nested `Forall`/`Exists` binders DER
    /// descends through; Boolean structure (`And`/`Or`/`Not`/`Implies`) is
    /// traversed without limit. It is a cost/completeness knob, not a safety
    /// guard: `DerTactic::apply_der` walks the term with an explicit heap
    /// stack, so exceeding it can only mean "this deeply nested quantifier
    /// was left alone", never a mis-elimination and never an aborted
    /// process. It used to bound total *term* nesting instead, which made a
    /// quantifier 11 Boolean connectives down invisible to DER.
    pub max_depth: usize,
    /// Whether to apply DER recursively to nested quantifiers
    pub recursive: bool,
    /// Whether to handle disequalities (x ≠ t implies false path)
    pub handle_diseq: bool,
}

impl Default for DerConfig {
    fn default() -> Self {
        Self {
            max_depth: 10,
            recursive: true,
            handle_diseq: true,
        }
    }
}

/// Which Boolean connective a [`DerFrame::Connective`] rebuilds.
#[derive(Debug, Clone, Copy)]
enum DerConnective {
    And,
    Or,
    Not,
    Implies,
}

/// One pending step of [`DerTactic::apply_der`]'s explicit-stack walk. Each
/// variant carries the state its recursive counterpart kept in live locals
/// across the recursive call.
#[derive(Debug)]
enum DerFrame {
    /// Apply DER to `term_id`, `qdepth` quantifiers below the assertion root.
    Eval { term_id: TermId, qdepth: usize },
    /// The body of a quantifier has been processed; run the ∀/∃ elimination
    /// rule on the rebuilt binder.
    Quantifier {
        term_id: TermId,
        qdepth: usize,
        vars: SmallVec<[(Spur, SortId); 2]>,
        patterns: SmallVec<[SmallVec<[TermId; 2]>; 2]>,
        is_forall: bool,
    },
    /// All arguments of a Boolean connective have been processed; rebuild it
    /// (keeping the original `TermId` when nothing changed, as before).
    Connective {
        term_id: TermId,
        qdepth: usize,
        op: DerConnective,
        orig: SmallVec<[TermId; 4]>,
    },
}

/// Represents a discovered eliminable equality
#[derive(Debug, Clone)]
struct EliminableEquality {
    /// The bound variable name
    var_name: Spur,
    /// The term to substitute for the variable
    substitute: TermId,
    /// Whether this is a positive (x = t) or negative (x ≠ t) equality
    /// Reserved for future disequality handling
    #[allow(dead_code)]
    is_positive: bool,
}

/// Destructive Equality Resolution (DER) Tactic
///
/// DER eliminates quantifiers when there are equalities that allow
/// direct variable substitution.
///
/// For universal quantifiers (∀x. φ), DER eliminates a **disequality** literal:
/// - ∀x. (x ≠ t ∨ ψ(x)) where x ∉ FV(t) becomes ψ(t)
/// - ∀x. (x = t → ψ(x)) is equivalent to the above (since x=t→ψ ≡ x≠t ∨ ψ)
///
/// Note the polarity: it is the *disequality* x ≠ t that is resolved, not a
/// positive equality.  Rewriting ∀x.(x = t ∨ ψ(x)) to ψ(t) would be **unsound**
/// (e.g. ∀x.(x=5 ∨ P(x)) ∧ ¬P(6) is UNSAT but P(5) ∧ ¬P(6) is SAT).
///
/// For existential quantifiers (∃x. φ), DER eliminates a positive equality:
/// - ∃x. (x = t ∧ ψ(x)) where x ∉ FV(t) becomes ψ(t)
///
/// This is a powerful simplification that can eliminate quantifiers entirely.
#[derive(Debug)]
pub struct DerTactic<'a> {
    manager: &'a mut TermManager,
    config: DerConfig,
}

impl<'a> DerTactic<'a> {
    /// Create a new DER tactic with default configuration
    pub fn new(manager: &'a mut TermManager) -> Self {
        Self {
            manager,
            config: DerConfig::default(),
        }
    }

    /// Create a new DER tactic with custom configuration
    pub fn with_config(manager: &'a mut TermManager, config: DerConfig) -> Self {
        Self { manager, config }
    }

    /// Apply the tactic to a goal
    pub fn apply_mut(&mut self, goal: &Goal) -> Result<TacticResult> {
        let mut changed = false;
        let mut new_assertions = Vec::with_capacity(goal.assertions.len());

        for &assertion in &goal.assertions {
            let simplified = self.apply_der(assertion);
            if simplified != assertion {
                changed = true;
            }
            new_assertions.push(simplified);
        }

        if !changed {
            return Ok(TacticResult::NotApplicable);
        }

        Ok(TacticResult::SubGoals(vec![Goal {
            assertions: new_assertions,
            precision: goal.precision,
        }]))
    }

    /// Apply DER to a single term.
    ///
    /// # Explicit work stack
    ///
    /// The walk is driven by a heap [`Vec`] of [`DerFrame`]s rather than
    /// native recursion. The old version recursed once per level of *term*
    /// nesting and guarded that with `DerConfig::max_depth` (default 10) — a
    /// cap on a `TermId`-returning function, so all it could do was silently
    /// stop applying DER at the eleventh level of `And`/`Or`/`Not` nesting.
    /// Now Boolean structure is traversed without limit and `max_depth`
    /// bounds only quantifier-alternation depth (see [`DerConfig::max_depth`]).
    ///
    /// Each frame owns the parent state its recursive counterpart kept in
    /// live locals, so every result a frame consumes was queued by that same
    /// frame — there is no "pop an empty stack" case to guard.
    ///
    /// # Memoization
    ///
    /// Results are memoized on `(TermId, quantifier depth)`. DER's output for
    /// a subterm depends on nothing else (the substitutions it performs are
    /// derived entirely from the binders inside that subterm), so re-reaching
    /// a shared node of the hash-consed DAG must give the same answer;
    /// without the memo a term sharing one subterm across k parents
    /// re-derived it k times, exponentially in the sharing depth.
    fn apply_der(&mut self, term_id: TermId) -> TermId {
        let mut frames: Vec<DerFrame> = vec![DerFrame::Eval { term_id, qdepth: 0 }];
        let mut results: Vec<TermId> = Vec::new();
        let mut memo: FxHashMap<(TermId, usize), TermId> = FxHashMap::default();

        while let Some(frame) = frames.pop() {
            match frame {
                DerFrame::Eval { term_id, qdepth } => {
                    self.der_eval(term_id, qdepth, &mut frames, &mut results, &memo);
                }

                DerFrame::Quantifier {
                    term_id,
                    qdepth,
                    vars,
                    patterns,
                    is_forall,
                } => {
                    let body = results.pop().unwrap_or(term_id);
                    let rebuilt = if is_forall {
                        self.apply_der_forall(vars, body, patterns)
                    } else {
                        self.apply_der_exists(vars, body, patterns)
                    };
                    memo.insert((term_id, qdepth), rebuilt);
                    results.push(rebuilt);
                }

                DerFrame::Connective {
                    term_id,
                    qdepth,
                    op,
                    orig,
                } => {
                    let start = results.len().saturating_sub(orig.len());
                    let mut new_args: SmallVec<[TermId; 4]> = results.split_off(start).into();
                    // `Eval` queued exactly `orig.len()` child evaluations
                    // before this frame; the fill keeps the unreachable short
                    // case expressible without a panic.
                    while new_args.len() < orig.len() {
                        new_args.push(orig[new_args.len()]);
                    }

                    let rebuilt = if new_args == orig {
                        term_id
                    } else {
                        match op {
                            DerConnective::And => self.manager.mk_and(new_args),
                            DerConnective::Or => self.manager.mk_or(new_args),
                            DerConnective::Not => self.manager.mk_not(new_args[0]),
                            DerConnective::Implies => {
                                self.manager.mk_implies(new_args[0], new_args[1])
                            }
                        }
                    };
                    memo.insert((term_id, qdepth), rebuilt);
                    results.push(rebuilt);
                }
            }
        }

        results.pop().unwrap_or(term_id)
    }

    /// Expand one [`DerFrame::Eval`]: either settle `term_id` immediately or
    /// queue its children plus the frame that rebuilds it.
    fn der_eval(
        &mut self,
        term_id: TermId,
        qdepth: usize,
        frames: &mut Vec<DerFrame>,
        results: &mut Vec<TermId>,
        memo: &FxHashMap<(TermId, usize), TermId>,
    ) {
        if let Some(&cached) = memo.get(&(term_id, qdepth)) {
            results.push(cached);
            return;
        }

        let term = match self.manager.get(term_id) {
            Some(t) => t.clone(),
            None => {
                results.push(term_id);
                return;
            }
        };

        match term.kind {
            TermKind::Forall {
                vars,
                body,
                patterns,
            }
            | TermKind::Exists {
                vars,
                body,
                patterns,
            } if qdepth > self.config.max_depth => {
                // Beyond the configured quantifier-alternation budget: leave
                // this quantifier exactly as it is. DER skips an elimination,
                // which is always sound — it never mis-eliminates.
                let _ = (vars, body, patterns);
                results.push(term_id);
            }

            TermKind::Forall {
                vars,
                body,
                patterns,
            } => {
                self.push_quantifier(frames, results, term_id, qdepth, vars, body, patterns, true);
            }

            TermKind::Exists {
                vars,
                body,
                patterns,
            } => {
                self.push_quantifier(
                    frames, results, term_id, qdepth, vars, body, patterns, false,
                );
            }

            // For non-quantifier terms, process children if configured
            // recursive.
            TermKind::And(args) if self.config.recursive => {
                Self::push_connective(frames, term_id, qdepth, DerConnective::And, args);
            }
            TermKind::Or(args) if self.config.recursive => {
                Self::push_connective(frames, term_id, qdepth, DerConnective::Or, args);
            }
            TermKind::Not(inner) if self.config.recursive => {
                Self::push_connective(
                    frames,
                    term_id,
                    qdepth,
                    DerConnective::Not,
                    SmallVec::from_slice(&[inner]),
                );
            }
            TermKind::Implies(lhs, rhs) if self.config.recursive => {
                Self::push_connective(
                    frames,
                    term_id,
                    qdepth,
                    DerConnective::Implies,
                    SmallVec::from_slice(&[lhs, rhs]),
                );
            }

            // Atoms, and every connective when `recursive` is off: DER has
            // nothing to do here, so the term is returned untouched (not
            // replaced by any default).
            _ => results.push(term_id),
        }
    }

    /// Queue a quantifier's body plus the frame that re-applies DER to the
    /// rebuilt binder. When `recursive` is off the body is used as-is,
    /// matching the previous behaviour.
    #[allow(clippy::too_many_arguments)]
    fn push_quantifier(
        &mut self,
        frames: &mut Vec<DerFrame>,
        results: &mut Vec<TermId>,
        term_id: TermId,
        qdepth: usize,
        vars: SmallVec<[(Spur, SortId); 2]>,
        body: TermId,
        patterns: SmallVec<[SmallVec<[TermId; 2]>; 2]>,
        is_forall: bool,
    ) {
        if self.config.recursive {
            frames.push(DerFrame::Quantifier {
                term_id,
                qdepth,
                vars,
                patterns,
                is_forall,
            });
            frames.push(DerFrame::Eval {
                term_id: body,
                qdepth: qdepth + 1,
            });
        } else {
            let rebuilt = if is_forall {
                self.apply_der_forall(vars, body, patterns)
            } else {
                self.apply_der_exists(vars, body, patterns)
            };
            results.push(rebuilt);
        }
    }

    /// Queue a Boolean connective's arguments plus the frame that rebuilds
    /// it, ordered so results land in argument order.
    fn push_connective(
        frames: &mut Vec<DerFrame>,
        term_id: TermId,
        qdepth: usize,
        op: DerConnective,
        args: SmallVec<[TermId; 4]>,
    ) {
        // `frames` is a LIFO: the rebuild frame goes on first so it runs
        // last, then the children in reverse so they pop in argument order.
        frames.push(DerFrame::Connective {
            term_id,
            qdepth,
            op,
            orig: args.clone(),
        });
        for &arg in args.iter().rev() {
            frames.push(DerFrame::Eval {
                term_id: arg,
                qdepth,
            });
        }
    }

    /// Apply DER to a universal quantifier
    ///
    /// The sound DER rule for ∀ resolves a **disequality** literal:
    /// - ∀x. (x ≠ t ∨ ψ) ≡ ψ[t/x]
    /// - ∀x. (x = t → ψ) ≡ ψ[t/x]   (since x=t→ψ ≡ x≠t ∨ ψ)
    ///
    /// where x ∉ FV(t).  A *positive* equality disjunct (x = t ∨ ψ) is **not**
    /// eliminable this way and is deliberately left untouched.
    fn apply_der_forall(
        &mut self,
        vars: SmallVec<[(Spur, SortId); 2]>,
        body: TermId,
        patterns: SmallVec<[SmallVec<[TermId; 2]>; 2]>,
    ) -> TermId {
        let bound_var_names: FxHashSet<Spur> = vars.iter().map(|(n, _)| *n).collect();

        // Implication pattern: x = t → ψ  ≡  ψ[t/x].
        // The antecedent here is a *positive* equality on the bound variable.
        if let Some(term) = self.manager.get(body)
            && let TermKind::Implies(lhs, rhs) = &term.kind
        {
            let lhs = *lhs;
            let rhs = *rhs;
            if let Some((var_name, substitute)) = self.extract_eq_var(lhs, &bound_var_names) {
                let eq = EliminableEquality {
                    var_name,
                    substitute,
                    is_positive: true,
                };
                return self.eliminate_variable_with_substitute(vars, rhs, patterns, &eq);
            }
        }

        // Disjunction pattern: x ≠ t ∨ ψ  ≡  ψ[t/x].
        // The eliminated literal is a *disequality* (Not(Eq(x, t))).
        if let Some(eq) = self.find_eliminable_diseq_in_or(body, &bound_var_names) {
            return self.eliminate_variable(vars, body, patterns, &eq, true);
        }

        // No eliminable disequality found - return original or rebuilt
        if vars.is_empty() {
            body
        } else {
            // Convert Spur names to owned strings first
            let var_names: Vec<_> = vars
                .iter()
                .map(|(n, s)| (self.manager.resolve_str(*n).to_string(), *s))
                .collect();
            // Now create references for the API
            let var_strs: Vec<_> = var_names
                .iter()
                .map(|(name, sort)| (name.as_str(), *sort))
                .collect();
            self.manager
                .mk_forall_with_patterns(var_strs, body, patterns)
        }
    }

    /// Apply DER to an existential quantifier
    ///
    /// For ∃x. φ, we look for patterns like:
    /// - (x = t ∧ ψ) → ψ[t/x]
    fn apply_der_exists(
        &mut self,
        vars: SmallVec<[(Spur, SortId); 2]>,
        body: TermId,
        patterns: SmallVec<[SmallVec<[TermId; 2]>; 2]>,
    ) -> TermId {
        let bound_var_names: FxHashSet<Spur> = vars.iter().map(|(n, _)| *n).collect();

        // Look for eliminable equality in conjunction: x = t ∧ ψ
        if let Some(eq) = self.find_eliminable_equality_in_and(body, &bound_var_names) {
            return self.eliminate_variable(vars, body, patterns, &eq, false);
        }

        // No eliminable equality found - return original or rebuilt
        if vars.is_empty() {
            body
        } else {
            // Convert Spur names to owned strings first
            let var_names: Vec<_> = vars
                .iter()
                .map(|(n, s)| (self.manager.resolve_str(*n).to_string(), *s))
                .collect();
            // Now create references for the API
            let var_strs: Vec<_> = var_names
                .iter()
                .map(|(name, sort)| (name.as_str(), *sort))
                .collect();
            self.manager
                .mk_exists_with_patterns(var_strs, body, patterns)
        }
    }

    /// Find an eliminable disequality (x ≠ t) in a disjunction (for ∀)
    ///
    /// Matches `Not(Eq(x, t))` either as a disjunct of an `Or` body or as the
    /// entire body.  The returned [`EliminableEquality`] carries the bound
    /// variable and the term `t` to substitute for it.
    fn find_eliminable_diseq_in_or(
        &self,
        term_id: TermId,
        bound_vars: &FxHashSet<Spur>,
    ) -> Option<EliminableEquality> {
        let term = self.manager.get(term_id)?;

        match &term.kind {
            TermKind::Or(args) => {
                // Look through disjuncts for x ≠ t
                for &arg in args.iter() {
                    if let Some(eq) = self.extract_diseq_var(arg, bound_vars) {
                        return Some(eq);
                    }
                }
                None
            }
            // The entire body is a bare disequality x ≠ t.
            TermKind::Not(_) => self.extract_diseq_var(term_id, bound_vars),
            _ => None,
        }
    }

    /// Find an eliminable equality in a conjunction (for ∃)
    fn find_eliminable_equality_in_and(
        &self,
        term_id: TermId,
        bound_vars: &FxHashSet<Spur>,
    ) -> Option<EliminableEquality> {
        let term = self.manager.get(term_id)?;

        match &term.kind {
            TermKind::And(args) => {
                // Look through conjuncts for x = t
                for &arg in args.iter() {
                    if let Some(eq) = self.extract_eq_var(arg, bound_vars) {
                        return Some(EliminableEquality {
                            var_name: eq.0,
                            substitute: eq.1,
                            is_positive: true,
                        });
                    }
                }
                None
            }
            TermKind::Eq(lhs, rhs) => {
                // Direct equality
                self.check_eliminable_eq(*lhs, *rhs, bound_vars)
                    .map(|(var_name, substitute)| EliminableEquality {
                        var_name,
                        substitute,
                        is_positive: true,
                    })
            }
            _ => None,
        }
    }

    /// Extract a disequality pattern Not(Eq(x, t)) where x is a bound var
    fn extract_diseq_var(
        &self,
        term_id: TermId,
        bound_vars: &FxHashSet<Spur>,
    ) -> Option<EliminableEquality> {
        let term = self.manager.get(term_id)?;

        if let TermKind::Not(inner) = &term.kind
            && let Some((var_name, substitute)) = self.extract_eq_var(*inner, bound_vars)
        {
            return Some(EliminableEquality {
                var_name,
                substitute,
                is_positive: false,
            });
        }

        None
    }

    /// Extract equality x = t where x is a bound variable
    fn extract_eq_var(
        &self,
        term_id: TermId,
        bound_vars: &FxHashSet<Spur>,
    ) -> Option<(Spur, TermId)> {
        let term = self.manager.get(term_id)?;

        if let TermKind::Eq(lhs, rhs) = &term.kind {
            return self.check_eliminable_eq(*lhs, *rhs, bound_vars);
        }

        None
    }

    /// Check if lhs = rhs is an eliminable equality (one side is a bound var,
    /// other side doesn't contain that var)
    fn check_eliminable_eq(
        &self,
        lhs: TermId,
        rhs: TermId,
        bound_vars: &FxHashSet<Spur>,
    ) -> Option<(Spur, TermId)> {
        // Check if lhs is a bound variable and rhs doesn't contain it
        if let Some(lhs_term) = self.manager.get(lhs)
            && let TermKind::Var(name) = &lhs_term.kind
            && bound_vars.contains(name)
            && !self.term_contains_var(rhs, *name)
        {
            return Some((*name, rhs));
        }

        // Check if rhs is a bound variable and lhs doesn't contain it
        if let Some(rhs_term) = self.manager.get(rhs)
            && let TermKind::Var(name) = &rhs_term.kind
            && bound_vars.contains(name)
            && !self.term_contains_var(lhs, *name)
        {
            return Some((*name, lhs));
        }

        None
    }

    /// Check if a term contains a specific variable
    fn term_contains_var(&self, term_id: TermId, var_name: Spur) -> bool {
        struct VarChecker {
            var_name: Spur,
            found: bool,
        }

        impl TermVisitor for VarChecker {
            fn visit_pre(&mut self, term_id: TermId, manager: &TermManager) -> VisitorAction {
                if let Some(term) = manager.get(term_id)
                    && let TermKind::Var(name) = &term.kind
                    && *name == self.var_name
                {
                    self.found = true;
                    return VisitorAction::Stop;
                }
                VisitorAction::Continue
            }
        }

        let mut checker = VarChecker {
            var_name,
            found: false,
        };
        let _ = traverse(term_id, self.manager, &mut checker);
        checker.found
    }

    /// Eliminate a variable using a discovered equality
    fn eliminate_variable(
        &mut self,
        vars: SmallVec<[(Spur, SortId); 2]>,
        body: TermId,
        patterns: SmallVec<[SmallVec<[TermId; 2]>; 2]>,
        eq: &EliminableEquality,
        is_forall: bool,
    ) -> TermId {
        // Remove the equality from the body and substitute
        let new_body = if is_forall {
            self.remove_from_or_and_substitute(body, eq)
        } else {
            self.remove_from_and_and_substitute(body, eq)
        };

        // Remove the eliminated variable from the bound vars
        let remaining_vars: SmallVec<[(Spur, SortId); 2]> = vars
            .iter()
            .filter(|(n, _)| *n != eq.var_name)
            .copied()
            .collect();

        // If no variables remain, just return the body
        if remaining_vars.is_empty() {
            return new_body;
        }

        // Rebuild quantifier with remaining variables
        // Convert Spur names to owned strings first
        let var_names: Vec<_> = remaining_vars
            .iter()
            .map(|(n, s)| (self.manager.resolve_str(*n).to_string(), *s))
            .collect();
        // Now create references for the API
        let var_strs: Vec<_> = var_names
            .iter()
            .map(|(name, sort)| (name.as_str(), *sort))
            .collect();

        if is_forall {
            self.manager
                .mk_forall_with_patterns(var_strs, new_body, patterns)
        } else {
            self.manager
                .mk_exists_with_patterns(var_strs, new_body, patterns)
        }
    }

    /// Eliminate a variable with a direct substitute (for implication pattern)
    fn eliminate_variable_with_substitute(
        &mut self,
        vars: SmallVec<[(Spur, SortId); 2]>,
        body: TermId,
        patterns: SmallVec<[SmallVec<[TermId; 2]>; 2]>,
        eq: &EliminableEquality,
    ) -> TermId {
        // Substitute the variable in the body
        let substituted_body = self.substitute_var(body, eq.var_name, eq.substitute);

        // Remove the eliminated variable from the bound vars
        let remaining_vars: SmallVec<[(Spur, SortId); 2]> = vars
            .iter()
            .filter(|(n, _)| *n != eq.var_name)
            .copied()
            .collect();

        // If no variables remain, just return the body
        if remaining_vars.is_empty() {
            return substituted_body;
        }

        // Rebuild quantifier with remaining variables
        // Convert Spur names to owned strings first
        let var_names: Vec<_> = remaining_vars
            .iter()
            .map(|(n, s)| (self.manager.resolve_str(*n).to_string(), *s))
            .collect();
        // Now create references for the API
        let var_strs: Vec<_> = var_names
            .iter()
            .map(|(name, sort)| (name.as_str(), *sort))
            .collect();

        self.manager
            .mk_forall_with_patterns(var_strs, substituted_body, patterns)
    }

    /// Remove the chosen disequality (x ≠ t) from an OR and substitute t for x
    /// in the remaining disjuncts.
    ///
    /// Implements ∀x.(x ≠ t ∨ ψ) ≡ ψ[t/x].  Only the specific disequality
    /// literal `x ≠ t` matching `eq` is dropped; any *other* disequalities on x
    /// (e.g. x ≠ t2) are kept and become t ≠ t2 under the substitution, so no
    /// constraint is silently lost.
    fn remove_from_or_and_substitute(
        &mut self,
        term_id: TermId,
        eq: &EliminableEquality,
    ) -> TermId {
        let term = match self.manager.get(term_id) {
            Some(t) => t.clone(),
            None => return term_id,
        };

        match &term.kind {
            TermKind::Or(args) => {
                // Drop the chosen disequality literal, substitute in the rest.
                let mut new_args = Vec::new();
                for &arg in args.iter() {
                    if self.is_target_diseq(arg, eq.var_name, eq.substitute) {
                        continue;
                    }
                    let substituted = self.substitute_var(arg, eq.var_name, eq.substitute);
                    new_args.push(substituted);
                }

                match new_args.len() {
                    // ∀x.(x ≠ t) ≡ false (there always exists x = t).
                    0 => self.manager.mk_false(),
                    1 => new_args[0],
                    _ => self.manager.mk_or(new_args),
                }
            }
            // The entire body is *the resolved* disequality x ≠ t, so
            // ∀x.(x ≠ t) ≡ false.
            //
            // The `is_target_diseq` guard is load-bearing: this arm used to
            // fire on *any* `Not(_)` body. A body such as `¬P(x)` — or a
            // disequality on a different term, `x ≠ t2` — would then have
            // been replaced by `false`, turning a satisfiable assertion
            // unsatisfiable. (Today's callers only reach this function with
            // an `eq` extracted from this same body, so the unguarded version
            // happened to be correct in-tree; making the guard explicit means
            // a future caller cannot silently turn it into a wrong answer.)
            // Mirrors the ∃ side's `is_target_eq` guard in
            // [`Self::remove_from_and_and_substitute`].
            TermKind::Not(_) if self.is_target_diseq(term_id, eq.var_name, eq.substitute) => {
                self.manager.mk_false()
            }
            _ => {
                // Just substitute
                self.substitute_var(term_id, eq.var_name, eq.substitute)
            }
        }
    }

    /// Check that `term_id` is exactly the disequality `x ≠ substitute`, i.e.
    /// `Not(Eq(a, b))` with `{a, b} = {Var(var_name), substitute}`.
    fn is_target_diseq(&self, term_id: TermId, var_name: Spur, substitute: TermId) -> bool {
        let Some(term) = self.manager.get(term_id) else {
            return false;
        };
        let TermKind::Not(inner) = &term.kind else {
            return false;
        };
        let Some(inner_term) = self.manager.get(*inner) else {
            return false;
        };
        let TermKind::Eq(lhs, rhs) = &inner_term.kind else {
            return false;
        };
        let (lhs, rhs) = (*lhs, *rhs);
        let is_bound_var = |&tid: &TermId| {
            matches!(
                self.manager.get(tid).map(|t| &t.kind),
                Some(TermKind::Var(n)) if *n == var_name
            )
        };
        (is_bound_var(&lhs) && rhs == substitute) || (is_bound_var(&rhs) && lhs == substitute)
    }

    /// Remove the chosen equality (x = t) from an AND and substitute t for x
    /// in the remaining conjuncts.
    ///
    /// Implements ∃x.(x = t ∧ ψ) ≡ ψ[t/x].  Only the specific equality literal
    /// `x = t` matching `eq` is dropped; any *other* equality on x (e.g.
    /// x = t2, or the non-eliminable x = g(x)) is kept and becomes t = t2
    /// (resp. t = g(t)) under the substitution, so no constraint is silently
    /// lost.  This mirrors [`Self::remove_from_or_and_substitute`]'s precision
    /// on the ∀ side.
    ///
    /// Dropping every equality mentioning x -- which this used to do, via a
    /// `is_equality_for_var(arg, eq.var_name)` test that ignored the
    /// right-hand side entirely -- *weakens* the conjunction, so it turned
    /// UNSAT into SAT: `∃x. (x = 5 ∧ x = 6)` is unsatisfiable but both
    /// conjuncts matched, leaving an empty `And`, i.e. `true`.  See
    /// `super::tests::der_keeps_a_second_equality_on_the_eliminated_variable`.
    fn remove_from_and_and_substitute(
        &mut self,
        term_id: TermId,
        eq: &EliminableEquality,
    ) -> TermId {
        let term = match self.manager.get(term_id) {
            Some(t) => t.clone(),
            None => return term_id,
        };

        match &term.kind {
            TermKind::And(args) => {
                // Drop the chosen equality literal, substitute in the rest.
                let mut new_args = Vec::new();
                for &arg in args.iter() {
                    if self.is_target_eq(arg, eq.var_name, eq.substitute) {
                        continue;
                    }
                    let substituted = self.substitute_var(arg, eq.var_name, eq.substitute);
                    new_args.push(substituted);
                }

                match new_args.len() {
                    // ∃x.(x = t) ≡ true (sorts are non-empty and x ∉ FV(t),
                    // which `check_eliminable_eq` guarantees).
                    0 => self.manager.mk_true(),
                    1 => new_args[0],
                    _ => self.manager.mk_and(new_args),
                }
            }
            // The entire body is the equality x = t: ∃x.(x = t) ≡ true. Any
            // other `Eq` body is not the resolved literal and must merely be
            // substituted into, never discarded.
            TermKind::Eq(_, _) if self.is_target_eq(term_id, eq.var_name, eq.substitute) => {
                self.manager.mk_true()
            }
            _ => {
                // Just substitute
                self.substitute_var(term_id, eq.var_name, eq.substitute)
            }
        }
    }

    /// Check that `term_id` is exactly the equality `x = substitute`, i.e.
    /// `Eq(a, b)` with `{a, b} = {Var(var_name), substitute}`.
    ///
    /// The ∃ analogue of [`Self::is_target_diseq`].
    fn is_target_eq(&self, term_id: TermId, var_name: Spur, substitute: TermId) -> bool {
        let Some(term) = self.manager.get(term_id) else {
            return false;
        };
        let TermKind::Eq(lhs, rhs) = &term.kind else {
            return false;
        };
        let (lhs, rhs) = (*lhs, *rhs);
        let is_bound_var = |&tid: &TermId| {
            matches!(
                self.manager.get(tid).map(|t| &t.kind),
                Some(TermKind::Var(n)) if *n == var_name
            )
        };
        (is_bound_var(&lhs) && rhs == substitute) || (is_bound_var(&rhs) && lhs == substitute)
    }

    /// Substitute a variable with a term throughout an expression.
    ///
    /// Delegates to the shared [`substitute_single_var`] helper, which is
    /// capture-avoiding (stops at binders that re-bind the variable) and
    /// descends into all standard term kinds including function applications.
    fn substitute_var(&mut self, term_id: TermId, var_name: Spur, replacement: TermId) -> TermId {
        substitute_single_var(self.manager, term_id, var_name, replacement)
    }
}

/// Stateless wrapper for DER tactic
#[derive(Debug, Clone, Default)]
pub struct StatelessDerTactic {
    config: DerConfig,
}

impl StatelessDerTactic {
    /// Create a new stateless DER tactic
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create with custom configuration
    #[must_use]
    pub fn with_config(config: DerConfig) -> Self {
        Self { config }
    }

    /// Apply the tactic
    pub fn apply(&self, goal: &Goal, manager: &mut TermManager) -> Result<TacticResult> {
        let mut tactic = DerTactic::with_config(manager, self.config.clone());
        tactic.apply_mut(goal)
    }
}
