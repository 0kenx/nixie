//! Existential quantifier handling for CHCs.
//!
//! This module provides support for CHC rules with existential quantifiers,
//! which are common in verification problems involving non-deterministic choice
//! or abstraction.
//!
//! ## Existentially Quantified CHCs
//!
//! Standard form: `forall X. (body => exists Y. head(X, Y))`
//!
//! Existential variables appear only in the head of rules and represent
//! non-deterministic values or abstracted program variables.
//!
//! ## Handling Strategy
//!
//! 1. **Skolemization**: Convert existentials to fresh constants/functions
//! 2. **Projection**: Project out existential variables when learning lemmas
//! 3. **Witness extraction**: Find concrete values for existentials in counterexamples
//!
//! Reference: Existential handling in Z3's Spacer

use crate::chc::{PredId, PredicateApp, Rule, RuleHead};
use crate::pdr::SpacerError;
use oxiz_core::{SortId, TermId, TermKind, TermManager};
use smallvec::SmallVec;
use std::collections::HashMap;
use thiserror::Error;

/// Errors related to existential quantifier handling
#[derive(Error, Debug)]
pub enum ExistentialError {
    /// Unsupported existential pattern
    #[error("unsupported existential pattern: {0}")]
    Unsupported(String),
    /// Skolemization failed
    #[error("skolemization failed: {0}")]
    SkolemizationFailed(String),
    /// Projection failed
    #[error("projection failed: {0}")]
    ProjectionFailed(String),
    /// Spacer error
    #[error("spacer error: {0}")]
    Spacer(#[from] SpacerError),
}

/// Result type for existential operations
pub type ExistentialResult<T> = Result<T, ExistentialError>;

/// Information about existential variables in a rule
#[derive(Debug, Clone)]
pub struct ExistentialInfo {
    /// Variables that are existentially quantified
    pub existential_vars: SmallVec<[(String, SortId); 4]>,
    /// Variables that are universally quantified
    pub universal_vars: SmallVec<[(String, SortId); 4]>,
    /// Whether this rule has any existentials
    pub has_existentials: bool,
}

impl ExistentialInfo {
    /// Analyze a rule for existential variables.
    ///
    /// Existentials are variables that appear in the head's predicate
    /// arguments but are not among the rule's declared universal
    /// variables (`rule.vars`). Actually walking the head's argument
    /// terms (rather than just comparing argument *counts*) requires
    /// resolving each argument's `TermId` back to a variable name/sort,
    /// hence the `terms` parameter.
    ///
    /// This used to leave `existential_vars` permanently empty (`SmallVec::new()`,
    /// never pushed to) and only derive `has_existentials` from a crude
    /// `arg_count > declared_var_count` heuristic -- so any caller that
    /// fed `existential_vars` into [`ExistentialProjector::project`] or
    /// [`SkolemContext::skolemize`] would silently skolemize/project
    /// *nothing*, even on a rule `has_existentials` correctly flagged as
    /// having them.
    pub fn analyze(rule: &Rule, terms: &TermManager) -> Self {
        // Start with all declared universal variables
        let universal_vars: SmallVec<[(String, SortId); 4]> = rule.vars.clone();

        // Collect all variable names that are universal (declared)
        let universal_names: rustc_hash::FxHashSet<&str> =
            rule.vars.iter().map(|(name, _)| name.as_str()).collect();

        // For existentials, walk the head predicate application's
        // argument terms: any argument that is itself a plain variable
        // not among the declared universals is existential.
        let mut existential_vars: SmallVec<[(String, SortId); 4]> = SmallVec::new();
        if let crate::chc::RuleHead::Predicate(app) = &rule.head {
            let mut seen: rustc_hash::FxHashSet<String> = rustc_hash::FxHashSet::default();
            for &arg in &app.args {
                let Some(term) = terms.get(arg) else {
                    continue;
                };
                let TermKind::Var(name_spur) = &term.kind else {
                    // A compound (non-variable) head argument cannot itself
                    // be *the* existentially-bound variable; any existentials
                    // nested inside it are out of scope for this per-argument
                    // scan.
                    continue;
                };
                let name = terms.resolve_str(*name_spur);
                if !universal_names.contains(name) && seen.insert(name.to_string()) {
                    existential_vars.push((name.to_string(), term.sort));
                }
            }
        }

        let has_existentials = !existential_vars.is_empty();

        Self {
            existential_vars,
            universal_vars,
            has_existentials,
        }
    }

    /// Get the number of existential variables
    pub fn num_existentials(&self) -> usize {
        self.existential_vars.len()
    }
}

/// Skolemization context for existential variables
pub struct SkolemContext {
    /// Mapping from existential variables to Skolem functions/constants
    skolem_map: HashMap<String, TermId>,
    /// Fresh counter for Skolem names
    fresh_counter: u32,
}

impl SkolemContext {
    /// Create a new Skolemization context
    pub fn new() -> Self {
        Self {
            skolem_map: HashMap::new(),
            fresh_counter: 0,
        }
    }

    /// Skolemize an existential variable
    ///
    /// For `exists Y. phi(X, Y)` with free variables X, we create:
    /// - A Skolem constant if X is empty: `sk_Y`
    /// - A Skolem function otherwise: `sk_Y(X)`
    pub fn skolemize(
        &mut self,
        terms: &mut TermManager,
        var_name: &str,
        var_sort: SortId,
        free_vars: &[(String, SortId)],
    ) -> ExistentialResult<TermId> {
        // Check if already skolemized
        if let Some(&skolem) = self.skolem_map.get(var_name) {
            return Ok(skolem);
        }

        // Create Skolem term
        // For simplicity, we always create a Skolem constant
        // A full implementation would create Skolem functions for dependent variables
        let sk_name = if free_vars.is_empty() {
            self.fresh_skolem_name(var_name)
        } else {
            // Include dependencies in the name for uniqueness
            let dep_names: Vec<&str> = free_vars.iter().map(|(n, _)| n.as_str()).collect();
            format!(
                "{}_{}",
                self.fresh_skolem_name(var_name),
                dep_names.join("_")
            )
        };

        let skolem = terms.mk_var(&sk_name, var_sort);

        // Cache the Skolem term
        self.skolem_map.insert(var_name.to_string(), skolem);

        Ok(skolem)
    }

    /// Get fresh Skolem name
    fn fresh_skolem_name(&mut self, base: &str) -> String {
        let name = format!("sk_{}_{}", base, self.fresh_counter);
        self.fresh_counter += 1;
        name
    }
}

impl Default for SkolemContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Existential variable projector
///
/// Projects existential variables out of formulas using quantifier elimination
/// or approximation techniques.
pub struct ExistentialProjector;

impl ExistentialProjector {
    /// Project out existential variables from a formula
    ///
    /// Given a formula `phi(X, Y)` where Y are existential variables,
    /// compute an over-approximation `psi(X)` such that:
    /// - `phi(X, Y)` implies `psi(X)` for all Y
    /// - `psi` contains only variables from X
    pub fn project(
        terms: &mut TermManager,
        formula: TermId,
        existential_vars: &[(String, SortId)],
    ) -> ExistentialResult<TermId> {
        // If no existential variables, return formula as-is
        if existential_vars.is_empty() {
            return Ok(formula);
        }

        // Strategy 1: Syntactic projection (sound over-approximation)
        // If formula is a conjunction, drop all conjuncts containing existentials
        // and keep the rest. This is a sound over-approximation.
        Self::syntactic_projection(terms, formula, existential_vars)
    }

    /// Syntactic projection: drop literals containing existential variables
    ///
    /// This is a sound over-approximation - the result may be weaker than necessary
    /// but is guaranteed to be an over-approximation.
    fn syntactic_projection(
        terms: &mut TermManager,
        formula: TermId,
        existential_vars: &[(String, SortId)],
    ) -> ExistentialResult<TermId> {
        // Enhanced implementation: analyze formula and drop conjuncts with existentials
        use oxiz_core::TermKind;

        // Get formula structure
        let Some(term) = terms.get(formula) else {
            return Ok(terms.mk_true());
        };

        match &term.kind.clone() {
            TermKind::And(args) => {
                // For conjunctions, keep only literals without existentials
                let args_vec: Vec<TermId> = args.to_vec();
                let projected_args: Vec<TermId> = args_vec
                    .into_iter()
                    .filter(|&arg| !Self::contains_existential(arg, terms, existential_vars))
                    .collect();

                // Build result
                if projected_args.is_empty() {
                    // All literals contained existentials - return True
                    Ok(terms.mk_true())
                } else if projected_args.len() == 1 {
                    Ok(projected_args[0])
                } else {
                    Ok(terms.mk_and(projected_args))
                }
            }
            TermKind::Or(args) => {
                // For disjunctions, we must be more conservative
                // Project each disjunct separately and combine
                let args_vec: Vec<TermId> = args.to_vec();
                let projected_args: Vec<TermId> = args_vec
                    .into_iter()
                    .map(|arg| {
                        Self::syntactic_projection(terms, arg, existential_vars)
                            .unwrap_or_else(|_| terms.mk_true())
                    })
                    .collect();

                Ok(terms.mk_or(projected_args))
            }
            _ => {
                // Atomic formula
                if Self::contains_existential(formula, terms, existential_vars) {
                    // Contains existentials - project out to True
                    Ok(terms.mk_true())
                } else {
                    // No existentials - keep as is
                    Ok(formula)
                }
            }
        }
    }

    /// Check if a term contains any existential variables
    #[allow(dead_code)]
    fn contains_existential(
        term: TermId,
        terms: &TermManager,
        existential_vars: &[(String, SortId)],
    ) -> bool {
        // Enhanced implementation: traverse term AST to check for existential variables
        use std::collections::HashSet;

        // Build set of existential variable names for fast lookup
        let existential_names: HashSet<&str> = existential_vars
            .iter()
            .map(|(name, _)| name.as_str())
            .collect();

        // Recursively check if term contains any existential variable
        Self::contains_existential_rec(term, terms, &existential_names)
    }

    /// Recursive helper for checking existential occurrence
    fn contains_existential_rec(
        term: TermId,
        terms: &TermManager,
        existential_names: &std::collections::HashSet<&str>,
    ) -> bool {
        use oxiz_core::TermKind;

        let Some(t) = terms.get(term) else {
            return false;
        };

        match &t.kind {
            TermKind::Var(name_spur) => {
                // Check if this variable is existential
                let var_name = terms.resolve_str(*name_spur);
                existential_names.contains(var_name)
            }
            TermKind::And(args)
            | TermKind::Or(args)
            | TermKind::Add(args)
            | TermKind::Mul(args) => {
                // Check any subterm
                args.iter()
                    .any(|&arg| Self::contains_existential_rec(arg, terms, existential_names))
            }
            TermKind::Not(arg) => Self::contains_existential_rec(*arg, terms, existential_names),
            TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Sub(a, b)
            | TermKind::Div(a, b)
            | TermKind::Mod(a, b) => {
                Self::contains_existential_rec(*a, terms, existential_names)
                    || Self::contains_existential_rec(*b, terms, existential_names)
            }
            _ => false, // Constants, true, false don't contain variables
        }
    }

    /// Compute model-based projection
    ///
    /// Given a model M for `phi(X, Y)`, project out Y to get a formula
    /// over X that is implied by the model.
    pub fn mbp(
        terms: &mut TermManager,
        formula: TermId,
        model: &HashMap<TermId, TermId>,
        existential_vars: &[TermId],
    ) -> ExistentialResult<TermId> {
        // Model-based projection substitutes existential variables with their values
        // from the model, then simplifies the result

        // Create a substitution from existential vars to their model values
        let mut subst = HashMap::new();
        for &var in existential_vars {
            if let Some(&value) = model.get(&var) {
                subst.insert(var, value);
            }
        }

        // Apply substitution to the formula
        let projected = Self::apply_substitution(terms, formula, &subst);

        // Simplify the result by evaluating any ground literals
        let simplified = Self::simplify_ground(terms, projected);

        Ok(simplified)
    }

    /// Apply a substitution to a term
    fn apply_substitution(
        terms: &mut TermManager,
        term: TermId,
        subst: &HashMap<TermId, TermId>,
    ) -> TermId {
        use oxiz_core::TermKind;

        // Check if this term should be substituted
        if let Some(&replacement) = subst.get(&term) {
            return replacement;
        }

        // Recursively apply to subterms
        let Some(t) = terms.get(term) else {
            return term;
        };

        match &t.kind.clone() {
            TermKind::And(args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| Self::apply_substitution(terms, arg, subst))
                    .collect();
                terms.mk_and(new_args)
            }
            TermKind::Or(args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| Self::apply_substitution(terms, arg, subst))
                    .collect();
                terms.mk_or(new_args)
            }
            TermKind::Not(arg) => {
                let new_arg = Self::apply_substitution(terms, *arg, subst);
                terms.mk_not(new_arg)
            }
            TermKind::Eq(a, b) => {
                let new_a = Self::apply_substitution(terms, *a, subst);
                let new_b = Self::apply_substitution(terms, *b, subst);
                terms.mk_eq(new_a, new_b)
            }
            TermKind::Le(a, b) => {
                let new_a = Self::apply_substitution(terms, *a, subst);
                let new_b = Self::apply_substitution(terms, *b, subst);
                terms.mk_le(new_a, new_b)
            }
            TermKind::Lt(a, b) => {
                let new_a = Self::apply_substitution(terms, *a, subst);
                let new_b = Self::apply_substitution(terms, *b, subst);
                terms.mk_lt(new_a, new_b)
            }
            _ => term, // Other terms remain unchanged
        }
    }

    /// Simplify ground (variable-free) formulas
    fn simplify_ground(terms: &mut TermManager, term: TermId) -> TermId {
        use oxiz_core::TermKind;

        // Recursively simplify ground formulas
        let Some(t) = terms.get(term) else {
            return term;
        };

        match &t.kind.clone() {
            // Boolean constants - already simplified
            TermKind::True | TermKind::False => term,

            // Boolean operations on ground terms
            TermKind::Not(arg) => {
                let simplified_arg = Self::simplify_ground(terms, *arg);
                if let Some(arg_term) = terms.get(simplified_arg) {
                    match &arg_term.kind {
                        TermKind::True => terms.mk_false(),
                        TermKind::False => terms.mk_true(),
                        _ => terms.mk_not(simplified_arg),
                    }
                } else {
                    terms.mk_not(simplified_arg)
                }
            }

            TermKind::And(args) => {
                let simplified_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| Self::simplify_ground(terms, arg))
                    .collect();

                // If any arg is false, return false
                if simplified_args
                    .iter()
                    .any(|&arg| matches!(terms.get(arg).map(|t| &t.kind), Some(TermKind::False)))
                {
                    return terms.mk_false();
                }

                // Filter out true values
                let non_true_args: Vec<TermId> = simplified_args
                    .into_iter()
                    .filter(|&arg| !matches!(terms.get(arg).map(|t| &t.kind), Some(TermKind::True)))
                    .collect();

                match non_true_args.len() {
                    0 => terms.mk_true(),
                    1 => non_true_args[0],
                    _ => terms.mk_and(non_true_args),
                }
            }

            TermKind::Or(args) => {
                let simplified_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| Self::simplify_ground(terms, arg))
                    .collect();

                // If any arg is true, return true
                if simplified_args
                    .iter()
                    .any(|&arg| matches!(terms.get(arg).map(|t| &t.kind), Some(TermKind::True)))
                {
                    return terms.mk_true();
                }

                // Filter out false values
                let non_false_args: Vec<TermId> = simplified_args
                    .into_iter()
                    .filter(|&arg| {
                        !matches!(terms.get(arg).map(|t| &t.kind), Some(TermKind::False))
                    })
                    .collect();

                match non_false_args.len() {
                    0 => terms.mk_false(),
                    1 => non_false_args[0],
                    _ => terms.mk_or(non_false_args),
                }
            }

            // Arithmetic comparisons on constants
            TermKind::Eq(a, b) => {
                let simplified_a = Self::simplify_ground(terms, *a);
                let simplified_b = Self::simplify_ground(terms, *b);

                // Check if both are integer constants
                if let (Some(a_term), Some(b_term)) =
                    (terms.get(simplified_a), terms.get(simplified_b))
                {
                    match (&a_term.kind, &b_term.kind) {
                        (TermKind::IntConst(a_val), TermKind::IntConst(b_val)) => {
                            if a_val == b_val {
                                terms.mk_true()
                            } else {
                                terms.mk_false()
                            }
                        }
                        (TermKind::True, TermKind::True) | (TermKind::False, TermKind::False) => {
                            terms.mk_true()
                        }
                        (TermKind::True, TermKind::False) | (TermKind::False, TermKind::True) => {
                            terms.mk_false()
                        }
                        _ => terms.mk_eq(simplified_a, simplified_b),
                    }
                } else {
                    terms.mk_eq(simplified_a, simplified_b)
                }
            }

            TermKind::Lt(a, b) => {
                let simplified_a = Self::simplify_ground(terms, *a);
                let simplified_b = Self::simplify_ground(terms, *b);

                if let (Some(a_term), Some(b_term)) =
                    (terms.get(simplified_a), terms.get(simplified_b))
                {
                    if let (TermKind::IntConst(a_val), TermKind::IntConst(b_val)) =
                        (&a_term.kind, &b_term.kind)
                    {
                        if a_val < b_val {
                            terms.mk_true()
                        } else {
                            terms.mk_false()
                        }
                    } else {
                        terms.mk_lt(simplified_a, simplified_b)
                    }
                } else {
                    terms.mk_lt(simplified_a, simplified_b)
                }
            }

            TermKind::Le(_, _) | TermKind::Gt(_, _) | TermKind::Ge(_, _) => {
                // Extract values and kind before recursive calls
                let (a, b, kind_tag) = match &t.kind {
                    TermKind::Le(a, b) => (*a, *b, 0),
                    TermKind::Gt(a, b) => (*a, *b, 1),
                    TermKind::Ge(a, b) => (*a, *b, 2),
                    _ => unreachable!(),
                };

                let simplified_a = Self::simplify_ground(terms, a);
                let simplified_b = Self::simplify_ground(terms, b);

                if let (Some(a_term), Some(b_term)) =
                    (terms.get(simplified_a), terms.get(simplified_b))
                {
                    if let (TermKind::IntConst(a_val), TermKind::IntConst(b_val)) =
                        (&a_term.kind, &b_term.kind)
                    {
                        let result = match kind_tag {
                            0 => a_val <= b_val, // Le
                            1 => a_val > b_val,  // Gt
                            2 => a_val >= b_val, // Ge
                            _ => unreachable!(),
                        };
                        if result {
                            terms.mk_true()
                        } else {
                            terms.mk_false()
                        }
                    } else {
                        // Not constants, rebuild the term
                        match kind_tag {
                            0 => terms.mk_le(simplified_a, simplified_b),
                            1 => terms.mk_gt(simplified_a, simplified_b),
                            2 => terms.mk_ge(simplified_a, simplified_b),
                            _ => unreachable!(),
                        }
                    }
                } else {
                    match kind_tag {
                        0 => terms.mk_le(simplified_a, simplified_b),
                        1 => terms.mk_gt(simplified_a, simplified_b),
                        2 => terms.mk_ge(simplified_a, simplified_b),
                        _ => unreachable!(),
                    }
                }
            }

            // For other terms, return as-is (constants, variables, etc.)
            _ => term,
        }
    }
}

/// Witness extraction for existential variables
///
/// Extracts concrete values (witnesses) for existential variables from
/// counterexamples or models.
pub struct WitnessExtractor;

impl WitnessExtractor {
    /// Extract witnesses for existential variables from a model.
    ///
    /// Matching a witness value to the variable it belongs to requires
    /// inspecting each model-key term's [`TermKind::Var`] name, which in turn
    /// needs the owning [`TermManager`]. This method therefore delegates to
    /// [`WitnessExtractor::extract_witnesses_with_terms`]. A previous version
    /// assigned an arbitrary (hash-ordered) model entry to every existential
    /// variable, producing wrong values under wrong names — an unsound result
    /// that this delegation removes.
    pub fn extract_witnesses(
        terms: &TermManager,
        model: &HashMap<TermId, TermId>,
        existential_vars: &[(String, SortId)],
    ) -> HashMap<String, TermId> {
        Self::extract_witnesses_with_terms(terms, model, existential_vars)
    }

    /// Extract witnesses with term manager access for better name matching
    pub fn extract_witnesses_with_terms(
        terms: &TermManager,
        model: &HashMap<TermId, TermId>,
        existential_vars: &[(String, SortId)],
    ) -> HashMap<String, TermId> {
        use oxiz_core::TermKind;

        let mut witnesses = HashMap::new();

        for (var_name, _sort) in existential_vars {
            // Search for the variable term in the model
            for (&term_id, &value) in model {
                if let Some(term) = terms.get(term_id) {
                    // Check if this is a variable with the matching name
                    if let TermKind::Var(name_spur) = &term.kind {
                        // Resolve the Spur to a string for comparison
                        if terms.resolve_str(*name_spur) == var_name {
                            witnesses.insert(var_name.clone(), value);
                            break;
                        }
                    }
                }
            }
        }

        witnesses
    }
}

/// Existential quantifier handler
pub struct ExistentialHandler {
    /// Skolem context
    skolem_ctx: SkolemContext,
    /// Cache of analyzed rules
    rule_cache: HashMap<usize, ExistentialInfo>,
}

impl ExistentialHandler {
    /// Create a new existential handler
    pub fn new() -> Self {
        Self {
            skolem_ctx: SkolemContext::new(),
            rule_cache: HashMap::new(),
        }
    }

    /// Analyze a rule for existentials
    pub fn analyze_rule(
        &mut self,
        rule_id: usize,
        rule: &Rule,
        terms: &TermManager,
    ) -> &ExistentialInfo {
        self.rule_cache
            .entry(rule_id)
            .or_insert_with(|| ExistentialInfo::analyze(rule, terms))
    }

    /// Preprocess a rule by eliminating existentials
    ///
    /// This function:
    /// 1. Identifies existential variables in the rule
    /// 2. Skolemizes them using fresh Skolem constants/functions
    /// 3. Returns a transformed rule with existentials replaced by Skolem terms
    pub fn preprocess_rule(
        &mut self,
        terms: &mut TermManager,
        _pred: PredId,
        rule: &Rule,
    ) -> ExistentialResult<Rule> {
        // Step 1: Analyze rule for existential variables
        // Clone the info to avoid borrow checker issues
        let info = self
            .analyze_rule(rule.id.raw() as usize, rule, terms)
            .clone();

        // If no existentials, return rule unchanged
        if !info.has_existentials || info.existential_vars.is_empty() {
            return Ok(rule.clone());
        }

        // Step 2: Skolemize existential variables
        // The universal variables are the free variables for Skolemization
        let mut skolem_substitution: HashMap<String, TermId> = HashMap::new();

        for (ex_var_name, ex_var_sort) in &info.existential_vars {
            let skolem_term = self.skolem_ctx.skolemize(
                terms,
                ex_var_name,
                *ex_var_sort,
                &info.universal_vars,
            )?;
            skolem_substitution.insert(ex_var_name.clone(), skolem_term);
        }

        // Step 3: Transform the rule by replacing every existential's
        // occurrence in the head with its Skolem term, and adding the
        // Skolem variables to the universal quantifiers.
        //
        // Existentials appear only in the head (per this module's own
        // documented contract), so only the head's predicate-application
        // arguments need rewriting -- the body never references them.
        let mut new_vars = rule.vars.clone();
        for (ex_var_name, ex_var_sort) in &info.existential_vars {
            if let Some(&skolem_term) = skolem_substitution.get(ex_var_name)
                && let Some(term) = terms.get(skolem_term)
                && let TermKind::Var(spur) = &term.kind
            {
                let name = terms.resolve_str(*spur);
                new_vars.push((name.to_string(), *ex_var_sort));
            }
        }

        let new_head = match &rule.head {
            RuleHead::Predicate(app) => {
                let new_args: SmallVec<[TermId; 4]> = app
                    .args
                    .iter()
                    .map(|&arg| {
                        // Replace an argument only if it's itself a plain
                        // variable matching one of the existentials this
                        // rule was just Skolemized for; every other
                        // argument (a universal variable, or any compound
                        // term) passes through unchanged.
                        let Some(term) = terms.get(arg) else {
                            return arg;
                        };
                        let TermKind::Var(name_spur) = &term.kind else {
                            return arg;
                        };
                        let name = terms.resolve_str(*name_spur);
                        skolem_substitution.get(name).copied().unwrap_or(arg)
                    })
                    .collect();
                RuleHead::Predicate(PredicateApp {
                    pred: app.pred,
                    args: new_args,
                })
            }
            RuleHead::Query => RuleHead::Query,
        };

        let transformed_rule = Rule {
            id: rule.id,
            vars: new_vars,
            body: rule.body.clone(),
            head: new_head,
            name: rule.name.clone(),
        };

        Ok(transformed_rule)
    }

    /// Get Skolem context
    pub fn skolem_context(&self) -> &SkolemContext {
        &self.skolem_ctx
    }

    /// Get Skolem context (mutable)
    pub fn skolem_context_mut(&mut self) -> &mut SkolemContext {
        &mut self.skolem_ctx
    }
}

impl Default for ExistentialHandler {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_skolem_context_fresh_names() {
        let mut ctx = SkolemContext::new();

        let name1 = ctx.fresh_skolem_name("x");
        let name2 = ctx.fresh_skolem_name("x");
        let name3 = ctx.fresh_skolem_name("y");

        assert_eq!(name1, "sk_x_0");
        assert_eq!(name2, "sk_x_1");
        assert_eq!(name3, "sk_y_2");
    }

    #[test]
    fn test_existential_info_no_existentials() {
        let info = ExistentialInfo {
            existential_vars: SmallVec::new(),
            universal_vars: vec![("x".to_string(), SortId(0))].into(),
            has_existentials: false,
        };

        assert_eq!(info.num_existentials(), 0);
        assert!(!info.has_existentials);
    }

    #[test]
    fn test_existential_info_with_existentials() {
        let info = ExistentialInfo {
            existential_vars: vec![("y1".to_string(), SortId(1)), ("y2".to_string(), SortId(1))]
                .into(),
            universal_vars: vec![("x".to_string(), SortId(0))].into(),
            has_existentials: true,
        };

        assert_eq!(info.num_existentials(), 2);
        assert!(info.has_existentials);
    }

    // -----------------------------------------------------------------------
    // Regression tests for the `sweep-backend-misc` triage sweep:
    // `ExistentialInfo::analyze` used to leave `existential_vars` always
    // empty (an unpopulated `SmallVec::new()`), so it was structurally
    // impossible for `ExistentialHandler::preprocess_rule` to ever
    // actually Skolemize anything, regardless of `has_existentials`.
    // -----------------------------------------------------------------------

    /// Build a rule whose head references one declared universal
    /// variable (`univ_x`) and one variable that is *not* declared in
    /// `vars` (`exist_y`) -- exactly the shape of a genuine existential.
    fn build_existential_rule() -> (
        TermManager,
        crate::chc::ChcSystem,
        crate::chc::RuleId,
        TermId,
        TermId,
    ) {
        let mut terms = TermManager::new();
        let mut system = crate::chc::ChcSystem::new();
        let pred =
            system.declare_predicate("ExistInv", [terms.sorts.int_sort, terms.sorts.int_sort]);

        let x = terms.mk_var("univ_x", terms.sorts.int_sort);
        let y = terms.mk_var("exist_y", terms.sorts.int_sort);
        let true_term = terms.mk_true();

        let rule_id = system.add_init_rule(
            [("univ_x".to_string(), terms.sorts.int_sort)],
            true_term,
            pred,
            [x, y],
        );

        (terms, system, rule_id, x, y)
    }

    #[test]
    fn test_analyze_populates_existential_vars_from_head() {
        let (terms, system, rule_id, _x, _y) = build_existential_rule();
        let rule = system.get_rule(rule_id).expect("rule must exist");

        let info = ExistentialInfo::analyze(rule, &terms);

        assert!(
            info.has_existentials,
            "a head argument absent from `vars` must be flagged existential"
        );
        assert_eq!(
            info.num_existentials(),
            1,
            "exactly one head argument (exist_y) is undeclared"
        );
        assert_eq!(info.existential_vars[0].0, "exist_y");

        // The declared universal `univ_x` must NOT be misclassified as
        // existential.
        assert!(
            !info
                .existential_vars
                .iter()
                .any(|(name, _)| name == "univ_x")
        );
    }

    #[test]
    fn test_preprocess_rule_applies_skolem_substitution_to_head() {
        let (mut terms, system, rule_id, x, y) = build_existential_rule();
        let rule = system.get_rule(rule_id).expect("rule must exist").clone();
        let pred = rule
            .head
            .as_predicate()
            .expect("head is a predicate application")
            .pred;

        let mut handler = ExistentialHandler::new();
        let transformed = handler
            .preprocess_rule(&mut terms, pred, &rule)
            .expect("preprocessing should not error");

        let RuleHead::Predicate(app) = &transformed.head else {
            panic!("transformed head must still be a predicate application");
        };

        // The universal argument (x) must be left untouched...
        assert_eq!(
            app.args[0], x,
            "a declared universal variable must not be rewritten"
        );
        // ...but the existential argument (y) must have been replaced by
        // a genuinely different (Skolem) term -- this is the exact
        // substitution the old code's own comment admitted never
        // happened ("we would also need to apply the substitution to
        // the rule body and head constraints/arguments").
        assert_ne!(
            app.args[1], y,
            "the existential argument must be replaced by its Skolem term, \
             not left as the original (unbound, out-of-scope) variable"
        );

        let skolem_term = terms.get(app.args[1]).expect("skolem term must exist");
        let TermKind::Var(spur) = &skolem_term.kind else {
            panic!("skolem term must be a variable");
        };
        let skolem_name = terms.resolve_str(*spur).to_string();
        assert!(
            skolem_name.starts_with("sk_exist_y"),
            "expected a Skolem name derived from exist_y, got {skolem_name:?}"
        );

        // The Skolem variable must be declared in the transformed rule's
        // universal variables so the rule remains well-formed (every
        // variable referenced in head/body is declared).
        assert!(
            transformed
                .vars
                .iter()
                .any(|(name, _)| *name == skolem_name),
            "the Skolem variable must be added to the transformed rule's \
             declared variables"
        );
    }
}
