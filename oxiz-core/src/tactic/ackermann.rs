//! Ackermannization tactic for removing uninterpreted functions.

use super::core::*;
use crate::ast::{TermId, TermManager};
use crate::error::Result;
#[allow(unused_imports)]
use crate::prelude::*;

/// Ackermannization tactic - removes uninterpreted functions
pub struct AckermannizeTactic<'a> {
    manager: &'a mut TermManager,
}

/// A function application occurrence
#[derive(Debug, Clone)]
struct FuncApp {
    /// Fresh variable representing this application
    fresh_var: TermId,
    /// The arguments
    args: smallvec::SmallVec<[TermId; 4]>,
}

impl<'a> AckermannizeTactic<'a> {
    /// Create a new ackermannize tactic
    pub fn new(manager: &'a mut TermManager) -> Self {
        Self { manager }
    }

    /// Collect all function applications from a term.
    ///
    /// # Soundness: quantifier-bound arguments
    ///
    /// Ackermannization replaces every application `f(a)` by a *ground* fresh
    /// variable and adds ground functional-consistency constraints
    /// `a = b => v_a = v_b`. That is only sound when the arguments `a` are
    /// themselves ground: an application `f(x)` whose argument `x` is bound by
    /// an enclosing `forall`/`exists` denotes a *different* value for each
    /// binding of `x`, so collapsing it into one ground variable (and adding
    /// ground congruence constraints) is unsound.
    ///
    /// We therefore track the set of binder names in scope (`bound`) while
    /// descending. An application whose arguments reference any in-scope bound
    /// variable is **not** collected; instead its function symbol is recorded
    /// in `tainted`. The caller then drops *every* application of a tainted
    /// symbol — even its ground occurrences — because Ackermannizing only some
    /// occurrences of `f` while leaving quantified ones as real `f` would
    /// decouple the fresh variables from `f` (the linking constraint
    /// `v_a = f(a)` is absent), again unsoundly. If nothing survives, the
    /// tactic is `NotApplicable`.
    ///
    /// Reference: Z3's `ackermannize_bv_tactic` / `ackr_helper` only collect
    /// ground applications.
    fn collect_func_apps(
        &self,
        term_id: TermId,
        bound: &mut Vec<crate::interner::Spur>,
        apps: &mut Vec<(
            crate::interner::Spur,
            smallvec::SmallVec<[TermId; 4]>,
            TermId,
        )>,
        tainted: &mut crate::prelude::FxHashSet<crate::interner::Spur>,
        visited: &mut crate::prelude::FxHashSet<TermId>,
    ) {
        use crate::ast::TermKind;

        if visited.contains(&term_id) {
            return;
        }
        visited.insert(term_id);

        if let Some(term) = self.manager.get(term_id) {
            match &term.kind {
                TermKind::Apply { func, args } => {
                    let refs_bound = !bound.is_empty()
                        && args.iter().any(|&a| self.references_bound_var(a, bound));
                    if refs_bound {
                        // Quantified occurrence: exclude this symbol entirely.
                        tainted.insert(*func);
                    } else {
                        apps.push((*func, args.clone(), term_id));
                    }
                    for &arg in args {
                        self.collect_func_apps(arg, bound, apps, tainted, visited);
                    }
                }
                TermKind::Not(a) | TermKind::Neg(a) | TermKind::BvNot(a) => {
                    self.collect_func_apps(*a, bound, apps, tainted, visited);
                }
                TermKind::BvExtract { arg, .. } => {
                    self.collect_func_apps(*arg, bound, apps, tainted, visited);
                }
                TermKind::And(args)
                | TermKind::Or(args)
                | TermKind::Add(args)
                | TermKind::Mul(args)
                | TermKind::Distinct(args) => {
                    for &arg in args {
                        self.collect_func_apps(arg, bound, apps, tainted, visited);
                    }
                }
                TermKind::Implies(a, b)
                | TermKind::Xor(a, b)
                | TermKind::Eq(a, b)
                | TermKind::Sub(a, b)
                | TermKind::Div(a, b)
                | TermKind::Mod(a, b)
                | TermKind::Lt(a, b)
                | TermKind::Le(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Ge(a, b)
                | TermKind::Select(a, b)
                | TermKind::BvConcat(a, b)
                | TermKind::BvAnd(a, b)
                | TermKind::BvOr(a, b)
                | TermKind::BvXor(a, b)
                | TermKind::BvAdd(a, b)
                | TermKind::BvSub(a, b)
                | TermKind::BvMul(a, b)
                | TermKind::BvUdiv(a, b)
                | TermKind::BvSdiv(a, b)
                | TermKind::BvUrem(a, b)
                | TermKind::BvSrem(a, b)
                | TermKind::BvShl(a, b)
                | TermKind::BvLshr(a, b)
                | TermKind::BvAshr(a, b)
                | TermKind::BvUlt(a, b)
                | TermKind::BvUle(a, b)
                | TermKind::BvSlt(a, b)
                | TermKind::BvSle(a, b) => {
                    self.collect_func_apps(*a, bound, apps, tainted, visited);
                    self.collect_func_apps(*b, bound, apps, tainted, visited);
                }
                TermKind::Ite(c, t, e) | TermKind::Store(c, t, e) => {
                    self.collect_func_apps(*c, bound, apps, tainted, visited);
                    self.collect_func_apps(*t, bound, apps, tainted, visited);
                    self.collect_func_apps(*e, bound, apps, tainted, visited);
                }
                TermKind::Forall { vars, body, .. } | TermKind::Exists { vars, body, .. } => {
                    let pushed = vars.len();
                    for (name, _) in vars.iter() {
                        bound.push(*name);
                    }
                    let body = *body;
                    self.collect_func_apps(body, bound, apps, tainted, visited);
                    bound.truncate(bound.len() - pushed);
                }
                TermKind::Let { bindings, body } => {
                    let bindings = bindings.clone();
                    let body = *body;
                    for (_, t) in &bindings {
                        self.collect_func_apps(*t, bound, apps, tainted, visited);
                    }
                    self.collect_func_apps(body, bound, apps, tainted, visited);
                }
                // Constants and variables don't contain function applications
                _ => {}
            }
        }
    }

    /// Whether `term` references any variable name in `bound` (the set of
    /// quantifier-bound names currently in scope). Used to detect
    /// applications that depend on bound variables — see
    /// [`Self::collect_func_apps`].
    fn references_bound_var(&self, term: TermId, bound: &[crate::interner::Spur]) -> bool {
        use crate::ast::TermKind;
        use crate::ast::traversal::collect_subterms;

        // `collect_subterms` walks the whole (hash-consed) subterm DAG once;
        // we then check whether any `Var` node's name is bound.
        for sub in collect_subterms(term, self.manager) {
            if let Some(t) = self.manager.get(sub)
                && let TermKind::Var(name) = &t.kind
                && bound.contains(name)
            {
                return true;
            }
        }
        false
    }

    /// Apply ackermannization to a goal.
    pub fn apply_mut(&mut self, goal: &Goal) -> Result<TacticResult> {
        Ok(self.apply_mut_with_converter(goal)?.0)
    }

    /// Apply ackermannization to a goal, additionally returning a
    /// [`ModelConverter`] that lifts a model of the transformed sub-goal back
    /// to a model over the original goal's variables (dropping the fresh
    /// Ackermann variables that are not part of the original signature).
    ///
    /// Returns `(TacticResult, None)` when the result is not a `SubGoals`
    /// transformation (nothing was eliminated), and `(SubGoals, Some(conv))`
    /// otherwise.
    pub fn apply_mut_with_converter(
        &mut self,
        goal: &Goal,
    ) -> Result<(TacticResult, Option<Box<dyn ModelConverter>>)> {
        use crate::prelude::{FxHashMap, FxHashSet};

        // Collect ground function applications, tracking symbols with any
        // quantifier-bound-argument occurrence (see `collect_func_apps`).
        let mut all_apps: Vec<(
            crate::interner::Spur,
            smallvec::SmallVec<[TermId; 4]>,
            TermId,
        )> = Vec::new();
        let mut tainted: FxHashSet<crate::interner::Spur> = FxHashSet::default();
        let mut bound: Vec<crate::interner::Spur> = Vec::new();
        let mut visited = FxHashSet::default();

        for &assertion in &goal.assertions {
            self.collect_func_apps(
                assertion,
                &mut bound,
                &mut all_apps,
                &mut tainted,
                &mut visited,
            );
        }

        // Drop every application of a symbol that had a quantified
        // (bound-variable-dependent) occurrence — Ackermannizing it would be
        // unsound.
        if !tainted.is_empty() {
            all_apps.retain(|(func, _, _)| !tainted.contains(func));
        }

        // No (ground) function applications left to eliminate.
        if all_apps.is_empty() {
            return Ok((TacticResult::NotApplicable, None));
        }

        // Group applications by function symbol
        let mut func_groups: FxHashMap<crate::interner::Spur, Vec<FuncApp>> = FxHashMap::default();
        let mut term_to_var: FxHashMap<TermId, TermId> = FxHashMap::default();
        let mut fresh_vars: FxHashSet<TermId> = FxHashSet::default();

        for (var_counter, (func, args, term_id)) in all_apps.into_iter().enumerate() {
            // Create a fresh variable for this application
            let Some(term) = self.manager.get(term_id) else {
                continue; // Skip if term not found
            };
            let sort = term.sort;
            let var_name = format!("!ack_{}", var_counter);
            let fresh_var = self.manager.mk_var(&var_name, sort);

            term_to_var.insert(term_id, fresh_var);
            fresh_vars.insert(fresh_var);

            func_groups
                .entry(func)
                .or_default()
                .push(FuncApp { fresh_var, args });
        }

        // Generate functional consistency constraints
        // For each pair of applications of the same function:
        // (a1 = b1 ∧ ... ∧ an = bn) => (f(a) = f(b))
        let mut constraints: Vec<TermId> = Vec::new();

        for apps in func_groups.values() {
            for i in 0..apps.len() {
                for j in (i + 1)..apps.len() {
                    let app_i = &apps[i];
                    let app_j = &apps[j];

                    // Only compare if they have the same arity
                    if app_i.args.len() != app_j.args.len() {
                        continue;
                    }

                    // Build: (a1 = b1) ∧ (a2 = b2) ∧ ... => (var_i = var_j)
                    let mut arg_eqs: Vec<TermId> = Vec::new();
                    for k in 0..app_i.args.len() {
                        let eq = self.manager.mk_eq(app_i.args[k], app_j.args[k]);
                        arg_eqs.push(eq);
                    }

                    let antecedent = if arg_eqs.len() == 1 {
                        arg_eqs[0]
                    } else {
                        self.manager.mk_and(arg_eqs)
                    };

                    let consequent = self.manager.mk_eq(app_i.fresh_var, app_j.fresh_var);
                    let constraint = self.manager.mk_implies(antecedent, consequent);
                    constraints.push(constraint);
                }
            }
        }

        // Substitute function applications with their fresh variables in the goal
        let mut new_assertions: Vec<TermId> = Vec::new();

        for &assertion in &goal.assertions {
            let substituted = self.manager.substitute(assertion, &term_to_var);
            new_assertions.push(substituted);
        }

        // Add the functional consistency constraints
        new_assertions.extend(constraints);

        let converter: Box<dyn ModelConverter> = Box::new(AckermannModelConverter { fresh_vars });

        Ok((
            TacticResult::SubGoals(vec![Goal {
                assertions: new_assertions,
                precision: goal.precision,
            }]),
            Some(converter),
        ))
    }
}

/// Model converter for [`AckermannizeTactic`].
///
/// Ackermannization introduces fresh `!ack_k` variables that replace ground
/// function applications; these are *not* part of the original goal's
/// signature. Given a model of the transformed sub-goal, this converter
/// projects those fresh variables out, returning a model over the original
/// variables. (The eliminated function symbols' interpretations are
/// recoverable from the projected-out fresh-variable values — each fresh
/// variable is exactly the value of its application — but a function table is
/// not representable in the variable-only [`TacticModel`], so it is not
/// reconstructed here.)
#[derive(Debug, Clone)]
struct AckermannModelConverter {
    fresh_vars: crate::prelude::FxHashSet<TermId>,
}

impl ModelConverter for AckermannModelConverter {
    fn convert(&self, model: &TacticModel, _manager: &mut TermManager) -> TacticModel {
        let mut out = TacticModel::new();
        for (&var, &value) in &model.values {
            if !self.fresh_vars.contains(&var) {
                out.set(var, value);
            }
        }
        out
    }
}

/// Stateless version for the Tactic trait
#[derive(Debug, Default)]
pub struct StatelessAckermannizeTactic;

impl Tactic for StatelessAckermannizeTactic {
    fn name(&self) -> &str {
        "ackermannize"
    }

    fn apply(&self, _goal: &Goal) -> Result<TacticResult> {
        // Ackermannization must allocate fresh variables and congruence
        // constraints, which requires `&mut TermManager` access that the
        // manager-free `Tactic::apply` signature does not provide. Rather
        // than silently return the goal unchanged (which would dishonestly
        // claim a successful transformation), report that this path does not
        // apply. Callers holding a `&mut TermManager` should use
        // `AckermannizeTactic::apply_mut` (or the registry's `create_managed`
        // path) for the real transformation.
        Ok(TacticResult::NotApplicable)
    }

    fn description(&self) -> &str {
        "Eliminates uninterpreted functions by adding functional consistency constraints \
         (requires a TermManager; the manager-free path is NotApplicable)"
    }
}
