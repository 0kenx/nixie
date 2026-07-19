//! Model Completion
//!
//! Completes partial models with default values for undefined terms.

use super::{Model, ValueFactory};
use crate::ast::{TermId, TermKind, TermManager};
use crate::prelude::HashSet;
#[allow(unused_imports)]
use crate::prelude::*;

/// Configuration for model completion
#[derive(Debug, Clone)]
pub struct ModelCompletionConfig {
    /// Use minimal values (0, false, etc.)
    pub use_minimal: bool,
    /// Complete function applications
    pub complete_functions: bool,
    /// Complete array defaults
    pub complete_arrays: bool,
}

impl Default for ModelCompletionConfig {
    fn default() -> Self {
        Self {
            use_minimal: true,
            complete_functions: true,
            complete_arrays: true,
        }
    }
}

/// Model completion utility
#[derive(Debug)]
pub struct ModelCompletion {
    config: ModelCompletionConfig,
    factory: ValueFactory,
    completed: HashSet<TermId>,
}

impl ModelCompletion {
    /// Create a new model completion utility
    pub fn new() -> Self {
        Self {
            config: ModelCompletionConfig::default(),
            factory: ValueFactory::new(),
            completed: HashSet::new(),
        }
    }

    /// Create with custom configuration
    pub fn with_config(config: ModelCompletionConfig) -> Self {
        Self {
            config,
            factory: ValueFactory::new(),
            completed: HashSet::new(),
        }
    }

    /// Get the configuration
    pub fn config(&self) -> &ModelCompletionConfig {
        &self.config
    }

    /// Complete a model by assigning default values to undefined terms
    pub fn complete(&mut self, model: &mut Model, terms: &[TermId], manager: &TermManager) {
        self.completed.clear();

        for &term in terms {
            if !model.has(term) && !self.completed.contains(&term) {
                self.complete_term(model, term, manager);
            }
        }
    }

    /// Complete a single term with a default value
    fn complete_term(&mut self, model: &mut Model, term: TermId, manager: &TermManager) {
        if self.completed.contains(&term) || model.has(term) {
            return;
        }

        self.completed.insert(term);

        // Use the term's *actual* sort (`Term::sort`, assigned correctly
        // at construction time by `TermManager`/`SortManager`) rather than
        // re-deriving a guess from the term's `TermKind`. The previous
        // `infer_sort` helper matched only a handful of `TermKind`
        // variants against hardcoded sort-id constants (`SortId(5)` for
        // any bitvector op, `SortId(100)` as a catch-all "uninterpreted"
        // fallback) that do not correspond to how sorts are actually
        // interned (bitvector/array/uninterpreted sorts get whatever id
        // they happened to be interned under, not a fixed magic number).
        // It also had no arm for `TermKind::Var(_)` at all, so every
        // variable completed via `complete_variables` silently fell
        // through to the wrong `SortId(100)` default — assigning it an
        // essentially arbitrary uninterpreted value regardless of its real
        // declared sort (Bool, Int, BitVec, ...).
        if let Some(t) = manager.get(term) {
            let value = self.factory.default_value(t.sort);
            model.assign(term, value);
        }
    }

    /// Complete all variables in a formula
    pub fn complete_variables(&mut self, model: &mut Model, root: TermId, manager: &TermManager) {
        let mut visited = HashSet::new();
        let mut worklist = vec![root];

        while let Some(term) = worklist.pop() {
            if visited.contains(&term) {
                continue;
            }
            visited.insert(term);

            if let Some(t) = manager.get(term) {
                match &t.kind {
                    TermKind::Var(_) => {
                        if !model.has(term) {
                            self.complete_term(model, term, manager);
                        }
                    }
                    _ => {
                        // Add children to worklist based on term kind
                        self.add_children(&t.kind, &mut worklist);
                    }
                }
            }
        }
    }

    /// Add children of a term kind to the worklist
    fn add_children(&self, kind: &TermKind, worklist: &mut Vec<TermId>) {
        match kind {
            TermKind::Not(a) | TermKind::Neg(a) | TermKind::BvNot(a) => {
                worklist.push(*a);
            }
            TermKind::And(args)
            | TermKind::Or(args)
            | TermKind::Add(args)
            | TermKind::Mul(args)
            | TermKind::Distinct(args) => {
                for arg in args.iter() {
                    worklist.push(*arg);
                }
            }
            TermKind::Xor(a, b)
            | TermKind::Implies(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Sub(a, b)
            | TermKind::Div(a, b)
            | TermKind::Mod(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Le(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::BvAnd(a, b)
            | TermKind::BvOr(a, b)
            | TermKind::BvXor(a, b)
            | TermKind::BvAdd(a, b)
            | TermKind::BvSub(a, b)
            | TermKind::BvMul(a, b)
            | TermKind::BvConcat(a, b) => {
                worklist.push(*a);
                worklist.push(*b);
            }
            TermKind::Ite(a, b, c) => {
                worklist.push(*a);
                worklist.push(*b);
                worklist.push(*c);
            }
            _ => {}
        }
    }

    /// Reset completion state
    pub fn reset(&mut self) {
        self.completed.clear();
    }

    /// Number of terms completed
    pub fn num_completed(&self) -> usize {
        self.completed.len()
    }
}

impl Default for ModelCompletion {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_completion_config() {
        let config = ModelCompletionConfig::default();
        assert!(config.use_minimal);
        assert!(config.complete_functions);
        assert!(config.complete_arrays);
    }

    #[test]
    fn test_completion_creation() {
        let completion = ModelCompletion::new();
        assert_eq!(completion.num_completed(), 0);
    }

    #[test]
    fn test_completion_reset() {
        let mut completion = ModelCompletion::new();
        completion.completed.insert(TermId::from(1u32));
        assert_eq!(completion.num_completed(), 1);

        completion.reset();
        assert_eq!(completion.num_completed(), 0);
    }
}
