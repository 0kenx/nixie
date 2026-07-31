//! Model Completion
//!
//! Completes partial models with default values for undefined terms.

use super::{Model, ValueFactory, ValueFactoryConfig};
use crate::ast::traversal::get_children;
use crate::ast::{TermId, TermKind, TermManager};
use crate::prelude::HashSet;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortKind;

/// Configuration for model completion
#[derive(Debug, Clone)]
pub struct ModelCompletionConfig {
    /// Use minimal values (0, false, etc.) rather than the alternate
    /// "maximal" ones (1, true, ...). Drives the internal [`ValueFactory`]'s
    /// [`ValueFactoryConfig::zero_numerics`].
    pub use_minimal: bool,
    /// Whether to assign a default value to an unassigned uninterpreted
    /// function application (a [`crate::ast::TermKind::Apply`] term — this
    /// also covers the regex sublanguage, which lowers to `Apply` under the
    /// hood; see `TermManager::mk_regex_op`). When `false`, such terms are
    /// left unassigned and recorded in [`ModelCompletion::incomplete_terms`]
    /// instead.
    pub complete_functions: bool,
    /// Whether to assign a default value to an unassigned Array-sorted term.
    /// When `false`, such terms are left unassigned and recorded in
    /// [`ModelCompletion::incomplete_terms`] instead.
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
    /// Terms `complete`/`complete_variables` attempted but could not assign a
    /// value to, either because their sort has no sound default
    /// ([`ValueFactory::default_value`] returned `None` — an unresolved sort
    /// parameter or a datatype sort) or because `complete_functions` /
    /// `complete_arrays` deliberately excluded them. Reset by [`Self::reset`].
    incomplete: HashSet<TermId>,
}

impl ModelCompletion {
    /// Create a new model completion utility
    pub fn new() -> Self {
        Self::with_config(ModelCompletionConfig::default())
    }

    /// Create with custom configuration
    pub fn with_config(config: ModelCompletionConfig) -> Self {
        // `use_minimal` used to be stored and never read; it now drives the
        // internal factory's `zero_numerics`, exactly the knob it names.
        let factory_config = ValueFactoryConfig {
            zero_numerics: config.use_minimal,
            ..ValueFactoryConfig::default()
        };
        Self {
            config,
            factory: ValueFactory::with_config(factory_config),
            completed: HashSet::new(),
            incomplete: HashSet::new(),
        }
    }

    /// Get the configuration
    pub fn config(&self) -> &ModelCompletionConfig {
        &self.config
    }

    /// Terms that could not be (or, per `complete_functions` /
    /// `complete_arrays`, deliberately were not) assigned a default value by
    /// the most recent `complete` / `complete_variables` run.
    pub fn incomplete_terms(&self) -> impl Iterator<Item = TermId> + '_ {
        self.incomplete.iter().copied()
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
        let Some(t) = manager.get(term) else {
            self.incomplete.insert(term);
            return;
        };

        // `complete_functions` / `complete_arrays` used to be stored and
        // never read: any config value produced identical behaviour. Both
        // now decide *whether* to default this term at all, before asking
        // `ValueFactory` *what* the default should be.
        if matches!(t.kind, TermKind::Apply { .. }) && !self.config.complete_functions {
            self.incomplete.insert(term);
            return;
        }
        let is_array_sort = matches!(
            manager.sorts.get(t.sort).map(|s| &s.kind),
            Some(SortKind::Array { .. })
        );
        if is_array_sort && !self.config.complete_arrays {
            self.incomplete.insert(term);
            return;
        }

        match self.factory.default_value(t.sort, &manager.sorts) {
            Some(value) => {
                model.assign(term, value);
            }
            // Genuinely cannot be defaulted (e.g. a datatype or unresolved
            // sort-parameter sort) — leave it unassigned rather than
            // fabricate a plausible-looking wrong value.
            None => {
                self.incomplete.insert(term);
            }
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

    /// Add children of a term kind to the worklist.
    ///
    /// Delegates to the crate's single [`get_children`] definition, which
    /// matches every [`TermKind`] variant exhaustively. This function used to
    /// carry its own partial match with a `_ => {}` catch-all covering roughly
    /// twenty of the ~110 variants: every other kind — `Select`/`Store`,
    /// `Apply`, `Concat` and the rest of the string ops, all of the
    /// floating-point ops, quantifier bodies, datatype constructors and
    /// selectors — reported *no children at all*, so `complete_variables`
    /// silently never reached the variables underneath them and left them
    /// unassigned in the completed model. Adding a `TermKind` variant is now a
    /// compile error in one place instead of a silent gap here.
    fn add_children(&self, kind: &TermKind, worklist: &mut Vec<TermId>) {
        worklist.extend(get_children(kind));
    }

    /// Reset completion state
    pub fn reset(&mut self) {
        self.completed.clear();
        self.incomplete.clear();
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
    use crate::model::Value;

    /// `add_children` used to carry a partial `TermKind` match with a
    /// `_ => {}` catch-all, so a variable underneath a `Select` (or a
    /// `Store`, `Apply`, string op, FP op, quantifier body, datatype node,
    /// ...) was never reached and silently stayed unassigned in the
    /// "completed" model. It now delegates to the exhaustive `get_children`.
    #[test]
    fn complete_variables_reaches_variables_under_a_select() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let array_sort = manager.sorts.array(int_sort, int_sort);
        let arr = manager.mk_var("a", array_sort);
        let idx = manager.mk_var("i", int_sort);
        let select = manager.mk_select(arr, idx);

        let mut model = Model::new();
        let mut completion = ModelCompletion::new();
        completion.complete_variables(&mut model, select, &manager);

        assert!(
            model.has(idx),
            "the index variable under a Select must be completed"
        );
        assert!(
            model.has(arr),
            "the array variable under a Select must be completed"
        );
    }

    /// Semantic pin for the shapes the old partial match already covered.
    #[test]
    fn complete_variables_still_reaches_variables_under_a_conjunction() {
        let mut manager = TermManager::new();
        let bool_sort = manager.sorts.bool_sort;
        let p = manager.mk_var("p", bool_sort);
        let q = manager.mk_var("q", bool_sort);
        let conj = manager.mk_and(vec![p, q]);

        let mut model = Model::new();
        let mut completion = ModelCompletion::new();
        completion.complete_variables(&mut model, conj, &manager);

        assert_eq!(model.get(p), Some(&Value::Bool(false)));
        assert_eq!(model.get(q), Some(&Value::Bool(false)));
    }

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

    // ── Item 3: Array completion + `complete_arrays` / `complete_functions`
    // / `use_minimal` actually driving behaviour ─────────────────────────

    /// `ValueFactory::default_value`'s new `Array` arm (see `factory.rs`)
    /// makes an Array-sorted term completable end to end: `complete` used to
    /// have no way to produce `Value::Array` at all, so `select`/`store` on a
    /// completed model always errored with `"Select: expected array"`.
    #[test]
    fn test_complete_assigns_array_default_value() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let arr_sort = manager.sorts.array(int_sort, int_sort);
        let a = manager.mk_var("a", arr_sort);

        let mut model = Model::new();
        let mut completion = ModelCompletion::new();
        completion.complete(&mut model, &[a], &manager);

        match model.get(a) {
            Some(Value::Array(default, exceptions)) => {
                assert_eq!(**default, Value::Int(0));
                assert!(exceptions.is_empty());
            }
            other => panic!("expected Some(Value::Array(..)), got {other:?}"),
        }
        assert_eq!(completion.incomplete_terms().count(), 0);
    }

    /// `complete_arrays` was declared and never read: any value produced the
    /// same behaviour. It must now actually gate Array-sorted completion.
    #[test]
    fn test_complete_arrays_false_leaves_array_terms_unassigned() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let arr_sort = manager.sorts.array(int_sort, int_sort);
        let a = manager.mk_var("a", arr_sort);

        let mut model = Model::new();
        let mut completion = ModelCompletion::with_config(ModelCompletionConfig {
            complete_arrays: false,
            ..ModelCompletionConfig::default()
        });
        completion.complete(&mut model, &[a], &manager);

        assert!(
            !model.has(a),
            "complete_arrays: false must leave the term unassigned"
        );
        assert!(completion.incomplete_terms().any(|t| t == a));

        // A non-Array sort in the same batch is unaffected by the flag.
        let x = manager.mk_var("x", int_sort);
        completion.complete(&mut model, &[x], &manager);
        assert_eq!(model.get(x), Some(&Value::Int(0)));
    }

    /// Same defect, same fix, for `complete_functions`: it must gate whether
    /// an unassigned `Apply` (uninterpreted function application, or a
    /// regex-lowered term) gets defaulted.
    #[test]
    fn test_complete_functions_false_leaves_apply_terms_unassigned() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let f_x = manager.mk_apply("f", [x], int_sort);

        let mut model = Model::new();
        let mut completion = ModelCompletion::with_config(ModelCompletionConfig {
            complete_functions: false,
            ..ModelCompletionConfig::default()
        });
        completion.complete(&mut model, &[f_x], &manager);

        assert!(!model.has(f_x));
        assert!(completion.incomplete_terms().any(|t| t == f_x));
    }

    /// `use_minimal` was declared and never read; it must now thread into the
    /// internal `ValueFactory`'s `zero_numerics`.
    #[test]
    fn test_use_minimal_false_threads_into_value_factory() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);

        let mut model = Model::new();
        let mut completion = ModelCompletion::with_config(ModelCompletionConfig {
            use_minimal: false,
            ..ModelCompletionConfig::default()
        });
        completion.complete(&mut model, &[x], &manager);

        assert_eq!(model.get(x), Some(&Value::Int(1)));
    }

    /// A sort `ValueFactory::default_value` genuinely cannot default (here, a
    /// datatype sort) must leave the term unassigned and recorded in
    /// `incomplete_terms`, never panic and never fabricate a value.
    #[test]
    fn test_complete_records_incomplete_for_undefaultable_sort() {
        let mut manager = TermManager::new();
        let red = crate::sort::DataTypeConstructor {
            name: manager.sorts.intern_str("red"),
            selectors: smallvec::SmallVec::new(),
        };
        manager.sorts.declare_datatype("Color", vec![red]);
        let color_sort = manager.sorts.mk_datatype_sort("Color");
        let c = manager.mk_var("c", color_sort);

        let mut model = Model::new();
        let mut completion = ModelCompletion::new();
        completion.complete(&mut model, &[c], &manager);

        assert!(!model.has(c));
        assert!(completion.incomplete_terms().any(|t| t == c));
    }
}
