//! A selector or a tester applied to a datatype **constructor application**,
//! decided at construction (`#P2b-82`, re-fix pass 16).
//!
//! Datatypes are free (SMT-LIB 2.6 §4.2.3): `(hd (cons a b))` is `a` and
//! `((_ is cons) (cons a b))` is `true` in every model, `((_ is nil) (cons a
//! b))` is `false`.  Only a selector of the constructor that built the value
//! is determined; `(hd nil)` is left alone — SMT-LIB leaves it unspecified.
//!
//! Folding in the builder reaches selectors nested inside other applications.
//! Substitution uses the same entry points; `fold_constructor_accessors` also
//! normalizes existing terms in a bottom-up heap traversal.
//!
//! Declaration keys belong to the sort manager; AST keys belong to the term
//! manager. Compare their resolved names, never numeric keys from different
//! interners. `TermManager::declare_datatype` normalizes term-key declarations
//! at the API boundary; `SortManager::declare_datatype` takes sort-local keys.

use super::super::term::{TermId, TermKind};
use super::super::traversal::get_children;
use super::TermManager;
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::SortId;

impl TermManager {
    /// `(selector arg)` of sort `result_sort`, folded to the field when `arg`
    /// is an application of the constructor `selector` belongs to.
    pub fn mk_dt_selector_spur(
        &mut self,
        selector: Spur,
        arg: TermId,
        result_sort: SortId,
    ) -> TermId {
        if let Some(lifted) = self.lift_over_dt_ite(arg, &mut |manager, branch| {
            manager.mk_dt_selector_leaf(selector, branch, result_sort)
        }) {
            return lifted;
        }
        self.mk_dt_selector_leaf(selector, arg, result_sort)
    }

    fn mk_dt_selector_leaf(&mut self, selector: Spur, arg: TermId, result_sort: SortId) -> TermId {
        if let Some(field) = self.selector_over_constructor(selector, arg, result_sort) {
            return field;
        }
        self.intern(TermKind::DtSelector { selector, arg }, result_sort)
    }

    /// `((_ is constructor) arg)`, folded to `true` / `false` when `arg` is an
    /// application of a constructor of the same datatype.
    pub fn mk_dt_tester_spur(&mut self, constructor: Spur, arg: TermId) -> TermId {
        if let Some(lifted) = self.lift_over_dt_ite(arg, &mut |manager, branch| {
            manager.mk_dt_tester_leaf(constructor, branch)
        }) {
            return lifted;
        }
        self.mk_dt_tester_leaf(constructor, arg)
    }

    fn mk_dt_tester_leaf(&mut self, constructor: Spur, arg: TermId) -> TermId {
        if let Some(holds) = self.tester_over_constructor(constructor, arg) {
            return self.mk_bool(holds);
        }
        self.intern(
            TermKind::DtTester { constructor, arg },
            self.sorts.bool_sort,
        )
    }

    /// Fold constructor selectors/testers throughout a term in one bottom-up
    /// traversal. Nested accessor chains have no native-stack or round limit.
    pub fn fold_constructor_accessors(&mut self, term: TermId) -> TermId {
        let mut stack = vec![(term, false)];
        let mut folded: FxHashMap<TermId, TermId> = FxHashMap::default();
        while let Some((current, expanded)) = stack.pop() {
            if folded.contains_key(&current) {
                continue;
            }
            let Some(node) = self.get(current).cloned() else {
                panic!("invalid term in constructor accessor rewrite: {current:?}");
            };
            if !expanded {
                stack.push((current, true));
                stack.extend(
                    get_children(&node.kind)
                        .into_iter()
                        .rev()
                        .map(|child| (child, false)),
                );
                continue;
            }
            let sub = |child| match folded.get(&child) {
                Some(&result) => result,
                None => panic!("missing constructor accessor rewrite child: {child:?}"),
            };
            // The rewrite is a context-independent identity, not a variable
            // substitution: binder names and lexical scopes stay unchanged.
            // Patterns are annotations, retained verbatim (as get_children does).
            let result = match node.kind {
                TermKind::Forall {
                    vars,
                    body,
                    patterns,
                } => self.intern(
                    TermKind::Forall {
                        vars,
                        body: sub(body),
                        patterns,
                    },
                    node.sort,
                ),
                TermKind::Exists {
                    vars,
                    body,
                    patterns,
                } => self.intern(
                    TermKind::Exists {
                        vars,
                        body: sub(body),
                        patterns,
                    },
                    node.sort,
                ),
                TermKind::Let { bindings, body } => self.intern(
                    TermKind::Let {
                        bindings: bindings
                            .into_iter()
                            .map(|(name, value)| (name, sub(value)))
                            .collect(),
                        body: sub(body),
                    },
                    node.sort,
                ),
                TermKind::Match {
                    scrutinee,
                    mut cases,
                } => {
                    for case in &mut cases {
                        case.body = sub(case.body);
                    }
                    self.intern(
                        TermKind::Match {
                            scrutinee: sub(scrutinee),
                            cases,
                        },
                        node.sort,
                    )
                }
                kind => self.rebuild_children_with(kind, node.sort, &sub),
            };
            folded.insert(current, result);
        }
        match folded.get(&term) {
            Some(&result) => result,
            None => panic!("missing constructor accessor rewrite root"),
        }
    }

    /// The field `selector` reads from the constructor application `arg`, or
    /// `None` when `arg` is not one, `selector` is not a selector of its
    /// constructor, or the field's sort is not `result_sort`.
    fn selector_over_constructor(
        &self,
        selector: Spur,
        arg: TermId,
        result_sort: SortId,
    ) -> Option<TermId> {
        let node = self.get(arg)?;
        let TermKind::DtConstructor { constructor, args } = &node.kind else {
            return None;
        };
        let name = self.sorts.datatype_name(node.sort)?;
        let def = self.sorts.get_datatype(name)?;
        let declared = def
            .constructors
            .iter()
            .find(|c| self.sorts.resolve_spur(c.name) == self.resolve_str(*constructor))?;
        if declared.selectors.len() != args.len() {
            return None;
        }
        let position = declared
            .selectors
            .iter()
            .position(|&(field, _)| self.sorts.resolve_spur(field) == self.resolve_str(selector))?;
        let field = *args.get(position)?;
        (self.get(field)?.sort == result_sort).then_some(field)
    }

    /// Whether the constructor application `arg` was built by `constructor`,
    /// or `None` when `arg` is not a constructor application or `constructor`
    /// is not a constructor of its datatype.
    fn tester_over_constructor(&self, constructor: Spur, arg: TermId) -> Option<bool> {
        let node = self.get(arg)?;
        let TermKind::DtConstructor {
            constructor: built, ..
        } = &node.kind
        else {
            return None;
        };
        let name = self.sorts.datatype_name(node.sort)?;
        let def = self.sorts.get_datatype(name)?;
        if !def
            .constructors
            .iter()
            .any(|c| self.sorts.resolve_spur(c.name) == self.resolve_str(constructor))
        {
            return None;
        }
        Some(*built == constructor)
    }
}

#[cfg(test)]
mod tests {
    use super::super::TermManager;
    use crate::ast::term::TermKind;
    #[allow(unused_imports)]
    use crate::prelude::*;
    use crate::sort::{DataTypeConstructor, SortId};
    use smallvec::smallvec;

    #[test]
    fn declaration_names_do_not_alias_term_interner_keys() {
        for term_local in [false, true] {
            let mut m = TermManager::new();
            for i in 0..32 {
                m.intern_str(&format!("padding{i}"));
            }
            let sort = m.sorts.mk_datatype_sort("Record");
            let int = m.sorts.int_sort;
            let (ctor, field) = if term_local {
                (m.intern_str("record"), m.intern_str("field"))
            } else {
                (m.sorts.intern_str("record"), m.sorts.intern_str("field"))
            };
            let decl = DataTypeConstructor {
                name: ctor,
                selectors: smallvec![(field, int)],
            };
            if term_local {
                m.declare_datatype("Record", vec![decl]);
            } else {
                m.sorts.declare_datatype("Record", vec![decl]);
            }
            let value = m.mk_int(42);
            let record = m.mk_dt_constructor("record", [value], sort);
            assert_eq!(m.mk_dt_selector("field", record, int), value);
            assert_eq!(m.mk_dt_tester("record", record), m.true_id);
            let stored = &m
                .sorts
                .get_datatype("Record")
                .expect("declaration")
                .constructors[0];
            assert_eq!(m.sorts.resolve_spur(stored.name), "record");
            assert_eq!(m.sorts.resolve_spur(stored.selectors[0].0), "field");
        }
    }

    /// `L = nil | cons(hd Int, tl L)` in `manager`, with its sort.
    fn list(manager: &mut TermManager) -> SortId {
        let sort = manager.sorts.mk_datatype_sort("L");
        let int = manager.sorts.int_sort;
        let cons = DataTypeConstructor {
            name: manager.intern_str("cons"),
            selectors: smallvec![
                (manager.intern_str("hd"), int),
                (manager.intern_str("tl"), sort)
            ],
        };
        let nil = DataTypeConstructor {
            name: manager.intern_str("nil"),
            selectors: smallvec![],
        };
        manager.declare_datatype("L", vec![nil, cons]);
        sort
    }

    #[test]
    fn a_selector_of_the_building_constructor_is_its_field() {
        let mut m = TermManager::new();
        let sort = list(&mut m);
        let int = m.sorts.int_sort;
        let one = m.mk_int(1);
        let l1 = m.mk_var("l1", sort);
        let cell = m.mk_dt_constructor("cons", [one, l1], sort);
        assert_eq!(m.mk_dt_selector("hd", cell, int), one);
        assert_eq!(m.mk_dt_selector("tl", cell, sort), l1);
        // `(hd nil)` is unspecified: kept as a selector node.
        let nil = m.mk_dt_constructor("nil", [], sort);
        let head_of_nil = m.mk_dt_selector("hd", nil, int);
        assert!(matches!(
            m.get(head_of_nil).map(|t| &t.kind),
            Some(TermKind::DtSelector { .. })
        ));
        // Over an opaque list, a selector node too.
        let head = m.mk_dt_selector("hd", l1, int);
        assert!(matches!(
            m.get(head).map(|t| &t.kind),
            Some(TermKind::DtSelector { .. })
        ));
    }

    #[test]
    fn a_tester_of_a_constructor_application_is_a_literal() {
        let mut m = TermManager::new();
        let sort = list(&mut m);
        let one = m.mk_int(1);
        let l1 = m.mk_var("l1", sort);
        let cell = m.mk_dt_constructor("cons", [one, l1], sort);
        assert_eq!(m.mk_dt_tester("cons", cell), m.mk_true());
        assert_eq!(m.mk_dt_tester("nil", cell), m.mk_false());
        let opaque = m.mk_dt_tester("nil", l1);
        assert!(matches!(
            m.get(opaque).map(|t| &t.kind),
            Some(TermKind::DtTester { .. })
        ));
    }

    /// A node interned past the builder (the pass's input) folds too.
    #[test]
    fn the_pass_folds_an_accessor_interned_unfolded() {
        let mut m = TermManager::new();
        let sort = list(&mut m);
        let int = m.sorts.int_sort;
        let bool_sort = m.sorts.bool_sort;
        let one = m.mk_int(1);
        let l1 = m.mk_var("l1", sort);
        let cell = m.mk_dt_constructor("cons", [one, l1], sort);
        let hd = m.intern_str("hd");
        let nil_name = m.intern_str("nil");
        let raw_head = m.intern_term(
            TermKind::DtSelector {
                selector: hd,
                arg: cell,
            },
            int,
        );
        let raw_tester = m.intern_term(
            TermKind::DtTester {
                constructor: nil_name,
                arg: cell,
            },
            bool_sort,
        );
        assert_eq!(m.fold_constructor_accessors(raw_head), one);
        assert_eq!(m.fold_constructor_accessors(raw_tester), m.mk_false());
    }

    /// What a printed model's certificate needs: `(fst p)` once `p` is its
    /// value, and a nested accessor chain in one call.
    #[test]
    fn a_substituted_value_folds_through_nested_accessors() {
        let mut m = TermManager::new();
        let sort = list(&mut m);
        let int_sort = m.sorts.int_sort;
        let seven = m.mk_int(7);
        let l1 = m.mk_var("l1", sort);
        let l2 = m.mk_var("l2", sort);
        let tail = m.mk_dt_selector("tl", l1, sort);
        let head_of_tail = m.mk_dt_selector("hd", tail, int_sort);
        let inner = m.mk_dt_constructor("cons", [seven, l2], sort);
        let value = m.mk_dt_constructor("cons", [seven, inner], sort);
        let mut subst: FxHashMap<_, _> = FxHashMap::default();
        subst.insert(l1, value);
        let closed = m.substitute(head_of_tail, &subst);
        assert_eq!(m.fold_constructor_accessors(closed), seven);
    }
}
