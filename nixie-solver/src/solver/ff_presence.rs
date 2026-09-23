//! Conservative field-presence survey, independent of the solving fragment.
//!
//! Result sorts matter even when there is no field constant or variable:
//! applications, array reads, and datatype selectors can all return fields.
//! Containers also inherit finite-domain obligations from their element sorts.

use crate::prelude::*;
use nixie_core::ast::get_children;
use nixie_core::{SortId, SortKind, TermId, TermKind, TermManager};

/// Includes fields in nested sorts. Malformed reachable nodes fail closed.
/// No-field workloads take the constant-time field-table fast path.
pub(super) fn contains(roots: &[TermId], manager: &TermManager) -> bool {
    if manager.sorts.field_table().is_empty() {
        return false;
    }
    enum Frame {
        Term(TermId),
        Sort(SortId),
    }
    let mut stack: Vec<_> = roots.iter().copied().map(Frame::Term).collect();
    let mut terms = FxHashSet::default();
    let mut sorts = FxHashSet::default();
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Term(id) => {
                if !terms.insert(id) {
                    continue;
                }
                let Some(term) = manager.get(id) else {
                    return true;
                };
                if matches!(
                    term.kind,
                    TermKind::FfConst { .. }
                        | TermKind::FfAdd(_)
                        | TermKind::FfMul(_)
                        | TermKind::FfNeg(_)
                        | TermKind::FfBitsum(_)
                ) {
                    return true;
                }
                stack.extend(get_children(&term.kind).into_iter().map(Frame::Term));
                stack.push(Frame::Sort(term.sort));
            }
            Frame::Sort(id) => {
                if !sorts.insert(id) {
                    continue;
                }
                let Some(sort) = manager.sorts.get(id) else {
                    return true;
                };
                match &sort.kind {
                    SortKind::FiniteField(_) => return true,
                    SortKind::Array { domain, range } => {
                        stack.push(Frame::Sort(*domain));
                        stack.push(Frame::Sort(*range));
                    }
                    SortKind::Set(e) | SortKind::Bag(e) | SortKind::Seq(e) => {
                        stack.push(Frame::Sort(*e));
                    }
                    SortKind::Datatype(name) => {
                        let name = manager.sorts.resolve_spur(*name);
                        let Some(def) = manager.sorts.get_datatype(name) else {
                            return true;
                        };
                        for constructor in &def.constructors {
                            stack
                                .extend(constructor.selectors.iter().map(|(_, s)| Frame::Sort(*s)));
                        }
                    }
                    SortKind::Parametric { name, args } => {
                        stack.extend(args.iter().copied().map(Frame::Sort));
                        let name = manager.sorts.resolve_spur(*name);
                        if let Some(def) = manager.sorts.get_datatype(name) {
                            for constructor in &def.constructors {
                                stack.extend(
                                    constructor.selectors.iter().map(|(_, s)| Frame::Sort(*s)),
                                );
                            }
                        }
                    }
                    SortKind::Bool
                    | SortKind::Int
                    | SortKind::Real
                    | SortKind::String
                    | SortKind::BitVec(_)
                    | SortKind::FloatingPoint { .. }
                    | SortKind::RoundingMode
                    | SortKind::Uninterpreted(_)
                    | SortKind::Parameter(_) => {}
                }
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_presence_checks_results_arguments_and_nested_sorts() {
        let mut manager = TermManager::new();
        let field = manager.sorts.binary_field(7u32.into()).unwrap();
        let integer = manager.mk_var("i", manager.sorts.int_sort);
        assert!(!contains(&[integer], &manager));
        let result = manager.mk_apply("f", [integer], field);
        assert!(contains(&[result], &manager));
        let predicate = manager.mk_apply("p", [result], manager.sorts.bool_sort);
        assert!(contains(&[predicate], &manager));
        for sort in [
            manager.sorts.set(field),
            manager.sorts.bag(field),
            manager.sorts.seq(field),
            manager.sorts.array(field, manager.sorts.bool_sort),
            manager.sorts.array(manager.sorts.bool_sort, field),
        ] {
            let value = manager.mk_var("container", sort);
            assert!(contains(&[value], &manager));
        }
    }

    #[test]
    fn field_presence_walks_deep_sorts_iteratively() {
        let mut manager = TermManager::new();
        let mut sort = manager.sorts.binary_field(7u32.into()).unwrap();
        for _ in 0..20_000 {
            sort = manager.sorts.array(manager.sorts.bool_sort, sort);
        }
        let value = manager.mk_var("deep", sort);
        assert!(contains(&[value], &manager));
    }
    #[test]
    fn field_presence_follows_recursive_datatype_definitions_and_parameters() {
        use nixie_core::sort::DataTypeConstructor;
        let mut manager = TermManager::new();
        let field = manager.sorts.binary_field(7u32.into()).unwrap();
        for (name, element, expected) in [
            ("FieldList", field, true),
            ("IntegerList", manager.sorts.int_sort, false),
        ] {
            let list = manager.sorts.mk_datatype_sort(name);
            let cons = manager.sorts.intern_str("cons");
            let nil = manager.sorts.intern_str("nil");
            let head = manager.sorts.intern_str("head");
            let tail = manager.sorts.intern_str("tail");
            manager.sorts.declare_datatype(
                name,
                vec![
                    DataTypeConstructor {
                        name: cons,
                        selectors: smallvec::smallvec![(head, element), (tail, list)],
                    },
                    DataTypeConstructor {
                        name: nil,
                        selectors: smallvec::smallvec![],
                    },
                ],
            );
            let value = manager.mk_var(name, list);
            assert_eq!(contains(&[value], &manager), expected);
        }
        manager.sorts.declare_parametric_sort("Container", 1);
        let sort = manager
            .sorts
            .instantiate_parametric_sort("Container", &[field])
            .unwrap();
        let value = manager.mk_var("parameterized", sort);
        assert!(contains(&[value], &manager));
    }
}
