//! Exact bounded cardinalities and exhaustive small array-index domains.

use super::ArrayStructure;
#[allow(unused_imports)]
use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::sort::{SortId, SortKind};
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Cardinality {
    Exact(usize),
    AboveCap,
    Unknown,
}

fn bounded(value: usize, cap: usize) -> Cardinality {
    if value <= cap {
        Cardinality::Exact(value)
    } else {
        Cardinality::AboveCap
    }
}

/// Only exact values at or below `cap` can justify a pigeonhole refutation.
/// Larger cardinalities and unknown cardinalities never become small numbers.
/// The explicit stack also handles deeply nested array sorts.
fn sort_cardinality(manager: &TermManager, root: SortId, cap: usize) -> Cardinality {
    enum Frame {
        Visit(SortId),
        Array(SortId, SortId, SortId),
    }
    let mut stack = vec![Frame::Visit(root)];
    let mut values = FxHashMap::default();
    let mut in_progress = FxHashSet::default();
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Visit(sort) => {
                if values.contains_key(&sort) {
                    continue;
                }
                if !in_progress.insert(sort) {
                    return Cardinality::Unknown;
                }
                let Some(data) = manager.sorts.get(sort) else {
                    return Cardinality::Unknown;
                };
                let value = match data.kind {
                    SortKind::Bool => bounded(2, cap),
                    SortKind::BitVec(0) => Cardinality::Unknown,
                    SortKind::BitVec(width) => match 1usize.checked_shl(width) {
                        Some(size) => bounded(size, cap),
                        None => Cardinality::AboveCap,
                    },
                    SortKind::RoundingMode => bounded(5, cap),
                    SortKind::Array { domain, range } => {
                        stack.push(Frame::Array(sort, domain, range));
                        stack.push(Frame::Visit(range));
                        stack.push(Frame::Visit(domain));
                        continue;
                    }
                    SortKind::Int
                    | SortKind::Real
                    | SortKind::String
                    | SortKind::FloatingPoint { .. }
                    | SortKind::Uninterpreted(_)
                    | SortKind::Parameter(_)
                    | SortKind::Parametric { .. }
                    | SortKind::Datatype(_)
                    | SortKind::Set(_)
                    | SortKind::Bag(_)
                    | SortKind::FiniteField(_)
                    | SortKind::Seq(_) => Cardinality::Unknown,
                };
                in_progress.remove(&sort);
                values.insert(sort, value);
            }
            Frame::Array(sort, domain, range) => {
                let domain = values.get(&domain).copied().unwrap_or(Cardinality::Unknown);
                let range = values.get(&range).copied().unwrap_or(Cardinality::Unknown);
                let value = match (domain, range) {
                    (Cardinality::Unknown, _) | (_, Cardinality::Unknown) => Cardinality::Unknown,
                    (_, Cardinality::Exact(1)) => bounded(1, cap),
                    // Every SMT sort is nonempty. Increasing either a positive
                    // exponent or a base >= 2 cannot decrease the cardinality.
                    (_, Cardinality::AboveCap) => Cardinality::AboveCap,
                    (Cardinality::AboveCap, Cardinality::Exact(base)) if base >= 2 => {
                        Cardinality::AboveCap
                    }
                    (Cardinality::Exact(exponent), Cardinality::Exact(base)) => {
                        bounded_power(base, exponent, cap)
                    }
                    _ => Cardinality::Unknown,
                };
                in_progress.remove(&sort);
                values.insert(sort, value);
            }
        }
    }
    values.get(&root).copied().unwrap_or(Cardinality::Unknown)
}

fn bounded_power(mut base: usize, mut exponent: usize, cap: usize) -> Cardinality {
    let mut result = 1usize;
    while exponent != 0 {
        if exponent & 1 != 0 {
            let Some(next) = result.checked_mul(base).filter(|&value| value <= cap) else {
                return Cardinality::AboveCap;
            };
            result = next;
        }
        exponent >>= 1;
        if exponent != 0 {
            let Some(next) = base.checked_mul(base).filter(|&value| value <= cap) else {
                return Cardinality::AboveCap;
            };
            base = next;
        }
    }
    bounded(result, cap)
}

/// An n-ary distinct atom is false when n exceeds the exact array cardinality.
/// The conclusion is universally valid, including conditional/negative atoms.
pub(super) fn build_cardinality_refutations(
    manager: &mut TermManager,
    collected: &ArrayStructure,
    candidates: &mut Vec<TermId>,
) {
    for &atom in &collected.distinct_atoms {
        let Some(TermKind::Distinct(args)) = manager.get(atom).map(|node| &node.kind) else {
            continue;
        };
        if args.len() < 2 {
            continue;
        }
        let Some(sort) = args
            .first()
            .and_then(|arg| manager.get(*arg))
            .map(|node| node.sort)
        else {
            continue;
        };
        if !manager
            .sorts
            .get(sort)
            .is_some_and(|s| matches!(s.kind, SortKind::Array { .. }))
            || args
                .iter()
                .any(|arg| manager.get(*arg).is_none_or(|node| node.sort != sort))
        {
            continue;
        }
        if matches!(
            sort_cardinality(manager, sort, args.len() - 1),
            Cardinality::Exact(_)
        ) {
            candidates.push(manager.mk_not(atom));
        }
    }
}

/// Complete value lists for Bool and bit-vector domains of at most eight values.
/// Other sorts continue to use the existing extensionality-witness path.
pub(super) fn enumerable_index_values(
    manager: &mut TermManager,
    sort: SortId,
) -> Option<Vec<TermId>> {
    match manager.sorts.get(sort)?.kind {
        SortKind::Bool => Some(vec![manager.mk_false(), manager.mk_true()]),
        SortKind::BitVec(width @ 1..=3) => Some(
            (0..1u32 << width)
                .map(|v| manager.mk_bitvec(v, width))
                .collect(),
        ),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn malformed_sort_graphs_decline_cardinality() {
        let mut manager = TermManager::new();
        assert_eq!(
            sort_cardinality(&manager, SortId(u32::MAX), 16),
            Cardinality::Unknown
        );
        let zero_width = manager.sorts.bitvec(0);
        assert_eq!(
            sort_cardinality(&manager, zero_width, 16),
            Cardinality::Unknown
        );
        let next = (0..1000)
            .map(SortId)
            .find(|&id| manager.sorts.get(id).is_none())
            .expect("next ID");
        let cyclic = manager.sorts.array(next, manager.sorts.bool_sort);
        assert_eq!(cyclic, next);
        assert_eq!(sort_cardinality(&manager, cyclic, 16), Cardinality::Unknown);
    }

    #[test]
    fn pigeonhole_refutes_only_more_than_the_exact_capacity() {
        let mut manager = TermManager::new();
        let boolean = manager.sorts.bool_sort;
        let array = manager.sorts.array(boolean, boolean);
        let terms: Vec<_> = (0..5)
            .map(|i| manager.mk_var(&format!("a{i}"), array))
            .collect();
        for count in [4, 5] {
            let atom = manager.mk_distinct(terms[..count].iter().copied());
            let structure = ArrayStructure {
                distinct_atoms: vec![atom],
                ..Default::default()
            };
            let mut lemmas = Vec::new();
            build_cardinality_refutations(&mut manager, &structure, &mut lemmas);
            if count == 4 {
                assert!(lemmas.is_empty());
            } else {
                assert_eq!(lemmas, vec![manager.mk_not(atom)]);
            }
        }
    }

    #[test]
    fn finite_array_cardinalities_are_exact_and_never_saturate_downward() {
        let mut manager = TermManager::new();
        let boolean = manager.sorts.bool_sort;
        let bv2 = manager.sorts.bitvec(2);
        let bv1 = manager.sorts.bitvec(1);
        let wide = manager.sorts.bitvec(129);
        let sixteen = manager.sorts.array(bv2, bv1);
        assert_eq!(
            sort_cardinality(&manager, sixteen, 15),
            Cardinality::AboveCap
        );
        assert_eq!(
            sort_cardinality(&manager, sixteen, 16),
            Cardinality::Exact(16)
        );
        assert_eq!(
            sort_cardinality(&manager, wide, usize::MAX),
            Cardinality::AboveCap
        );
        let many = manager.sorts.array(wide, boolean);
        assert_eq!(
            sort_cardinality(&manager, many, usize::MAX),
            Cardinality::AboveCap
        );
        let modes_to_bool = manager
            .sorts
            .array(manager.sorts.rounding_mode_sort, boolean);
        assert_eq!(
            sort_cardinality(&manager, modes_to_bool, 32),
            Cardinality::Exact(32)
        );
        let bool_to_modes = manager
            .sorts
            .array(boolean, manager.sorts.rounding_mode_sort);
        assert_eq!(
            sort_cardinality(&manager, bool_to_modes, 25),
            Cardinality::Exact(25)
        );
        let four = manager.sorts.array(boolean, boolean);
        let nested = manager.sorts.array(four, four);
        assert_eq!(
            sort_cardinality(&manager, nested, 256),
            Cardinality::Exact(256)
        );
        let infinite = manager.sorts.array(boolean, manager.sorts.int_sort);
        assert_eq!(
            sort_cardinality(&manager, infinite, usize::MAX),
            Cardinality::Unknown
        );
        assert_eq!(
            bounded_power(2, usize::MAX, usize::MAX),
            Cardinality::AboveCap
        );
    }

    #[test]
    fn nested_sort_cardinality_uses_a_heap_stack() {
        std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                let mut manager = TermManager::new();
                let boolean = manager.sorts.bool_sort;
                let mut sort = boolean;
                for _ in 0..10000 {
                    sort = manager.sorts.array(boolean, sort);
                }
                assert_eq!(sort_cardinality(&manager, sort, 16), Cardinality::AboveCap);
            })
            .expect("thread")
            .join()
            .expect("bounded stack");
    }

    #[test]
    fn only_complete_small_domains_are_enumerated() {
        let mut manager = TermManager::new();
        let boolean = manager.sorts.bool_sort;
        assert_eq!(
            enumerable_index_values(&mut manager, boolean).expect("Bool"),
            vec![manager.mk_false(), manager.mk_true()]
        );
        for width in 1..=3 {
            let sort = manager.sorts.bitvec(width);
            let values = enumerable_index_values(&mut manager, sort).expect("small BV");
            assert_eq!(values.len(), 1 << width);
            for (index, value) in values.iter().enumerate() {
                assert_eq!(*value, manager.mk_bitvec(index as u32, width));
            }
        }
        for width in [4, 64, 129] {
            let sort = manager.sorts.bitvec(width);
            assert!(enumerable_index_values(&mut manager, sort).is_none());
        }
    }
}
